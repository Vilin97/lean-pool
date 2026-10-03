/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2Induction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.TimeIncrement.Recursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Composition
public import Mathlib.Analysis.Real.Pi.Bounds

/-! The first stream-regularity increment estimate from the finite-overlap stream recursion.

The only analytic input left explicit here is the source-form App. B.2
estimate for the inverse flow, applied after the induction bound at the
previous scale. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
open scoped ContDiff BigOperators

noncomputable section

namespace AVenhance.Infra.Construction

/-- The Section 2 scalar recurrences `e.recurrence`, including their initial
values. -/
structure Section2Scales {β : ℝ} (I : Ingredients β)
    (R M : ℕ → ℝ) : Prop where
  radius_zero : R 0 = 1
  amplitude_zero : M 0 = 1
  radius_step : ∀ m : ℕ, R (m + 1) =
    (9 / 4) * R m + 2 ^ 7 * (epsilon β I.Λ (m + 1))⁻¹
  amplitude_step : ∀ m : ℕ, M (m + 1) = M m +
    2 ^ 7 * a β I.Λ (m + 1) * epsilon β I.Λ (m + 1) ^ 2 * R m ^ 2 +
      2 ^ 18 * a β I.Λ (m + 1)

/-- The source induction hypothesis `e.indyhyp` at one scale. -/
def Section2StreamInductionHypothesis {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (R M : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
    FaaDiBruno.snorm (Φ m t) n (R m) ≤
      ENNReal.ofReal (M m * (R m)⁻¹ ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))

/-- App. B.2 in the source seminorm, specialized to the inverse flow in the
stream recursion. Its input is exactly `e.indyhyp`; its output is the
`e.flowinv2` bound on the radius `9 R_{m-1}/8`. -/
structure AppB2InverseFlowData {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsStreamSeq I Φ)
    (R M : ℕ → ℝ) : Prop where
  inverse_spatial_smooth : ∀ m : ℕ, 1 ≤ m → ∀ s u : ℝ,
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
      constructionFlowInv hseq (m - 1) (s + u) x s)
  inverse_transport_estimate : ∀ m : ℕ, 1 ≤ m →
    Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1) →
    ∀ s u : ℝ, |u| ≤ (2 : ℝ) ^ (-6 : ℤ) * (M (m - 1))⁻¹ →
    ∀ n : ℕ, 1 ≤ n →
      FaaDiBruno.snorm
        (fun x : Vec 2 => constructionFlowInv hseq (m - 1) (s + u) x s)
        n ((9 / 8) * R (m - 1)) ≤
          ENNReal.ofReal (5 * (8 / 9 : ℝ) * (R (m - 1))⁻¹)

/-- Time cutoff multiplying a stream recursion increment. -/
def RecursionIncrement.streamRecursionCutoff {β : ℝ} (I : Ingredients β) (m : ℕ)
    (k : ℤ) (t : ℝ) : ℝ :=
  I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t

theorem RecursionIncrement.zetaMK_nonzero_distance {β : ℝ} {I : Ingredients β}
    (m : ℕ) (k : ℤ) (t : ℝ) (hne : I.zetaMK m k t ≠ 0) :
    |t - (k : ℝ) * tau β I.Λ m| ≤ (2 / 3 : ℝ) * tau β I.Λ m := by
  have hτ := I.tau_pos' m
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hpos : 0 < I.zeta u := by
    change I.zeta u ≠ 0 at hne
    exact lt_of_le_of_ne (I.zeta_nonneg u) (Ne.symm hne)
  have hle := I.zeta_le_ind u
  have hu : u ∈ Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
    by_contra hnot
    have hzero : indIcc (-(2 / 3 : ℝ)) (2 / 3) u = 0 := by
      simp [indIcc, hnot]
    rw [hzero] at hle
    linarith
  have hbound : |u| ≤ 2 / 3 := abs_le.mpr ⟨hu.1, hu.2⟩
  rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at hbound
  simpa [abs_of_pos hτ] using hbound

theorem RecursionIncrement.active_recursion_index {β : ℝ} {I : Ingredients β}
    (m : ℕ) (k : ℤ) (r t : ℝ)
    (hclose : |r - t| < tau β I.Λ m / 6)
    (hactive : RecursionIncrement.streamRecursionCutoff I m k r ≠ 0) :
    k ∈ Set.Icc (⌊t / tau β I.Λ m⌋ : ℤ)
      ((⌊t / tau β I.Λ m⌋ : ℤ) + 1) := by
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hzk : I.zetaMK m k r ≠ 0 := by
    intro hz
    apply hactive
    simp [RecursionIncrement.streamRecursionCutoff, hz]
  have hdist := RecursionIncrement.zetaMK_nonzero_distance m k r hzk
  have htriangle : |t - (k : ℝ) * tau β I.Λ m| < (5 / 6 : ℝ) * tau β I.Λ m := by
    calc
      |t - (k : ℝ) * tau β I.Λ m| =
          |(t - r) + (r - (k : ℝ) * tau β I.Λ m)| := by congr 1; ring
      _ ≤ |t - r| + |r - (k : ℝ) * tau β I.Λ m| := abs_add_le _ _
      _ < tau β I.Λ m / 6 + (2 / 3) * tau β I.Λ m := by
        have hclose' : |t - r| < tau β I.Λ m / 6 := by
          simpa [abs_sub_comm] using hclose
        nlinarith [hclose', hdist]
      _ = (5 / 6 : ℝ) * tau β I.Λ m := by ring
  have hquot : |t / tau β I.Λ m - (k : ℝ)| < 1 := by
    have hscaled : |t / tau β I.Λ m - (k : ℝ)| < 5 / 6 := by
      have hEq : t / tau β I.Λ m - (k : ℝ) =
          (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m := by field_simp
      rw [hEq, abs_div, abs_of_pos hτ]
      exact (div_lt_iff₀ hτ).2 htriangle
    linarith
  have hquot' := abs_lt.mp hquot
  have hfloorle : (⌊t / tau β I.Λ m⌋ : ℝ) ≤ t / tau β I.Λ m :=
    Int.floor_le (t / tau β I.Λ m)
  have hfloorlt : t / tau β I.Λ m < (⌊t / tau β I.Λ m⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one (t / tau β I.Λ m)
  simp only [Set.mem_Icc]
  constructor
  · by_contra hnot
    have hk : k < ⌊t / tau β I.Λ m⌋ := lt_of_not_ge hnot
    have hk' : (k : ℝ) + 1 ≤ (⌊t / tau β I.Λ m⌋ : ℝ) := by
      exact_mod_cast (show k + 1 ≤ ⌊t / tau β I.Λ m⌋ by omega)
    linarith [hquot'.2, hfloorle]
  · by_contra hnot
    have hk : ⌊t / tau β I.Λ m⌋ + 2 ≤ k := by omega
    have hk' : (⌊t / tau β I.Λ m⌋ : ℝ) + 2 ≤ (k : ℝ) := by
      exact_mod_cast hk
    have hquotlow : (k : ℝ) - 1 < t / tau β I.Λ m := by
      linarith [hquot'.1]
    linarith [hfloorlt]

theorem section2_radius_nonneg {β : ℝ} {I : Ingredients β}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M) (m : ℕ) : 0 ≤ R m := by
  induction m with
  | zero => rw [hscales.radius_zero]; norm_num
  | succ m ih =>
      rw [hscales.radius_step m]
      have he := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
        (m := m + 1)
      positivity

theorem section2_radius_pos {β : ℝ} {I : Ingredients β}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M) (m : ℕ) : 0 < R m := by
  induction m with
  | zero => rw [hscales.radius_zero]; norm_num
  | succ m ih =>
      rw [hscales.radius_step m]
      have he := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
        (m := m + 1)
      positivity

theorem section2_amplitude_pos {β : ℝ} {I : Ingredients β}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M) (m : ℕ) : 0 < M m := by
  induction m with
  | zero => rw [hscales.amplitude_zero]; norm_num
  | succ m ih =>
      rw [hscales.amplitude_step m]
      have he := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
        (m := m + 1)
      have ha : 0 ≤ a β I.Λ (m + 1) := Real.rpow_nonneg he.le _
      positivity

theorem RecursionIncrement.section2_recursion_radius_bound {β : ℝ} {I : Ingredients β}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M) (m : ℕ) (hm : 1 ≤ m) :
    (9 / 8) * R (m - 1) + 20 * Real.pi * (epsilon β I.Λ m)⁻¹ ≤
      2 ^ 7 * (epsilon β I.Λ m)⁻¹ := by
  have hR : R (m - 1) ≤ 131 * (epsilon β I.Λ (m - 1))⁻¹ := by
    by_cases hm1 : m = 1
    · subst m
      rw [hscales.radius_zero]
      have he0 : epsilon β I.Λ 0 = 1 := by simp [epsilon]
      rw [he0]
      norm_num
    · have hmPrev : 1 ≤ m - 1 := by omega
      have hbound := radius_recurrence_bound I.one_lt_beta I.beta_lt
        I.two_pow_seven_le R hscales.radius_zero hscales.radius_step
        (m := m - 1) hmPrev
      norm_num at hbound ⊢
      exact hbound
  have hePrev := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have he := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hmin := Ingredients.epsilon_minsep I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m - 1)
  have hΛ : (128 : ℝ) ≤ (I.Λ : ℝ) := by exact_mod_cast I.two_pow_seven_le
  have hsep : epsilon β I.Λ m ≤ (1 / 128 : ℝ) * epsilon β I.Λ (m - 1) := by
    have hΛstep : (I.Λ : ℝ) * epsilon β I.Λ m ≤ epsilon β I.Λ (m - 1) := by
      simpa [Nat.sub_add_cancel hm] using hmin
    have hstep : epsilon β I.Λ m * 128 ≤ epsilon β I.Λ (m - 1) := by
      calc
        epsilon β I.Λ m * 128 ≤ epsilon β I.Λ m * (I.Λ : ℝ) :=
          mul_le_mul_of_nonneg_left hΛ he.le
        _ ≤ epsilon β I.Λ (m - 1) := by
          rw [mul_comm]
          exact hΛstep
    nlinarith
  have hRscaled : epsilon β I.Λ m * R (m - 1) ≤ (131 : ℝ) / 128 := by
    calc
      epsilon β I.Λ m * R (m - 1) ≤
          epsilon β I.Λ m * (131 * (epsilon β I.Λ (m - 1))⁻¹) :=
            mul_le_mul_of_nonneg_left hR (he.le)
      _ = 131 * (epsilon β I.Λ m / epsilon β I.Λ (m - 1)) := by
        field_simp [he.ne', hePrev.ne']
      _ ≤ 131 / 128 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : 0 ≤ (131 : ℝ))
        apply (div_le_iff₀ hePrev).2
        nlinarith [hsep]
  have hmul := mul_le_mul_of_nonneg_left hRscaled (by norm_num : 0 ≤ (9 / 8 : ℝ))
  have htarget : (9 / 8 : ℝ) * ((131 : ℝ) / 128) + 20 * Real.pi ≤ 128 := by
    nlinarith [Real.pi_lt_four]
  have hscaled : (epsilon β I.Λ m) *
      ((9 / 8) * R (m - 1) + 20 * Real.pi * (epsilon β I.Λ m)⁻¹) ≤ 128 := by
    have hcancel : epsilon β I.Λ m *
        (20 * Real.pi * (epsilon β I.Λ m)⁻¹) = 20 * Real.pi := by
      field_simp [he.ne']
    calc
      _ = (9 / 8) * (epsilon β I.Λ m * R (m - 1)) + 20 * Real.pi := by
        rw [mul_add, show epsilon β I.Λ m * ((9 / 8) * R (m - 1)) =
          (9 / 8) * (epsilon β I.Λ m * R (m - 1)) by ring, hcancel]
      _ ≤ (9 / 8) * ((131 : ℝ) / 128) + 20 * Real.pi :=
        add_le_add hmul le_rfl
      _ ≤ 128 := htarget
  apply (le_div_iff₀ he).2
  rw [show (2 : ℝ) ^ 7 = 128 by norm_num]
  nlinarith [hscaled]

theorem RecursionIncrement.composition_radius_identity {R e : ℝ} (hR : 0 < R) (he : 0 < e) :
    ((9 / 8) * R) *
      (1 + 2 * (5 * (8 / 9 : ℝ) * R⁻¹) * (2 * Real.pi / e)) =
      (9 / 8) * R + 20 * Real.pi / e := by
  field_simp [hR.ne', he.ne']
  ring

/-- The App. B.2 inverse estimate and App. B.3 composition estimate bound one
profile term at the radius used by the induction. -/
theorem section2_composed_profile_barNorm_bound {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (s u : ℝ) (hu : |u| ≤ (2 : ℝ) ^ (-6 : ℤ) * (M (m - 1))⁻¹)
    (k : ℤ) (n : ℕ) :
    barNorm n ((9 / 8) * R (m - 1) +
      20 * Real.pi / epsilon β I.Λ m)
      (fun x : Vec 2 => psi β I.Λ m k
        (constructionFlowInv hseq (m - 1) (s + u) x s)) ≤
      ENNReal.ofReal (5 * a β I.Λ m * epsilon β I.Λ m ^ 2) := by
  let g : Vec 2 → Vec 2 := fun x =>
    constructionFlowInv hseq (m - 1) (s + u) x s
  let Rh : ℝ := 2 * Real.pi / epsilon β I.Λ m
  let Rg : ℝ := (9 / 8) * R (m - 1)
  let Cg : ℝ := 5 * (8 / 9 : ℝ) * (R (m - 1))⁻¹
  let Ch : ℝ := 5 * a β I.Λ m * epsilon β I.Λ m ^ 2
  have hRprev : 0 < R (m - 1) := section2_radius_pos hscales (m - 1)
  have he : 0 < epsilon β I.Λ m :=
    Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hRh : 0 < Rh := by dsimp [Rh]; positivity
  have hRg : 0 < Rg := by dsimp [Rg]; positivity
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  have hCh : 0 < Ch := by
    dsimp [Ch]
    exact mul_pos (mul_pos (by norm_num) (Cutoff.a_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le)) (pow_pos he 2)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (psi β I.Λ m k) :=
    psi_timeIncrement_contDiff (β := β) (I := I) m k
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    dsimp [g]
    exact happB2.inverse_spatial_smooth m hm s u
  have hH : ∀ j : ℕ, j ≤ n →
      FaaDiBruno.snorm (psi β I.Λ m k) j Rh ≤ ENNReal.ofReal Ch := by
    intro j hj
    rw [← barNorm_eq_snorm (psi β I.Λ m k) j Rh (hψ.of_le (by simp))]
    exact psi_barNorm_le I m k j (by dsimp [Rh]; exact le_rfl)
  have hG : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      FaaDiBruno.snorm g j Rg ≤ ENNReal.ofReal Cg := by
    intro j hj1 hjn
    dsimp [g, Rg, Cg]
    exact happB2.inverse_transport_estimate m hm hprev s u hu j hj1
  have hcomp := FaaDiBruno.compositionEstimate10528
    (d := 2) (m := n) (psi β I.Λ m k) g
    (hψ.of_le (by simp)) (hg.of_le (by simp))
    hCh hCg hRh hRg hH hG n le_rfl
  have hcompRadius := RecursionIncrement.composition_radius_identity hRprev he
  have hradius : Rg * (1 + (2 : ℝ) * Cg * Rh) =
      (9 / 8) * R (m - 1) + 20 * Real.pi / epsilon β I.Λ m := by
    dsimp [Rg, Cg, Rh]
    exact hcompRadius
  have hcomp' :
      FaaDiBruno.snorm (psi β I.Λ m k ∘ g) n
        ((9 / 8) * R (m - 1) + 20 * Real.pi / epsilon β I.Λ m) ≤
        ENNReal.ofReal Ch := by
    change FaaDiBruno.snorm (psi β I.Λ m k ∘ g) n
      (Rg * (1 + (2 : ℝ) * Cg * Rh)) ≤ ENNReal.ofReal Ch at hcomp
    rw [hradius] at hcomp
    exact hcomp
  have hcompSmooth : ContDiff ℝ n (psi β I.Λ m k ∘ g) :=
    (hψ.comp hg).of_le (by simp)
  change barNorm n ((9 / 8) * R (m - 1) +
      20 * Real.pi / epsilon β I.Λ m) (psi β I.Λ m k ∘ g) ≤ _
  rw [barNorm_eq_snorm (psi β I.Λ m k ∘ g) n
    ((9 / 8) * R (m - 1) + 20 * Real.pi / epsilon β I.Λ m) hcompSmooth]
  simpa [g, Ch, Function.comp_def] using hcomp'

/-- Multiplication by a spatially constant cutoff in `[0,1]` does not increase
the seminorm. -/
theorem RecursionIncrement.barNorm_mul_const_Icc_le {f : Vec 2 → ℝ} {n : ℕ} {R c : ℝ}
    (hf : ContDiff ℝ n f) (hc : c ∈ Set.Icc 0 1) :
    barNorm n R (fun x => c * f x) ≤ barNorm n R f := by
  have hcf : ContDiff ℝ n (fun x : Vec 2 => c * f x) := contDiff_const.mul hf
  rw [barNorm_eq_pointwise _ n R hcf, barNorm_eq_pointwise f n R hf]
  have hderiv (J : Fin n → Fin 2) (x : Vec 2) :
      ‖iteratedFDeriv ℝ n (fun y : Vec 2 => c * f y) x
          (fun j => basisVec (J j))‖ₑ =
        ENNReal.ofReal c *
          ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ := by
    rw [show (fun y : Vec 2 => c * f y) = fun y => c • f y by
      funext y
      simp [smul_eq_mul]]
    rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt]
    simp [Real.enorm_of_nonneg hc.1, smul_eq_mul]
  have hinner :
      (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
        ‖iteratedFDeriv ℝ n (fun y : Vec 2 => c * f y) x
          (fun j => basisVec (J j))‖ₑ) ≤
      ENNReal.ofReal c * (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
        ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ) := by
    apply iSup_le
    intro J
    apply iSup_le
    intro x
    rw [hderiv]
    exact mul_le_mul_of_nonneg_left
      (le_iSup_of_le J (le_iSup_of_le x le_rfl)) (by positivity)
  have hcENN : ENNReal.ofReal c ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hc.2
  calc
    _ ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (ENNReal.ofReal R)⁻¹ ^ n *
            (ENNReal.ofReal c * (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
              ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ)) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal c) *
            (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
              ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ) := by ac_rfl
    _ ≤ (ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (ENNReal.ofReal R)⁻¹ ^ n * 1) *
            (⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
              ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcENN (by positivity)) (by positivity)
    _ = _ := by simp

theorem RecursionIncrement.barNorm_radius_monotone {f : Vec 2 → ℝ} {n : ℕ} {R S : ℝ}
    (hf : ContDiff ℝ n f) (hR : 0 < R) (hRS : R ≤ S) :
    barNorm n S f ≤ barNorm n R f := by
  by_cases hS : 0 < S
  · rw [barNorm_radius_change hf hR hS]
    have hratio : 0 ≤ R / S ∧ R / S ≤ 1 := by
      constructor
      · exact (div_pos hR hS).le
      · exact (div_le_one hS).2 hRS
    have hq : ENNReal.ofReal (R / S) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hratio.2
    have hq0 : 0 ≤ ENNReal.ofReal (R / S) := by positivity
    have hpAll (k : ℕ) : ENNReal.ofReal (R / S) ^ k ≤ 1 := by
      induction k with
      | zero => simp
      | succ k ih =>
          exact pow_le_one₀ hq0 hq
    have hp : ENNReal.ofReal (R / S) ^ n ≤ 1 := hpAll n
    calc
      barNorm n R f * ENNReal.ofReal (R / S) ^ n ≤ barNorm n R f * 1 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = barNorm n R f := by simp
  · have : S ≤ 0 := le_of_not_gt hS
    linarith

theorem RecursionIncrement.hatZeta_nonzero_distance {β : ℝ} {I : Ingredients β}
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ)
    (hne : I.hatZetaML m l t ≠ 0) :
    |t - (l : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m / 2 := by
  have hpos : 0 < I.hatZetaML m l t := by
    exact lt_of_le_of_ne (Infra.Section3.hatZetaML_mem_Icc I hm l t).1
      (Ne.symm hne)
  have hle := I.hatZeta_le m hm l t
  have hτp := Cutoff.tauP_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hmem : t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m) := by
    by_contra hnot
    have hz := indIcc_eq_zero_of_not_mem hnot
    rw [hz] at hle
    have hle' : I.hatZetaML m l t ≤ 0 := by
      simpa [Ingredients.hatZetaML] using hle
    exact (not_lt_of_ge hle') hpos
  rw [abs_le]
  constructor <;> nlinarith [hmem.1, hmem.2]

private theorem stream_increment_bounds_at_scale_profileBound1 :
  ∀ {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ},
    Section2Scales I R M →
      AppB2InverseFlowData I Φ hseq R M →
        ∀ (m : ℕ),
          1 ≤ m →
            Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1) →
              ∀ (t : ℝ) (n : ℕ) (hφ : IsAdmissibleStream (Φ (m - 1))),
                let d : ℤ → Vec 2 → ℝ := fun k x =>
                  I.nextStreamTerm m (Φ (m - 1)) hφ t x k;
                let E : ℝ := epsilon β I.Λ m;
                let Rcomp : ℝ := (9 / 8) * R (m - 1) + 20 * Real.pi / E;
                (∀ (k : ℤ), RecursionIncrement.streamRecursionCutoff I m k t ∈ Set.Icc 0 1) →
                  ∀ (k : ℤ), barNorm n Rcomp (d k) ≤ ENNReal.ofReal (5 * a β I.Λ m * E ^ 2)
    := by
  intro β I Φ hseq R M hscales happB2 m hm hprev t n hφ d E Rcomp hcutIcc k
  let s : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m
  let u : ℝ := t - s
  by_cases hcut : RecursionIncrement.streamRecursionCutoff I m k t = 0
  · have hd : d k = 0 := by
      funext x
      change I.nextStreamTerm m (Φ (m - 1)) hφ t x k = 0
      have hcoeff : I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t = 0 := by
        simpa [RecursionIncrement.streamRecursionCutoff] using hcut
      simp [Ingredients.nextStreamTerm, hcoeff]
    rw [hd]
    simp [barNorm]
  · have hhat : I.hatZetaML m (lIdx β I.Λ m k) t ≠ 0 := by
      intro hz
      apply hcut
      simp [RecursionIncrement.streamRecursionCutoff, hz]
    have hdist := RecursionIncrement.hatZeta_nonzero_distance hm (lIdx β I.Λ m k) t hhat
    have hMbound := full_amplitude_recurrence_bound
      I.one_lt_beta I.beta_lt I.two_pow_seven_le R M
      hscales.radius_zero hscales.amplitude_zero hscales.radius_step
      hscales.amplitude_step (m - 1)
    have hMpos := section2_amplitude_pos hscales (m - 1)
    have hwindow := tauPP_induction_window I.one_lt_beta I.beta_lt
      I.two_pow_seven_le hm hMpos hMbound
    have hu : |u| ≤ (2 : ℝ) ^ (-6 : ℤ) * (M (m - 1))⁻¹ := by
      have hu0 : |u| = |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| := by
        dsimp [u, s]
      rw [hu0]
      have hdist' : |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤
          (2 : ℝ) ^ (-6 : ℤ) * (M (m - 1))⁻¹ := by
        have hhalf : tauPP β I.Λ m / 2 ≤
            (2 : ℝ) ^ (-6 : ℤ) * (M (m - 1))⁻¹ := by
          have hsmall := hwindow.2
          nlinarith [hsmall]
        exact hdist.trans hhalf
      exact hdist'
    have hpsi := section2_composed_profile_barNorm_bound hscales happB2 m hm
      hprev s u hu k n
    have hprof' : barNorm n Rcomp
        (fun x : Vec 2 => psi β I.Λ m k
          (constructionFlowInv hseq (m - 1) t x s)) ≤
        ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) := by
      have hst : s + u = t := by dsimp [s, u]; ring
      simpa [Rcomp, E, hst] using hpsi
    have hcoeff : RecursionIncrement.streamRecursionCutoff I m k t ∈ Set.Icc 0 1 := hcutIcc k
    have hprofileSmooth : ContDiff ℝ n (fun x : Vec 2 =>
        psi β I.Λ m k (constructionFlowInv hseq (m - 1) t x s)) := by
      have hg := happB2.inverse_spatial_smooth m hm s u
      have hst : s + u = t := by dsimp [s, u]; ring
      have hprofile' : ContDiff ℝ n (fun x : Vec 2 =>
          psi β I.Λ m k (constructionFlowInv hseq (m - 1) (s + u) x s)) :=
        ((psi_timeIncrement_contDiff (β := β) (I := I) m k).comp hg).of_le
          (by simp)
      simpa only [Function.comp_apply, hst] using hprofile'
    have htermEq : d k = fun x : Vec 2 =>
          RecursionIncrement.streamRecursionCutoff I m k t *
          psi β I.Λ m k (constructionFlowInv hseq (m - 1) t x s) := by
      funext x
      dsimp [d]
      simp [Ingredients.nextStreamTerm, RecursionIncrement.streamRecursionCutoff,
        constructionFlowInv, s]
    rw [htermEq]
    exact (RecursionIncrement.barNorm_mul_const_Icc_le hprofileSmooth hcoeff).trans hprof'

/-- The finite-overlap `nextStream` recursion gives both the raw composition
radius estimate needed by the induction and the first stream-regularity increment display. -/
theorem stream_increment_bounds_at_scale {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (t : ℝ) (n : ℕ) :
    barNorm n ((9 / 8) * R (m - 1) + 20 * Real.pi / epsilon β I.Λ m)
        (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * a β I.Λ m * epsilon β I.Λ m ^ 2) ∧
    barNorm n (2 ^ 7 * (epsilon β I.Λ m)⁻¹) (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * epsilon β I.Λ m ^ β) := by
  classical
  obtain ⟨hφ, hrec⟩ := hseq.2 m hm
  have hφeq : hφ = streamSeq_isAdmissible hseq (m - 1) := Subsingleton.elim _ _
  let S : Finset ℤ :=
    {(⌊t / tau β I.Λ m⌋ : ℤ), (⌊t / tau β I.Λ m⌋ : ℤ) + 1}
  let d : ℤ → Vec 2 → ℝ := fun k x =>
    I.nextStreamTerm m (Φ (m - 1)) hφ t x k
  have hzero (k : ℤ) (hk : k ∉ S) (x : Vec 2) : d k x = 0 := by
    have hcut : RecursionIncrement.streamRecursionCutoff I m k t = 0 := by
      by_contra hne
      have hpair := RecursionIncrement.active_recursion_index m k t t
        (by have hτ := I.tau_pos' m; simp [abs_zero, hτ]) hne
      have hpair' : ⌊t / tau β I.Λ m⌋ ≤ k ∧
          k ≤ ⌊t / tau β I.Λ m⌋ + 1 := by
        simpa using hpair
      have heq : k = ⌊t / tau β I.Λ m⌋ ∨
          k = ⌊t / tau β I.Λ m⌋ + 1 := by omega
      have hmem : k ∈ S := by
        rcases heq with h | h <;> simp [S, h]
      exact hk hmem
    change I.nextStreamTerm m (Φ (m - 1)) hφ t x k = 0
    have hcoeff : I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t = 0 := by
      simpa [RecursionIncrement.streamRecursionCutoff] using hcut
    simp [Ingredients.nextStreamTerm, hcoeff]
  have hincrement :
      (fun x : Vec 2 => Φ m t x - Φ (m - 1) t x) = ∑ k ∈ S, d k := by
    funext x
    have htsum : (∑' k : ℤ, d k x) = ∑ k ∈ S, d k x := by
      exact tsum_eq_sum (s := S) (fun k hk => hzero k hk x)
    have hrecPoint : Φ m t x =
        Φ (m - 1) t x + ∑' k : ℤ, d k x := by
      have hpoint := congrFun (congrFun hrec t) x
      simpa [Ingredients.nextStream, d] using hpoint
    rw [hrecPoint, htsum]
    simp [Finset.sum_apply, sub_eq_add_neg, add_assoc]
  let E : ℝ := epsilon β I.Λ m
  let Rcomp : ℝ := (9 / 8) * R (m - 1) + 20 * Real.pi / E
  let Rout : ℝ := 2 ^ 7 * E⁻¹
  have hE : 0 < E := by
    dsimp [E]
    exact Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hRcomp : 0 < Rcomp := by
    have hRprev := section2_radius_nonneg hscales (m - 1)
    dsimp [Rcomp]
    positivity
  have hRout : 0 < Rout := by dsimp [Rout, E]; positivity
  have hRcompOut : Rcomp ≤ Rout := by
    have h := RecursionIncrement.section2_recursion_radius_bound hscales m hm
    simpa [Rcomp, Rout, E, div_eq_mul_inv] using h
  have hcutIcc (k : ℤ) : RecursionIncrement.streamRecursionCutoff I m k t ∈ Set.Icc 0 1 := by
    constructor
    · exact mul_nonneg (Infra.Section3.hatZetaML_mem_Icc I hm _ _).1
        (Infra.Section3.zetaMK_mem_Icc I k t).1
    · have ha := (Infra.Section3.hatZetaML_mem_Icc I hm
          (lIdx β I.Λ m k) t).2
      have hz := (Infra.Section3.zetaMK_mem_Icc I (m := m) k t).2
      have hhz := (Infra.Section3.zetaMK_mem_Icc I (m := m) k t).1
      dsimp [RecursionIncrement.streamRecursionCutoff]
      calc
        I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t ≤
            1 * I.zetaMK m k t := mul_le_mul_of_nonneg_right ha hhz
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hz (by norm_num)
        _ = 1 := by ring
  have htermSmooth (k : ℤ) : ContDiff ℝ n (d k) := by
    let s : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m
    let u : ℝ := t - s
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
        constructionFlowInv hseq (m - 1) (s + u) x s) :=
      happB2.inverse_spatial_smooth m hm s u
    have hprofileTop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
        psi β I.Λ m k (constructionFlowInv hseq (m - 1) (s + u) x s)) :=
      (psi_timeIncrement_contDiff (β := β) (I := I) m k).comp hg
    have hcutEq : s + u = t := by dsimp [s, u]; ring
    have hprofile : ContDiff ℝ n (fun x : Vec 2 =>
        psi β I.Λ m k (constructionFlowInv hseq (m - 1) t x s)) := by
      have hprofile' : ContDiff ℝ n (fun x : Vec 2 =>
          psi β I.Λ m k (constructionFlowInv hseq (m - 1) (s + u) x s)) :=
        hprofileTop.of_le (by simp)
      simpa only [hcutEq] using hprofile'
    have htermEq : d k = fun x : Vec 2 =>
      RecursionIncrement.streamRecursionCutoff I m k t *
          psi β I.Λ m k (constructionFlowInv hseq (m - 1) t x s) := by
      funext x
      dsimp [d]
      simp [Ingredients.nextStreamTerm, RecursionIncrement.streamRecursionCutoff,
        constructionFlowInv, s]
    rw [htermEq]
    exact contDiff_const.mul hprofile
  have hprofileBound (k : ℤ) : barNorm n Rcomp (d k) ≤
      ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) := by
    apply stream_increment_bounds_at_scale_profileBound1
    all_goals assumption
  have hsum := Infra.Construction.barNorm_sum_le S d n Rout
    (fun k hk => (htermSmooth k).of_le le_rfl)
  have hsumComp := Infra.Construction.barNorm_sum_le S d n Rcomp
    (fun k hk => (htermSmooth k).of_le le_rfl)
  have hsumCompBound : barNorm n Rcomp (∑ k ∈ S, d k) ≤
      ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by
    calc
      barNorm n Rcomp (∑ k ∈ S, d k) ≤ ∑ k ∈ S, barNorm n Rcomp (d k) := hsumComp
      _ ≤ ∑ k ∈ S, ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hprofileBound k
      _ ≤ ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by
        have hcard : S.card ≤ 2 := by simp [S]
        have ha := Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
        have hsumConst : (∑ _k ∈ S, ENNReal.ofReal (5 * a β I.Λ m * E ^ 2)) =
            (S.card : ENNReal) * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        rw [hsumConst]
        have hcard' : (S.card : ENNReal) ≤ 2 := by exact_mod_cast hcard
        calc
          (S.card : ENNReal) * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) ≤
              2 * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) :=
            mul_le_mul_of_nonneg_right hcard' (by positivity)
          _ = ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by
            calc
              2 * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) =
                  ENNReal.ofReal 2 * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) := by norm_num
              _ = ENNReal.ofReal (2 * (5 * a β I.Λ m * E ^ 2)) :=
                (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
              _ = ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by congr 1; ring
  have hsumBound : barNorm n Rout (∑ k ∈ S, d k) ≤
      ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by
    calc
      barNorm n Rout (∑ k ∈ S, d k) ≤ ∑ k ∈ S, barNorm n Rout (d k) := hsum
    _ ≤ ∑ k ∈ S, ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hmono := RecursionIncrement.barNorm_radius_monotone (htermSmooth k) hRcomp hRcompOut
      exact (hmono.trans (hprofileBound k))
    _ ≤ ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by
      have hcard : S.card ≤ 2 := by simp [S]
      have ha := Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hA : 0 ≤ 5 * a β I.Λ m * E ^ 2 := by positivity
      have hsumConst : (∑ _k ∈ S, ENNReal.ofReal (5 * a β I.Λ m * E ^ 2)) =
          (S.card : ENNReal) * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [hsumConst]
      have hcard' : (S.card : ENNReal) ≤ 2 := by exact_mod_cast hcard
      calc
        (S.card : ENNReal) * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) ≤
            2 * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
        _ = ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by
          calc
            2 * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) =
                ENNReal.ofReal 2 * ENNReal.ofReal (5 * a β I.Λ m * E ^ 2) := by norm_num
            _ = ENNReal.ofReal (2 * (5 * a β I.Λ m * E ^ 2)) :=
              (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
            _ = ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by congr 1; ring
  have hamp : a β I.Λ m * E ^ 2 = E ^ β := by
    dsimp [E]
    rw [a]
    rw [← Real.rpow_natCast (epsilon β I.Λ m) 2]
    rw [← Real.rpow_add hE]
    congr 1
    ring
  have hraw : barNorm n Rout (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by
    have hpoint : Φ m t - Φ (m - 1) t = ∑ k ∈ S, d k := by
      funext x
      exact congrFun hincrement x
    rw [hpoint]
    exact hsumBound
  have hamp10 : 10 * a β I.Λ m * E ^ 2 = 10 * E ^ β := by
    calc
      10 * a β I.Λ m * E ^ 2 = 10 * (a β I.Λ m * E ^ 2) := by ring
      _ = 10 * E ^ β := by rw [hamp]
  have hrawComp : barNorm n Rcomp (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * a β I.Λ m * E ^ 2) := by
    have hpoint : Φ m t - Φ (m - 1) t = ∑ k ∈ S, d k := by
      funext x
      exact congrFun hincrement x
    rw [hpoint]
    exact hsumCompBound
  exact ⟨by simpa [Rcomp, E] using hrawComp,
    by simpa [Rout, E, hamp10] using hraw⟩

/-- The first stream-regularity increment display at its radius, extracted from the
stronger composition-radius estimate. -/
theorem stream_increment_bound_at_scale {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ}
    {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (t : ℝ) (n : ℕ) :
    barNorm n (2 ^ 7 * (epsilon β I.Λ m)⁻¹) (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * epsilon β I.Λ m ^ β) := by
  exact (stream_increment_bounds_at_scale hscales happB2 m hm hprev t n).2

end AVenhance.Infra.Construction
