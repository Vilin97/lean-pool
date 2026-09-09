/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatTailEdit
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# The physical heat edit: diffusion is `1 - eta^2`

The diffusion variable is allowed to reach zero.  All endpoint derivatives
below are derivatives within the closed parameter domain; no extension to
negative diffusion is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.ParametricHeatTail

/-! ## Differentiation of dominated derivative chains on the closed half-line -/

section IntegralChain

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {J : ℕ → ℝ → α → ℝ}

/-- The domination is uniform in the parameter on each bounded interval. -/
def ChainDominated (J : ℕ → ℝ → α → ℝ) (μ : Measure α) : Prop :=
  ∀ n L, 0 < L → ∃ b : α → ℝ, Integrable b μ ∧
    ∀ᵐ t ∂μ, ∀ ν ∈ Icc (0 : ℝ) L, ‖J n ν t‖ ≤ b t

variable
  (hJ : ∀ᵐ t ∂μ, ∀ n ν, 0 ≤ ν →
    HasDerivWithinAt (fun u => J n u t) (J (n + 1) ν t) (Ici 0) ν)
  (hm : ∀ n ν, 0 ≤ ν → AEStronglyMeasurable (J n ν) μ)
  (hb : ChainDominated J μ)

include hJ hm hb

omit hJ in
theorem chain_integrable (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    Integrable (J n ν) μ := by
  obtain ⟨b, hi, hbound⟩ := hb n (ν + 1) (by linarith)
  exact hi.mono' (hm n ν hν)
    (hbound.mono fun t ht => ht ν ⟨hν, by linarith⟩)

theorem integral_chain_continuousOn (n : ℕ) :
    ContinuousOn (fun ν => ∫ t, J n ν t ∂μ) (Ici 0) := by
  intro ν hν
  obtain ⟨b, hi, hbound⟩ := hb n (ν + 1) (by linarith [show 0 ≤ ν from hν])
  have hev : ∀ᶠ u in 𝓝[Ici 0] ν, u ∈ Icc (0 : ℝ) (ν + 1) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show ν < ν + 1 by linarith)).filter_mono nhdsWithin_le_nhds]
      with u hu hu'
    exact ⟨hu, hu'.le⟩
  apply tendsto_integral_filter_of_dominated_convergence b
  · exact hev.mono fun u hu => hm n u hu.1
  · exact hev.mono fun u hu => hbound.mono fun t ht => ht u hu
  · exact hi
  · filter_upwards [hJ] with t ht
    exact (ht n ν hν).continuousWithinAt

theorem integral_chain_hasDerivAt (n : ℕ) {ν : ℝ} (hν : 0 < ν) :
    HasDerivAt (fun u => ∫ t, J n u t ∂μ) (∫ t, J (n + 1) ν t ∂μ) ν := by
  obtain ⟨b, hi, hbound⟩ := hb (n + 1) (2 * ν + 1) (by linarith)
  have hball : ∀ u ∈ Metric.ball ν (ν / 2),
      0 < u ∧ u ≤ 2 * ν + 1 := by
    intro u hu
    have hd : |u - ν| < ν / 2 := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hu
    rcases abs_lt.mp hd with ⟨hl, hr⟩
    constructor <;> linarith
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u t => J n u t) (F' := fun u t => J (n + 1) u t)
    (bound := b) (μ := μ) (Metric.ball_mem_nhds ν (show 0 < ν / 2 by linarith))
    (by
      filter_upwards [isOpen_Ioi.mem_nhds hν] with u hu
      exact hm n u (show 0 < u from hu).le)
    (chain_integrable hm hb n hν.le) (hm (n + 1) ν hν.le)
    (hbound.mono fun t ht u hu => ht u ⟨(hball u hu).1.le, (hball u hu).2⟩)
    hi (by
      filter_upwards [hJ] with t ht
      intro u hu
      exact (ht n u (hball u hu).1.le).hasDerivAt (Ici_mem_nhds (hball u hu).1))).2

theorem integral_chain_hasDerivWithinAt (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    HasDerivWithinAt (fun u => ∫ t, J n u t ∂μ) (∫ t, J (n + 1) ν t ∂μ)
      (Ici 0) ν := by
  rcases eq_or_lt_of_le hν with rfl | hν
  · apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
    · intro u hu
      exact (integral_chain_hasDerivAt hJ hm hb n hu).differentiableAt.differentiableWithinAt
    · exact (integral_chain_continuousOn hJ hm hb n 0 (by simp)).mono Ioi_subset_Ici_self
    · exact self_mem_nhdsWithin
    · have hc := (integral_chain_continuousOn hJ hm hb (n + 1) 0 (by simp)).mono
        Ioi_subset_Ici_self
      apply hc.congr'
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (integral_chain_hasDerivAt hJ hm hb n hu).deriv.symm
  · exact (integral_chain_hasDerivAt hJ hm hb n hν).hasDerivWithinAt

theorem iteratedDerivWithin_integral_chain (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    iteratedDerivWithin n (fun u => ∫ t, J 0 u t ∂μ) (Ici 0) ν =
      ∫ t, J n ν t ∂μ := by
  induction n generalizing ν with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      exact ((integral_chain_hasDerivWithinAt hJ hm hb n hν).congr_of_mem
        (fun u hu => ih hu) hν).derivWithin ((uniqueDiffOn_Ici 0) ν hν)

theorem contDiffOn_integral_chain :
    ContDiffOn ℝ ∞ (fun ν => ∫ t, J 0 ν t ∂μ) (Ici 0) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro n _ ν hν
  exact ((integral_chain_hasDerivWithinAt hJ hm hb n hν).congr_of_mem
    (fun u hu => iteratedDerivWithin_integral_chain hJ hm hb n hu) hν).differentiableWithinAt

end IntegralChain

/-! ## Explicit algebra of genuine derivative chains -/

/-- Recursive Leibniz product. Its derivative identity is proved below. -/
noncomputable def jetProduct (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0 * b 0
  | n + 1 => jetProduct (fun i => a (i + 1)) b n +
      jetProduct a (fun i => b (i + 1)) n

theorem jetProduct_nonneg {a b : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (n : ℕ) :
    0 ≤ jetProduct a b n := by
  induction n generalizing a b with
  | zero => exact mul_nonneg (ha 0) (hb 0)
  | succ n ih =>
      exact add_nonneg (ih (fun i => ha (i + 1)) hb)
        (ih ha (fun i => hb (i + 1)))

theorem jetProduct_hasDerivWithinAt {a b : ℕ → ℝ → ℝ} {s : Set ℝ} {ν : ℝ}
    (ha : ∀ i, HasDerivWithinAt (a i) (a (i + 1) ν) s ν)
    (hb : ∀ i, HasDerivWithinAt (b i) (b (i + 1) ν) s ν) (n : ℕ) :
    HasDerivWithinAt (fun u => jetProduct (fun i => a i u) (fun i => b i u) n)
      (jetProduct (fun i => a i ν) (fun i => b i ν) (n + 1)) s ν := by
  induction n generalizing a b with
  | zero => exact (ha 0).mul (hb 0)
  | succ n ih =>
      exact (ih (fun i => ha (i + 1)) hb).add (ih ha (fun i => hb (i + 1)))

theorem jetProduct_continuousOn {a b : ℕ → ℝ → ℝ} {s : Set ℝ}
    (ha : ∀ i, ContinuousOn (a i) s) (hb : ∀ i, ContinuousOn (b i) s) (n : ℕ) :
    ContinuousOn (fun x => jetProduct (fun i => a i x) (fun i => b i x) n) s := by
  induction n generalizing a b with
  | zero => exact (ha 0).mul (hb 0)
  | succ n ih => exact (ih (fun i => ha (i + 1)) hb).add (ih ha (fun i => hb (i + 1)))

theorem jetProduct_bound {a b A B : ℕ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (ha : ∀ i, |a i| ≤ A i / X) (hb : ∀ i, |b i| ≤ B i / X) (n : ℕ) :
    |jetProduct a b n| ≤ jetProduct A B n / X := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  induction n generalizing a b A B with
  | zero =>
      change |a 0 * b 0| ≤ A 0 * B 0 / X
      rw [abs_mul]
      calc
        _ ≤ (A 0 / X) * (B 0 / X) :=
          mul_le_mul (ha 0) (hb 0) (abs_nonneg _) (div_nonneg (hA 0) hXp.le)
        _ ≤ A 0 * B 0 / X := by
          rw [div_mul_div_comm]
          exact div_le_div_of_nonneg_left (mul_nonneg (hA 0) (hB 0)) hXp
            (by nlinarith)
  | succ n ih =>
      calc
        _ ≤ |jetProduct (fun i => a (i + 1)) b n| +
            |jetProduct a (fun i => b (i + 1)) n| := abs_add_le _ _
        _ ≤ jetProduct (fun i => A (i + 1)) B n / X +
            jetProduct A (fun i => B (i + 1)) n / X :=
          add_le_add (ih (fun i => hA (i + 1)) hB (fun i => ha (i + 1)) hb)
            (ih hA (fun i => hB (i + 1)) ha (fun i => hb (i + 1)))
        _ = _ := by rw [← add_div]; rfl

/-! ## The actual diffusion jets of the switched multiplier -/

open HeatTailEdit

noncomputable def heatJetBound (h : ℝ) (n : ℕ) : ℝ :=
  |(Real.Gamma (1 + h))⁻¹ * RadialHeatProfile.derivativeCoeff (1 + h) n| *
    Real.Gamma (1 + h + (n : ℝ))

noncomputable def correctionJet (h K : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, ν, X => switch K X * (RadialHeatProfile.profile (1 + h) (2 * ν / X) - 1)
  | n + 1, ν, X => switch K X * (2 / X) ^ (n + 1) *
      RadialHeatProfile.profileJet (1 + h) (n + 1) (2 * ν / X)

noncomputable def correctionBound (h L : ℝ) : ℕ → ℝ
  | 0 => heatConstant h L
  | n + 1 => 2 ^ (n + 1) * heatJetBound h (n + 1)

theorem correctionJet_zero (h K ν X : ℝ) :
    correctionJet h K 0 ν X = multiplier h ν K X - 1 := by
  unfold correctionJet multiplier
  ring

theorem heatJetBound_nonneg {h : ℝ} (hh : 0 < h) (n : ℕ) :
    0 ≤ heatJetBound h n := by
  exact mul_nonneg (abs_nonneg _)
    (Real.Gamma_pos_of_pos (by positivity : 0 < 1 + h + (n : ℝ))).le

theorem correctionBound_nonneg {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ correctionBound h L n := by
  cases n with
  | zero => dsimp [correctionBound, heatConstant]; positivity
  | succ n => exact mul_nonneg (by positivity) (heatJetBound_nonneg hh _)

theorem correctionJet_hasDerivWithinAt {h K ν X : ℝ} (hh : 0 < h)
    (hX : 0 < X) (hν : 0 ≤ ν) (n : ℕ) :
    HasDerivWithinAt (fun u => correctionJet h K n u X)
      (correctionJet h K (n + 1) ν X) (Ici 0) ν := by
  have hz : 0 ≤ 2 * ν / X := by positivity
  have hi : HasDerivWithinAt (fun u : ℝ => 2 * u / X) (2 / X) (Ici 0) ν := by
    simpa using (((hasDerivAt_id ν).const_mul 2).div_const X).hasDerivWithinAt (s := Ici 0)
  have hmap : MapsTo (fun u : ℝ => 2 * u / X) (Ici 0) (Ici 0) := by
    intro u hu
    exact div_nonneg (mul_nonneg (by norm_num) hu) hX.le
  cases n with
  | zero =>
      have hd := (((RadialHeatProfile.profile_hasDerivWithinAt (a := 1 + h)
        (by linarith) hz).comp ν hi hmap).sub_const 1).const_mul (switch K X)
      convert! hd using 1
      simp only [correctionJet]
      ring
  | succ n =>
      have hd := ((RadialHeatProfile.profileJet_hasDerivWithinAt (a := 1 + h)
        (by linarith) (n + 1) hz).comp ν hi hmap).const_mul
          (switch K X * (2 / X) ^ (n + 1))
      convert! hd using 1
      simp only [correctionJet, pow_succ]
      ring

theorem correctionJet_continuousOn_X {h K ν : ℝ} (hh : 0 < h)
    (hK : 0 < K) (hν : 0 ≤ ν) (n : ℕ) :
    ContinuousOn (fun X => correctionJet h K n ν X) (Ioi 0) := by
  have hr : ContinuousOn (fun X : ℝ => 2 * ν / X) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun X hX => (show 0 < X from hX).ne')
  have hmap : MapsTo (fun X : ℝ => 2 * ν / X) (Ioi 0) (Ici 0) := by
    intro X hX
    exact div_nonneg (mul_nonneg (by norm_num) hν) (show 0 < X from hX).le
  cases n with
  | zero =>
      exact (switch_contDiffOn hK).continuousOn.mul
        (((RadialHeatProfile.profile_contDiffOn (a := 1 + h) (by linarith)).continuousOn.comp
          hr hmap).sub continuousOn_const)
  | succ n =>
      have hj : ContinuousOn (RadialHeatProfile.profileJet (1 + h) (n + 1)) (Ici 0) :=
        continuousOn_const.mul (RadialHeatProfile.moment_continuousOn (by linarith) (n + 1))
      have hc : ContinuousOn (fun X : ℝ => (2 : ℝ) / X) (Ioi 0) :=
        continuousOn_const.div continuousOn_id (fun X hX => (show 0 < X from hX).ne')
      exact ((switch_contDiffOn hK).continuousOn.mul
        (hc.pow (n + 1))).mul (hj.comp hr hmap)

theorem correctionJet_bound {h K L ν X : ℝ} (hh : 0 < h) (hX : 1 ≤ X)
    (hν : ν ∈ Icc (0 : ℝ) L) (n : ℕ) :
    |correctionJet h K n ν X| ≤ correctionBound h L n / X := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  cases n with
  | zero =>
      rw [correctionJet_zero]
      apply (multiplier_sub_one_bound hh hν.1 hXp).trans
      apply div_le_div_of_nonneg_right _ hXp.le
      dsimp [heatConstant, correctionBound]
      gcongr
      exact hν.2
  | succ n =>
      have hz : 0 ≤ 2 * ν / X := div_nonneg (mul_nonneg (by norm_num) hν.1) hXp.le
      have hj : |RadialHeatProfile.profileJet (1 + h) (n + 1) (2 * ν / X)| ≤
          heatJetBound h (n + 1) := by
        rw [← RadialHeatProfile.iteratedDerivWithin_profile (by linarith) (n + 1) hz]
        exact RadialHeatProfile.profile_derivative_bound (by linarith) (n + 1) hz
      have hp : (2 / X) ^ (n + 1) ≤ 2 ^ (n + 1) / X := by
        rw [div_pow]
        exact div_le_div_of_nonneg_left (by positivity) hXp (le_self_pow₀ hX (by omega))
      rw [correctionJet, abs_mul, abs_mul, abs_of_nonneg (switch_bounds K X).1,
        abs_of_nonneg (pow_nonneg (div_nonneg (by norm_num) hXp.le) _)]
      calc
        _ ≤ 1 * (2 ^ (n + 1) / X) * heatJetBound h (n + 1) := by
          gcongr
          exact (switch_bounds K X).2
        _ = correctionBound h L (n + 1) / X := by
          simp only [correctionBound]
          ring

/-- All diffusion derivatives of `M^2-1`, with `M` the actual switched multiplier. -/
noncomputable def squareCorrectionJet (h K : ℝ) (n : ℕ) (ν X : ℝ) : ℝ :=
  2 * correctionJet h K n ν X +
    jetProduct (fun i => correctionJet h K i ν X) (fun i => correctionJet h K i ν X) n

noncomputable def squareCorrectionBound (h L : ℝ) (n : ℕ) : ℝ :=
  2 * correctionBound h L n + jetProduct (correctionBound h L) (correctionBound h L) n

theorem squareCorrectionJet_zero (h K ν X : ℝ) :
    squareCorrectionJet h K 0 ν X = multiplier h ν K X ^ 2 - 1 := by
  simp only [squareCorrectionJet, jetProduct, correctionJet_zero]
  ring

theorem squareCorrectionJet_hasDerivWithinAt {h K ν X : ℝ} (hh : 0 < h)
    (hX : 0 < X) (hν : 0 ≤ ν) (n : ℕ) :
    HasDerivWithinAt (fun u => squareCorrectionJet h K n u X)
      (squareCorrectionJet h K (n + 1) ν X) (Ici 0) ν :=
  ((correctionJet_hasDerivWithinAt hh hX hν n).const_mul 2).add
    (jetProduct_hasDerivWithinAt (fun i => correctionJet_hasDerivWithinAt hh hX hν i)
      (fun i => correctionJet_hasDerivWithinAt hh hX hν i) n)

theorem squareCorrectionJet_continuousOn_X {h K ν : ℝ} (hh : 0 < h)
    (hK : 0 < K) (hν : 0 ≤ ν) (n : ℕ) :
    ContinuousOn (fun X => squareCorrectionJet h K n ν X) (Ioi 0) :=
  (continuousOn_const.mul (correctionJet_continuousOn_X hh hK hν n)).add
    (jetProduct_continuousOn (fun i => correctionJet_continuousOn_X hh hK hν i)
      (fun i => correctionJet_continuousOn_X hh hK hν i) n)

theorem squareCorrectionBound_nonneg {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ squareCorrectionBound h L n := by
  exact add_nonneg (mul_nonneg (by norm_num) (correctionBound_nonneg hh hL n))
    (jetProduct_nonneg (correctionBound_nonneg hh hL) (correctionBound_nonneg hh hL) n)

theorem squareCorrectionJet_bound {h K L ν X : ℝ} (hh : 0 < h) (hX : 1 ≤ X)
    (hν : ν ∈ Icc (0 : ℝ) L) (n : ℕ) :
    |squareCorrectionJet h K n ν X| ≤ squareCorrectionBound h L n / X := by
  have hL : 0 ≤ L := hν.1.trans hν.2
  calc
    _ ≤ |2 * correctionJet h K n ν X| +
        |jetProduct (fun i => correctionJet h K i ν X) (fun i => correctionJet h K i ν X) n| :=
      abs_add_le _ _
    _ ≤ 2 * (correctionBound h L n / X) +
        jetProduct (correctionBound h L) (correctionBound h L) n / X := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left (correctionJet_bound hh hX hν n) (by norm_num))
        (jetProduct_bound hX (correctionBound_nonneg hh hL) (correctionBound_nonneg hh hL)
          (fun i => correctionJet_bound hh hX hν i) (fun i => correctionJet_bound hh hX hν i) n)
    _ = _ := by unfold squareCorrectionBound; ring

/-! ## Actual improper integrals of the diffusion jets -/

/-- `false` selects the linear edit, `true` the square edit. -/
noncomputable def editJet (square : Bool) (h K : ℝ) (n : ℕ) (ν X : ℝ) : ℝ :=
  if square then squareCorrectionJet h K n ν X else correctionJet h K n ν X

noncomputable def editBound (square : Bool) (h L : ℝ) (n : ℕ) : ℝ :=
  if square then squareCorrectionBound h L n else correctionBound h L n

theorem editJet_hasDerivWithinAt {h K ν X : ℝ} (hh : 0 < h)
    (hX : 0 < X) (hν : 0 ≤ ν) (square : Bool) (n : ℕ) :
    HasDerivWithinAt (fun u => editJet square h K n u X)
      (editJet square h K (n + 1) ν X) (Ici 0) ν := by
  cases square
  · exact correctionJet_hasDerivWithinAt hh hX hν n
  · exact squareCorrectionJet_hasDerivWithinAt hh hX hν n

theorem editJet_continuousOn_X {h K ν : ℝ} (hh : 0 < h)
    (hK : 0 < K) (hν : 0 ≤ ν) (square : Bool) (n : ℕ) :
    ContinuousOn (fun X => editJet square h K n ν X) (Ioi 0) := by
  cases square
  · exact correctionJet_continuousOn_X hh hK hν n
  · exact squareCorrectionJet_continuousOn_X hh hK hν n

theorem editBound_nonneg {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L) (square : Bool) (n : ℕ) :
    0 ≤ editBound square h L n := by
  cases square
  · exact correctionBound_nonneg hh hL n
  · exact squareCorrectionBound_nonneg hh hL n

theorem editJet_bound {h K L ν X : ℝ} (hh : 0 < h) (hX : 1 ≤ X)
    (hν : ν ∈ Icc (0 : ℝ) L) (square : Bool) (n : ℕ) :
    |editJet square h K n ν X| ≤ editBound square h L n / X := by
  cases square
  · exact correctionJet_bound hh hX hν n
  · exact squareCorrectionJet_bound hh hX hν n

noncomputable def weightedJet (W : ℝ → ℝ) (square : Bool) (h K q : ℝ)
    (n : ℕ) (ν X : ℝ) : ℝ := X ^ q * W X * editJet square h K n ν X

noncomputable def weightedDebtJet (W : ℝ → ℝ) (square : Bool) (h K q : ℝ)
    (n : ℕ) (ν : ℝ) : ℝ := ∫ X in Ioi K, weightedJet W square h K q n ν X

section Weighted

variable {W : ℝ → ℝ} {h K p q B : ℝ}
  (hh : 0 < h) (hK : 1 ≤ K)
  (hW : ContinuousOn W (Ioi K))
  (hB : 0 ≤ B)
  (hweight : ∀ X ∈ Ioi K, |W X| ≤ B * (X / K) ^ p)
  (hpq : p + q < 0)

include hh hK

theorem weightedJet_derivative (square : Bool) :
    ∀ᵐ X ∂volume.restrict (Ioi K), ∀ n ν, 0 ≤ ν →
      HasDerivWithinAt (fun u => weightedJet W square h K q n u X)
        (weightedJet W square h K q (n + 1) ν X) (Ici 0) ν := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  intro n ν hν
  exact (editJet_hasDerivWithinAt hh
    (lt_of_lt_of_le zero_lt_one (hK.trans hX.le)) hν square n).const_mul (X ^ q * W X)

include hW

theorem weightedJet_continuousOn (square : Bool) (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    ContinuousOn (weightedJet W square h K q n ν) (Ioi K) := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  exact ((continuousOn_id.rpow_const (fun X hX => Or.inl (hKp.trans hX).ne')).mul hW).mul
    ((editJet_continuousOn_X hh hKp hν square n).mono (Ioi_subset_Ioi hKp.le))

theorem weightedJet_measurable (square : Bool) (n : ℕ) (ν : ℝ) (hν : 0 ≤ ν) :
    AEStronglyMeasurable (weightedJet W square h K q n ν) (volume.restrict (Ioi K)) :=
  (weightedJet_continuousOn hh hK hW square n hν).aestronglyMeasurable measurableSet_Ioi

include hB hweight

omit hW in
theorem weightedJet_bound (square : Bool) (n : ℕ) {L ν X : ℝ}
    (hν : ν ∈ Icc (0 : ℝ) L) (hX : X ∈ Ioi K) :
    ‖weightedJet W square h K q n ν X‖ ≤
      (B * editBound square h L n) * weightedKernel K p q X := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one (hK.trans hX.le)
  rw [weightedJet, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hXp q)]
  calc
    _ ≤ X ^ q * (B * (X / K) ^ p) * (editBound square h L n / X) := by
      gcongr
      · exact hweight X hX
      · exact editJet_bound hh (hK.trans hX.le) hν square n
    _ = _ := by unfold weightedKernel; ring

include hpq

omit hW in
theorem weightedJet_dominated (square : Bool) :
    ChainDominated (weightedJet W square h K q) (volume.restrict (Ioi K)) := by
  intro n L hL
  refine ⟨fun X => (B * editBound square h L n) * weightedKernel K p q X,
    (weightedKernel_integrable (lt_of_lt_of_le zero_lt_one hK) hpq).const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  intro ν hν
  exact weightedJet_bound hh hK hB hweight square n hν hX

omit hW in
theorem weightedDebtJet_bound (square : Bool) (n : ℕ) {L ν : ℝ}
    (_ : 0 < L) (hν : ν ∈ Icc (0 : ℝ) L) :
    |weightedDebtJet W square h K q n ν| ≤
      B * editBound square h L n * K ^ q / (-p - q) := by
  have hi := (weightedKernel_integrable (lt_of_lt_of_le zero_lt_one hK) hpq).const_mul
    (B * editBound square h L n)
  have hb' := norm_integral_le_of_norm_le hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
      exact weightedJet_bound hh hK hB hweight square n hν hX)
  simpa only [weightedDebtJet, Real.norm_eq_abs, integral_const_mul,
    integral_weightedKernel (lt_of_lt_of_le zero_lt_one hK) hpq, mul_div_assoc] using hb'

theorem weightedJet_integrable (square : Bool) (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    IntegrableOn (weightedJet W square h K q n ν) (Ioi K) :=
  chain_integrable (weightedJet_measurable hh hK hW square)
    (weightedJet_dominated hh hK hB hweight hpq square) n hν

theorem weightedDebtJet_derivative (square : Bool) (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    HasDerivWithinAt (weightedDebtJet W square h K q n)
      (weightedDebtJet W square h K q (n + 1) ν) (Ici 0) ν :=
  integral_chain_hasDerivWithinAt (weightedJet_derivative hh hK square)
    (weightedJet_measurable hh hK hW square)
    (weightedJet_dominated hh hK hB hweight hpq square) n hν

theorem weightedDebtJet_eq_iteratedDerivWithin (square : Bool) (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    iteratedDerivWithin n (weightedDebtJet W square h K q 0) (Ici 0) ν =
      weightedDebtJet W square h K q n ν :=
  iteratedDerivWithin_integral_chain (weightedJet_derivative hh hK square)
    (weightedJet_measurable hh hK hW square)
    (weightedJet_dominated hh hK hB hweight hpq square) n hν

theorem weightedDebt_contDiffOn (square : Bool) :
    ContDiffOn ℝ ∞ (weightedDebtJet W square h K q 0) (Ici 0) :=
  contDiffOn_integral_chain (weightedJet_derivative hh hK square)
    (weightedJet_measurable hh hK hW square)
    (weightedJet_dominated hh hK hB hweight hpq square)

end Weighted

/-! ## The actual outgoing shape and the three physical debts -/

open OutgoingTail

noncomputable def tailWeight (d : TailData) (K : ℝ) (square : Bool) (X : ℝ) : ℝ :=
  if square then (powerTail d.h (outgoingAmplitude d) K (outgoingShape d) X) ^ 2
  else powerTail d.h (outgoingAmplitude d) K (outgoingShape d) X

noncomputable def tailDecay (d : TailData) (square : Bool) : ℝ :=
  if square then -2 * exponent d.h else -exponent d.h

noncomputable def tailSize (d : TailData) (square : Bool) : ℝ :=
  if square then outgoingAmplitude d ^ 2 else outgoingAmplitude d

noncomputable def nuDebtJet (d : TailData) (K : ℝ) (square : Bool) (q : ℝ)
    (n : ℕ) (ν : ℝ) : ℝ := weightedDebtJet (tailWeight d K square) square d.h K q n ν

noncomputable def nuConstant (d : TailData) (square : Bool) (q : ℝ) (n : ℕ) : ℝ :=
  tailSize d square * editBound square d.h 1 n / (-tailDecay d square - q)

theorem tailSize_nonneg (d : TailData) (square : Bool) : 0 ≤ tailSize d square := by
  cases square
  · exact (outgoingAmplitude_pos d).le
  · exact sq_nonneg _

theorem tailWeight_continuousOn (d : TailData) {K : ℝ} (hK : 0 < K) (square : Bool) :
    ContinuousOn (tailWeight d K square) (Ioi K) := by
  have hc := (powerTail_contDiffOn hK d.h (outgoingAmplitude d) (outgoingShape_contDiff
    d)).continuousOn
  cases square
  · exact hc.mono (Ioi_subset_Ioi hK.le)
  · exact (hc.pow 2).mono (Ioi_subset_Ioi hK.le)

theorem tailWeight_bound (d : TailData) {K : ℝ} (hK : 0 < K) (square : Bool)
    (X : ℝ) (hX : X ∈ Ioi K) :
    |tailWeight d K square X| ≤ tailSize d square * (X / K) ^ tailDecay d square := by
  cases square
  · simpa only [tailWeight, Bool.false_eq_true, ite_false, tailSize, tailDecay, mul_one] using
      powerTail_bound hK (outgoingAmplitude_pos d).le hX.le d.h
        (M := 1) (fun t _ => outgoingShape_bound d t)
  · simp only [tailWeight, ite_true, tailSize, tailDecay]
    rw [abs_of_nonneg (sq_nonneg (powerTail d.h (outgoingAmplitude d) K (outgoingShape d) X))]
    simpa only [one_pow, mul_one] using
      powerTail_square_bound hK (outgoingAmplitude_pos d).le (show (0 : ℝ) ≤ 1 by norm_num)
        hX.le d.h (fun t _ => outgoingShape_bound d t)

theorem nuConstant_nonneg (d : TailData) (square : Bool) {q : ℝ}
    (hq : tailDecay d square + q < 0) (n : ℕ) : 0 ≤ nuConstant d square q n := by
  exact div_nonneg (mul_nonneg (tailSize_nonneg d square)
    (editBound_nonneg d.h_pos (by norm_num) square n)) (by linarith)

theorem nuDebtJet_derivative (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    HasDerivWithinAt (nuDebtJet d K square q n) (nuDebtJet d K square q (n + 1) ν)
      (Ici 0) ν :=
  weightedDebtJet_derivative d.h_pos hK
    (tailWeight_continuousOn d (lt_of_lt_of_le zero_lt_one hK) square)
    (tailSize_nonneg d square) (tailWeight_bound d (lt_of_lt_of_le zero_lt_one hK) square)
    hq square n hν

theorem nuDebt_contDiffOn (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) :
    ContDiffOn ℝ ∞ (nuDebtJet d K square q 0) (Ici 0) :=
  weightedDebt_contDiffOn d.h_pos hK
    (tailWeight_continuousOn d (lt_of_lt_of_le zero_lt_one hK) square)
    (tailSize_nonneg d square) (tailWeight_bound d (lt_of_lt_of_le zero_lt_one hK) square)
    hq square

theorem nuDebtJet_eq_iteratedDerivWithin (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (square : Bool) {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ)
    {ν : ℝ} (hν : 0 ≤ ν) :
    iteratedDerivWithin n (nuDebtJet d K square q 0) (Ici 0) ν =
      nuDebtJet d K square q n ν :=
  weightedDebtJet_eq_iteratedDerivWithin d.h_pos hK
    (tailWeight_continuousOn d (lt_of_lt_of_le zero_lt_one hK) square)
    (tailSize_nonneg d square) (tailWeight_bound d (lt_of_lt_of_le zero_lt_one hK) square)
    hq square n hν

theorem nuDebtJet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ) {ν : ℝ}
    (hν : ν ∈ Icc (0 : ℝ) 1) :
    |nuDebtJet d K square q n ν| ≤ nuConstant d square q n * K ^ q := by
  have hb' := weightedDebtJet_bound d.h_pos hK
    (tailSize_nonneg d square) (tailWeight_bound d (lt_of_lt_of_le zero_lt_one hK) square)
    hq square n (by norm_num : (0 : ℝ) < 1) hν
  convert! hb' using 1 ; unfold nuConstant ; ring

noncomputable def diffusion (eta : ℝ) : ℝ := 1 - eta ^ 2

noncomputable def physicalPressure (d : TailData) (K eta : ℝ) : ℝ :=
  pressureDebt (outgoingProfile d K eta) d.h (diffusion eta) K

noncomputable def physicalEnergy (d : TailData) (K eta : ℝ) : ℝ :=
  energyDebt (outgoingProfile d K eta) d.h (diffusion eta) K

noncomputable def physicalAngular (d : TailData) (K eta : ℝ) : ℝ :=
  angularDebt (outgoingProfile d K eta) d.h (diffusion eta) K

theorem physicalPressure_eq (d : TailData) {K : ℝ} (hK : 0 < K) (eta : ℝ) :
    physicalPressure d K eta = nuDebtJet d K true (-1) 0 (diffusion eta) := by
  rw [physicalPressure, outgoing_pressureDebt_eq d (diffusion eta) eta hK, pressureDebt_eq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  simp only [weightedJet, tailWeight, editJet, ite_true]
  rw [squareCorrectionJet_zero]
  dsimp only [squareChange, edit]
  ring

theorem physicalEnergy_eq (d : TailData) {K : ℝ} (hK : 0 < K) (eta : ℝ) :
    physicalEnergy d K eta = nuDebtJet d K true 0 0 (diffusion eta) := by
  rw [physicalEnergy, outgoing_energyDebt_eq d (diffusion eta) eta hK]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  simp only [weightedJet, tailWeight, editJet, ite_true]
  rw [squareCorrectionJet_zero, Real.rpow_zero]
  dsimp only [squareChange, edit]
  ring

theorem physicalAngular_eq (d : TailData) {K : ℝ} (hK : 0 < K) (eta : ℝ) :
    physicalAngular d K eta = Real.sqrt 2 * nuDebtJet d K false (1 / 2) 0 (diffusion eta) := by
  rw [physicalAngular, outgoing_angularDebt_eq d (diffusion eta) eta hK, angularDebt_eq]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  simp only [weightedJet, tailWeight, editJet, Bool.false_eq_true, ite_false]
  rw [correctionJet_zero]
  dsimp only [change, edit]
  ring

/-! ## Composition with the physical diffusion `1 - eta^2` -/

theorem diffusion_contDiff : ContDiff ℝ ∞ diffusion :=
  contDiff_const.sub (contDiff_id.pow 2)

theorem diffusion_mem {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    diffusion eta ∈ Icc (0 : ℝ) 1 := by
  have hp := mul_nonneg (show 0 ≤ 1 - eta by linarith [hη.2])
    (show 0 ≤ 1 + eta by linarith [hη.1])
  dsimp [diffusion]
  constructor <;> nlinarith [sq_nonneg eta]

theorem diffusion_hasDerivAt (eta : ℝ) : HasDerivAt diffusion (-2 * eta) eta := by
  convert! (hasDerivAt_const eta (1 : ℝ)).sub ((hasDerivAt_id eta).pow 2) using 1 ;
    simp only [Nat.cast_ofNat, id_eq] ; ring

theorem diffusion_deriv : deriv diffusion = fun eta => -2 * eta :=
  funext fun eta => (diffusion_hasDerivAt eta).deriv

theorem diffusion_second : iteratedDeriv 2 diffusion = fun _ => -2 := by
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, diffusion_deriv]
  funext eta
  simp

theorem diffusion_higher (n : ℕ) : iteratedDeriv (n + 3) diffusion = fun _ => 0 := by
  induction n with
  | zero =>
      rw [show 0 + 3 = 2 + 1 from rfl, iteratedDeriv_succ, diffusion_second]
      funext eta
      exact deriv_const eta (-2 : ℝ)
  | succ n ih =>
      rw [show n + 1 + 3 = (n + 3) + 1 by omega, iteratedDeriv_succ, ih]
      funext eta
      exact deriv_const eta (0 : ℝ)

theorem diffusion_jet_bound {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDerivWithin ℝ n diffusion (Icc (-1 : ℝ) 1) eta‖ ≤ (2 : ℝ) ^ n := by
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc (by norm_num))
    ((diffusion_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt) hη,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · rw [iteratedDeriv_one, diffusion_deriv, Real.norm_eq_abs, abs_mul]
    norm_num
    exact abs_le.mpr hη
  rcases n with _ | n
  · rw [diffusion_second]
    norm_num
  · rw [show n + 1 + 1 + 1 = n + 3 by omega, diffusion_higher]
    simp only [norm_zero]
    positivity

noncomputable def etaDebt (d : TailData) (K : ℝ) (square : Bool) (q eta : ℝ) : ℝ :=
  nuDebtJet d K square q 0 (diffusion eta)

noncomputable def etaConstant (d : TailData) (square : Bool) (q : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * (∑ i ∈ Finset.range (n + 1), nuConstant d square q i) * 2 ^ n

theorem etaConstant_nonneg (d : TailData) (square : Bool) {q : ℝ}
    (hq : tailDecay d square + q < 0) (n : ℕ) : 0 ≤ etaConstant d square q n := by
  unfold etaConstant
  exact mul_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => nuConstant_nonneg d square hq i)) (by positivity)

theorem etaDebt_contDiffOn (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) :
    ContDiffOn ℝ ∞ (etaDebt d K square q) (Icc (-1 : ℝ) 1) :=
  (nuDebt_contDiffOn d hK square hq).comp diffusion_contDiff.contDiffOn
    (fun _ hη => (diffusion_mem hη).1)

theorem etaDebt_hasDerivWithinAt (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (etaDebt d K square q)
      (nuDebtJet d K square q 1 (diffusion eta) * (-2 * eta)) (Icc (-1 : ℝ) 1) eta :=
  (nuDebtJet_derivative d hK square hq 0 (diffusion_mem hη).1).comp eta
    (diffusion_hasDerivAt eta).hasDerivWithinAt (fun _ hη => (diffusion_mem hη).1)

theorem etaDebt_jet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ) {eta : ℝ}
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    |iteratedDerivWithin n (etaDebt d K square q) (Icc (-1 : ℝ) 1) eta| ≤
      etaConstant d square q n * K ^ q := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hb' := norm_iteratedFDerivWithin_comp_le (nuDebt_contDiffOn d hK square hq)
    diffusion_contDiff.contDiffOn (WithTop.coe_le_coe.mpr le_top)
    (uniqueDiffOn_Ici 0) (uniqueDiffOn_Icc (by norm_num))
    (fun _ hη => (diffusion_mem hη).1) hη
    (C := (∑ i ∈ Finset.range (n + 1), nuConstant d square q i) * K ^ q)
    (D := 2) (n := n) ?_ ?_
  · rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs] at hb'
    convert! hb' using 1 ; simp only [etaConstant] ; ring
  · intro i hi
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs,
      nuDebtJet_eq_iteratedDerivWithin d hK square hq i (diffusion_mem hη).1]
    apply (nuDebtJet_bound d hK square hq i (diffusion_mem hη)).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hKp.le q)
    exact Finset.single_le_sum (fun j _ => nuConstant_nonneg d square hq j)
      (Finset.mem_range.mpr (by omega))
  · intro i hi _
    exact diffusion_jet_bound hη i hi

theorem pressure_decay (d : TailData) : tailDecay d true + (-1) < 0 := by
  dsimp [tailDecay, exponent]
  linarith [d.h_pos]

theorem energy_decay (d : TailData) : tailDecay d true + 0 < 0 := by
  dsimp [tailDecay, exponent]
  linarith [d.h_pos]

theorem angular_decay (d : TailData) : tailDecay d false + (1 / 2) < 0 := by
  dsimp [tailDecay, exponent]
  linarith [d.h_pos]

theorem physicalPressure_contDiffOn (d : TailData) {K : ℝ} (hK : 1 ≤ K) :
    ContDiffOn ℝ ∞ (physicalPressure d K) (Icc (-1 : ℝ) 1) := by
  have he : physicalPressure d K = etaDebt d K true (-1) :=
    funext (physicalPressure_eq d (lt_of_lt_of_le zero_lt_one hK))
  rw [he]
  exact etaDebt_contDiffOn d hK true (pressure_decay d)

theorem physicalEnergy_contDiffOn (d : TailData) {K : ℝ} (hK : 1 ≤ K) :
    ContDiffOn ℝ ∞ (physicalEnergy d K) (Icc (-1 : ℝ) 1) := by
  have he : physicalEnergy d K = etaDebt d K true 0 :=
    funext (physicalEnergy_eq d (lt_of_lt_of_le zero_lt_one hK))
  rw [he]
  exact etaDebt_contDiffOn d hK true (energy_decay d)

theorem physicalAngular_contDiffOn (d : TailData) {K : ℝ} (hK : 1 ≤ K) :
    ContDiffOn ℝ ∞ (physicalAngular d K) (Icc (-1 : ℝ) 1) := by
  have he : physicalAngular d K = fun eta => Real.sqrt 2 * etaDebt d K false (1 / 2) eta :=
    funext (physicalAngular_eq d (lt_of_lt_of_le zero_lt_one hK))
  rw [he]
  exact contDiffOn_const.mul (etaDebt_contDiffOn d hK false (angular_decay d))

theorem physicalPressure_hasDerivWithinAt (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (physicalPressure d K)
      (nuDebtJet d K true (-1) 1 (diffusion eta) * (-2 * eta)) (Icc (-1 : ℝ) 1) eta := by
  have he : physicalPressure d K = etaDebt d K true (-1) :=
    funext (physicalPressure_eq d (lt_of_lt_of_le zero_lt_one hK))
  rw [he]
  exact etaDebt_hasDerivWithinAt d hK true (pressure_decay d) hη

theorem physicalEnergy_hasDerivWithinAt (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (physicalEnergy d K)
      (nuDebtJet d K true 0 1 (diffusion eta) * (-2 * eta)) (Icc (-1 : ℝ) 1) eta := by
  have he : physicalEnergy d K = etaDebt d K true 0 :=
    funext (physicalEnergy_eq d (lt_of_lt_of_le zero_lt_one hK))
  rw [he]
  exact etaDebt_hasDerivWithinAt d hK true (energy_decay d) hη

theorem physicalAngular_hasDerivWithinAt (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (physicalAngular d K)
      (Real.sqrt 2 * (nuDebtJet d K false (1 / 2) 1 (diffusion eta) * (-2 * eta)))
      (Icc (-1 : ℝ) 1) eta := by
  have he : physicalAngular d K = fun eta => Real.sqrt 2 * etaDebt d K false (1 / 2) eta :=
    funext (physicalAngular_eq d (lt_of_lt_of_le zero_lt_one hK))
  rw [he]
  exact (etaDebt_hasDerivWithinAt d hK false (angular_decay d) hη).const_mul _

theorem physicalPressure_jet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (n : ℕ) {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    |iteratedDerivWithin n (physicalPressure d K) (Icc (-1 : ℝ) 1) eta| ≤
      etaConstant d true (-1) n / K := by
  have he : physicalPressure d K = etaDebt d K true (-1) :=
    funext (physicalPressure_eq d (lt_of_lt_of_le zero_lt_one hK))
  rw [he]
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
    etaDebt_jet_bound d hK true (pressure_decay d) n hη

theorem physicalEnergy_jet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (n : ℕ) {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    |iteratedDerivWithin n (physicalEnergy d K) (Icc (-1 : ℝ) 1) eta| ≤
      etaConstant d true 0 n := by
  have he : physicalEnergy d K = etaDebt d K true 0 :=
    funext (physicalEnergy_eq d (lt_of_lt_of_le zero_lt_one hK))
  rw [he]
  simpa only [Real.rpow_zero, mul_one] using
    etaDebt_jet_bound d hK true (energy_decay d) n hη

theorem physicalAngular_jet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (n : ℕ) {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    |iteratedDerivWithin n (physicalAngular d K) (Icc (-1 : ℝ) 1) eta| ≤
      (Real.sqrt 2 * etaConstant d false (1 / 2) n) * Real.sqrt K := by
  have he : physicalAngular d K = fun eta => Real.sqrt 2 * etaDebt d K false (1 / 2) eta :=
    funext (physicalAngular_eq d (lt_of_lt_of_le zero_lt_one hK))
  rw [he, iteratedDerivWithin_const_mul hη (uniqueDiffOn_Icc (by norm_num)) _
    ((etaDebt_contDiffOn d hK false (angular_decay d) eta hη).of_le
      (WithTop.coe_le_coe.mpr le_top)), abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hb' := mul_le_mul_of_nonneg_left
    (etaDebt_jet_bound d hK false (angular_decay d) n hη) (Real.sqrt_nonneg 2)
  simpa only [← Real.sqrt_eq_rpow K, mul_assoc] using hb'

/-- Every fixed genuine eta jet has the manuscript's three unnormalized scales. -/
theorem exists_physical_debt_jet_bounds (d : TailData) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ eta ∈ Icc (-1 : ℝ) 1,
      |iteratedDerivWithin n (physicalPressure d K) (Icc (-1 : ℝ) 1) eta| ≤ C / K ∧
      |iteratedDerivWithin n (physicalEnergy d K) (Icc (-1 : ℝ) 1) eta| ≤ C ∧
      |iteratedDerivWithin n (physicalAngular d K) (Icc (-1 : ℝ) 1) eta| ≤ C * Real.sqrt K := by
  let CP := etaConstant d true (-1) n
  let CS := etaConstant d true 0 n
  let CI := Real.sqrt 2 * etaConstant d false (1 / 2) n
  have hp : 0 ≤ CP := etaConstant_nonneg d true (pressure_decay d) n
  have hs : 0 ≤ CS := etaConstant_nonneg d true (energy_decay d) n
  have hi : 0 ≤ CI := mul_nonneg (Real.sqrt_nonneg 2)
    (etaConstant_nonneg d false (angular_decay d) n)
  refine ⟨1 + CP + CS + CI, by linarith, ?_⟩
  intro K hK eta hη
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨(physicalPressure_jet_bound d hK n hη).trans ?_,
    (physicalEnergy_jet_bound d hK n hη).trans ?_,
    (physicalAngular_jet_bound d hK n hη).trans ?_⟩
  · exact div_le_div_of_nonneg_right (show CP ≤ 1 + CP + CS + CI by linarith) hKp.le
  · change CS ≤ 1 + CP + CS + CI
    linarith
  · exact mul_le_mul_of_nonneg_right (show CI ≤ 1 + CP + CS + CI by linarith)
      (Real.sqrt_nonneg K)

/-- A single constant controls values and actual first within derivatives.
This is the scalar input to the variable-debt nonlinear compensation theorem. -/
theorem exists_physical_debt_C1_bounds (d : TailData) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ eta ∈ Icc (-1 : ℝ) 1,
      |physicalPressure d K eta| ≤ C / K ∧
      |derivWithin (physicalPressure d K) (Icc (-1 : ℝ) 1) eta| ≤ C / K ∧
      |physicalEnergy d K eta| ≤ C ∧
      |derivWithin (physicalEnergy d K) (Icc (-1 : ℝ) 1) eta| ≤ C ∧
      |physicalAngular d K eta| ≤ C * Real.sqrt K ∧
      |derivWithin (physicalAngular d K) (Icc (-1 : ℝ) 1) eta| ≤ C * Real.sqrt K := by
  obtain ⟨C0, hC0, hb0⟩ := exists_physical_debt_jet_bounds d 0
  obtain ⟨C1, hC1, hb1⟩ := exists_physical_debt_jet_bounds d 1
  refine ⟨C0 + C1, by linarith, ?_⟩
  intro K hK eta hη
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rcases hb0 K hK eta hη with ⟨hp0, hs0, hi0⟩
  rcases hb1 K hK eta hη with ⟨hp1, hs1, hi1⟩
  simp only [iteratedDerivWithin_zero, iteratedDerivWithin_one] at hp0 hs0 hi0 hp1 hs1 hi1
  refine ⟨hp0.trans ?_, hp1.trans ?_, hs0.trans ?_, hs1.trans ?_, hi0.trans ?_, hi1.trans ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hKp.le
  · exact div_le_div_of_nonneg_right (by linarith) hKp.le
  · linarith
  · linarith
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg K)
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg K)

/-! ## Endpoint jets and the velocity in physical units -/

theorem correctionJet_eq_iteratedDerivWithin {h K X ν : ℝ} (hh : 0 < h)
    (hX : 0 < X) (hν : 0 ≤ ν) (n : ℕ) :
    iteratedDerivWithin n (fun u => multiplier h u K X - 1) (Ici 0) ν =
      correctionJet h K n ν X := by
  induction n generalizing ν with
  | zero => exact (correctionJet_zero h K ν X).symm
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      exact ((correctionJet_hasDerivWithinAt hh hX hν n).congr_of_mem
        (fun u hu => ih hu) hν).derivWithin ((uniqueDiffOn_Ici 0) ν hν)

theorem multiplier_nu_contDiffOn {h K X : ℝ} (hh : 0 < h) (hX : 0 < X) :
    ContDiffOn ℝ ∞ (fun ν => multiplier h ν K X) (Ici 0) := by
  have hmap : MapsTo (fun ν : ℝ => 2 * ν / X) (Ici 0) (Ici 0) := by
    intro ν hν
    exact div_nonneg (mul_nonneg (by norm_num) hν) hX.le
  exact contDiffOn_const.add (contDiffOn_const.mul
    (((RadialHeatProfile.profile_contDiffOn (a := 1 + h) (by linarith)).comp
      ((contDiffOn_const.mul contDiffOn_id).div_const X) hmap).sub contDiffOn_const))

theorem multiplier_nu_jet {h K X ν : ℝ} (hh : 0 < h) (hX : 0 < X)
    (hν : 0 ≤ ν) (n : ℕ) :
    iteratedDerivWithin (n + 1) (fun u => multiplier h u K X) (Ici 0) ν =
      correctionJet h K (n + 1) ν X := by
  have he : (fun u => multiplier h u K X) = fun u => 1 + (multiplier h u K X - 1) := by
    funext u
    ring
  rw [he, iteratedDerivWithin_const_add (Nat.succ_pos n) (1 : ℝ)]
  exact correctionJet_eq_iteratedDerivWithin hh hX hν (n + 1)

theorem multiplier_nu_jet_bound {h K X ν : ℝ} (hh : 0 < h) (hX : 1 ≤ X)
    (hν : ν ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    |iteratedDerivWithin (n + 1) (fun u => multiplier h u K X) (Ici 0) ν| ≤
      correctionBound h 1 (n + 1) / X := by
  rw [multiplier_nu_jet hh (lt_of_lt_of_le zero_lt_one hX) hν.1 n]
  exact correctionJet_bound hh hX hν (n + 1)

theorem multiplier_zero {h : ℝ} (hh : 0 < h) (K X : ℝ) : multiplier h 0 K X = 1 := by
  simp [multiplier, RadialHeatProfile.profile_zero (a := 1 + h) (by linarith)]

theorem outgoing_debts_integrable (d : TailData) {K ν : ℝ} (hK : 0 < K) (hν : 0 ≤ ν)
    (eta : ℝ) :
    IntegrableOn (fun X => squareChange (outgoingProfile d K eta) d.h ν K X / X) (Ioi K) ∧
    IntegrableOn (squareChange (outgoingProfile d K eta) d.h ν K) (Ioi K) ∧
    IntegrableOn (fun X => Real.sqrt (2 * X) * change (outgoingProfile d K eta) d.h ν K X)
      (Ioi K) := by
  rcases eq_or_lt_of_le hν with rfl | hν
  · have hsq : squareChange (outgoingProfile d K eta) d.h 0 K = fun _ => 0 := by
      funext X
      simp only [squareChange, edit, multiplier_zero d.h_pos, mul_one, sub_self]
    simp only [hsq, change, edit, multiplier_zero d.h_pos, mul_one, sub_self,
      zero_div, mul_zero]
    exact ⟨integrableOn_zero, integrableOn_zero, integrableOn_zero⟩
  · exact ⟨(outgoing_pressure d hν hK eta).1, (outgoing_energy d hν hK eta).1,
      (outgoing_angular d hν hK eta).1⟩

theorem physical_debts_integrable (d : TailData) {K eta : ℝ} (hK : 0 < K)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    IntegrableOn (fun X => squareChange (outgoingProfile d K eta) d.h (diffusion eta) K X / X)
      (Ioi K) ∧
    IntegrableOn (squareChange (outgoingProfile d K eta) d.h (diffusion eta) K) (Ioi K) ∧
    IntegrableOn (fun X => Real.sqrt (2 * X) *
      change (outgoingProfile d K eta) d.h (diffusion eta) K X) (Ioi K) :=
  outgoing_debts_integrable d hK (diffusion_mem hη).1 eta

theorem physical_debts_zero (d : TailData) (K : ℝ) {eta : ℝ} (hη : diffusion eta = 0) :
    physicalPressure d K eta = 0 ∧ physicalEnergy d K eta = 0 ∧ physicalAngular d K eta = 0 := by
  simp [physicalPressure, physicalEnergy, physicalAngular, pressureDebt, energyDebt, angularDebt,
    hη, squareChange, change, edit, multiplier_zero d.h_pos]

noncomputable def physicalEdit (d : TailData) (K eta X : ℝ) : ℝ :=
  outgoingEdit d (diffusion eta) K eta X

theorem physicalEdit_pos (d : TailData) (K : ℝ) {eta X : ℝ}
    (hη : eta ∈ Icc (-1 : ℝ) 1) (hX : 0 < X) : 0 < physicalEdit d K eta X :=
  outgoingEdit_pos d (diffusion_mem hη).1 hX eta

theorem physicalEdit_before (d : TailData) {K X : ℝ} (hK : 0 < K) (hX : 0 < X)
    (hXK : X ≤ K) (eta : ℝ) : physicalEdit d K eta X = outgoingProfile d K eta X :=
  outgoingEdit_before d (diffusion eta) eta hK hX hXK

theorem physicalEdit_joint_contDiffOn (d : TailData) {K : ℝ} (hK : 0 < K) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => physicalEdit d K p.2 p.1)
      (Ioi 0 ×ˢ Icc (-1 : ℝ) 1) := by
  have hE := (outgoingProfile_joint_contDiffOn d hK).mono
    (show Ioi (0 : ℝ) ×ˢ Icc (-1 : ℝ) 1 ⊆ Ioi 0 ×ˢ univ from fun p hp => ⟨hp.1, mem_univ _⟩)
  have hD : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => diffusion p.2)
      (Ioi 0 ×ˢ Icc (-1 : ℝ) 1) := diffusion_contDiff.comp_contDiffOn contDiffOn_snd
  have hr : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 2 * diffusion p.2 / p.1)
      (Ioi 0 ×ˢ Icc (-1 : ℝ) 1) :=
    (contDiffOn_const.mul hD).div contDiffOn_fst (fun p hp => (show 0 < p.1 from hp.1).ne')
  have hH := (RadialHeatProfile.profile_contDiffOn (a := 1 + d.h) (by linarith [d.h_pos])).comp
    hr (show MapsTo (fun p : ℝ × ℝ => 2 * diffusion p.2 / p.1)
      (Ioi 0 ×ˢ Icc (-1 : ℝ) 1) (Ici 0) from fun p hp =>
        div_nonneg (mul_nonneg (by norm_num) (diffusion_mem hp.2).1) (show 0 < p.1 from hp.1).le)
  have hs := (switch_contDiffOn hK).comp contDiffOn_fst
    (show MapsTo (Prod.fst : ℝ × ℝ → ℝ) (Ioi 0 ×ˢ Icc (-1 : ℝ) 1) (Ioi 0) from fun _ hp => hp.1)
  exact hE.mul (contDiffOn_const.add (hs.mul (hH.sub contDiffOn_const)))

theorem diffusion_of_physical_coordinates {q τ z : ℝ} (hq : 0 < q) (hrel : q = τ + z ^ 2) :
    diffusion (z / Real.sqrt q) = τ / q := by
  unfold diffusion
  rw [div_pow, Real.sq_sqrt hq.le]
  field_simp [hq.ne']
  linarith

theorem heat_ratio_physical {q s τ : ℝ} (hq : 0 < q) (hs : 0 < s) :
    2 * (τ / q) / (s / q) = 2 * τ / s := by
  field_simp [hq.ne', hs.ne']

/-- The similarity prefactor cancels all powers of `q`. The carrier is
exactly a constant times `s^(-A) H(2 tau / s)`. -/
theorem physicalEdit_heat_carrier (d : TailData) {K q s τ eta : ℝ}
    (hK : 0 < K) (hq : 0 < q) (hs : 0 < s) (hν : diffusion eta = τ / q)
    (hfull : 1 / 2 ≤ Real.log ((s / q) / K) + 1 / 5) :
    q ^ (-exponent d.h) * physicalEdit d K eta (s / q) =
      (outgoingAmplitude d * K ^ exponent d.h) *
        RadialHeatProfile.spatialProfile (1 + d.h) τ s *
          tailShape d (Real.log ((s / q) / K) + 1 / 5) := by
  unfold physicalEdit
  rw [outgoingEdit_heat_factorization d (diffusion eta) eta hK (div_pos hs hq) hfull, hν]
  have hexp : RadialHeatProfile.spatialExponent (1 + d.h) = -exponent d.h := by
    unfold RadialHeatProfile.spatialExponent exponent
    ring
  have hp : (s / q) ^ (-exponent d.h) = s ^ (-exponent d.h) * q ^ exponent d.h := by
    rw [Real.div_rpow hs.le hq.le, Real.rpow_neg hq.le, div_inv_eq_mul]
  have hcancel : q ^ (-exponent d.h) * q ^ exponent d.h = 1 := by
    rw [Real.rpow_neg hq.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hq _).ne']
  simp only [RadialHeatProfile.spatialProfile, hexp, heat_ratio_physical hq hs, hp]
  calc
    _ = (q ^ (-exponent d.h) * q ^ exponent d.h) *
        ((outgoingAmplitude d * K ^ exponent d.h) *
          (s ^ (-exponent d.h) * RadialHeatProfile.profile (1 + d.h) (2 * τ / s)) *
            tailShape d (Real.log ((s / q) / K) + 1 / 5)) := by ring
    _ = _ := by rw [hcancel, one_mul]

theorem physicalEdit_eventual_heat_carrier (d : TailData) {K q s τ eta : ℝ}
    (hK : 0 < K) (hq : 0 < q) (hs : 0 < s) (hν : diffusion eta = τ / q)
    (hlate : 3 ≤ Real.log ((s / q) / K) + 1 / 5) :
    q ^ (-exponent d.h) * physicalEdit d K eta (s / q) =
      (outgoingAmplitude d * K ^ exponent d.h) *
        RadialHeatProfile.spatialProfile (1 + d.h) τ s := by
  rw [physicalEdit_heat_carrier d hK hq hs hν (by linarith), tailShape_late d hlate, mul_one]

/-! The eta derivatives are not identically zero. In particular, the actual
one-sided angular derivative at the physical endpoint `eta = 1` is positive. -/

theorem switch_pos {K X : ℝ} (hK : 0 < K) (hX : K < X) : 0 < switch K X := by
  have hl : 0 < Real.log (X / K) := Real.log_pos ((one_lt_div hK).mpr hX)
  exact div_pos (FlatCutoff.edge_pos 1 (div_pos hl (by norm_num)))
    (OutgoingSchedule.sigma_denom_pos _)

theorem profile_first_jet_neg {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) :
    RadialHeatProfile.profileJet (1 + h) 1 z < 0 := by
  have hg : 0 < (Real.Gamma (1 + h))⁻¹ :=
    inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))
  have hm := RadialHeatProfile.moment_pos (a := 1 + h) (by linarith) 1 hz
  have he : RadialHeatProfile.profileJet (1 + h) 1 z =
      ((Real.Gamma (1 + h))⁻¹ * (-h)) * RadialHeatProfile.moment (1 + h) 1 z := by
    simp only [RadialHeatProfile.profileJet, RadialHeatProfile.derivativeCoeff,
      Nat.cast_zero, sub_zero]
    ring
  rw [he]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hg (neg_neg_of_pos hh)) hm

theorem nuDebt_linear_first_neg (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    {q : ℝ} (hq : tailDecay d false + q < 0) {ν : ℝ} (hν : 0 ≤ ν) :
    nuDebtJet d K false q 1 ν < 0 := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let g := weightedJet (tailWeight d K false) false d.h K q 1 ν
  have hi : IntegrableOn g (Ioi K) :=
    weightedJet_integrable d.h_pos hK (tailWeight_continuousOn d hKp false)
      (tailSize_nonneg d false) (tailWeight_bound d hKp false) hq false 1 hν
  have hg : ∀ X ∈ Ioi K, g X < 0 := by
    intro X hX
    have hXp : 0 < X := hKp.trans hX
    have he : 0 < tailWeight d K false X := by
      change 0 < powerTail d.h (outgoingAmplitude d) K (outgoingShape d) X
      exact mul_pos (mul_pos (outgoingAmplitude_pos d)
        (Real.rpow_pos_of_pos (div_pos hXp hKp) _)) (tailShape_pos d _)
    have hc : correctionJet d.h K 1 ν X < 0 := by
      change switch K X * (2 / X) ^ 1 * RadialHeatProfile.profileJet (1 + d.h) 1 (2 * ν / X) < 0
      exact mul_neg_of_pos_of_neg (mul_pos (switch_pos hKp hX) (pow_pos (by positivity) _))
        (profile_first_jet_neg d.h_pos (by positivity))
    exact mul_neg_of_pos_of_neg (mul_pos (Real.rpow_pos_of_pos hXp q) he) hc
  have hs : Function.support (fun X => -g X) ∩ Ioi K = Ioi K := by
    rw [inter_eq_right]
    intro X hX
    exact (neg_pos.mpr (hg X hX)).ne'
  have hp : 0 < ∫ X in Ioi K, -g X := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · rw [hs, Real.volume_Ioi]
      simp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
      exact (neg_pos.mpr (hg X hX)).le
    · exact hi.neg
  rw [integral_neg] at hp
  exact neg_pos.mp hp

theorem physicalAngular_endpoint_derivative_pos (d : TailData) {K : ℝ} (hK : 1 ≤ K) :
    0 < derivWithin (physicalAngular d K) (Icc (-1 : ℝ) 1) 1 := by
  have hd := physicalAngular_hasDerivWithinAt d hK (eta := 1) (by norm_num)
  rw [hd.derivWithin ((uniqueDiffOn_Icc (by norm_num)) 1 (by norm_num))]
  have hn := nuDebt_linear_first_neg d hK (angular_decay d) (ν := 0) (by norm_num)
  simp only [diffusion, one_pow, sub_self, mul_one]
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) (mul_pos_of_neg_of_neg hn (by norm_num))

end NavierStokes.ParametricHeatTail
