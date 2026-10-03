/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamVelocityConstants

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.TimeIncrement.FlowBounds

/-! # Recursion

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance

/-- Product cutoff localizing one term of the stream recursion in time. -/
def Recursion.recursionCutoff {β : ℝ} (I : Ingredients β) (m : ℕ)
    (k : ℤ) : ℝ → ℝ :=
  fun t => I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t

theorem Recursion.recursionCutoff_contDiff {β : ℝ} {I : Ingredients β}
    (m : ℕ) (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (Recursion.recursionCutoff I m k) := by
  have hz : ContDiff ℝ (⊤ : ℕ∞) (I.zetaMK m k) := by
    unfold Ingredients.zetaMK scaledCutoff
    exact I.zeta_smooth.comp (by fun_prop)
  have hh : ContDiff ℝ (⊤ : ℕ∞) (I.hatZetaML m (lIdx β I.Λ m k)) := by
    unfold Ingredients.hatZetaML shiftCutoff
    exact (I.hatZeta_smooth m).comp (by fun_prop)
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun t => I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t)
  exact hh.mul hz

theorem Recursion.recursionCutoff_deriv_bound {β : ℝ} {I : Ingredients β}
    (m : ℕ) (hm : 1 ≤ m) (k : ℤ) (t : ℝ) :
    |deriv (Recursion.recursionCutoff I m k) t| ≤
      I.Czeta * I.Chat *
        ((tau β I.Λ m)⁻¹ + (tauP β I.Λ m)⁻¹) := by
  have h := Infra.Construction.zetaMK_hatZetaML_product_deriv_le
    I m hm k (lIdx β I.Λ m k) (j := 1)
    (by exact Nat.le_trans (by norm_num) (Infra.Ingredients.Nstar_ge_256
      I.one_lt_beta I.beta_lt)) t
  change |deriv (I.hatZetaML m (lIdx β I.Λ m k) * I.zetaMK m k) t| ≤ _
  simpa [iteratedDeriv_one, mul_comm] using h

theorem Recursion.zetaMK_ne_zero_distance {β : ℝ} {I : Ingredients β}
    (m : ℕ) (k : ℤ) (t : ℝ) (hne : I.zetaMK m k t ≠ 0) :
    |t - (k : ℝ) * tau β I.Λ m| ≤ 2 / 3 * tau β I.Λ m := by
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
  rw [show u = (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m by rfl,
    abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at hbound
  simpa [abs_of_pos hτ] using hbound

theorem Recursion.hatZetaML_ne_zero_distance {β : ℝ} {I : Ingredients β}
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ)
    (hne : I.hatZetaML m l t ≠ 0) :
    |t - (l : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m / 2 := by
  have hpos : 0 < I.hatZetaML m l t := by
    exact lt_of_le_of_ne (Infra.Section3.hatZetaML_mem_Icc I hm l t).1
      (Ne.symm hne)
  have hle := I.hatZeta_le m hm l t
  have hτp := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt
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

theorem Recursion.recursionCutoff_nonneg {β : ℝ} {I : Ingredients β}
    (m : ℕ) (hm : 1 ≤ m) (k : ℤ) (t : ℝ) :
    0 ≤ Recursion.recursionCutoff I m k t :=
  mul_nonneg (Infra.Section3.hatZetaML_mem_Icc I hm _ _).1
    (Infra.Section3.zetaMK_mem_Icc I k t).1

theorem Recursion.recursionCutoff_deriv_zero_of_zero {β : ℝ} {I : Ingredients β}
    (m : ℕ) (hm : 1 ≤ m) (k : ℤ) (t : ℝ)
    (hz : Recursion.recursionCutoff I m k t = 0) :
    deriv (Recursion.recursionCutoff I m k) t = 0 := by
  have hmin : IsLocalMin (Recursion.recursionCutoff I m k) t := by
    change ∀ᶠ r in 𝓝 t, Recursion.recursionCutoff I m k t ≤ Recursion.recursionCutoff I m k r
    rw [hz]
    exact Filter.Eventually.of_forall (Recursion.recursionCutoff_nonneg m hm k)
  exact hmin.deriv_eq_zero

theorem Recursion.epsilon_rpow_delta_le_one {β : ℝ} {I : Ingredients β}
    (m : ℕ) : epsilon β I.Λ m ^ delta β ≤ 1 := by
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have he1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  exact Real.rpow_le_one he.le he1 (le_of_lt (Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt))

theorem Recursion.epsilon_mul_previous_amplitude_le {β : ℝ} {I : Ingredients β}
    (m : ℕ) (hm : 1 ≤ m) :
    epsilon β I.Λ m * a β I.Λ (m - 1) ≤
      1 + Infra.Ingredients.supergeoConstant β := by
  by_cases hm1 : m = 1
  · subst m
    have he := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := 1)
    have hs : 0 ≤ Infra.Ingredients.supergeoConstant β := by
      have hq : 0 < q β := lt_trans zero_lt_one
        (Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt)
      dsimp [Infra.Ingredients.supergeoConstant]; positivity
    have ha0 : a β I.Λ 0 = 1 := by simp [a, epsilon]
    rw [ha0, mul_one]
    linarith
  · have hp : 1 ≤ m - 1 := by omega
    have he : 0 < epsilon β I.Λ (m - 1) := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le
    have he1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m - 1)
    have hsuper := Infra.Ingredients.epsilon_supergeo I.one_lt_beta I.beta_lt I.two_pow_seven_le hp
    have hupper : epsilon β I.Λ m ≤
        (1 + Infra.Ingredients.supergeoConstant β * epsilon β I.Λ (m - 1)) *
          epsilon β I.Λ (m - 1) ^ q β := by
      simpa [Nat.sub_add_cancel hm] using hsuper.2
    have hs : 0 ≤ Infra.Ingredients.supergeoConstant β := by
      have hq : 0 < q β := lt_trans zero_lt_one
        (Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt)
      dsimp [Infra.Ingredients.supergeoConstant]; positivity
    have hcoeff : 1 + Infra.Ingredients.supergeoConstant β * epsilon β I.Λ (m - 1) ≤
        1 + Infra.Ingredients.supergeoConstant β := by nlinarith
    have hexp : 0 < q β + β - 2 := by
      have hq := q_minus_time_exponent_pos I.one_lt_beta I.beta_lt
      have hd := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
      linarith
    have hpw : epsilon β I.Λ (m - 1) ^ (q β + β - 2) ≤ 1 :=
      Real.rpow_le_one he.le he1 (le_of_lt hexp)
    have heq : epsilon β I.Λ (m - 1) ^ q β * a β I.Λ (m - 1) =
        epsilon β I.Λ (m - 1) ^ (q β + β - 2) := by
      rw [a, ← Real.rpow_add he]
      congr 1; ring
    calc
      epsilon β I.Λ m * a β I.Λ (m - 1) ≤
          ((1 + Infra.Ingredients.supergeoConstant β) *
            epsilon β I.Λ (m - 1) ^ q β) * a β I.Λ (m - 1) := by
              exact mul_le_mul_of_nonneg_right (hupper.trans
                (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg he.le _)))
                (Real.rpow_nonneg he.le _)
      _ = (1 + Infra.Ingredients.supergeoConstant β) *
          (epsilon β I.Λ (m - 1) ^ q β * a β I.Λ (m - 1)) := by ring
      _ ≤ 1 + Infra.Ingredients.supergeoConstant β := by
        rw [heq]
        nlinarith [mul_nonneg hs (sub_nonneg.mpr hpw)]

theorem Recursion.constructionFlow_zero {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) :
    constructionFlow hseq 0 = fun _ x _ => x := by
  have hb : streamVel (Φ 0) = 0 := by
    rw [hseq.1]
    exact streamVel_spatialConstant (fun _ => 0)
  have hφ := streamSeq_isAdmissible hseq 0
  have hX : IsFlow (streamVel (Φ 0)) (constructionFlow hseq 0) := by
    simpa [constructionFlow] using flow_isFlow (streamVel (Φ 0))
      hφ.vel_continuous hφ.vel_lipschitz
  have hId : IsFlow (streamVel (Φ 0)) (fun _ x _ => x) := by
    constructor
    · intro x s; rfl
    · intro x s t
      rw [hb]
      exact hasDerivAt_const t x
  have hL : ∃ L : ℝ, ∀ t x y,
      ‖streamVel (Φ 0) t x - streamVel (Φ 0) t y‖ ≤ L * ‖x - y‖ := by
    refine ⟨0, ?_⟩
    intro; rw [hb]; simp
  have heq := Infra.Flow.flow_eq_of_isFlow (streamVel (Φ 0)) hL hX hId
  simpa [constructionFlow] using heq

theorem Recursion.constructionFlowInv_zero {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) :
    constructionFlowInv hseq 0 = fun _ x _ => x := by
  have hz := Recursion.constructionFlow_zero hseq
  have hφ := streamSeq_isAdmissible hseq 0
  have hz' : flow (streamVel (Φ 0)) hφ.vel_continuous hφ.vel_lipschitz =
      fun _ x _ => x := by simpa [constructionFlow] using hz
  funext t x s i
  change (flow (streamVel (Φ 0)) hφ.vel_continuous hφ.vel_lipschitz s x t) i = x i
  exact congrFun (congrFun (congrFun (congrFun hz' s) x) t) i

theorem Recursion.constructionFlowInvJacobian_zero {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (t s : ℝ) (x : Vec 2) :
    constructionFlowInvJacobian hseq 0 t s x = ContinuousLinearMap.id ℝ (Vec 2) := by
  simp [constructionFlowInvJacobian, Recursion.constructionFlowInv_zero hseq]

theorem Recursion.transported_profile_deriv_bound {β C Cmat : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (hflow : FlowBoundsData I Φ hseq Cmat)
    {m : ℕ} (hm : 1 ≤ m)
    (k : ℤ) {c : ℝ → ℝ} {c' : ℝ} (hcdef : c = Recursion.recursionCutoff I m k)
    {Y : ℝ → Vec 2} {D : ℝ → Vec 2 →L[ℝ] Vec 2}
    {Ydot : Vec 2} {Ddot : Vec 2 →L[ℝ] Vec 2} (t : ℝ)
    (j : Fin 2) (hc : HasDerivAt c c' t)
    (hcval : c t ∈ Set.Icc 0 1) (hY : HasDerivAt Y Ydot t)
    (hD : ∀ v, HasDerivAt (fun r => D r v) (Ddot v) t)
    (hactive : c t ≠ 0 → ‖Ydot‖ ≤ 2 * (2 * (|C| + 1) ^ 2) ∧
      ‖D t (basisVec j)‖ ≤ 2 ∧ ‖Ddot (basisVec j)‖ ≤ 16 *
        (Cmat * epsilon β I.Λ (m - 1) ^ (β - 2) +
          2 ^ 15 * (epsilon β I.Λ (m - 1))⁻¹ * (2 * (|C| + 1) ^ 2))) :
    |deriv (fun r => c r * fderiv ℝ (psi β I.Λ m k) (Y r)
      (D r (basisVec j))) t| ≤
      (80 * I.Czeta * I.Chat *
        (2 ^ 33 * (1 + Infra.Ingredients.supergeoConstant β)) +
        1152 * (2 * (|C| + 1) ^ 2) +
        320 * Cmat * (1 + Infra.Ingredients.supergeoConstant β) +
        320 * 2 ^ 15 * (2 * (|C| + 1) ^ 2)) * a β I.Λ m := by
  let B : ℝ := 2 * (|C| + 1) ^ 2
  let K : ℝ := Cmat * epsilon β I.Λ (m - 1) ^ (β - 2) +
    2 ^ 15 * (epsilon β I.Λ (m - 1))⁻¹ * B
  let T : ℝ := 2 ^ 33 * (1 + Infra.Ingredients.supergeoConstant β)
  let H : ℝ := 80 * I.Czeta * I.Chat * T + 1152 * B +
    320 * Cmat * (1 + Infra.Ingredients.supergeoConstant β) + 320 * 2 ^ 15 * B
  have ha : 0 < a β I.Λ m := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he : 0 < epsilon β I.Λ m := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
  have he1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hp : 0 < epsilon β I.Λ (m - 1) := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
  have hbeta : 0 < β - 1 := by linarith [I.one_lt_beta]
  have hS : 0 ≤ Infra.Ingredients.supergeoConstant β := by
    have hq : 0 < q β := lt_trans zero_lt_one
      (Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt)
    dsimp [Infra.Ingredients.supergeoConstant]; positivity
  have hT : 0 ≤ T := by dsimp [T]; nlinarith
  have hCz : 0 ≤ I.Czeta := le_trans (by norm_num) I.one_le_Czeta
  have hChat : 0 ≤ I.Chat := le_trans (by norm_num) I.one_le_Chat
  have hCmat : 0 ≤ Cmat := le_trans (by norm_num) hflow.material_constant_ge_one
  have hscale := epsilon_div_tau_le_constant (β := β) (I := I) m hm
  have hτ := tau_le_tauP (β := β) (I := I) m hm
  have hτpos := I.tau_pos' m
  have hτPpos := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hinv : (tauP β I.Λ m)⁻¹ ≤ (tau β I.Λ m)⁻¹ :=
    by simpa [one_div] using one_div_le_one_div_of_le hτpos hτ
  have hceq : c' = deriv (Recursion.recursionCutoff I m k) t := by
    simpa only [hcdef] using hc.deriv.symm
  have hinvτ : (tau β I.Λ m)⁻¹ ≤ T / epsilon β I.Λ m := by
    apply (le_div_iff₀ he).2
    simpa [one_div, div_eq_mul_inv, mul_comm] using hscale
  have hcut' : |c'| ≤ 2 * I.Czeta * I.Chat * T / epsilon β I.Λ m := by
    have hCz : 0 ≤ I.Czeta := le_trans (by norm_num) I.one_le_Czeta
    have hCh : 0 ≤ I.Chat := le_trans (by norm_num) I.one_le_Chat
    have hsum : (tau β I.Λ m)⁻¹ + (tauP β I.Λ m)⁻¹ ≤
        2 * (tau β I.Λ m)⁻¹ := by linarith
    calc
      |c'| ≤ I.Czeta * I.Chat *
          ((tau β I.Λ m)⁻¹ + (tauP β I.Λ m)⁻¹) := by
            rw [hceq]
            exact Recursion.recursionCutoff_deriv_bound m hm k t
      _ ≤ I.Czeta * I.Chat * (2 * (tau β I.Λ m)⁻¹) :=
            mul_le_mul_of_nonneg_left hsum (mul_nonneg hCz hCh)
      _ ≤ 2 * I.Czeta * I.Chat * (T / epsilon β I.Λ m) := by
            have hC : 0 ≤ 2 * I.Czeta * I.Chat := by positivity
            calc
              _ = (2 * I.Czeta * I.Chat) * (tau β I.Λ m)⁻¹ := by ring
              _ ≤ (2 * I.Czeta * I.Chat) * (T / epsilon β I.Λ m) :=
                mul_le_mul_of_nonneg_left hinvτ hC
      _ = 2 * I.Czeta * I.Chat * T / epsilon β I.Λ m := by ring
  have hcut : HasDerivAt c c' t := hc
  have hder := hasDerivAt_cutoff_mul_profile_spatialDerivative hcut
    (psi_timeIncrement_contDiff (β := β) (I := I) m k) hY hD (basisVec j)
  have hderiv := hder.deriv
  by_cases hz : c t = 0
  · have hczero : c' = 0 := by
      have hl := Recursion.recursionCutoff_deriv_zero_of_zero m hm k t (by simpa only [hcdef]
          using hz)
      rw [hceq]
      exact hl
    rw [hz, hczero] at hderiv
    have hnonneg : 0 ≤ H * a β I.Λ m :=
      mul_nonneg (by dsimp [H, T]; positivity) ha.le
    rw [hderiv]
    simpa [H, B, T] using hnonneg
  · have hca : 0 ≤ c t := hcval.1
    have hcb : c t ≤ 1 := hcval.2
    obtain ⟨hYnorm, hDcol, hDdot⟩ := hactive hz
    have hp0 := psi_first_partial_timeIncrement_le (β := β) (I := I) m k 0 (Y t)
    have hp1 := psi_first_partial_timeIncrement_le (β := β) (I := I) m k 1 (Y t)
    have hgradB : 0 ≤ 10 * a β I.Λ m * epsilon β I.Λ m := by positivity
    have hgrad0 := timeIncrement_clm_norm_le_two_basis (B := 10 * a β I.Λ m * epsilon β I.Λ m)
      hgradB hp0 hp1
    have hgrad : ‖fderiv ℝ (psi β I.Λ m k) (Y t)‖ ≤ 20 * a β I.Λ m * epsilon β I.Λ m := by
      calc _ ≤ 2 * (10 * a β I.Λ m * epsilon β I.Λ m) := hgrad0
        _ = 20 * a β I.Λ m * epsilon β I.Λ m := by ring
    have hprofile : |fderiv ℝ (psi β I.Λ m k) (Y t) (D t (basisVec j))| ≤
        40 * a β I.Λ m * epsilon β I.Λ m := by
      rw [← Real.norm_eq_abs]
      calc
        _ ≤ ‖fderiv ℝ (psi β I.Λ m k) (Y t)‖ * ‖D t (basisVec j)‖ :=
          (fderiv ℝ (psi β I.Λ m k) (Y t)).le_opNorm _
        _ ≤ (20 * a β I.Λ m * epsilon β I.Λ m) * 2 :=
          mul_le_mul hgrad hDcol (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hess := psi_hessian_apply_timeIncrement_le (β := β) (I := I) m k
      (Y t) Ydot (D t (basisVec j))
    have hDterm : |fderiv ℝ (psi β I.Λ m k) (Y t) (Ddot (basisVec j))| ≤
        320 * a β I.Λ m * epsilon β I.Λ m * K := by
      rw [← Real.norm_eq_abs]
      calc
        _ ≤ ‖fderiv ℝ (psi β I.Λ m k) (Y t)‖ * ‖Ddot (basisVec j)‖ :=
          (fderiv ℝ (psi β I.Λ m k) (Y t)).le_opNorm _
        _ ≤ (20 * a β I.Λ m * epsilon β I.Λ m) * (16 * K) :=
          mul_le_mul hgrad hDdot (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have heβ := Real.rpow_le_one he.le he1 (by linarith : 0 ≤ β - 1)
    have hratio := Recursion.epsilon_mul_previous_amplitude_le (β := β) (I := I) m hm
    have hratioAmp : epsilon β I.Λ m * epsilon β I.Λ (m - 1) ^ (β - 2) ≤
        1 + Infra.Ingredients.supergeoConstant β := by
      simpa [a] using hratio
    have hminsep := Infra.Ingredients.epsilon_minsep I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m - 1)
    have hΛ : 1 ≤ (I.Λ : ℝ) := by
      exact_mod_cast le_trans (by norm_num : 1 ≤ 2 ^ 7) I.two_pow_seven_le
    have hprevle : epsilon β I.Λ m ≤ epsilon β I.Λ (m - 1) := by
      simpa [Nat.sub_add_cancel hm] using (le_trans
        (mul_le_mul_of_nonneg_right hΛ (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
          I.two_pow_seven_le (m := m)).le)
        (by simpa [Nat.sub_add_cancel hm] using hminsep))
    have hratio' : epsilon β I.Λ m / epsilon β I.Λ (m - 1) ≤ 1 :=
      (div_le_iff₀ hp).2 (by nlinarith [hprevle])
    have hterm : epsilon β I.Λ m * K ≤
      Cmat * (1 + Infra.Ingredients.supergeoConstant β) + 2 ^ 15 * B := by
      dsimp [K, B]
      have hratioAmp' : epsilon β I.Λ m * epsilon β I.Λ (m - 1) ^ (β - 2) ≤
          1 + Infra.Ingredients.supergeoConstant β := by
        simpa [a] using hratio
      calc
        _ = Cmat * (epsilon β I.Λ m * epsilon β I.Λ (m - 1) ^ (β - 2)) +
            2 ^ 15 * B * (epsilon β I.Λ m / epsilon β I.Λ (m - 1)) := by
              rw [div_eq_mul_inv]
              ring
        _ ≤ Cmat * (1 + Infra.Ingredients.supergeoConstant β) + 2 ^ 15 * B := by
              have hB0 : 0 ≤ B := by dsimp [B]; positivity
              calc
                _ ≤ Cmat * (1 + Infra.Ingredients.supergeoConstant β) +
                    2 ^ 15 * B * 1 := add_le_add
                      (mul_le_mul_of_nonneg_left hratioAmp'
                        (by linarith [hflow.material_constant_ge_one]))
                      (mul_le_mul_of_nonneg_left hratio' (by positivity : 0 ≤ 2 ^ 15 * B))
                _ = _ := by ring
    have hprofH : |fderiv ℝ (fderiv ℝ (psi β I.Λ m k)) (Y t) Ydot
        (D t (basisVec j))| ≤ 1152 * a β I.Λ m * B := by
      calc
        _ ≤ 4 * (72 * a β I.Λ m) * ‖Ydot‖ * ‖D t (basisVec j)‖ := hess
        _ ≤ 4 * (72 * a β I.Λ m) * (2 * B) * 2 := by gcongr
        _ = 1152 * a β I.Λ m * B := by dsimp [B]; ring
    have hDprofile : |fderiv ℝ (psi β I.Λ m k) (Y t) (Ddot (basisVec j))| ≤
        320 * a β I.Λ m * (Cmat * (1 + Infra.Ingredients.supergeoConstant β) +
          2 ^ 15 * B) := by
      calc
        _ ≤ 320 * a β I.Λ m * epsilon β I.Λ m * K := hDterm
        _ = (320 * a β I.Λ m) * (epsilon β I.Λ m * K) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hterm (by positivity)
    have hcabs : |c t| ≤ 1 := abs_le.mpr ⟨by linarith, hcb⟩
    have hcutprod : |c'| * |fderiv ℝ (psi β I.Λ m k) (Y t)
        (D t (basisVec j))| ≤ 80 * I.Czeta * I.Chat * T * a β I.Λ m := by
      calc
        _ ≤ (2 * I.Czeta * I.Chat * T / epsilon β I.Λ m) *
            (40 * a β I.Λ m * epsilon β I.Λ m) :=
              mul_le_mul hcut' hprofile (abs_nonneg _) (by positivity)
        _ = 80 * I.Czeta * I.Chat * T * a β I.Λ m := by field_simp [he.ne']; ring
    have hrest : |c t| *
        (|fderiv ℝ (fderiv ℝ (psi β I.Λ m k)) (Y t) Ydot (D t (basisVec j))| +
          |fderiv ℝ (psi β I.Λ m k) (Y t) (Ddot (basisVec j))|) ≤
        (1152 * B + 320 * Cmat * (1 + Infra.Ingredients.supergeoConstant β) +
          320 * 2 ^ 15 * B) * a β I.Λ m := by
      calc
        _ ≤ 1 * (1152 * a β I.Λ m * B + 320 * a β I.Λ m *
            (Cmat * (1 + Infra.Ingredients.supergeoConstant β) + 2 ^ 15 * B)) :=
              mul_le_mul hcabs (add_le_add hprofH hDprofile) (by positivity) (by norm_num)
        _ = _ := by ring
    have hderivBound : |c' * fderiv ℝ (psi β I.Λ m k) (Y t) (D t (basisVec j)) +
        c t * (fderiv ℝ (fderiv ℝ (psi β I.Λ m k)) (Y t) Ydot (D t (basisVec j)) +
          fderiv ℝ (psi β I.Λ m k) (Y t) (Ddot (basisVec j)))| ≤ H * a β I.Λ m := by
      let P := fderiv ℝ (psi β I.Λ m k) (Y t) (D t (basisVec j))
      let Q := fderiv ℝ (fderiv ℝ (psi β I.Λ m k)) (Y t) Ydot (D t (basisVec j))
      let R := fderiv ℝ (psi β I.Λ m k) (Y t) (Ddot (basisVec j))
      have habs : |c' * P + c t * (Q + R)| ≤
          |c'| * |P| + |c t| * (|Q| + |R|) := by
        calc
          _ ≤ |c' * P| + |c t * (Q + R)| := abs_add_le (c' * P) (c t * (Q + R))
          _ = |c'| * |P| + |c t| * |Q + R| := by rw [abs_mul, abs_mul]
          _ ≤ _ := add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (abs_add_le Q R) (abs_nonneg _))
      calc
        _ ≤ |c'| * |P| + |c t| * (|Q| + |R|) := by simpa [P, Q, R] using habs
        _ ≤ 80 * I.Czeta * I.Chat * T * a β I.Λ m +
            (1152 * B + 320 * Cmat * (1 + Infra.Ingredients.supergeoConstant β) +
              320 * 2 ^ 15 * B) * a β I.Λ m := by
                simpa [P, Q, R] using add_le_add hcutprod hrest
        _ = H * a β I.Λ m := by dsimp [H]; ring
    have hnonneg : 0 ≤ H * a β I.Λ m := mul_nonneg (by dsimp [H, B, T]; positivity) ha.le
    rw [hderiv]
    exact hderivBound

theorem Recursion.nextStreamTerm_fderiv_formula {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (m : ℕ) (_hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (k : ℤ) (t : ℝ) (x : Vec 2) (j : Fin 2) :
    DifferentiableAt ℝ (fun y : Vec 2 => I.nextStreamTerm m (Φ (m - 1)) hφ t y k) x ∧
    fderiv ℝ (fun y : Vec 2 => I.nextStreamTerm m (Φ (m - 1)) hφ t y k) x
        (basisVec j) =
      Recursion.recursionCutoff I m k t *
        fderiv ℝ (psi β I.Λ m k)
          (constructionFlowInv hseq (m - 1) t x
            ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m))
          (constructionFlowInvJacobian hseq (m - 1)
            (t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)
            ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) x (basisVec j)) := by
  let s : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m
  let Y : Vec 2 → Vec 2 := fun y => constructionFlowInv hseq (m - 1) t y s
  have hprev : IsAdmissibleStream (Φ (m - 1)) := streamSeq_isAdmissible hseq (m - 1)
  have hproof : hφ = hprev := Subsingleton.elim _ _
  have hb : Infra.Flow.SmoothPeriodicField (streamVel (Φ (m - 1))) :=
    Infra.Construction.smoothPeriodic_streamVel hprev
  have hφprev := streamSeq_isAdmissible hseq (m - 1)
  have hX : IsFlow (streamVel (Φ (m - 1))) (constructionFlow hseq (m - 1)) := by
    simpa [constructionFlow] using flow_isFlow (streamVel (Φ (m - 1)))
      hφprev.vel_continuous hφprev.vel_lipschitz
  have hYcont : ContDiff ℝ 1 Y := by
    dsimp [Y]
    simpa [constructionFlowInv, constructionFlow, flowInv] using
      Infra.Flow.flow_spatial_contDiff_one hb hX t s
  have hYdiff : DifferentiableAt ℝ Y x := hYcont.differentiable (by norm_num) x
  have hYf : HasFDerivAt Y
      (constructionFlowInvJacobian hseq (m - 1) (t - s) s x) x := by
    simpa [Y, constructionFlowInvJacobian, add_sub_cancel_left] using hYdiff.hasFDerivAt
  have hψ : DifferentiableAt ℝ (psi β I.Λ m k)
      (constructionFlowInv hseq (m - 1) t x s) := by
    exact (psi_timeIncrement_contDiff (β := β) (I := I) m k).differentiable
      (by norm_num) _
  have hcomp := hψ.hasFDerivAt.comp x hYf
  have hterm := hcomp.const_smul
    (I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t)
  have heq : (fun y : Vec 2 => I.nextStreamTerm m (Φ (m - 1)) hφ t y k) =ᶠ[𝓝 x]
      (fun y : Vec 2 =>
        (I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t) •
          psi β I.Λ m k (constructionFlowInv hseq (m - 1) t y s)) := by
    filter_upwards with y
    simp [Ingredients.nextStreamTerm, constructionFlowInv, s, smul_eq_mul]
  have htermF := hterm.congr_of_eventuallyEq heq
  have hfd := htermF.fderiv
  have hval := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec j)) hfd
  constructor
  · exact htermF.differentiableAt
  · simpa [Recursion.recursionCutoff, s, smul_eq_mul, ContinuousLinearMap.comp_apply] using hval

theorem Recursion.recursionCutoff_active_time_window {β : ℝ} {I : Ingredients β}
    (m : ℕ) (hm : 1 ≤ m) (k : ℤ) (t : ℝ)
    (hactive : Recursion.recursionCutoff I m k t ≠ 0) :
    |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤
      2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by
  have hhat : I.hatZetaML m (lIdx β I.Λ m k) t ≠ 0 := by
    intro hz
    apply hactive
    simp [Recursion.recursionCutoff, hz]
  have hdist := Recursion.hatZetaML_ne_zero_distance hm (lIdx β I.Λ m k) t hhat
  have hτ := Infra.Construction.tauPP_inverse_amplitude_bound
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hm
  have hpow := Recursion.epsilon_rpow_delta_le_one (β := β) (I := I) (m - 1)
  have ha : 0 ≤ (a β I.Λ (m - 1))⁻¹ := inv_nonneg.mpr
    (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hbase : 0 ≤ (2 : ℝ) ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ :=
    mul_nonneg (by positivity) ha
  calc
    |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m / 2 := hdist
    _ ≤ (2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ *
        epsilon β I.Λ (m - 1) ^ delta β) / 2 := by
          exact div_le_div_of_nonneg_right hτ (by norm_num)
    _ ≤ 2 ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by
          have hp := mul_le_mul_of_nonneg_left hpow hbase
          nlinarith [Real.rpow_nonneg
            (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
              I.two_pow_seven_le (m := m - 1)).le (delta β)]

/-- Constant controlling the spatial derivative of a recursive profile. -/
def recursionProfileDerivativeConstant {β : ℝ} {I : Ingredients β}
    (C Cmat : ℝ) : ℝ :=
  80 * I.Czeta * I.Chat *
      (2 ^ 33 * (1 + Infra.Ingredients.supergeoConstant β)) +
    1152 * (2 * (|C| + 1) ^ 2) +
    320 * Cmat * (1 + Infra.Ingredients.supergeoConstant β) +
    320 * 2 ^ 15 * (2 * (|C| + 1) ^ 2)

/-- Cutoff-weighted spatial derivative of a single recursive profile. -/
def Recursion.recursionProfileSpatialDerivative {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (m : ℕ) (k : ℤ) (x : Vec 2) (j : Fin 2) : ℝ → ℝ :=
  fun r => Recursion.recursionCutoff I m k r *
    fderiv ℝ (psi β I.Λ m k)
      (constructionFlowInv hseq (m - 1) r x
        ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m))
      (constructionFlowInvJacobian hseq (m - 1)
        (r - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)
        ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) x (basisVec j))

theorem Recursion.recursion_profile_component_deriv_bound {β C Cmat : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (hreg : StreamRegularityBounds C I Φ)
    (hflow : FlowBoundsData I Φ hseq Cmat) (m : ℕ) (hm : 1 ≤ m)
    (k : ℤ) (t : ℝ) (x : Vec 2) (j : Fin 2) :
    DifferentiableAt ℝ (Recursion.recursionProfileSpatialDerivative hseq m k x j) t ∧
    abs (deriv (Recursion.recursionProfileSpatialDerivative hseq m k x j) t) ≤
      recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m := by
  let s : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m
  let c : ℝ → ℝ := Recursion.recursionCutoff I m k
  let Y : ℝ → Vec 2 := fun r => constructionFlowInv hseq (m - 1) r x s
  let D : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => constructionFlowInvJacobian hseq (m - 1) (r - s) s x
  let p := m - 1
  let Ydot : Vec 2 :=
    -(constructionFlowInvJacobian hseq p (t - s) s x (streamVel (Φ p) t x))
  let Ddot : Vec 2 →L[ℝ] Vec 2 :=
    deriv D t
  have hcut : HasDerivAt c (deriv c t) t := by
    exact (((Recursion.recursionCutoff_contDiff m k).contDiffAt (x := t)).differentiableAt
      (by norm_num)).hasDerivAt
  have hcval : c t ∈ Set.Icc 0 1 := by
    have hh := Infra.Section3.hatZetaML_mem_Icc I hm (lIdx β I.Λ m k) t
    have hz := Infra.Section3.zetaMK_mem_Icc (m := m) I k t
    change 0 ≤ I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t ∧
      I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t ≤ 1
    constructor
    · exact mul_nonneg hh.1 hz.1
    · calc
        _ ≤ 1 * 1 := mul_le_mul hh.2 hz.2 hz.1 (by norm_num)
        _ = 1 := by norm_num
  have hY : HasDerivAt Y Ydot t := by
    by_cases hmone : m = 1
    · subst m
      have hvel0 : streamVel (Φ 0) = 0 := by
        rw [hseq.1]
        exact streamVel_spatialConstant (fun _ => 0)
      have hYdotzero : Ydot = 0 := by
        dsimp [Ydot, p]
        simp [Recursion.constructionFlowInvJacobian_zero hseq, hvel0]
      have hconst : Y = fun _ => (x : Vec 2) := by
        funext r
        simp [Y, Recursion.constructionFlowInv_zero hseq]
      rw [hconst, hYdotzero]
      exact hasDerivAt_const t x
    · have hp : 1 ≤ p := by dsimp [p]; omega
      have hsource := hflow.inverse_transport p hp t s x
      simpa [Y, Ydot, p, constructionFlowInv] using hsource
  have hD : ∀ v : Vec 2, HasDerivAt (fun r => D r v) (Ddot v) t := by
    by_cases hmone : m = 1
    · subst m
      intro v
      have hconst : D = fun _ => ContinuousLinearMap.id ℝ (Vec 2) := by
        funext r
        exact Recursion.constructionFlowInvJacobian_zero hseq (r - s) s x
      have hDdotzero : Ddot = 0 := by
        have hconst : D = fun _ => ContinuousLinearMap.id ℝ (Vec 2) := by
          funext r
          exact Recursion.constructionFlowInvJacobian_zero hseq (r - s) s x
        simp [Ddot, hconst]
      rw [hconst, hDdotzero]
      simpa using (hasDerivAt_const t
        ((ContinuousLinearMap.id ℝ (Vec 2)) v))
    · have hp : 1 ≤ p := by dsimp [p]; omega
      intro v
      let G : ℝ → Vec 2 →L[ℝ] Vec 2 :=
        fun u => constructionFlowInvJacobian hseq p u s x
      have hG : DifferentiableAt ℝ G (t - s) := by
        exact hflow.inverse_jacobian_time_diff p hp s (t - s) x
      have hshift : DifferentiableAt ℝ (fun r : ℝ => r - s) t := by fun_prop
      have hcomp := DifferentiableAt.comp t hG hshift
      have hcol := hcomp.hasDerivAt.clm_apply (hasDerivAt_const t v)
      simpa [D, Ddot, G, Function.comp_def] using hcol
  have hactive : c t ≠ 0 →
      ‖Ydot‖ ≤ 2 * (2 * (|C| + 1) ^ 2) ∧
      ‖D t (basisVec j)‖ ≤ 2 ∧
      ‖Ddot (basisVec j)‖ ≤ 16 *
        (Cmat * epsilon β I.Λ (m - 1) ^ (β - 2) +
          2 ^ 15 * (epsilon β I.Λ (m - 1))⁻¹ * (2 * (|C| + 1) ^ 2)) := by
    intro hc
    have hwindow := Recursion.recursionCutoff_active_time_window m hm k t hc
    by_cases hmone : m = 1
    · subst m
      have hYdotzero : Ydot = 0 := by
        have hvel0 : streamVel (Φ 0) = 0 := by
          rw [hseq.1]
          exact streamVel_spatialConstant (fun _ => 0)
        dsimp [Ydot, p]
        simp [Recursion.constructionFlowInvJacobian_zero hseq, hvel0]
      have hDcol : ‖D t (basisVec j)‖ ≤ 2 := by
        dsimp [D]
        rw [Recursion.constructionFlowInvJacobian_zero hseq]
        have hb : ‖basisVec j‖ = 1 := by fin_cases j <;> simp [basisVec, Pi.norm_single]
        calc
          ‖(ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j)‖ = 1 := by
            simpa using hb
          _ ≤ 2 := by norm_num
      have hDdotzero : Ddot (basisVec j) = 0 := by
        have hconst : D = fun _ => ContinuousLinearMap.id ℝ (Vec 2) := by
          funext r
          exact Recursion.constructionFlowInvJacobian_zero hseq (r - s) s x
        simp [Ddot, hconst]
      have hbound : 0 ≤ 16 *
          (Cmat * epsilon β I.Λ (1 - 1) ^ (β - 2) +
            2 ^ 15 * (epsilon β I.Λ (1 - 1))⁻¹ * (2 * (|C| + 1) ^ 2)) := by
        have he0 : 0 < epsilon β I.Λ 0 :=
          Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
        have hC : 0 < Cmat := lt_of_lt_of_le (by norm_num) hflow.material_constant_ge_one
        have hpow : 0 ≤ epsilon β I.Λ 0 ^ (β - 2) :=
          Real.rpow_nonneg he0.le _
        have hB : 0 ≤ 2 * (|C| + 1) ^ 2 := by positivity
        have hsum : 0 ≤ Cmat * epsilon β I.Λ 0 ^ (β - 2) +
            2 ^ 15 * (epsilon β I.Λ 0)⁻¹ * (2 * (|C| + 1) ^ 2) := by
          apply add_nonneg
          · exact mul_nonneg hC.le hpow
          · exact mul_nonneg (mul_nonneg (by positivity)
              (inv_nonneg.mpr he0.le)) hB
        simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hsum)
      refine ⟨?_, hDcol, ?_⟩
      · simpa [hYdotzero] using
          (show 0 ≤ 2 * (2 * (|C| + 1) ^ 2) by positivity)
      rw [hDdotzero]
      simpa using hbound
    · have hp : 1 ≤ p := by dsimp [p]; omega
      have hwindow' : |t - s| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ p)⁻¹ := by
        simpa [p, s] using hwindow
      have hJ := inverse_flowJacobian_column_bound hflow p hp s (t - s)
        hwindow' x
      have hvel := stream_member_velocity_bound hseq hreg p t x
      have hYbound : ‖Ydot‖ ≤ 2 * (2 * (|C| + 1) ^ 2) := by
        dsimp [Ydot, p]
        rw [norm_neg]
        calc
          ‖constructionFlowInvJacobian hseq p (t - s) s x
              (streamVel (Φ p) t x)‖ ≤
              ‖constructionFlowInvJacobian hseq p (t - s) s x‖ *
                ‖streamVel (Φ p) t x‖ :=
                  (constructionFlowInvJacobian hseq p (t - s) s x).le_opNorm _
          _ ≤ 2 * (2 * (|C| + 1) ^ 2) := by
            exact mul_le_mul hJ hvel (norm_nonneg _) (by positivity)
      have hDcol : ‖D t (basisVec j)‖ ≤ 2 := by
        dsimp [D]
        have hnorm : ‖constructionFlowInvJacobian hseq p (t - s) s x‖ ≤ 2 := by
          exact inverse_flowJacobian_column_bound hflow p hp s (t - s) hwindow' x
        have hb : ‖basisVec j‖ = 1 := by fin_cases j <;> simp [basisVec, Pi.norm_single]
        calc
          _ ≤ ‖constructionFlowInvJacobian hseq p (t - s) s x‖ *
              ‖basisVec j‖ := (constructionFlowInvJacobian hseq p (t - s) s x).le_opNorm _
          _ ≤ 2 := by simpa [hb] using hnorm
      have hK := inverseFlowJacobian_column_time_deriv_bound
        hflow hreg (m := p) hp s (t - s) hwindow' x j
      have hG : DifferentiableAt ℝ
          (fun u => constructionFlowInvJacobian hseq p u s x) (t - s) :=
        hflow.inverse_jacobian_time_diff p hp s (t - s) x
      have hshift : HasDerivAt (fun r : ℝ => r - s) 1 t := by
        simpa using (hasDerivAt_id t).sub_const s
      have hchain := hG.hasDerivAt.scomp t hshift
      have hDdotEq : Ddot = deriv
          (fun u => constructionFlowInvJacobian hseq p u s x) (t - s) := by
        simpa [Ddot, D, Function.comp_def] using hchain.deriv
      have hcol := hG.hasDerivAt.clm_apply
        (hasDerivAt_const (t - s) (basisVec j))
      have hDdotcol : ‖Ddot (basisVec j)‖ ≤ 16 *
          (Cmat * epsilon β I.Λ p ^ (β - 2) +
            2 ^ 15 * (epsilon β I.Λ p)⁻¹ * (2 * (|C| + 1) ^ 2)) := by
        have heq : deriv (fun u =>
            constructionFlowInvJacobian hseq p u s x (basisVec j)) (t - s) =
            (deriv (fun u => constructionFlowInvJacobian hseq p u s x)
              (t - s)) (basisVec j) := by
          simpa using hcol.deriv
        rw [hDdotEq, ← heq]
        exact hK
      simpa [p] using ⟨hYbound, hDcol, hDdotcol⟩
  have hbound := Recursion.transported_profile_deriv_bound hflow (m := m) hm k
    (c := c) (c' := deriv c t) rfl (Y := Y) (D := D)
    (Ydot := Ydot) (Ddot := Ddot) t j hcut hcval hY hD hactive
  have hhas := hasDerivAt_cutoff_mul_profile_spatialDerivative hcut
    (psi_timeIncrement_contDiff (β := β) (I := I) m k) hY hD (basisVec j)
  constructor
  · change DifferentiableAt ℝ
      (fun r => c r * fderiv ℝ (psi β I.Λ m k) (Y r) (D r (basisVec j))) t
    exact hhas.differentiableAt
  · change abs (deriv (fun r =>
        c r * fderiv ℝ (psi β I.Λ m k) (Y r) (D r (basisVec j))) t) ≤
      (80 * I.Czeta * I.Chat *
        (2 ^ 33 * (1 + Infra.Ingredients.supergeoConstant β)) +
        1152 * (2 * (|C| + 1) ^ 2) +
        320 * Cmat * (1 + Infra.Ingredients.supergeoConstant β) +
        320 * 2 ^ 15 * (2 * (|C| + 1) ^ 2)) * a β I.Λ m
    exact hbound

/-- Velocity associated with one cutoff-weighted term of the stream recursion. -/
def Recursion.recursionTermVelocity {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (_hseq : IsStreamSeq I Φ)
    (m : ℕ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (k : ℤ) (x : Vec 2) : ℝ → Vec 2 :=
  fun r => timeIncrementRotate
    (fderiv ℝ (fun y : Vec 2 => I.nextStreamTerm m (Φ (m - 1)) hφ r y k) x)

theorem Recursion.recursionTermVelocity_hasDeriv_bound {β C Cmat : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (hflow : FlowBoundsData I Φ hseq Cmat) (m : ℕ) (hm : 1 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (k : ℤ) (t : ℝ) (x : Vec 2) :
    HasDerivAt (Recursion.recursionTermVelocity hseq m hφ k x)
      (deriv (Recursion.recursionTermVelocity hseq m hφ k x) t) t ∧
    ‖deriv (Recursion.recursionTermVelocity hseq m hφ k x) t‖ ≤
      2 * recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m := by
  let V := Recursion.recursionTermVelocity hseq m hφ k x
  let d0 := deriv (Recursion.recursionProfileSpatialDerivative hseq m k x 1) t
  let d1 := deriv (Recursion.recursionProfileSpatialDerivative hseq m k x 0) t
  let Vdot : Vec 2 := fun i => if i = 0 then -d0 else d1
  have hprof0 := Recursion.recursion_profile_component_deriv_bound hreg hflow m hm k t x 0
  have hprof1 := Recursion.recursion_profile_component_deriv_bound hreg hflow m hm k t x 1
  have hformula (j : Fin 2) (r : ℝ) :
      fderiv ℝ (fun y : Vec 2 => I.nextStreamTerm m (Φ (m - 1)) hφ r y k) x
        (basisVec j) = Recursion.recursionProfileSpatialDerivative hseq m k x j r := by
    exact (Recursion.nextStreamTerm_fderiv_formula hseq m hm hφ k r x j).2
  have hcoord0 : HasDerivAt (fun r => V r 0) (-d0) t := by
    have hneg := hprof1.1.hasDerivAt.neg
    apply hneg.congr_of_eventuallyEq
    filter_upwards with r
    simp [V, Recursion.recursionTermVelocity, timeIncrementRotate, hformula 1 r]
  have hcoord1 : HasDerivAt (fun r => V r 1) d1 t := by
    apply hprof0.1.hasDerivAt.congr_of_eventuallyEq
    filter_upwards with r
    simp [V, Recursion.recursionTermVelocity, timeIncrementRotate, hformula 0 r]
  have hV : HasDerivAt V Vdot t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [Vdot, d0] using hcoord0
    · simpa [Vdot, d1] using hcoord1
  have hd0 : |d0| ≤ recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m := by
    simpa [d0] using hprof1.2
  have hd1 : |d1| ≤ recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m := by
    simpa [d1] using hprof0.2
  have hnorm : ‖Vdot‖ ≤
      2 * recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m := by
    calc
      ‖Vdot‖ ≤ |Vdot 0| + |Vdot 1| := timeIncrement_vec_norm_le_coords _
      _ ≤ recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m +
          recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m := by
            simp only [Vdot]
            exact add_le_add (by simpa using hd0) (by simpa using hd1)
      _ = _ := by ring
  constructor
  · rw [← hV.deriv] at hV
    exact hV
  · rw [hV.deriv]
    exact hnorm

theorem Recursion.recursionCutoff_active_index {β : ℝ} {I : Ingredients β}
    (m : ℕ) (k : ℤ) (r t : ℝ)
    (hclose : |r - t| < tau β I.Λ m / 6)
    (hactive : Recursion.recursionCutoff I m k r ≠ 0) :
    k ∈ Set.Icc (⌊t / tau β I.Λ m⌋ : ℤ)
      ((⌊t / tau β I.Λ m⌋ : ℤ) + 1) := by
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hzk : I.zetaMK m k r ≠ 0 := by
    intro hz
    apply hactive
    simp [Recursion.recursionCutoff, hz]
  have hdist := Recursion.zetaMK_ne_zero_distance m k r hzk
  have htriangle : |t - (k : ℝ) * tau β I.Λ m| <
      5 / 6 * tau β I.Λ m := by
    calc
      |t - (k : ℝ) * tau β I.Λ m| = |(t - r) + (r - (k : ℝ) * tau β I.Λ m)| := by
        congr 1; ring
      _ ≤ |t - r| + |r - (k : ℝ) * tau β I.Λ m| := abs_add_le _ _
      _ < tau β I.Λ m / 6 + (2 / 3) * tau β I.Λ m := by
        have hclose' : |t - r| < tau β I.Λ m / 6 := by
          simpa [abs_sub_comm] using hclose
        nlinarith [hclose', hdist]
      _ = 5 / 6 * tau β I.Λ m := by ring
  have hquot : |t / tau β I.Λ m - (k : ℝ)| < 1 := by
    have hscaled : |t / tau β I.Λ m - (k : ℝ)| < 5 / 6 := by
      have hEq : t / tau β I.Λ m - (k : ℝ) =
          (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m := by
        field_simp
      rw [hEq, abs_div, abs_of_pos hτ]
      exact (div_lt_iff₀ hτ).2 htriangle
    linarith
  have hquot' := abs_lt.mp hquot
  have hfloorlow := Int.floor_le (t / tau β I.Λ m)
  have hfloorhigh := Int.lt_floor_add_one (t / tau β I.Λ m)
  simp only [Set.mem_Icc]
  constructor
  · by_contra hnot
    have hk : k < ⌊t / tau β I.Λ m⌋ := lt_of_not_ge hnot
    have hk' : (k : ℝ) + 1 ≤ (⌊t / tau β I.Λ m⌋ : ℝ) := by
      exact_mod_cast (show k + 1 ≤ ⌊t / tau β I.Λ m⌋ by omega)
    linarith
  · by_contra hnot
    have hk : ⌊t / tau β I.Λ m⌋ + 2 ≤ k := by omega
    have hk' : (⌊t / tau β I.Λ m⌋ : ℝ) + 2 ≤ (k : ℝ) := by
      exact_mod_cast hk
    have hquotlow : (k : ℝ) - 1 < t / tau β I.Λ m := by
      linarith [hquot'.1]
    linarith

theorem Recursion.recursion_velocity_eq_pair_sum {β : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (hrec : Φ m = I.nextStream m (Φ (m - 1)) hφ)
    (t r : ℝ) (x : Vec 2) (hclose : |r - t| < tau β I.Λ m / 6) :
    streamVel (Φ m) r x - streamVel (Φ (m - 1)) r x =
      ∑ k ∈ ({(⌊t / tau β I.Λ m⌋ : ℤ), (⌊t / tau β I.Λ m⌋ : ℤ) + 1} : Finset ℤ),
        Recursion.recursionTermVelocity hseq m hφ k x r := by
  classical
  let S : Finset ℤ := {(⌊t / tau β I.Λ m⌋ : ℤ), (⌊t / tau β I.Λ m⌋ : ℤ) + 1}
  let p := m - 1
  let T : Vec 2 → ℝ := fun y =>
    ∑ k ∈ S, I.nextStreamTerm m (Φ p) hφ r y k
  have htermzero (k : ℤ) (hk : k ∉ S) (y : Vec 2) :
      I.nextStreamTerm m (Φ p) hφ r y k = 0 := by
    have hcut : Recursion.recursionCutoff I m k r = 0 := by
      by_contra hne
      have hpair := Recursion.recursionCutoff_active_index m k r t hclose hne
      have hpair' : (⌊t / tau β I.Λ m⌋ : ℤ) ≤ k ∧
          k ≤ (⌊t / tau β I.Λ m⌋ : ℤ) + 1 := by simpa using hpair
      have hin : k ∈ S := by simp [S]; omega
      exact hk hin
    simpa [Ingredients.nextStreamTerm, Recursion.recursionCutoff] using congrArg
      (fun z : ℝ => z * psi β I.Λ m k
        (flowInv (streamVel (Φ p)) hφ.vel_continuous hφ.vel_lipschitz r y
          ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m))) hcut
  have htsum : (∑' k : ℤ, I.nextStreamTerm m (Φ p) hφ r x k) =
      ∑ k ∈ S, I.nextStreamTerm m (Φ p) hφ r x k := by
    apply tsum_eq_sum (s := S)
    intro k hk
    exact htermzero k hk x
  have hrecpoint (y : Vec 2) : Φ m r y = Φ p r y + T y := by
    calc
      Φ m r y = I.nextStream m (Φ p) hφ r y := by
        exact congrFun (congrFun hrec r) y
      _ = Φ p r y + ∑ k ∈ S, I.nextStreamTerm m (Φ p) hφ r y k := by
        rw [Ingredients.nextStream]
        congr 1
        apply tsum_eq_sum (s := S)
        intro k hk
        exact htermzero k hk y
  have hsumHas : HasFDerivAt T
      (∑ k ∈ S, fderiv ℝ
        (fun y : Vec 2 => I.nextStreamTerm m (Φ p) hφ r y k) x) x := by
    apply HasFDerivAt.fun_sum (u := S)
    intro k hk
    exact (Recursion.nextStreamTerm_fderiv_formula hseq m hm hφ k r x 0).1.hasFDerivAt
  have hprevHas : HasFDerivAt (Φ p r)
      (fderiv ℝ (Φ p r) x) x := by
    exact (((timeIncrementSlice_contDiff hseq p r).contDiffAt (x := x)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hadd := hprevHas.add hsumHas
  have hlocal : (fun y : Vec 2 => Φ p r y + T y) =ᶠ[𝓝 x] (Φ m r) :=
    Filter.Eventually.of_forall fun y => (hrecpoint y).symm
  have hcurrent := hadd.congr_of_eventuallyEq hlocal.symm
  have hfd := hcurrent.fderiv
  have hvelocity :
      streamVel (Φ m) r x - streamVel (Φ p) r x =
        ∑ k ∈ S, Recursion.recursionTermVelocity hseq m hφ k x r := by
    rw [streamVel_eq_timeIncrementRotate, streamVel_eq_timeIncrementRotate,
      hfd]
    ext i
    fin_cases i <;>
      simp [timeIncrementRotate, Recursion.recursionTermVelocity, S,
        Finset.sum_apply] <;> ring
  simpa [p, S] using hvelocity

/-- The source-derived constant in the time increment estimate, assembled
from the cutoff, inverse-flow, and material-Jacobian displays. -/
def differentiatedRecursionTimeConstant {β : ℝ} (I : Ingredients β)
    (C Cmat : ℝ) : ℝ :=
  4 * recursionProfileDerivativeConstant (I := I) C Cmat

/-- Differentiating the stream recursion on its two-index local overlap gives
the time increment bound required by the limit-field regularity argument. -/
theorem differentiated_recursion_time_increment_bound {β C Cmat : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (hflow : FlowBoundsData I Φ hseq Cmat) :
    StreamVelocityTimeIncrementBound
      (differentiatedRecursionTimeConstant I C Cmat) I Φ := by
  classical
  intro m hm s t x
  let F : ℝ → Vec 2 := fun r =>
    streamVel (Φ m) r x - streamVel (Φ (m - 1)) r x
  have hdiff : ∀ r : ℝ, DifferentiableAt ℝ F r := by
    intro r
    obtain ⟨hφ, hrec⟩ := hseq.2 m hm
    let S : Finset ℤ := {(⌊r / tau β I.Λ m⌋ : ℤ),
      (⌊r / tau β I.Λ m⌋ : ℤ) + 1}
    let G : ℝ → Vec 2 := fun q =>
      ∑ k ∈ S, Recursion.recursionTermVelocity hseq m hφ k x q
    let Gdot : Vec 2 :=
      ∑ k ∈ S, deriv (Recursion.recursionTermVelocity hseq m hφ k x) r
    have hGhas : HasDerivAt G Gdot r := by
      apply HasDerivAt.fun_sum (u := S)
      intro k hk
      exact (Recursion.recursionTermVelocity_hasDeriv_bound
        hseq hreg hflow m hm hφ k r x).1
    have hτ := I.tau_pos' m
    have hnear : Set.Ioo (r - tau β I.Λ m / 6) (r + tau β I.Λ m / 6) ∈ 𝓝 r := by
      apply isOpen_Ioo.mem_nhds
      constructor <;> linarith
    have hlocal : F =ᶠ[𝓝 r] G := by
      filter_upwards [hnear] with q hq
      have hclose : |q - r| < tau β I.Λ m / 6 := by
        rw [abs_lt]
        constructor <;> linarith [hq.1, hq.2]
      have hsum := Recursion.recursion_velocity_eq_pair_sum hseq m hm hφ hrec r q x hclose
      simpa [F, G, S] using hsum
    exact (hGhas.congr_of_eventuallyEq hlocal).differentiableAt
  have hderiv : ∀ r : ℝ, ‖deriv F r‖ ≤
      differentiatedRecursionTimeConstant I C Cmat * a β I.Λ m := by
    intro r
    obtain ⟨hφ, hrec⟩ := hseq.2 m hm
    let S : Finset ℤ := {(⌊r / tau β I.Λ m⌋ : ℤ),
      (⌊r / tau β I.Λ m⌋ : ℤ) + 1}
    let G : ℝ → Vec 2 := fun q =>
      ∑ k ∈ S, Recursion.recursionTermVelocity hseq m hφ k x q
    let Gdot : Vec 2 :=
      ∑ k ∈ S, deriv (Recursion.recursionTermVelocity hseq m hφ k x) r
    have hGhas : HasDerivAt G Gdot r := by
      apply HasDerivAt.fun_sum (u := S)
      intro k hk
      exact (Recursion.recursionTermVelocity_hasDeriv_bound
        hseq hreg hflow m hm hφ k r x).1
    have hτ := I.tau_pos' m
    have hnear : Set.Ioo (r - tau β I.Λ m / 6) (r + tau β I.Λ m / 6) ∈ 𝓝 r := by
      apply isOpen_Ioo.mem_nhds
      constructor <;> linarith
    have hlocal : F =ᶠ[𝓝 r] G := by
      filter_upwards [hnear] with q hq
      have hclose : |q - r| < tau β I.Λ m / 6 := by
        rw [abs_lt]
        constructor <;> linarith [hq.1, hq.2]
      have hsum := Recursion.recursion_velocity_eq_pair_sum hseq m hm hφ hrec r q x hclose
      simpa [F, G, S] using hsum
    have hFhas := hGhas.congr_of_eventuallyEq hlocal
    have htermBound (k : ℤ) (hk : k ∈ S) :
        ‖deriv (Recursion.recursionTermVelocity hseq m hφ k x) r‖ ≤
          2 * recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m :=
      (Recursion.recursionTermVelocity_hasDeriv_bound hseq hreg hflow m hm hφ k r x).2
    have hGdotBound : ‖Gdot‖ ≤
        4 * recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m := by
      calc
        ‖Gdot‖ ≤ ∑ k ∈ S,
            ‖deriv (Recursion.recursionTermVelocity hseq m hφ k x) r‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ S,
            2 * recursionProfileDerivativeConstant (I := I) C Cmat * a β I.Λ m :=
              Finset.sum_le_sum fun k hk => htermBound k hk
        _ = 2 * (2 * recursionProfileDerivativeConstant (I := I) C Cmat *
            a β I.Λ m) := by simp [S]
        _ = 4 * recursionProfileDerivativeConstant (I := I) C Cmat *
            a β I.Λ m := by ring
    have hfd := hFhas.deriv
    rw [hfd]
    simpa [differentiatedRecursionTimeConstant] using hGdotBound
  have hmv := norm_sub_le_of_uniform_deriv_le hdiff hderiv s t
  simpa [F, StreamVelocityTimeIncrementBound, a] using hmv

/-- The packaged limit-field regularity conclusion follows from the stream-regularity spatial data
and the explicit source-form flow/material bounds used to differentiate the
stream recursion. -/
theorem limit_field_regular_of_stream_regularity {β C Cmat α : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (hflow : FlowBoundsData I Φ hseq Cmat)
    (hα : 0 < α) (hαβ : α < β - 1) :
    ∃ φ : ℝ → Vec 2 → ℝ,
      (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) ∧
      (∀ M t x, |φ t x - Φ M t x| ≤ 11 * epsilon β I.Λ (M + 1) ^ β) ∧
      (∀ t, Differentiable ℝ (φ t)) ∧
      TendstoUniformlyOn (fun M (p : ℝ × Vec 2) => streamVel (Φ M) p.1 p.2)
        (fun p => streamVel φ p.1 p.2) atTop
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
      IsHolderClass α (streamVel φ) ∧ IsDivFree (streamVel φ) := by
  exact Infra.Construction.limitField_regular_conditional hseq hreg
    (differentiated_recursion_time_increment_bound hseq hreg hflow) hα hαβ

end AVenhance
