/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamVelocityConstants

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingEnergyReduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxScale

/-! Finite convex-combination bounds for the transition flux. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

theorem R46FluxEstimate.r46_abs_weighted_sum_le {ι : Type*} (S : Finset ι)
    (w f : ι → ℝ) (B : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hsum : ∑ i ∈ S, w i = 1)
    (hf : ∀ i ∈ S, |f i| ≤ B) :
    |∑ i ∈ S, w i * f i| ≤ B := by
  classical
  calc
    |∑ i ∈ S, w i * f i| ≤ ∑ i ∈ S, |w i * f i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ S, w i * |f i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ S, w i * B := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hf i hi) (hw i hi)
    _ = B := by rw [← Finset.sum_mul, hsum]; ring

theorem R46FluxEstimate.r46_matrix_diff_component {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (η : ℝ)
    (hAB : ∀ i j, |(A - B) i j| ≤ η / 2)
    (v : Vec 2) (i : Fin 2) :
    |((A - B).mulVec v) i| ≤ η * (|v 0| + |v 1|) / 2 := by
  have h0 := hAB i 0
  have h1 := hAB i 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  calc
    |(A - B) i 0 * v 0 + (A - B) i 1 * v 1| ≤
        |(A - B) i 0 * v 0| + |(A - B) i 1 * v 1| := abs_add_le _ _
    _ = |(A - B) i 0| * |v 0| + |(A - B) i 1| * |v 1| := by rw [abs_mul, abs_mul]
    _ ≤ (η / 2) * |v 0| + (η / 2) * |v 1| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right h0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
    _ = η * (|v 0| + |v 1|) / 2 := by ring

/-- Two successive finite convex averages preserve the entrywise flow
distortion bound, with the sharp two-dimensional Euclidean square constant. -/
theorem R46FluxEstimate.r46_finite_mixture_distortion
    {κ ι : Type*} (U : Finset κ) (S : Finset ι)
    (wk : κ → ℝ) (wl : ι → ℝ)
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (B : κ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : Vec 2) (η : ℝ)
    (hwk : ∀ k ∈ U, 0 ≤ wk k) (hsumk : ∑ k ∈ U, wk k = 1)
    (hwl : ∀ l ∈ S, 0 ≤ wl l) (hsuml : ∑ l ∈ S, wl l = 1)
    (hclose : ∀ k ∈ U, ∀ l ∈ S, ∀ i j,
      |(A l - B k) i j| ≤ η / 2) (hη : 0 ≤ η) :
    vecNormSq (∑ k ∈ U, wk k •
      ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) ≤
      η ^ 2 * vecNormSq v := by
  have hcoord (k : κ) (hk : k ∈ U) (i : Fin 2) :
      |(∑ l ∈ S, wl l • ((A l - B k).mulVec v)) i| ≤
        η * (|v 0| + |v 1|) / 2 := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    apply R46FluxEstimate.r46_abs_weighted_sum_le S wl
      (fun l => ((A l - B k).mulVec v) i)
      (η * (|v 0| + |v 1|) / 2)
    · exact hwl
    · exact hsuml
    · intro l hl
      exact R46FluxEstimate.r46_matrix_diff_component η (hclose k hk l hl) v i
  have hcoord' (i : Fin 2) :
      |(∑ k ∈ U, wk k •
        ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) i| ≤
        η * (|v 0| + |v 1|) / 2 := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    apply R46FluxEstimate.r46_abs_weighted_sum_le U wk
      (fun k => (∑ l ∈ S, wl l • ((A l - B k).mulVec v)) i)
      (η * (|v 0| + |v 1|) / 2)
    · exact hwk
    · exact hsumk
    · intro k hk
      exact hcoord k hk i
  have h0 := hcoord' 0
  have h1 := hcoord' 1
  have hbound : 0 ≤ η * (|v 0| + |v 1|) / 2 :=
    div_nonneg (mul_nonneg hη (add_nonneg (abs_nonneg _) (abs_nonneg _))) (by norm_num)
  have hsumSq : (|v 0| + |v 1|) ^ 2 ≤ 2 * vecNormSq v := by
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]
    have h0sq : |v 0| * |v 0| = v 0 * v 0 := by
      simpa only [pow_two] using (sq_abs (v 0))
    have h1sq : |v 1| * |v 1| = v 1 * v 1 := by
      simpa only [pow_two] using (sq_abs (v 1))
    nlinarith [sq_nonneg (|v 0| - |v 1|), h0sq, h1sq]
  have hsumSq' := hsumSq
  simp only [vecNormSq, vecDot, Fin.sum_univ_two] at hsumSq'
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  calc
    (∑ k ∈ U, wk k • ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) 0 *
      (∑ k ∈ U, wk k • ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) 0 +
      (∑ k ∈ U, wk k • ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) 1 *
      (∑ k ∈ U, wk k • ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) 1 ≤
        (η * (|v 0| + |v 1|) / 2) ^ 2 +
      (η * (|v 0| + |v 1|) / 2) ^ 2 := by
        have h0abs := abs_le.mp h0
        have h1abs := abs_le.mp h1
        nlinarith [hbound,
          sq_nonneg ((η * (|v 0| + |v 1|) / 2) -
            (∑ k ∈ U, wk k • ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) 0),
          sq_nonneg ((η * (|v 0| + |v 1|) / 2) +
            (∑ k ∈ U, wk k • ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) 0),
          sq_nonneg ((η * (|v 0| + |v 1|) / 2) -
            (∑ k ∈ U, wk k • ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) 1),
          sq_nonneg ((η * (|v 0| + |v 1|) / 2) +
            (∑ k ∈ U, wk k • ∑ l ∈ S, wl l • ((A l - B k).mulVec v)) 1)]
    _ = η ^ 2 * ((|v 0| + |v 1|) ^ 2 / 2) := by ring
    _ ≤ η ^ 2 * (v 0 * v 0 + v 1 * v 1) := by
        have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
        nlinarith [hsumSq', hη2]

theorem R46FluxEstimate.r46_xFlowInv_right_inverse_at
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x) = x := by
  let b := streamVel (Φ (m - 1))
  let F := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  have hF : IsFlow b F := flow_isFlow b
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  change F t (F s x t) s = x
  calc
    F t (F s x t) s = F t x t :=
      Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hF x t s t
    _ = x := hF.1 x t

/-- The two cutoff partitions turn the defect into a finite
double convex average of differences of flow Jacobians. -/
theorem R46FluxEstimate.r46_defect_eq_finite_mixture
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (hT : ContDiff ℝ 1 (T t))
    (x : Vec 2) :
    (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
      (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x)) =
      ∑ k ∈ (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m k.1 t •
          ∑ l ∈ (I.hatXiML_support_finite hm t).toFinset,
            I.hatXiML m l t •
              ((I.flowGrad hΦ m l t x -
                I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x).mulVec
                (spaceGrad (T t) x)) := by
  classical
  let S := (I.hatXiML_support_finite hm t).toFinset
  let U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  let η (l : ℤ) := I.hatXiML m l t
  let A (l : ℤ) := I.flowGrad hΦ m l t x
  let B (k : {k : ℤ // Odd k}) := I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x
  let v := spaceGrad (T t) x
  have hsumHat : ∑ l ∈ S, η l = 1 := by
    have hfinite : (∑ l ∈ S, η l) = ∑' l : ℤ, η l := by
      symm
      apply tsum_eq_sum
      intro l hl
      have hzero : η l = 0 := by
        by_contra hn
        exact hl ((I.hatXiML_support_finite hm t).mem_toFinset.mpr hn)
      simp [hzero]
    rw [hfinite]
    exact Infra.Ingredients.hatXiML_partition I hm t
  have hsumXi : ∑ k ∈ U, I.xiMK m k.1 t = 1 := by
    have hfinite : (∑ k ∈ U, I.xiMK m k.1 t) =
        ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t := by
      symm
      apply tsum_eq_sum
      intro k hk
      have hzero : I.xiMK m k.1 t = 0 := by
        by_contra hn
        exact hk ((Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mpr hn)
      simp [hzero]
    rw [hfinite]
    exact Infra.Section3.xiMK_odd_partition I hm t
  have hG (l : ℤ) : G I hΦ m T l t x = (A l).mulVec v := by
    exact G_eq_flowGrad_mulVec I hΦ m T l t x
      (hT.differentiable (by norm_num) x).hasFDerivAt
      ((xFlow_spatial_contDiff_two I hΦ m l t).differentiable
        (by norm_num) (I.xFlowInv hΦ m l t x)).hasFDerivAt
      (R46FluxEstimate.r46_xFlowInv_right_inverse_at hΦ m l t x)
  have hbar : Gbar I hΦ m T t x = ∑ l ∈ S, η l • (A l).mulVec v := by
    rw [Gbar_eq_finite_support I hΦ m hm T t x]
    apply Finset.sum_congr rfl
    intro l hl
    rw [hG l]
  have hinner (k : {k : ℤ // Odd k}) :
      Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x =
        ∑ l ∈ S, η l • ((A l - B k).mulVec v) := by
    have hsumB : ∑ l ∈ S, η l • (B k).mulVec v = (B k).mulVec v := by
      calc
        _ = (∑ l ∈ S, η l) • (B k).mulVec v := by rw [Finset.sum_smul]
        _ = (B k).mulVec v := by rw [hsumHat, one_smul]
    calc
      _ = (∑ l ∈ S, η l • (A l).mulVec v) -
          ∑ l ∈ S, η l • (B k).mulVec v := by
        rw [hbar, hG (lIdx β I.Λ m k.1)]
        exact congrArg
          (fun z : Vec 2 => (∑ l ∈ S, η l • (A l).mulVec v) - z) hsumB.symm
      _ = ∑ l ∈ S, η l • ((A l).mulVec v - (B k).mulVec v) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro l hl
        ext i
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      _ = ∑ l ∈ S, η l • ((A l - B k).mulVec v) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Matrix.sub_mulVec]
  have htsum : (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
      (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x)) =
      ∑ k ∈ U, I.xiMK m k.1 t •
        (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    apply tsum_eq_sum
    intro k hk
    have hzero : I.xiMK m k.1 t = 0 := by
      by_contra hn
      exact hk ((Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mpr hn)
    simp [hzero]
  rw [htsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hinner k]

theorem R46FluxEstimate.r46_vecNormSq_smul (c : ℝ) (v : Vec 2) :
    vecNormSq (c • v) = c ^ 2 * vecNormSq v := by
  simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring

theorem R46FluxEstimate.r46_gradMatrix_id (x : Vec 2) :
    gradMatrix (fun y : Vec 2 => y) x = 1 := by
  ext i j
  change fderiv ℝ (fun y : Vec 2 => y j) x (basisVec i) = _
  rw [fderiv_apply differentiableAt_id j]
  change ((ContinuousLinearMap.proj j).comp (fderiv ℝ id x)) (basisVec i) = _
  rw [fderiv_id]
  by_cases hij : i = j
  · subst j
    simp [basisVec]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [basisVec, hij, hji]

theorem R46FluxEstimate.r46_flowGrad_one_eq
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    I.flowGrad hΦ 1 l t x = 1 := by
  have hb : streamVel (Φ 0) = 0 := by
    rw [hΦ.1]
    exact streamVel_spatialConstant (fun _ => 0)
  let b := streamVel (Φ 0)
  have hφ := hΦ.adm_pred 1
  have hX : IsFlow b (flow b hφ.vel_continuous hφ.vel_lipschitz) := by
    exact flow_isFlow b hφ.vel_continuous hφ.vel_lipschitz
  have hId : IsFlow b (fun _ y _ => y) := by
    constructor
    · intro y s
      rfl
    · intro y s r
      rw [show b = 0 by exact hb]
      exact hasDerivAt_const r y
  have hL : ∃ L : ℝ, ∀ s y z, ‖b s y - b s z‖ ≤ L * ‖y - z‖ := by
    refine ⟨0, ?_⟩
    intro s y z
    rw [show b = 0 by exact hb]
    simp
  have hflow := Infra.Flow.flow_eq_of_isFlow b hL hX hId
  have hxflow : I.xFlow hΦ 1 l t = fun y => y := by
    funext y
    change flow b hφ.vel_continuous hφ.vel_lipschitz t y
      ((l : ℝ) * tauPP β I.Λ 1) = y
    rw [hflow]
  have hxinv : I.xFlowInv hΦ 1 l t = fun y => y := by
    funext y
    change flowInv b hφ.vel_continuous hφ.vel_lipschitz t y
      ((l : ℝ) * tauPP β I.Λ 1) = y
    rw [flowInv, hflow]
  simp [Ingredients.flowGrad, hxflow, hxinv, R46FluxEstimate.r46_gradMatrix_id]

/-- Actual pointwise flux bound from stream-function estimates `flow_close`. On refresh windows
the defect vanishes exactly; off them the odd-mode flux is molecular, and the
two cutoff partitions average Jacobian differences. -/
theorem r46Flux_pointwise_sq_le_of_flowBounds
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (Cmat : ℝ)
    (hflow : FlowBoundsData I Φ hΦ Cmat)
    (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hT : ContDiff ℝ 1 (T t))
    (x : Vec 2) :
    vecNormSq (r46Flux I hΦ m κm T t x) ≤
      κm ^ 2 * (epsilon β I.Λ (m - 1) ^ (2 * delta β)) ^ 2 *
        vecNormSq (spaceGrad (T t) x) := by
  classical
  have hm' : 1 ≤ m := hm
  let S := (I.hatXiML_support_finite hm' t).toFinset
  let U := (Infra.Section3.xiMK_odd_support_finite I hm' t).toFinset
  let η : ℝ := epsilon β I.Λ (m - 1) ^ (2 * delta β)
  by_cases hrefresh : ∃ l : ℤ, I.hatZetaML m l t ≠ 0
  · obtain ⟨l, hl⟩ := hrefresh
    have hz := r46Flux_eq_zero_of_hatZeta_ne_zero I hΦ m hm' κm T l t hl
    have hx := congrArg (fun F : Vec 2 → Vec 2 => F x) hz
    calc
      vecNormSq (r46Flux I hΦ m κm T t x) = 0 := by
        rw [hx]
        simp [vecNormSq, vecDot]
      _ ≤ κm ^ 2 * (epsilon β I.Λ (m - 1) ^ (2 * delta β)) ^ 2 *
          vecNormSq (spaceGrad (T t) x) := by
            have hvec := vecNormSq_nonneg (spaceGrad (T t) x)
            positivity
  · have hzero : ∀ l : ℤ, I.hatZetaML m l t = 0 := by
      intro l
      by_contra hn
      exact hrefresh ⟨l, hn⟩
    have heps : 0 < epsilon β I.Λ (m - 1) :=
      Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hη : 0 ≤ η := by
      dsimp [η]
      exact Real.rpow_nonneg heps.le _
    have hsumXi : ∑ k ∈ U, I.xiMK m k.1 t = 1 := by
      have hfinite : (∑ k ∈ U, I.xiMK m k.1 t) =
          ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t := by
        symm
        apply tsum_eq_sum
        intro k hk
        have hcut : I.xiMK m k.1 t = 0 := by
          by_contra hn
          exact hk ((Infra.Section3.xiMK_odd_support_finite I hm' t).mem_toFinset.mpr hn)
        simp [hcut]
      rw [hfinite]
      exact Infra.Section3.xiMK_odd_partition I hm' t
    have hsumHat : ∑ l ∈ S, I.hatXiML m l t = 1 := by
      have hfinite : (∑ l ∈ S, I.hatXiML m l t) =
          ∑' l : ℤ, I.hatXiML m l t := by
        symm
        apply tsum_eq_sum
        intro l hl
        have hcut : I.hatXiML m l t = 0 := by
          by_contra hn
          exact hl ((I.hatXiML_support_finite hm' t).mem_toFinset.mpr hn)
        simp [hcut]
      rw [hfinite]
      exact Infra.Ingredients.hatXiML_partition I hm' t
    have hclose : ∀ k ∈ U, ∀ l ∈ S, ∀ i j,
        |(I.flowGrad hΦ m l t x -
          I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x) i j| ≤ η / 2 := by
      intro k hk l hl i j
      by_cases hmone : m = 1
      · subst m
        rw [R46FluxEstimate.r46_flowGrad_one_eq I hΦ l t x,
          R46FluxEstimate.r46_flowGrad_one_eq I hΦ (lIdx β I.Λ 1 k.1) t x]
        simp only [Matrix.sub_apply, sub_self, abs_zero]
        exact div_nonneg hη (by norm_num)
      · have hm2 : 2 ≤ m := by omega
        have hξ : I.xiMK m k.1 t ≠ 0 :=
          (Infra.Section3.xiMK_odd_support_finite I hm' t).mem_toFinset.mp hk
        have hhat : I.hatXiML m l t ≠ 0 :=
          (I.hatXiML_support_finite hm' t).mem_toFinset.mp hl
        have hA := flowGrad_entry_close_on_tauPP_window I Cmat hΦ hflow m hm2
          l t x (hatXiML_time_distance_le_tauPP I m hm' l t hhat) i j
        have hB := flowGrad_entry_close_on_tauPP_window I Cmat hΦ hflow m hm2
          (lIdx β I.Λ m k.1) t x
          (lIdx_flow_time_distance_le_tauPP I m hm' k.1 t hξ) i j
        calc
          |(I.flowGrad hΦ m l t x -
              I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x) i j| =
              |(I.flowGrad hΦ m l t x - 1) i j -
                (I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x - 1) i j| := by
                  congr 1
                  simp [Matrix.sub_apply]
          _ ≤ |(I.flowGrad hΦ m l t x - 1) i j| +
              |(I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x - 1) i j| := abs_sub _ _
          _ ≤ η / 4 + η / 4 := by
            calc
              _ ≤ (1 / 4 : ℝ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) +
                  (1 / 4 : ℝ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
                add_le_add hA hB
              _ = η / 4 + η / 4 := by dsimp [η]; ring
          _ = η / 2 := by ring
    have hmix := R46FluxEstimate.r46_finite_mixture_distortion U S
      (fun k => I.xiMK m k.1 t) (fun l => I.hatXiML m l t)
      (fun l => I.flowGrad hΦ m l t x)
      (fun k => I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x)
      (spaceGrad (T t) x) η
      (fun k hk => (Infra.Section3.xiMK_mem_Icc I hm' k.1 t).1)
      hsumXi
      (fun l hl => (Infra.Ingredients.hatXiML_mem_Icc I hm' l t).1)
      hsumHat hclose hη
    have hdefect := R46FluxEstimate.r46_defect_eq_finite_mixture I hΦ m hm' T t hT x
    have hsupp : {k : {k : ℤ // Odd k} | I.xiMK m k.1 t •
        (Gbar I hΦ m T t - G I hΦ m T (lIdx β I.Λ m k.1) t) ≠
          (0 : Vec 2 → Vec 2)}.Finite :=
      (Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn
        (I.xiMK_support_finite m t)).subset (by
          intro k hk
          by_contra hxi
          have hxi0 : I.xiMK m k.1 t = 0 := by
            by_contra hne
            exact hxi (by simpa using hne)
          apply hk
          simp [hxi0])
    have hsumFun : Summable (fun k : {k : ℤ // Odd k} => I.xiMK m k.1 t •
        (Gbar I hΦ m T t - G I hΦ m T (lIdx β I.Λ m k.1) t)) :=
      summable_of_hasFiniteSupport hsupp
    have hEval : (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
        (Gbar I hΦ m T t - G I hΦ m T (lIdx β I.Λ m k.1) t)) x =
        ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
          (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
      rw [Pi.tsum_apply hsumFun]
      simp only [Pi.smul_apply, Pi.sub_apply]
    have hfluxFun := r46Flux_eq_kappa_smul_defect_of_hatZeta_zero
      I hΦ m hm' κm T t hzero
    have hfluxAt := congrArg (fun F : Vec 2 → Vec 2 => F x) hfluxFun
    have hflux : r46Flux I hΦ m κm T t x = κm •
        (∑ k ∈ U, I.xiMK m k.1 t •
          ∑ l ∈ S, I.hatXiML m l t •
            ((I.flowGrad hΦ m l t x -
              I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x).mulVec
              (spaceGrad (T t) x))) := by
      have hfinite := calc
        (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
            (Gbar I hΦ m T t - G I hΦ m T (lIdx β I.Λ m k.1) t)) x =
          ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
            (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x) := hEval
        _ = ∑ k ∈ U, I.xiMK m k.1 t •
            ∑ l ∈ S, I.hatXiML m l t •
              ((I.flowGrad hΦ m l t x -
                I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x).mulVec
                (spaceGrad (T t) x)) := hdefect
      simpa only [Pi.smul_apply] using hfluxAt.trans
        (congrArg (fun v : Vec 2 => κm • v) hfinite)
    rw [hflux]
    calc
      vecNormSq (κm •
          (∑ k ∈ U, I.xiMK m k.1 t •
            ∑ l ∈ S, I.hatXiML m l t •
              ((I.flowGrad hΦ m l t x -
                I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x).mulVec
                (spaceGrad (T t) x)))) =
          κm ^ 2 * vecNormSq
            (∑ k ∈ U, I.xiMK m k.1 t •
              ∑ l ∈ S, I.hatXiML m l t •
                ((I.flowGrad hΦ m l t x -
                  I.flowGrad hΦ m (lIdx β I.Λ m k.1) t x).mulVec
                  (spaceGrad (T t) x))) := by
            rw [R46FluxEstimate.r46_vecNormSq_smul]
      _ ≤ κm ^ 2 * (η ^ 2 * vecNormSq (spaceGrad (T t) x)) :=
        mul_le_mul_of_nonneg_left hmix (sq_nonneg κm)
      _ = κm ^ 2 * η ^ 2 * vecNormSq (spaceGrad (T t) x) := by ring
      _ = κm ^ 2 * (epsilon β I.Λ (m - 1) ^ (2 * delta β)) ^ 2 *
          vecNormSq (spaceGrad (T t) x) := by rfl

theorem R46FluxEstimate.r46_gradNormSq_nonneg (F : Vec 2 → Vec 2) :
    0 ≤ gradNormSq F := by
  unfold gradNormSq
  exact integral_nonneg fun x => vecNormSq_nonneg (F x)

theorem R46FluxEstimate.r46_slice_contDiff {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ (⊤ : ℕ∞) (T t) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
  have hmaps : ∀ x : Vec 2, (t, x) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ :=
    fun x => ⟨ht, Set.mem_univ x⟩
  simpa only [Function.comp_def, Prod.fst, Prod.snd] using
    hT.comp_contDiff hmap hmaps

theorem R46FluxEstimate.r46_spaceGrad_continuous {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) : Continuous (spaceGrad u) := by
  apply continuous_pi
  intro i
  exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const

theorem R46FluxEstimate.r46_gradient_continuousOn {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  have hV : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    LeftToShow.spaceGrad_continuousOn (by
      exact hT)
  exact hV.mono (by intro p hp; exact ⟨hp.1.1, hp.2⟩)

theorem R46FluxEstimate.r46_gradNormSq_continuousOn {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun t => gradNormSq (fun x => spaceGrad (T t) x))
      (Set.Icc (0 : ℝ) 1) := by
  have hV := R46FluxEstimate.r46_gradient_continuousOn hT
  have hsq : ContinuousOn (fun p : ℝ × Vec 2 =>
      vecNormSq (spaceGrad (T p.1) p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    LeftToShow.continuous_vecNormSq_two.comp_continuousOn hV
  have hcont := LeftToShow.continuousOn_integral_unitCube
    (h := fun t x => vecNormSq (spaceGrad (T t) x)) hsq
  simpa only [gradNormSq] using hcont

theorem R46FluxEstimate.r46_lintegrand_eq {F : ℝ → Vec 2 → Vec 2} (t : ℝ) :
    ENNReal.ofReal (Real.sqrt (gradNormSq (F t))) ^ 2 =
      ENNReal.ofReal (gradNormSq (F t)) := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
    Real.sq_sqrt (R46FluxEstimate.r46_gradNormSq_nonneg (F t))]

theorem R46FluxEstimate.r46TimeL2_eq_lintegral (F : ℝ → Vec 2 → Vec 2) :
    r46TimeL2 F =
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (gradNormSq (F t))) ^ (1 / 2 : ℝ) := by
  unfold r46TimeL2
  congr 1
  apply lintegral_congr
  intro t
  exact R46FluxEstimate.r46_lintegrand_eq (F := F) t

/-- The source n=0 energy norm is the same slice norm as the one consumed by
the `R46` time estimate. Joint smoothness gives the Fubini identification. -/
theorem r46TimeL2_gradient_eq_spaceTime
    (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    r46TimeL2 (fun t x => spaceGrad (T t) x) =
      ENNReal.ofReal (Real.sqrt
        (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x))) := by
  let V : ℝ → Vec 2 → Vec 2 := fun t x => spaceGrad (T t) x
  have hV := R46FluxEstimate.r46_gradient_continuousOn hT
  have hg := R46FluxEstimate.r46_gradNormSq_continuousOn hT
  have hgi : IntegrableOn (fun t => gradNormSq (V t)) (Set.Ioo (0 : ℝ) 1) :=
    (hg.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hgnn (t : ℝ) : 0 ≤ gradNormSq (V t) := R46FluxEstimate.r46_gradNormSq_nonneg (V t)
  have hspace : spaceTimeGradNormSq V =
      ∫ t in Set.Ioo (0 : ℝ) 1, gradNormSq (V t) := by
    calc
      spaceTimeGradNormSq V =
          ∫ t in (0 : ℝ)..1, ∫ x in unitCube, vecNormSq (V t x) :=
        LeftToShow.spaceTimeGradNormSq_eq_intervalIntegral hV
      _ = ∫ t in Set.Ioo (0 : ℝ) 1, gradNormSq (V t) := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          integral_Ioc_eq_integral_Ioo]
        rfl
  have hlin : ENNReal.ofReal (spaceTimeGradNormSq V) =
      ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (gradNormSq (V t)) := by
    rw [hspace]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgi
      (ae_of_all _ hgnn)
  have hspace_nn : 0 ≤ spaceTimeGradNormSq V := by
    rw [hspace]
    exact integral_nonneg fun t => hgnn t
  rw [R46FluxEstimate.r46TimeL2_eq_lintegral, ← hlin]
  rw [ENNReal.ofReal_rpow_of_nonneg hspace_nn (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [Real.sqrt_eq_rpow]

/-- Spatial integration preserves the sharp pointwise estimate. -/
theorem gradNormSq_r46Flux_sq_le_of_flowBounds
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (Cmat : ℝ)
    (hflow : FlowBoundsData I Φ hΦ Cmat)
    (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (t : ℝ) (ht : 0 ≤ t) (hF : ContDiff ℝ (⊤ : ℕ∞) (r46Flux I hΦ m κm T t)) :
    gradNormSq (r46Flux I hΦ m κm T t) ≤
      (κm * epsilon β I.Λ (m - 1) ^ (2 * delta β)) ^ 2 *
        gradNormSq (fun x => spaceGrad (T t) x) := by
  let F := r46Flux I hΦ m κm T t
  let V := fun x => spaceGrad (T t) x
  let c := κm * epsilon β I.Λ (m - 1) ^ (2 * delta β)
  have hFc : Continuous F := hF.continuous
  have hVc : Continuous V := R46FluxEstimate.r46_spaceGrad_continuous
      (R46FluxEstimate.r46_slice_contDiff hT ht)
  have hfi : IntegrableOn (fun x => vecNormSq (F x)) unitCube :=
    LeftToShow.integrableOn_unitCube_of_continuous
      (LeftToShow.continuous_vecNormSq_two.comp hFc)
  have hvi : IntegrableOn (fun x => vecNormSq (V x)) unitCube :=
    LeftToShow.integrableOn_unitCube_of_continuous
      (LeftToShow.continuous_vecNormSq_two.comp hVc)
  have hpoint (x : Vec 2) : vecNormSq (F x) ≤ c ^ 2 * vecNormSq (V x) := by
    dsimp [F, V, c]
    have hp := r46Flux_pointwise_sq_le_of_flowBounds I hΦ Cmat hflow m hm κm T
      ((R46FluxEstimate.r46_slice_contDiff hT ht).of_le (by simp)) x
    simpa only [mul_pow] using hp
  calc
    gradNormSq F ≤ ∫ x in unitCube, c ^ 2 * vecNormSq (V x) := by
      unfold gradNormSq
      exact integral_mono hfi (hvi.const_mul (c ^ 2)) hpoint
    _ = c ^ 2 * gradNormSq V := by
      rw [integral_const_mul]
      rfl

/-- The actual stream-function flow estimate gives the sharp `R46` flux-to-gradient
space-time bound, with the stronger intermediate exponent 2δ. -/
theorem r46TimeL2_flux_le_of_flowBounds
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (Cmat : ℝ)
    (hflow : FlowBoundsData I Φ hΦ Cmat)
    (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ContDiff ℝ (⊤ : ℕ∞) (r46Flux I hΦ m κm T t))
    (hκm : 0 ≤ κm) :
    r46TimeL2 (fun t => r46Flux I hΦ m κm T t) ≤
      ENNReal.ofReal (κm * epsilon β I.Λ (m - 1) ^ (2 * delta β)) *
        r46TimeL2 (fun t x => spaceGrad (T t) x) := by
  let c := κm * epsilon β I.Λ (m - 1) ^ (2 * delta β)
  let g := fun t => gradNormSq (fun x => spaceGrad (T t) x)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg hκm (Real.rpow_nonneg
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _)
  have hgi_cont := R46FluxEstimate.r46_gradNormSq_continuousOn hT
  have hgi : IntegrableOn g (Set.Ioo (0 : ℝ) 1) :=
    (hgi_cont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hgaemeas : AEMeasurable (fun t => ENNReal.ofReal (g t))
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) := by
    have hgi' : Integrable g ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) := hgi
    exact hgi'.aemeasurable.ennreal_ofReal
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      ENNReal.ofReal (gradNormSq (r46Flux I hΦ m κm T t)) ≤
        ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (g t) := by
    calc
      _ ≤ ENNReal.ofReal (c ^ 2 * g t) :=
        ENNReal.ofReal_le_ofReal
          (gradNormSq_r46Flux_sq_le_of_flowBounds I hΦ Cmat hflow m hm κm T hT t
            ht.1.le (hF t ht))
      _ = ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (g t) :=
        ENNReal.ofReal_mul (sq_nonneg c)
  have hlin :
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (gradNormSq (r46Flux I hΦ m κm T t))) ≤
      ENNReal.ofReal (c ^ 2) *
        (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (g t)) := by
    calc
      _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (g t) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hpoint t ht
      _ = _ := by rw [lintegral_const_mul'' _ hgaemeas]
  rw [R46FluxEstimate.r46TimeL2_eq_lintegral, R46FluxEstimate.r46TimeL2_eq_lintegral]
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (gradNormSq (r46Flux I hΦ m κm T t))) ^ (1 / 2 : ℝ) ≤
        (ENNReal.ofReal (c ^ 2) *
          (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (g t))) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hlin (by norm_num)
    _ = ENNReal.ofReal c *
        (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (g t)) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg c) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
    _ = _ := by rw [← R46FluxEstimate.r46TimeL2_eq_lintegral]

theorem R46FluxEstimate.r46_epsilon_two_delta_le_delta (β : ℝ) (I : Ingredients β)
    (m : ℕ) :
    epsilon β I.Λ m ^ (2 * delta β) ≤ epsilon β I.Λ m ^ delta β := by
  have he : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : epsilon β I.Λ m ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hd : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hpow : epsilon β I.Λ m ^ delta β ≤ 1 :=
    Real.rpow_le_one he.le he1 hd.le
  calc
    epsilon β I.Λ m ^ (2 * delta β) =
        epsilon β I.Λ m ^ delta β * epsilon β I.Λ m ^ delta β := by
      rw [show 2 * delta β = delta β + delta β by ring, Real.rpow_add he]
    _ ≤ epsilon β I.Λ m ^ delta β := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg he.le (delta β))

end AVenhance.Infra.Section5
end
