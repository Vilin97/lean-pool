/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-!
# Smooth spatial cutoffs for whole-space comparison

The fixed bump is one on the unit ball and supported in the ball of radius two.
All scaled cutoffs are obtained from this same bump by dilation.  In particular,
the constants in their derivative estimates do not depend on the radius.
-/


noncomputable section

open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.ComparisonCutoffs

open ProblemStatement
open NavierStokes.ProblemStatement (coordinateVector)

/-- The fixed bump with inner radius one and outer radius two. -/
noncomputable def baseBump : ContDiffBump (0 : Space) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The unscaled cutoff. -/
def baseCutoff (x : Space) : ℝ := baseBump x

/-- The cutoff at spatial radius `R`; its estimates are stated for `0 < R`. -/
def cutoff (R : ℝ) (x : Space) : ℝ := baseCutoff (R⁻¹ • x)

/-- The weight in the localized energy. -/
def weight (R : ℝ) (x : Space) : ℝ := cutoff R x ^ 8

/-- The multiplier used to commute the pressure operator. -/
def multiplier (R : ℝ) (x : Space) : ℝ := cutoff R x ^ 2

theorem baseCutoff_smooth : ContDiff ℝ ∞ baseCutoff := baseBump.contDiff

theorem baseCutoff_nonneg (x : Space) : 0 ≤ baseCutoff x := baseBump.nonneg

theorem baseCutoff_le_one (x : Space) : baseCutoff x ≤ 1 := baseBump.le_one

theorem baseCutoff_eq_one {x : Space} (hx : ‖x‖ ≤ 1) : baseCutoff x = 1 := by
  apply baseBump.one_of_mem_closedBall
  simpa [baseBump, mem_closedBall, dist_zero_right] using hx

theorem baseCutoff_eq_zero {x : Space} (hx : 2 ≤ ‖x‖) : baseCutoff x = 0 := by
  apply baseBump.zero_of_le_dist
  simpa [baseBump, dist_zero_right] using hx

theorem baseCutoff_hasCompactSupport : HasCompactSupport baseCutoff :=
  baseBump.hasCompactSupport

theorem baseCutoff_tsupport : tsupport baseCutoff = closedBall (0 : Space) 2 := by
  exact baseBump.tsupport_eq

theorem cutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (cutoff R) :=
  baseCutoff_smooth.comp (by fun_prop)

theorem cutoff_nonneg (R : ℝ) (x : Space) : 0 ≤ cutoff R x :=
  baseCutoff_nonneg _

theorem cutoff_le_one (R : ℝ) (x : Space) : cutoff R x ≤ 1 :=
  baseCutoff_le_one _

theorem cutoff_mem_Icc (R : ℝ) (x : Space) : cutoff R x ∈ Icc (0 : ℝ) 1 :=
  ⟨cutoff_nonneg R x, cutoff_le_one R x⟩

theorem norm_scaled {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖R⁻¹ • x‖ = ‖x‖ / R := by
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, div_eq_inv_mul]

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) :
    cutoff R x = 1 := by
  apply baseCutoff_eq_one
  rw [norm_scaled hR, div_le_one hR]
  exact hx

theorem cutoff_eq_one_on_closedBall {R : ℝ} (hR : 0 < R) :
    EqOn (cutoff R) (fun _ => 1) (closedBall (0 : Space) R) := by
  intro x hx
  exact cutoff_eq_one hR (by simpa [mem_closedBall, dist_zero_right] using hx)

theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : Space} (hx : 2 * R ≤ ‖x‖) :
    cutoff R x = 0 := by
  apply baseCutoff_eq_zero
  rw [norm_scaled hR, le_div_iff₀ hR]
  exact hx

theorem cutoff_support_subset {R : ℝ} (hR : 0 < R) :
    Function.support (cutoff R) ⊆ ball (0 : Space) (2 * R) := by
  intro x hx
  by_contra h
  apply hx
  exact cutoff_eq_zero hR (by simpa [mem_ball, dist_zero_right, not_lt] using h)

theorem cutoff_tsupport_subset {R : ℝ} (hR : 0 < R) :
    tsupport (cutoff R) ⊆ closedBall (0 : Space) (2 * R) :=
  closure_minimal ((cutoff_support_subset hR).trans ball_subset_closedBall) isClosed_closedBall

theorem cutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutoff R) :=
  (isCompact_closedBall (0 : Space) (2 * R)).of_isClosed_subset
    isClosed_closure (cutoff_tsupport_subset hR)

theorem weight_smooth (R : ℝ) : ContDiff ℝ ∞ (weight R) :=
  (cutoff_smooth R).pow 8

theorem multiplier_smooth (R : ℝ) : ContDiff ℝ ∞ (multiplier R) :=
  (cutoff_smooth R).pow 2

theorem weight_nonneg (R : ℝ) (x : Space) : 0 ≤ weight R x :=
  pow_nonneg (cutoff_nonneg R x) 8

theorem weight_le_one (R : ℝ) (x : Space) : weight R x ≤ 1 := by
  exact pow_le_one₀ (cutoff_nonneg R x) (cutoff_le_one R x)

theorem multiplier_nonneg (R : ℝ) (x : Space) : 0 ≤ multiplier R x :=
  sq_nonneg _

theorem multiplier_le_one (R : ℝ) (x : Space) : multiplier R x ≤ 1 := by
  exact pow_le_one₀ (cutoff_nonneg R x) (cutoff_le_one R x)

theorem weight_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (weight R) := by
  change HasCompactSupport ((fun a : ℝ => a ^ 8) ∘ cutoff R)
  exact (cutoff_hasCompactSupport hR).comp_left (by norm_num)

theorem multiplier_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (multiplier R) := by
  change HasCompactSupport ((fun a : ℝ => a ^ 2) ∘ cutoff R)
  exact (cutoff_hasCompactSupport hR).comp_left (by norm_num)

theorem weight_eq_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) :
    weight R x = 1 := by simp [weight, cutoff_eq_one hR hx]

theorem multiplier_eq_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) :
    multiplier R x = 1 := by simp [multiplier, cutoff_eq_one hR hx]

theorem exists_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space, ‖iteratedFDeriv ℝ n baseCutoff x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (baseCutoff_hasCompactSupport.iteratedFDeriv n).exists_bound_of_continuous
    (ContDiff.continuous_iteratedFDeriv le_rfl (contDiff_infty.1 baseCutoff_smooth n))
  exact ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hC x).trans (le_max_right _ _)⟩

/-- A fixed positive bound for the `n`th derivative of the unscaled bump. -/
def derivativeConstant (n : ℕ) : ℝ := Classical.choose (exists_derivative_bound n)

theorem derivativeConstant_pos (n : ℕ) : 0 < derivativeConstant n :=
  (Classical.choose_spec (exists_derivative_bound n)).1

theorem baseCutoff_iteratedFDeriv_le (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n baseCutoff x‖ ≤ derivativeConstant n :=
  (Classical.choose_spec (exists_derivative_bound n)).2 x

private def dilation (R : ℝ) : Space →L[ℝ] Space :=
  R⁻¹ • ContinuousLinearMap.id ℝ Space

private theorem norm_dilation_le {R : ℝ} (hR : 0 < R) : ‖dilation R‖ ≤ R⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hR.le)
  intro x
  change ‖R⁻¹ • x‖ ≤ R⁻¹ * ‖x‖
  rw [norm_scaled hR, div_eq_inv_mul]

/-- Each spatial derivative contributes precisely one inverse power of the radius. -/
theorem cutoff_iteratedFDeriv_le {R : ℝ} (hR : 0 < R) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (cutoff R) x‖ ≤ derivativeConstant n / R ^ n := by
  change ‖iteratedFDeriv ℝ n (baseCutoff ∘ dilation R) x‖ ≤ _
  rw [(dilation R).iteratedFDeriv_comp_right (contDiff_infty.1 baseCutoff_smooth n) x le_rfl]
  calc
    ‖(iteratedFDeriv ℝ n baseCutoff (dilation R x)).compContinuousLinearMap
        (fun _ => dilation R)‖
        ≤ ‖iteratedFDeriv ℝ n baseCutoff (dilation R x)‖ *
          ∏ _ : Fin n, ‖dilation R‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n baseCutoff (dilation R x)‖ * (R⁻¹) ^ n := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        ∏ _ : Fin n, ‖dilation R‖ ≤ ∏ _ : Fin n, R⁻¹ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_dilation_le hR)
        _ = (R⁻¹) ^ n := by simp
    _ ≤ derivativeConstant n * (R⁻¹) ^ n :=
      mul_le_mul_of_nonneg_right (baseCutoff_iteratedFDeriv_le n _) (by positivity)
    _ = derivativeConstant n / R ^ n := by simp [div_eq_mul_inv]

theorem cutoff_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (cutoff R) x‖ ≤ derivativeConstant 1 / R := by
  have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := cutoff R) (x := x) (n := 0)
  simp only [norm_iteratedFDeriv_zero] at hn
  rw [hn]
  simpa only [pow_one] using cutoff_iteratedFDeriv_le hR 1 x

theorem cutoff_second_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fderiv ℝ (cutoff R)) x‖ ≤ derivativeConstant 2 / R ^ 2 := by
  have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fderiv ℝ (cutoff R))
    (x := x) (n := 0)
  simp only [norm_iteratedFDeriv_zero] at hn
  rw [hn, norm_iteratedFDeriv_fderiv]
  exact cutoff_iteratedFDeriv_le hR 2 x

/-- The scalar spatial Laplacian, using the fixed standard coordinate vectors. -/
def laplacian (f : Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, NavierStokes.PeriodicIntegration.spatialPartial i
    (NavierStokes.PeriodicIntegration.spatialPartial i f) x

theorem fderiv_apply_derivative {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (x a b : Space) :
    fderiv ℝ (fun y => fderiv ℝ f y b) x a =
      fderiv ℝ (fderiv ℝ f) x a b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  simpa using congrArg (fun A : Space →L[ℝ] ℝ => A a)
    (fderiv_clm_apply hd (differentiableAt_const b))

theorem norm_partial_partial_le {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (x : Space) :
    ‖NavierStokes.PeriodicIntegration.spatialPartial i
      (NavierStokes.PeriodicIntegration.spatialPartial j f) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  change ‖fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j)) x (coordinateVector i)‖ ≤ _
  rw [fderiv_apply_derivative hf]
  have hv (k : Fin 3) : ‖coordinateVector k‖ ≤ 1 := by
    simp [coordinateVector]
  exact ((fderiv ℝ (fderiv ℝ f) x (coordinateVector i)).unit_le_opNorm
    (coordinateVector j) (hv j)).trans
    ((fderiv ℝ (fderiv ℝ f) x).unit_le_opNorm (coordinateVector i) (hv i))

theorem cutoff_partial_partial_le {R : ℝ} (hR : 0 < R) (i j : Fin 3) (x : Space) :
    ‖NavierStokes.PeriodicIntegration.spatialPartial i
      (NavierStokes.PeriodicIntegration.spatialPartial j (cutoff R)) x‖ ≤
      derivativeConstant 2 / R ^ 2 :=
  (norm_partial_partial_le (cutoff_smooth R) i j x).trans (cutoff_second_fderiv_le hR x)

theorem cutoff_laplacian_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖laplacian (cutoff R) x‖ ≤ (3 * derivativeConstant 2) / R ^ 2 := by
  calc
    ‖laplacian (cutoff R) x‖
        ≤ ∑ i : Fin 3, ‖NavierStokes.PeriodicIntegration.spatialPartial i
          (NavierStokes.PeriodicIntegration.spatialPartial i (cutoff R)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, derivativeConstant 2 / R ^ 2 :=
      Finset.sum_le_sum (fun i _ => cutoff_partial_partial_le hR i i x)
    _ = (3 * derivativeConstant 2) / R ^ 2 := by simp [mul_div_assoc]

/-- Every fixed compact set lies in the plateau of all sufficiently large cutoffs. -/
theorem compact_plateau {K : Set Space} (hK : IsCompact K) :
    ∃ R₀ > 0, ∀ R ≥ R₀, EqOn (cutoff R) (fun _ => 1) K := by
  obtain ⟨R₀, hR₀, hbound⟩ := hK.isBounded.exists_pos_norm_le
  exact ⟨R₀, hR₀, fun R hR x hx => cutoff_eq_one (hR₀.trans_le hR)
    ((hbound x hx).trans hR)⟩

theorem eventually_compact_plateau {K : Set Space} (hK : IsCompact K) :
    ∀ᶠ R : ℝ in atTop, EqOn (cutoff R) (fun _ => 1) K := by
  obtain ⟨R₀, _, h⟩ := compact_plateau hK
  exact eventually_atTop.2 ⟨R₀, h⟩

theorem eventually_cutoff_eq_one (x : Space) :
    ∀ᶠ R : ℝ in atTop, cutoff R x = 1 := by
  filter_upwards [eventually_compact_plateau (isCompact_singleton (x := x))] with R hR
  exact hR (mem_singleton x)

theorem cutoff_tendsto_one (x : Space) :
    Tendsto (fun R : ℝ => cutoff R x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_cutoff_eq_one x] with R hR
  exact hR.symm

end NavierStokesR3.ComparisonCutoffs
