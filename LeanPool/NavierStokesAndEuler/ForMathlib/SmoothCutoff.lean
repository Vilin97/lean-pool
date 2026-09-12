/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Code4me2
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The dilated radius-1-to-2 bump cutoff

This family supports localization arguments in real inner-product spaces:
one fixed `ContDiffBump` that equals one on the closed unit ball and vanishes
outside the ball of radius two, dilated to `cutoff E R x = χ (R⁻¹ • x)`.
Because every member of the family is a dilation of the same bump, its
derivative bounds have `R`-independent constants:
`‖iteratedFDeriv ℝ n (cutoff E R) x‖ ≤ derivativeConstant E n / R ^ n`, and the
scale-invariant `‖fderiv ℝ (cutoff E R) x‖ * ‖x‖ ≤ 2 * derivativeConstant E 1`.

The space is an explicit argument of the definitions so that partial applications
such as `cutoff E R` elaborate without an expected type. The derivative constant
is accessed through its positivity and bound lemmas; its choice is private.
-/

public section

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace NavierStokesAndEuler.SmoothCutoff

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The fixed bump with inner radius one and outer radius two. -/
@[expose] def baseBump : ContDiffBump (0 : E) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The unscaled cutoff. -/
@[expose] def baseCutoff (x : E) : ℝ := baseBump E x

/-- The cutoff at spatial radius `R`; its estimates are stated for `0 < R`. -/
@[expose] def cutoff (R : ℝ) (x : E) : ℝ := baseCutoff E (R⁻¹ • x)

variable {E}

theorem baseCutoff_smooth : ContDiff ℝ ∞ (baseCutoff E) := (baseBump E).contDiff

theorem baseCutoff_nonneg (x : E) : 0 ≤ baseCutoff E x := (baseBump E).nonneg

theorem baseCutoff_le_one (x : E) : baseCutoff E x ≤ 1 := (baseBump E).le_one

theorem baseCutoff_eq_one {x : E} (hx : ‖x‖ ≤ 1) : baseCutoff E x = 1 := by
  apply (baseBump E).one_of_mem_closedBall
  simpa [baseBump, mem_closedBall, dist_zero_right] using hx

theorem baseCutoff_eq_zero {x : E} (hx : 2 ≤ ‖x‖) : baseCutoff E x = 0 := by
  apply (baseBump E).zero_of_le_dist
  simpa [baseBump, dist_zero_right] using hx

theorem cutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (cutoff E R) :=
  baseCutoff_smooth.comp (contDiff_id.const_smul R⁻¹)

theorem cutoff_nonneg (R : ℝ) (x : E) : 0 ≤ cutoff E R x :=
  baseCutoff_nonneg _

theorem cutoff_le_one (R : ℝ) (x : E) : cutoff E R x ≤ 1 :=
  baseCutoff_le_one _

theorem cutoff_mem_Icc (R : ℝ) (x : E) : cutoff E R x ∈ Icc (0 : ℝ) 1 :=
  ⟨cutoff_nonneg R x, cutoff_le_one R x⟩

theorem norm_cutoff_le_one (R : ℝ) (x : E) : ‖cutoff E R x‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (cutoff_nonneg R x)]
  exact cutoff_le_one R x

theorem norm_inv_smul {R : ℝ} (hR : 0 < R) (x : E) : ‖R⁻¹ • x‖ = ‖x‖ / R := by
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, div_eq_inv_mul]

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    cutoff E R x = 1 := by
  apply baseCutoff_eq_one
  rw [norm_inv_smul hR, div_le_one hR]
  exact hx

theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : 2 * R ≤ ‖x‖) :
    cutoff E R x = 0 := by
  apply baseCutoff_eq_zero
  rw [norm_inv_smul hR, le_div_iff₀ hR]
  exact hx

theorem cutoff_support_subset {R : ℝ} (hR : 0 < R) :
    Function.support (cutoff E R) ⊆ ball (0 : E) (2 * R) := by
  intro x hx
  by_contra h
  apply hx
  exact cutoff_eq_zero hR (by simpa [mem_ball, dist_zero_right, not_lt] using h)

theorem cutoff_tsupport_subset {R : ℝ} (hR : 0 < R) :
    tsupport (cutoff E R) ⊆ closedBall (0 : E) (2 * R) :=
  closure_minimal ((cutoff_support_subset hR).trans ball_subset_closedBall) isClosed_closedBall

/-- Near any point of the open ball of radius `R` the cutoff is identically one. -/
theorem cutoff_eventuallyEq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ < R) :
    cutoff E R =ᶠ[𝓝 x] 1 := by
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy
  exact cutoff_eq_one hR hy.le

/-! ### Plateaus -/

/-- Every bounded set lies in the plateau of all sufficiently large cutoffs. -/
theorem bounded_plateau {K : Set E} (hK : Bornology.IsBounded K) :
    ∃ R₀ > 0, ∀ R ≥ R₀, EqOn (cutoff E R) (fun _ => 1) K := by
  obtain ⟨R₀, hR₀, hbound⟩ := hK.exists_pos_norm_le
  exact ⟨R₀, hR₀, fun R hR x hx => cutoff_eq_one (hR₀.trans_le hR)
    ((hbound x hx).trans hR)⟩

/-- On a fixed bounded set the cutoffs eventually agree with the constant one. -/
theorem eventually_bounded_plateau {K : Set E} (hK : Bornology.IsBounded K) :
    ∀ᶠ R : ℝ in atTop, EqOn (cutoff E R) (fun _ => 1) K := by
  obtain ⟨R₀, _, h⟩ := bounded_plateau hK
  exact eventually_atTop.2 ⟨R₀, h⟩

/-- Every fixed compact set lies in the plateau of all sufficiently large cutoffs. -/
theorem compact_plateau {K : Set E} (hK : IsCompact K) :
    ∃ R₀ > 0, ∀ R ≥ R₀, EqOn (cutoff E R) (fun _ => 1) K :=
  bounded_plateau hK.isBounded

theorem eventually_compact_plateau {K : Set E} (hK : IsCompact K) :
    ∀ᶠ R : ℝ in atTop, EqOn (cutoff E R) (fun _ => 1) K := by
  obtain ⟨R₀, _, h⟩ := compact_plateau hK
  exact eventually_atTop.2 ⟨R₀, h⟩

theorem eventually_cutoff_eq_one (x : E) :
    ∀ᶠ R : ℝ in atTop, cutoff E R x = 1 := by
  filter_upwards [eventually_compact_plateau (isCompact_singleton (x := x))] with R hR
  exact hR (mem_singleton x)

theorem cutoff_tendsto_one (x : E) :
    Tendsto (fun R : ℝ => cutoff E R x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_cutoff_eq_one x] with R hR
  exact hR.symm

/-! ### Derivative bounds under dilation -/

section Dilation

variable {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The dilation `x ↦ R⁻¹ • x` as a continuous linear map. -/
private def dilation (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] (R : ℝ) :
    D →L[ℝ] D :=
  R⁻¹ • ContinuousLinearMap.id ℝ D

private theorem norm_dilation_le {R : ℝ} (hR : 0 < R) : ‖dilation D R‖ ≤ R⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hR.le)
  intro x
  change ‖R⁻¹ • x‖ ≤ R⁻¹ * ‖x‖
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, le_refl]

/-- Dilating a smooth function by `R⁻¹` divides a uniform bound on its `n`th
derivative by `R ^ n`. -/
theorem iteratedFDeriv_comp_inv_smul_le {χ : D → F} {n : ℕ} (hχ : ContDiff ℝ n χ) {C : ℝ}
    (hC : ∀ y, ‖iteratedFDeriv ℝ n χ y‖ ≤ C) {R : ℝ} (hR : 0 < R) (x : D) :
    ‖iteratedFDeriv ℝ n (fun y => χ (R⁻¹ • y)) x‖ ≤ C / R ^ n := by
  change ‖iteratedFDeriv ℝ n (χ ∘ dilation D R) x‖ ≤ _
  rw [(dilation D R).iteratedFDeriv_comp_right hχ x le_rfl]
  calc
    ‖(iteratedFDeriv ℝ n χ (dilation D R x)).compContinuousLinearMap
        (fun _ => dilation D R)‖
        ≤ ‖iteratedFDeriv ℝ n χ (dilation D R x)‖ * ∏ _ : Fin n, ‖dilation D R‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n χ (dilation D R x)‖ * (R⁻¹) ^ n := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        ∏ _ : Fin n, ‖dilation D R‖ ≤ ∏ _ : Fin n, R⁻¹ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_dilation_le hR)
        _ = (R⁻¹) ^ n := by simp
    _ ≤ C * (R⁻¹) ^ n := mul_le_mul_of_nonneg_right (hC _) (by positivity)
    _ = C / R ^ n := by simp [div_eq_mul_inv]

end Dilation

/-! ### Compact support

From here on the space is finite-dimensional, so the closed balls containing the
supports are compact and every derivative of the bump is bounded. -/

variable [FiniteDimensional ℝ E]

theorem baseCutoff_hasCompactSupport : HasCompactSupport (baseCutoff E) :=
  (baseBump E).hasCompactSupport

theorem cutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutoff E R) :=
  (isCompact_closedBall (0 : E) (2 * R)).of_isClosed_subset
    isClosed_closure (cutoff_tsupport_subset hR)

private theorem exists_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (baseCutoff E) x‖ ≤ C := by
  have hc : HasCompactSupport (iteratedFDeriv ℝ n (baseCutoff E)) :=
    baseCutoff_hasCompactSupport.iteratedFDeriv n
  have hcont : Continuous (iteratedFDeriv ℝ n (baseCutoff E)) :=
    ContDiff.continuous_iteratedFDeriv le_rfl (contDiff_infty.1 baseCutoff_smooth n)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hcont
  exact ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hC x).trans (le_max_right _ _)⟩

variable (E) in
/-- A fixed positive bound for the `n`th derivative of the unscaled bump. -/
def derivativeConstant (n : ℕ) : ℝ := Classical.choose (exists_derivative_bound (E := E) n)

theorem derivativeConstant_pos (n : ℕ) : 0 < derivativeConstant E n :=
  (Classical.choose_spec (exists_derivative_bound (E := E) n)).1

theorem baseCutoff_iteratedFDeriv_le (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (baseCutoff E) x‖ ≤ derivativeConstant E n :=
  (Classical.choose_spec (exists_derivative_bound (E := E) n)).2 x

/-- Each spatial derivative contributes precisely one inverse power of the radius. -/
theorem cutoff_iteratedFDeriv_le {R : ℝ} (hR : 0 < R) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (cutoff E R) x‖ ≤ derivativeConstant E n / R ^ n :=
  iteratedFDeriv_comp_inv_smul_le (contDiff_infty.1 baseCutoff_smooth n)
    (baseCutoff_iteratedFDeriv_le n) hR x

theorem cutoff_fderiv_le {R : ℝ} (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (cutoff E R) x‖ ≤ derivativeConstant E 1 / R := by
  have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := cutoff E R) (x := x) (n := 0)
  simp only [norm_iteratedFDeriv_zero] at hn
  rw [hn]
  simpa only [pow_one] using cutoff_iteratedFDeriv_le hR 1 x

theorem cutoff_second_fderiv_le {R : ℝ} (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (cutoff E R)) x‖ ≤ derivativeConstant E 2 / R ^ 2 := by
  have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fderiv ℝ (cutoff E R))
    (x := x) (n := 0)
  simp only [norm_iteratedFDeriv_zero] at hn
  rw [hn, norm_iteratedFDeriv_fderiv]
  exact cutoff_iteratedFDeriv_le hR 2 x

/-- The scale-invariant derivative bound: the gradient of `cutoff E R` is of size
`R⁻¹` and lives where `‖x‖ ≤ 2 R`, so the product is bounded independently of `R`. -/
theorem cutoff_fderiv_mul_norm_le {R : ℝ} (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (cutoff E R) x‖ * ‖x‖ ≤ 2 * derivativeConstant E 1 := by
  by_cases hx : ‖x‖ ≤ 2 * R
  · calc
      ‖fderiv ℝ (cutoff E R) x‖ * ‖x‖ ≤ (derivativeConstant E 1 / R) * (2 * R) :=
        mul_le_mul (cutoff_fderiv_le hR x) hx (norm_nonneg _)
          (div_pos (derivativeConstant_pos 1) hR).le
      _ = 2 * derivativeConstant E 1 := by field_simp
  · have hz : fderiv ℝ (cutoff E R) x = 0 := by
      by_contra h
      exact hx (mem_closedBall_zero_iff.mp
        (cutoff_tsupport_subset hR (support_fderiv_subset (𝕜 := ℝ) h)))
    rw [hz, norm_zero, zero_mul]
    exact (mul_pos zero_lt_two (derivativeConstant_pos 1)).le

end NavierStokesAndEuler.SmoothCutoff
