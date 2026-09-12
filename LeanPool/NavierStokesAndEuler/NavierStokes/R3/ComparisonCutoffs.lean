/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SolutionDifference
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
public import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothCutoff

/-!
# Smooth spatial cutoffs for whole-space comparison

The fixed bump is one on the unit ball and supported in the ball of radius two.
All scaled cutoffs are obtained from this same bump by dilation.  In particular,
the constants in their derivative estimates do not depend on the radius.
-/

@[expose] public section



noncomputable section

open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.ComparisonCutoffs

open ProblemStatement
open NavierStokes.ProblemStatement (coordinateVector)

/-- The fixed bump with inner radius one and outer radius two. -/
noncomputable def baseBump : ContDiffBump (0 : Space) :=
  NavierStokesAndEuler.SmoothCutoff.baseBump Space

/-- The unscaled cutoff. -/
def baseCutoff (x : Space) : ℝ :=
  NavierStokesAndEuler.SmoothCutoff.baseCutoff Space x

/-- The cutoff at spatial radius `R`; its estimates are stated for `0 < R`. -/
def cutoff (R : ℝ) (x : Space) : ℝ :=
  NavierStokesAndEuler.SmoothCutoff.cutoff Space R x

/-- The weight in the localized energy. -/
def weight (R : ℝ) (x : Space) : ℝ := cutoff R x ^ 8

/-- The multiplier used to commute the pressure operator. -/
def multiplier (R : ℝ) (x : Space) : ℝ := cutoff R x ^ 2

theorem baseCutoff_smooth : ContDiff ℝ ∞ baseCutoff :=
  NavierStokesAndEuler.SmoothCutoff.baseCutoff_smooth

theorem baseCutoff_nonneg (x : Space) : 0 ≤ baseCutoff x :=
  NavierStokesAndEuler.SmoothCutoff.baseCutoff_nonneg x

theorem baseCutoff_le_one (x : Space) : baseCutoff x ≤ 1 :=
  NavierStokesAndEuler.SmoothCutoff.baseCutoff_le_one x

theorem baseCutoff_eq_one {x : Space} (hx : ‖x‖ ≤ 1) : baseCutoff x = 1 :=
  NavierStokesAndEuler.SmoothCutoff.baseCutoff_eq_one hx

theorem baseCutoff_eq_zero {x : Space} (hx : 2 ≤ ‖x‖) : baseCutoff x = 0 :=
  NavierStokesAndEuler.SmoothCutoff.baseCutoff_eq_zero hx

theorem baseCutoff_hasCompactSupport : HasCompactSupport baseCutoff :=
  NavierStokesAndEuler.SmoothCutoff.baseCutoff_hasCompactSupport

theorem baseCutoff_tsupport : tsupport baseCutoff = closedBall (0 : Space) 2 := by
  exact baseBump.tsupport_eq

theorem cutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (cutoff R) :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_smooth R

theorem cutoff_nonneg (R : ℝ) (x : Space) : 0 ≤ cutoff R x :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_nonneg R x

theorem cutoff_le_one (R : ℝ) (x : Space) : cutoff R x ≤ 1 :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_le_one R x

theorem cutoff_mem_Icc (R : ℝ) (x : Space) : cutoff R x ∈ Icc (0 : ℝ) 1 :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_mem_Icc R x

theorem norm_scaled {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖R⁻¹ • x‖ = ‖x‖ / R :=
  NavierStokesAndEuler.SmoothCutoff.norm_inv_smul hR x

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) :
    cutoff R x = 1 :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_eq_one hR hx

theorem cutoff_eq_one_on_closedBall {R : ℝ} (hR : 0 < R) :
    EqOn (cutoff R) (fun _ => 1) (closedBall (0 : Space) R) := by
  intro x hx
  exact cutoff_eq_one hR (by simpa [mem_closedBall, dist_zero_right] using hx)

theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : Space} (hx : 2 * R ≤ ‖x‖) :
    cutoff R x = 0 :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_eq_zero hR hx

theorem cutoff_support_subset {R : ℝ} (hR : 0 < R) :
    Function.support (cutoff R) ⊆ ball (0 : Space) (2 * R) :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_support_subset hR

theorem cutoff_tsupport_subset {R : ℝ} (hR : 0 < R) :
    tsupport (cutoff R) ⊆ closedBall (0 : Space) (2 * R) :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_tsupport_subset hR

theorem cutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutoff R) :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_hasCompactSupport hR

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
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space, ‖iteratedFDeriv ℝ n baseCutoff x‖ ≤ C :=
  ⟨NavierStokesAndEuler.SmoothCutoff.derivativeConstant Space n,
    NavierStokesAndEuler.SmoothCutoff.derivativeConstant_pos n,
    NavierStokesAndEuler.SmoothCutoff.baseCutoff_iteratedFDeriv_le n⟩

/-- A fixed positive bound for the `n`th derivative of the unscaled bump. -/
def derivativeConstant (n : ℕ) : ℝ :=
  NavierStokesAndEuler.SmoothCutoff.derivativeConstant Space n

theorem derivativeConstant_pos (n : ℕ) : 0 < derivativeConstant n :=
  NavierStokesAndEuler.SmoothCutoff.derivativeConstant_pos n

theorem baseCutoff_iteratedFDeriv_le (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n baseCutoff x‖ ≤ derivativeConstant n :=
  NavierStokesAndEuler.SmoothCutoff.baseCutoff_iteratedFDeriv_le n x

/-- Each spatial derivative contributes precisely one inverse power of the radius. -/
theorem cutoff_iteratedFDeriv_le {R : ℝ} (hR : 0 < R) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (cutoff R) x‖ ≤ derivativeConstant n / R ^ n :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_iteratedFDeriv_le hR n x

theorem cutoff_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (cutoff R) x‖ ≤ derivativeConstant 1 / R :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_fderiv_le hR x

theorem cutoff_second_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fderiv ℝ (cutoff R)) x‖ ≤ derivativeConstant 2 / R ^ 2 :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_second_fderiv_le hR x

/-- The scalar spatial Laplacian, using the fixed standard coordinate vectors. -/
def laplacian (f : Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, NavierStokes.SolutionDifference.spatialPartial i
    (NavierStokes.SolutionDifference.spatialPartial i f) x

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
    ‖NavierStokes.SolutionDifference.spatialPartial i
      (NavierStokes.SolutionDifference.spatialPartial j f) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  change ‖fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j)) x (coordinateVector i)‖ ≤ _
  rw [fderiv_apply_derivative hf]
  have hv (k : Fin 3) : ‖coordinateVector k‖ ≤ 1 := by
    simp [coordinateVector]
  exact ((fderiv ℝ (fderiv ℝ f) x (coordinateVector i)).unit_le_opNorm
    (coordinateVector j) (hv j)).trans
    ((fderiv ℝ (fderiv ℝ f) x).unit_le_opNorm (coordinateVector i) (hv i))

theorem cutoff_partial_partial_le {R : ℝ} (hR : 0 < R) (i j : Fin 3) (x : Space) :
    ‖NavierStokes.SolutionDifference.spatialPartial i
      (NavierStokes.SolutionDifference.spatialPartial j (cutoff R)) x‖ ≤
      derivativeConstant 2 / R ^ 2 :=
  (norm_partial_partial_le (cutoff_smooth R) i j x).trans (cutoff_second_fderiv_le hR x)

theorem cutoff_laplacian_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖laplacian (cutoff R) x‖ ≤ (3 * derivativeConstant 2) / R ^ 2 := by
  calc
    ‖laplacian (cutoff R) x‖
        ≤ ∑ i : Fin 3, ‖NavierStokes.SolutionDifference.spatialPartial i
          (NavierStokes.SolutionDifference.spatialPartial i (cutoff R)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, derivativeConstant 2 / R ^ 2 :=
      Finset.sum_le_sum (fun i _ => cutoff_partial_partial_le hR i i x)
    _ = (3 * derivativeConstant 2) / R ^ 2 := by simp [mul_div_assoc]

/-- Every fixed compact set lies in the plateau of all sufficiently large cutoffs. -/
theorem compact_plateau {K : Set Space} (hK : IsCompact K) :
    ∃ R₀ > 0, ∀ R ≥ R₀, EqOn (cutoff R) (fun _ => 1) K :=
  NavierStokesAndEuler.SmoothCutoff.compact_plateau hK

theorem eventually_compact_plateau {K : Set Space} (hK : IsCompact K) :
    ∀ᶠ R : ℝ in atTop, EqOn (cutoff R) (fun _ => 1) K :=
  NavierStokesAndEuler.SmoothCutoff.eventually_compact_plateau hK

theorem eventually_cutoff_eq_one (x : Space) :
    ∀ᶠ R : ℝ in atTop, cutoff R x = 1 :=
  NavierStokesAndEuler.SmoothCutoff.eventually_cutoff_eq_one x

theorem cutoff_tendsto_one (x : Space) :
    Tendsto (fun R : ℝ => cutoff R x) atTop (𝓝 1) :=
  NavierStokesAndEuler.SmoothCutoff.cutoff_tendsto_one x

end NavierStokesR3.ComparisonCutoffs
