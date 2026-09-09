/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LocalizedDifferenceEnergy
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeightedSobolev
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs

@[expose] public section

/-!
# Non-pressure terms in the localized difference energy balance

The velocity difference need not have compact support or globally integrable
derivatives. The compact cutoff supplies local integrability; the estimates
use its weighted `L⁶` norm and the unweighted `L²` norm of the difference.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff BigOperators InnerProductSpace

namespace NavierStokesR3.LocalizedFluxEstimates

open ProblemStatement Comparison
open NavierStokes.ProblemStatement (spatialDerivative coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)

/-- The cutoff makes the coupling integral finite. -/
theorem coupling_integrable {χ : Space → ℝ} {u w : VelocityField} {t : ℝ}
    (hχ : Continuous χ) (hs : HasCompactSupport χ)
    (hu : ContDiff ℝ 1 (fun x => u (t, x)))
    (hw : Continuous (fun x => w (t, x))) :
    Integrable (fun x => χ x *
      ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ) volume := by
  apply LocalizedDifferenceEnergy.integrable_cutoff_mul hχ hs
  exact hw.inner ((hu.continuous_fderiv (by simp)).clm_apply hw)

/-- The indefinite coupling is controlled by the gradient of the reference
velocity and the actual compactly weighted energy. -/
theorem neg_coupling_le_weightedEnergy {χ : Space → ℝ} {u w : VelocityField} {t G : ℝ}
    (hχ : Continuous χ) (hs : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hu : ContDiff ℝ 1 (fun x => u (t, x)))
    (hw : Continuous (fun x => w (t, x)))
    (hG : ∀ x, ‖spatialDerivative u t x‖ ≤ G) :
    -(∫ x, χ x * ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ) ≤
      G * weightedEnergy χ w t := by
  have hi := coupling_integrable hχ hs hu hw
  have he := LocalizedDifferenceEnergy.integrable_weighted_energy hχ hs hw
  rw [← integral_neg]
  change (∫ x, -(χ x * ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ)) ≤
    G * (∫ x, χ x * ‖w (t, x)‖ ^ 2)
  rw [← integral_const_mul]
  apply integral_mono hi.neg (he.const_mul G)
  intro x
  change -(χ x * ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ) ≤
    G * (χ x * ‖w (t, x)‖ ^ 2)
  have h := NavierStokes.PeriodicUniqueness.nonlinear_energy_bound
    (spatialDerivative u t x) (w (t, x)) (hG x)
  nlinarith [mul_le_mul_of_nonneg_left h (hχ0 x)]

/-- Derivative of the energy weight. -/
theorem fderiv_cutoff_eight {φ : Space → ℝ} {x : Space}
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (fun y => φ y ^ 8) x = (8 * φ x ^ 7) • fderiv ℝ φ x := by
  simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
    ((hasDerivAt_pow 8 (φ x)).comp_hasFDerivAt x hφ.hasFDerivAt).fderiv

/-- One power of the cutoff is harmless because it lies in `[0,1]`. -/
theorem norm_fderiv_cutoff_eight_apply_le {φ : Space → ℝ} {x : Space}
    (hφ : DifferentiableAt ℝ φ x) (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ‖fderiv ℝ φ x‖ ≤ L) (z : Space) :
    ‖fderiv ℝ (fun y => φ y ^ 8) x z‖ ≤ (8 * L) * φ x ^ 6 * ‖z‖ := by
  have h76 : φ x ^ 7 ≤ φ x ^ 6 := by
    calc
      φ x ^ 7 = φ x ^ 6 * φ x := by ring
      _ ≤ φ x ^ 6 * 1 := mul_le_mul_of_nonneg_left hφ1 (pow_nonneg hφ0 6)
      _ = φ x ^ 6 := mul_one _
  have hd : ‖fderiv ℝ φ x z‖ ≤ L * ‖z‖ :=
    ((fderiv ℝ φ x).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg z))
  rw [fderiv_cutoff_eight hφ, _root_.smul_apply, smul_eq_mul,
    norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 8 * φ x ^ 7)]
  calc
    (8 * φ x ^ 7) * ‖fderiv ℝ φ x z‖ ≤ (8 * φ x ^ 7) * (L * ‖z‖) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = φ x ^ 7 * ((8 * L) * ‖z‖) := by ring
    _ ≤ φ x ^ 6 * ((8 * L) * ‖z‖) :=
      mul_le_mul_of_nonneg_right h76 (by positivity)
    _ = (8 * L) * φ x ^ 6 * ‖z‖ := by ring

/-- The reference velocity vanishes in the cutoff derivative, leaving only
the difference velocity in the transport flux. -/
theorem transport_flux_bound {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L)
    (hvanish : ∀ x, fderiv ℝ (fun y => φ y ^ 8) x (u (t, x)) = 0) :
    Integrable (fun x => ‖(u - v) (t, x)‖ ^ 2 *
      fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))) volume ∧
    |∫ x, ‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))| ≤
      (8 * L) * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
        cutoffL6 φ (u - v) t ^ (3 / 2 : ℝ) := by
  have hw : Continuous (fun x => (u - v) (t, x)) := hu.sub hv
  have hweighted := WeightedSobolev.memLp_cutoff_pow_smul hφ.continuous hs hw
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hT, hTb⟩ := WeightedInterpolation.cutoff_transport_bound
    hφ.continuous.aestronglyMeasurable hφ0 hw2 hweighted
  have hswitch (x : Space) : fderiv ℝ (fun y => φ y ^ 8) x (v (t, x)) =
      -fderiv ℝ (fun y => φ y ^ 8) x ((u - v) (t, x)) := by
    simp only [Pi.sub_apply, map_sub, hvanish x, zero_sub, neg_neg]
  have hbound (x : Space) :
      ‖‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))‖ ≤
        (8 * L) * (φ x ^ 6 * ‖(u - v) (t, x)‖ ^ 3) := by
    rw [norm_mul, norm_pow, norm_norm, hswitch, norm_neg]
    calc
      ‖(u - v) (t, x)‖ ^ 2 *
          ‖fderiv ℝ (fun y => φ y ^ 8) x ((u - v) (t, x))‖ ≤
          ‖(u - v) (t, x)‖ ^ 2 * ((8 * L) * φ x ^ 6 * ‖(u - v) (t, x)‖) :=
        mul_le_mul_of_nonneg_left
          (norm_fderiv_cutoff_eight_apply_le (hφ.differentiable (by simp) x)
            (hφ0 x) (hφ1 x) hL0 (hL x) _) (sq_nonneg _)
      _ = _ := by ring
  have hmajor := hT.const_mul (8 * L)
  have hflux : Continuous (fun x => ‖(u - v) (t, x)‖ ^ 2 *
      fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))) :=
    (hw.norm.pow 2).mul (((hφ.pow 8).continuous_fderiv (by simp)).clm_apply hv)
  refine ⟨hmajor.mono' hflux.aestronglyMeasurable (Eventually.of_forall hbound), ?_⟩
  calc
    |∫ x, ‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))| ≤
        ∫ x, (8 * L) * (φ x ^ 6 * ‖(u - v) (t, x)‖ ^ 3) :=
      norm_integral_le_of_norm_le hmajor (Eventually.of_forall hbound)
    _ = (8 * L) * (∫ x, φ x ^ 6 * ‖(u - v) (t, x)‖ ^ 3) := integral_const_mul _ _
    _ ≤ (8 * L) * (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
        cutoffL6 φ (u - v) t ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hTb (by positivity)
    _ = _ := by ring

theorem continuous_laplacian {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (ComparisonCutoffs.laplacian χ) := by
  unfold ComparisonCutoffs.laplacian
  exact continuous_finsetSum _ fun i _ =>
    (NavierStokes.PeriodicUniqueness.spatial_partial_contDiff
      (NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hχ i) i).continuous

/-- A bounded Laplacian can be paired with any square-integrable field. -/
theorem laplacian_flux_bound {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw2 : MemLp w 2 volume) {K : ℝ}
    (hK : ∀ x, ‖ComparisonCutoffs.laplacian χ x‖ ≤ K) :
    Integrable (fun x => ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x) volume ∧
      |∫ x, ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x| ≤ K * comparisonLpNorm 2 w ^ 2 := by
  have hsquare : Integrable (fun x => ‖w x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hw2.aestronglyMeasurable).mp hw2
  have hmajor := hsquare.const_mul K
  have hbound (x : Space) : ‖‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x‖ ≤
      K * ‖w x‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_norm]
    exact (mul_le_mul_of_nonneg_left (hK x) (sq_nonneg _)).trans_eq (mul_comm _ _)
  have hmeas : AEStronglyMeasurable
      (fun x => ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x) volume :=
    (hw2.aestronglyMeasurable.norm.pow 2).mul (continuous_laplacian hχ).aestronglyMeasurable
  refine ⟨hmajor.mono' hmeas (Eventually.of_forall hbound), ?_⟩
  calc
    |∫ x, ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x| ≤ ∫ x, K * ‖w x‖ ^ 2 :=
      norm_integral_le_of_norm_le hmajor (Eventually.of_forall hbound)
    _ = K * l2Sq w := integral_const_mul _ _
    _ = K * comparisonLpNorm 2 w ^ 2 := by rw [← LpNormTools.lpNorm_two_sq_eq_l2Sq hw2]

private def baseWeight (x : Space) : ℝ := ComparisonCutoffs.baseCutoff x ^ 8

private theorem baseWeight_smooth : ContDiff ℝ ∞ baseWeight :=
  ComparisonCutoffs.baseCutoff_smooth.pow 8

private theorem baseWeight_hasCompactSupport : HasCompactSupport baseWeight :=
  ComparisonCutoffs.baseCutoff_hasCompactSupport.comp_left
    (g := fun r : ℝ => r ^ 8) (by norm_num)

private theorem exists_weight_second_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space, ‖iteratedFDeriv ℝ 2 baseWeight x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (baseWeight_hasCompactSupport.iteratedFDeriv 2).exists_bound_of_continuous
    (ContDiff.continuous_iteratedFDeriv le_rfl (contDiff_infty.1 baseWeight_smooth 2))
  exact ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hC x).trans (le_max_right _ _)⟩

/-- A fixed derivative bound for the unscaled energy weight. -/
def weightSecondDerivativeConstant : ℝ := Classical.choose exists_weight_second_derivative_bound

theorem weightSecondDerivativeConstant_pos : 0 < weightSecondDerivativeConstant :=
  (Classical.choose_spec exists_weight_second_derivative_bound).1

private theorem baseWeight_iteratedFDeriv_two_le (x : Space) :
    ‖iteratedFDeriv ℝ 2 baseWeight x‖ ≤ weightSecondDerivativeConstant :=
  (Classical.choose_spec exists_weight_second_derivative_bound).2 x

private def weightDilation (R : ℝ) : Space →L[ℝ] Space :=
  R⁻¹ • ContinuousLinearMap.id ℝ Space

private theorem norm_weightDilation_le {R : ℝ} (hR : 0 < R) :
    ‖weightDilation R‖ ≤ R⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hR.le)
  intro x
  change ‖R⁻¹ • x‖ ≤ R⁻¹ * ‖x‖
  rw [ComparisonCutoffs.norm_scaled hR, div_eq_inv_mul]

/-- Apply scaling to the fixed eighth-power weight before estimating its
derivatives. The second derivative has the same inverse-square scaling. -/
theorem weight_iteratedFDeriv_two_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖iteratedFDeriv ℝ 2 (ComparisonCutoffs.weight R) x‖ ≤
      weightSecondDerivativeConstant / R ^ 2 := by
  change ‖iteratedFDeriv ℝ 2 (baseWeight ∘ weightDilation R) x‖ ≤ _
  rw [(weightDilation R).iteratedFDeriv_comp_right
    (contDiff_infty.1 baseWeight_smooth 2) x le_rfl]
  calc
    ‖(iteratedFDeriv ℝ 2 baseWeight (weightDilation R x)).compContinuousLinearMap
        (fun _ => weightDilation R)‖ ≤
        ‖iteratedFDeriv ℝ 2 baseWeight (weightDilation R x)‖ *
          ∏ _ : Fin 2, ‖weightDilation R‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ 2 baseWeight (weightDilation R x)‖ * (R⁻¹) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        ∏ _ : Fin 2, ‖weightDilation R‖ ≤ ∏ _ : Fin 2, R⁻¹ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_weightDilation_le hR)
        _ = (R⁻¹) ^ 2 := by simp
    _ ≤ weightSecondDerivativeConstant * (R⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right (baseWeight_iteratedFDeriv_two_le _) (by positivity)
    _ = weightSecondDerivativeConstant / R ^ 2 := by simp [div_eq_mul_inv]

theorem weight_second_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fderiv ℝ (ComparisonCutoffs.weight R)) x‖ ≤
      weightSecondDerivativeConstant / R ^ 2 := by
  have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
    (f := fderiv ℝ (ComparisonCutoffs.weight R)) (x := x) (n := 0)
  simp only [norm_iteratedFDeriv_zero] at hn
  rw [hn, norm_iteratedFDeriv_fderiv]
  exact weight_iteratedFDeriv_two_le hR x

/-- The fixed constant in the inverse-square Laplacian estimate. -/
def weightLaplacianConstant : ℝ := 3 * weightSecondDerivativeConstant

theorem weightLaplacianConstant_pos : 0 < weightLaplacianConstant :=
  mul_pos (by norm_num) weightSecondDerivativeConstant_pos

theorem weight_laplacian_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖ComparisonCutoffs.laplacian (ComparisonCutoffs.weight R) x‖ ≤
      weightLaplacianConstant / R ^ 2 := by
  calc
    ‖ComparisonCutoffs.laplacian (ComparisonCutoffs.weight R) x‖ ≤
        ∑ i : Fin 3, ‖spatialPartial i (spatialPartial i (ComparisonCutoffs.weight R)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, weightSecondDerivativeConstant / R ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        (ComparisonCutoffs.norm_partial_partial_le (ComparisonCutoffs.weight_smooth R)
          i i x).trans (weight_second_fderiv_le hR x)
    _ = weightLaplacianConstant / R ^ 2 := by
      simp [weightLaplacianConstant, mul_div_assoc]

/-- The Laplacian term in the energy identity is of order `R⁻² M²`.
Finiteness is explicit and only requires `L²` membership of the velocity. -/
theorem weight_laplacian_flux_bound {R : ℝ} (hR : 0 < R) {w : VelocityField} {t : ℝ}
    (hw2 : MemLp (fun x => w (t, x)) 2 volume) :
    Integrable (fun x => ‖w (t, x)‖ ^ 2 *
      ∑ i : Fin 3, spatialPartial i (spatialPartial i (ComparisonCutoffs.weight R)) x) volume ∧
      |∫ x, ‖w (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i (ComparisonCutoffs.weight R)) x| ≤
          (weightLaplacianConstant / R ^ 2) * comparisonLpNorm 2 (fun x => w (t, x)) ^ 2 :=
  laplacian_flux_bound (ComparisonCutoffs.weight_smooth R) hw2 (weight_laplacian_le hR)

end NavierStokesR3.LocalizedFluxEstimates
