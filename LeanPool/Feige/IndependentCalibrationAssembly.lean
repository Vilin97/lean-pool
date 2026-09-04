/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.AugmentedLatentSupport
import LeanPool.Feige.MarginalLaw
import LeanPool.Feige.MixtureCalibration
import LeanPool.Feige.RecursiveLatentProbability
import LeanPool.Feige.Calibration

/-!
# Assembly of calibration for independent variables

Independent nonnegative variables are first normalized to mean one.  Their
joint law is then the product of their marginal laws, which is represented
by the augmented latent mixture and averaged using the two-point bound.
-/

open MeasureTheory ProbabilityTheory Set

namespace Feige

noncomputable section

/-- The finite two-point rejection theorem implies universal calibration
of the Dirichlet statistic. -/
theorem universalCalibration_dirichletK_of_twoPointRejectionBound
    {n : ℕ} (htwo : TwoPointRejectionBound) :
    UniversalCalibration (dirichletK : (Fin n → ℝ) → ℝ) := by
  intro Ω _ μ _ Y hYmeas hYint hYindep hYnonneg hYmean α hα _hαle
  let Z : Fin n → Ω → ℝ := meanOneNormalize Y μ
  let marginal : Fin n → Measure ℝ := fun i ↦ μ.map (Z i)
  have hZmeas : ∀ i, Measurable (Z i) :=
    meanOneNormalize_measurable Y hYmeas
  have hZint : ∀ i, Integrable (Z i) μ :=
    meanOneNormalize_integrable Y hYint
  have hZmean : ∀ i, (∫ ω, Z i ω ∂μ) = 1 :=
    meanOneNormalize_mean Y
  have hZnonneg : ∀ i ω, 0 ≤ Z i ω :=
    meanOneNormalize_nonneg Y hYnonneg
  have hZindep : iIndepFun Z μ :=
    meanOneNormalize_iIndepFun Y hYindep
  let hmarginal : ∀ i, IsProbabilityMeasure (marginal i) :=
    fun i ↦ Measure.isProbabilityMeasure_map (hZmeas i).aemeasurable
  have hmarginalInt :
      ∀ i, Integrable (fun x : ℝ ↦ x) (marginal i) :=
    fun i ↦ integrable_id_map (hZmeas i) (hZint i)
  have hmarginalMean :
      ∀ i, (∫ x : ℝ, x ∂marginal i) = 1 := by
    intro i
    rw [integral_id_map (hZmeas i)]
    exact hZmean i
  have hmarginalSupport :
      ∀ i, marginal i (Iio 0) = 0 :=
    fun i ↦ map_apply_Iio_zero_of_nonnegative (hZmeas i) (hZnonneg i)
  let latent :=
    recursiveAugmentedLatent n
      (fun i ↦ meanOneAugmentedLatent (marginal i))
  let hcoordinateLatent : ∀ i, IsProbabilityMeasure
      (meanOneAugmentedLatent (marginal i)) :=
    fun i ↦ meanOneAugmentedLatent_isProbability
      (hmarginalInt i) (hmarginalMean i)
  let : IsProbabilityMeasure latent := by
    unfold latent
    infer_instance
  have hlatentSupport :
      ∀ᵐ p ∂latent, AugmentedParamsNonnegative p := by
    exact ae_recursiveAugmentedLatent_nonnegative n marginal
      hmarginalInt hmarginalMean hmarginalSupport
  have hmixture :
      recursiveAugmentedKernel n ∘ₘ latent = Measure.pi marginal := by
    unfold latent
    exact pi_eq_recursiveMeanOneAugmented_mixture n marginal
      hmarginalInt hmarginalMean
  have hproduct :
      (Measure.pi marginal).real {y | dirichletK y ≤ α} ≤ α := by
    rw [← hmixture]
    exact augmentedMixture_rejection_le htwo latent hlatentSupport hα
  have hjoint :
      μ.map (fun ω i ↦ Z i ω) = Measure.pi marginal := by
    exact (iIndepFun_iff_map_fun_eq_pi_map
      (fun i ↦ (hZmeas i).aemeasurable)).mp hZindep
  calc
    μ.real {ω | dirichletK (fun i ↦ Y i ω) ≤ α} ≤
        μ.real {ω | dirichletK (fun i ↦ Z i ω) ≤ α} :=
      rejection_probability_le_normalized Y hYint hYnonneg hYmean α
    _ = (μ.map (fun ω i ↦ Z i ω)).real
        {y | dirichletK y ≤ α} := by
      exact (map_measureReal_apply
        (measurable_pi_lambda _ hZmeas)
        (measurableSet_dirichletK_le α)).symm
    _ = (Measure.pi marginal).real {y | dirichletK y ≤ α} := by
      rw [hjoint]
    _ ≤ α := hproduct

end

end Feige
