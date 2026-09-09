/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatVolterra
public import LeanPool.NavierStokesAndEuler.Euler.SobolevPressureResolvent

@[expose] public section

/-! The actual Gaussian heat and Volterra integrals preserve the lifted divergence constraint. -/

noncomputable section

namespace EulerDivergenceFreeHeat

open MeasureTheory ProbabilityTheory EulerLiftedGradientSpace EulerGaussianCylinderHeat
  EulerCylinderSobolevSpace EulerSobolevHeat EulerVolterraConvolution
    EulerSobolevCoefficientPressure
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The actual lifted gradient projection commutes with each Gaussian directional heat average. -/
theorem gradientProjection_lineHeat (κ : ℝ) (m : Vector3) (a : LiftTangent) (v : ℝ≥0) (f : LiftL2
  period) :
    gradientProjection period κ m (lineHeat period a v f) =
      lineHeat period a v (gradientProjection period κ m f) := by
  unfold lineHeat
  rw [← (gradientProjection period κ m).integral_comp_comm (lineOrbit_integrable period a f _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r =>
    (gradientProjection_translation period κ m (EulerPressureSpatialRegularity.translationPath
      period a r) f).symm

/-- The lifted gradient projection commutes with every finite product of Gaussian heat averages. -/
theorem gradientProjection_heatList (κ : ℝ) (m : Vector3) (directions : List LiftTangent)
    (v : ℝ≥0) (f : LiftL2 period) :
    gradientProjection period κ m (heatList period directions v f) =
      heatList period directions v (gradientProjection period κ m f) := by
  induction directions with
  | nil => rfl
  | cons a tail ih => rw [heatList, heatList, gradientProjection_lineHeat, ih]

/-- The actual cylinder heat semigroup preserves the lifted gradient projection exactly. -/
theorem gradientProjection_cylinderHeat (κ : ℝ) (m : Vector3) (v : ℝ≥0) (f : LiftL2 period) :
    gradientProjection period κ m (cylinderHeat period v f) =
      cylinderHeat period v (gradientProjection period κ m f) :=
  gradientProjection_heatList period κ m cylinderDirections v f

/-- The continuous constraint map on an actual complete Sobolev space. -/
def gradientEvaluation (q : ℕ) (κ : ℝ) (m : Vector3) : SobolevSpace period q →L[ℝ] LiftL2 period :=
  (gradientProjection period κ m).comp (valueOperator period q)

/-- The Sobolev constraint is exactly the underlying lifted L² gradient projection. -/
@[simp]
theorem gradientEvaluation_apply {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q) :
    gradientEvaluation period q κ m u = gradientProjection period κ m (value period u) := rfl

/-- Vanishing of the continuous constraint map is exactly membership in the genuine divergence-free subspace. -/
theorem gradientEvaluation_zero_iff {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q) :
    gradientEvaluation period q κ m u = 0 ↔ value period u ∈ divergenceFreeSpace period κ m := by
  constructor
  · intro h
    apply (gradientSpace period κ m).orthogonalProjectionOnto_eq_zero_iff.mp
    apply Subtype.ext
    exact h
  · intro h
    have hz := (gradientSpace period κ m).orthogonalProjectionOnto_eq_zero_iff.mpr h
    exact congrArg Subtype.val hz

/-- The Sobolev heat flow evolves the divergence constraint by the same genuine L² heat semigroup. -/
theorem gradientEvaluation_heat {q : ℕ} (κ : ℝ) (m : Vector3) (v : ℝ≥0) (u : SobolevSpace period q)
  :
    gradientEvaluation period q κ m (heatOperator period q v u) =
      cylinderHeat period v (gradientEvaluation period q κ m u) := by
  rw [gradientEvaluation_apply, heatOperator_value, gradientProjection_cylinderHeat,
    gradientEvaluation_apply]

/-- The derivative-gaining heat operator preserves vanishing lifted divergence. -/
theorem heatGain_preserves_gradient_zero {q : ℕ} (κ : ℝ) (m : Vector3)
    (v : ℝ≥0) (hv : 0 < v) (u : SobolevSpace period q)
    (hu : gradientEvaluation period q κ m u = 0) :
    gradientEvaluation period (q + 1) κ m (heatGain period q v hv u) = 0 := by
  rw [gradientEvaluation_apply, heatGain_value, gradientProjection_cylinderHeat]
  change cylinderHeat period v (gradientEvaluation period q κ m u) = 0
  rw [hu, map_zero]

/-- The actual viscosity-scaled heat kernel preserves zero lifted divergence at every real time. -/
theorem heatKernel_preserves_gradient_zero {q : ℕ} (κ : ℝ) (m : Vector3) (ν : ℝ) (hν : 0 < ν)
    (r : ℝ) (u : SobolevSpace period q) (hu : gradientEvaluation period q κ m u = 0) :
    gradientEvaluation period (q + 1) κ m (heatKernel period q ν hν r u) = 0 := by
  by_cases hr : 0 < r
  · rw [heatKernel, dite_eq_left hr]
    exact heatGain_preserves_gradient_zero period κ m _ _ u hu
  · simp only [heatKernel, hr, dite_false, zero_apply, map_zero]

/-- The actual Bochner Volterra convolution of divergence-free forcing remains divergence-free. -/
theorem heatConvolution_preserves_gradient_zero {q : ℕ} (κ : ℝ) (m : Vector3)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Set.Icc (0 : ℝ) T, SobolevSpace period q))
    (hf : ∀ t, gradientEvaluation period q κ m (f t) = 0) (t : Set.Icc (0 : ℝ) T) :
    gradientEvaluation period (q + 1) κ m
      (convolution T hT (heatKernel period q ν hν) (parabolicKernelBound ν)
        (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT)
        (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
        (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f t) = 0 := by
  let L := gradientEvaluation period (q + 1) κ m
  change L (∫ r in Set.Ioc 0 T, causalIntegrand T hT (heatKernel period q ν hν) f t r) = 0
  rw [← L.integral_comp_comm (causalIntegrand_integrable T hT (heatKernel period q ν hν)
    (parabolicKernelBound ν) (heatKernel_joint_continuous period q ν hν)
    (parabolicKernelBound_integrable ν T hT) (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f t)]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun r => by
    by_cases hr : r ≤ t.val
    · simp only [causalIntegrand, Set.indicator, Set.mem_Iic, hr, ite_true]
      exact heatKernel_preserves_gradient_zero period κ m ν hν r _ (hf _)
    · simp only [causalIntegrand, Set.indicator, Set.mem_Iic, hr, ite_false, map_zero,
      Pi.zero_apply]

/-- Every actual heat mild solution with projected forcing preserves the initial lifted divergence constraint. -/
theorem mild_solution_preserves_gradient_zero {q : ℕ} (κ : ℝ) (m : Vector3)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T) (u₀ : SobolevSpace period (q + 1))
    (hu₀ : gradientEvaluation period (q + 1) κ m u₀ = 0)
    (F : Set.Icc (0 : ℝ) T → SobolevSpace period (q + 1) → SobolevSpace period q)
    (hF : Continuous (fun p : Set.Icc (0 : ℝ) T × SobolevSpace period (q + 1) => F p.1 p.2))
    (hFzero : ∀ t u, gradientEvaluation period q κ m (F t u) = 0)
    (u : C(Set.Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Set.Icc (0 : ℝ) T,
      u t = heatOperator period (q + 1) (2 * ν * t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (F (Set.projIcc 0 T hT (t.val - r)) (u (Set.projIcc 0 T hT (t.val - r))))) :
    ∀ t, gradientEvaluation period (q + 1) κ m (u t) = 0 := by
  intro t
  let f := pathNonlinearity T F hF u
  have hconv := heatConvolution_preserves_gradient_zero period κ m ν hν T hT f (fun s => hFzero s
    (u s)) t
  have hci := convolution_eq_interval T hT (heatKernel period q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f t
  rw [hci] at hconv
  rw [hsol t, map_add, gradientEvaluation_heat, hu₀, map_zero, zero_add]
  exact hconv

end EulerDivergenceFreeHeat
