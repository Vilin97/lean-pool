/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaPair
import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveSpatialRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialMultiplier

/-! Spatial smoothness of the source vector potential, derived from its literal integral. -/

@[expose] public section


noncomputable section

namespace EulerPacketPiola

open EulerSmoothLimit EulerPacketCrossProduct EulerPacketAngularPotential
  EulerAngleMeanZeroPrimitive EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerMeanBoundary Set MeasureTheory InnerProductSpace
open scoped ContDiff

/-- Curl linear, bundling `toFun`, `map_add`, `map_smul`. -/
def curlLinear : (Space →L[ℝ] Space) →ₗ[ℝ] Space where
  toFun := curlMatrix
  map_add' := curlMatrix_add
  map_smul' := curlMatrix_smul

/-- Curl operator, given by `curlLinear.toContinuousLinearMap`. -/
def curlOperator : (Space →L[ℝ] Space) →L[ℝ] Space := curlLinear.toContinuousLinearMap

@[simp] theorem curlOperator_apply (A : Space →L[ℝ] Space) : curlOperator A = curlMatrix A := rfl

theorem coveringPotential_contDiff (P : ℝ) (hP : 0 ≤ P)
    (m : Space → Space) (A : LiftTangent → Space)
    (hm : ContDiff ℝ ∞ m) (hnz : ∀ y, m y ≠ 0) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (coveringPotential P m A) := by
  exact primitive_joint_contDiff P hP
    (fun z : LiftTangent => potentialMultiplier (m z.1) (A z))
    (((potentialMultiplier_contDiff m hm hnz).comp contDiff_fst).clm_apply hA)

/-- The curl is the actual first spatial derivative of the constructed potential. -/
theorem coveringSlowCurl_contDiff (P : ℝ) (hP : 0 ≤ P)
    (m : Space → Space) (A : LiftTangent → Space)
    (G : Space → Space →L[ℝ] Space)
    (hm : ContDiff ℝ ∞ m) (hnz : ∀ y, m y ≠ 0) (hA : ContDiff ℝ ∞ A)
    (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun z : LiftTangent => coveringSlowCurl (G z.1) (coveringPotential P m A) z) := by
  have hQ := coveringPotential_contDiff P hP m A hm hnz hA
  exact curlOperator.contDiff.comp
    ((contDiff_infty_iff_fderiv.mp hQ).2.clm_comp
      (contDiff_const.clm_comp (hG.comp contDiff_fst)))

/-- The Piola identity now needs regularity only for the input fields, not for Q. -/
theorem smooth_coveringPotential_pair_piola (P κ : ℝ) (hP : 0 ≤ P)
    (m₀ : Space) (Ξ : Space → Space) (A : LiftTangent → Space)
    (hΞ : ContDiff ℝ 2 Ξ) (F : Space → Space ≃L[ℝ] Space)
    (hNormal : ContDiff ℝ ∞ (fun y => (F y).symm.toContinuousLinearMap.adjoint m₀))
    (hm : ∀ y, (F y).symm.toContinuousLinearMap.adjoint m₀ ≠ 0)
    (hA : ContDiff ℝ ∞ A) (z : LiftTangent)
    (hF : fderiv ℝ Ξ z.1 = (F z.1).toContinuousLinearMap)
    (hdet : (operatorMatrix (F z.1).toContinuousLinearMap).det = 1)
    (htan : ⟪(F z.1).symm.toContinuousLinearMap.adjoint m₀, A z⟫_ℝ = 0) :
    (F z.1).symm (A z+κ • coveringSlowCurl (F z.1).symm.toContinuousLinearMap
      (coveringPotential P (fun y => (F y).symm.toContinuousLinearMap.adjoint m₀) A) z) =
      coveringCurl κ m₀ (coveringPullbackCovector Ξ
        (coveringPotential P (fun y => (F y).symm.toContinuousLinearMap.adjoint m₀) A)) z := by
  exact coveringPotential_pair_piola P κ m₀ Ξ A hΞ F z hF hdet (hm z.1) htan
    (hA.continuous.comp (continuous_const.prodMk continuous_id))
    ((coveringPotential_contDiff P hP _ A hNormal hm hA).differentiable (by simp) z)

end EulerPacketPiola
