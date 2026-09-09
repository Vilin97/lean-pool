/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ClassicalDivergence
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerRepresentative

@[expose] public section

/-! The four-dimensional transport velocity associated with a lifted
solenoidal field has zero ordinary trace on the real covering space. -/

noncomputable section

namespace EulerLiftedTransportTrace

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerSmoothLimit EulerClassicalDivergence
open scoped ContDiff

def transportLinear (κ : ℝ) (m : Vector3) : Vector3 →L[ℝ] LiftTangent :=
  (κ • ContinuousLinearMap.id ℝ Vector3).prod (toDual ℝ Vector3 m)

@[simp] theorem transportLinear_apply (κ : ℝ) (m v : Vector3) :
    transportLinear κ m v = transportDirection κ m v := rfl

@[simp] theorem transportLinear_single (κ : ℝ) (m : Vector3) (i : Fin 3) :
    transportLinear κ m (EuclideanSpace.single i 1) = coordinateDirection κ m i := by
  apply Prod.ext
  · rfl
  · simp [transportLinear,coordinateDirection,EuclideanSpace.inner_single_right]

theorem trace_transportLinear (κ : ℝ) (m : Vector3) (L : LiftTangent →L[ℝ] Vector3) :
    LinearMap.trace ℝ LiftTangent ((transportLinear κ m).comp L).toLinearMap =
      ∑ i : Fin 3, (L (coordinateDirection κ m i)) i := by
  change LinearMap.trace ℝ LiftTangent ((transportLinear κ m).toLinearMap ∘ₗ L.toLinearMap) = _
  rw [LinearMap.trace_comp_comm']
  change LinearMap.trace ℝ Vector3 (L.comp (transportLinear κ m)).toLinearMap = _
  rw [← coordinateTrace_eq_linearTrace]
  simp only [coordinateTrace,sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,transportLinear_single]
  rfl

variable (P κ : ℝ) (m : Vector3) (g : LiftDomain P → Vector3)

def coverVelocity (z : LiftTangent) : LiftTangent :=
  transportDirection κ m (g (coveringMap P z))

theorem coverVelocity_trace
    (hg : ∀ q, ContDiff ℝ ∞ (localFieldLift P g q)) (z : LiftTangent) :
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (coverVelocity P κ m g) z).toLinearMap =
      ∑ i : Fin 3, (fieldDerivative P (coordinateDirection κ m i) g (coveringMap P z)) i := by
  have he : g ∘ coveringMap P = localFieldLift P g 0 := by
    funext w
    simp [localFieldLift,coveringMap]
  have hdg : Differentiable ℝ (g ∘ coveringMap P) := by
    rw [he]
    exact (hg 0).differentiable (by simp)
  have hd := (transportLinear κ m).hasFDerivAt.comp z (hdg z).hasFDerivAt
  change HasFDerivAt (coverVelocity P κ m g) ((transportLinear κ m).comp (fderiv ℝ (g ∘ coveringMap
    P) z)) z at hd
  rw [hd.fderiv,trace_transportLinear,he]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fieldDerivative,fderiv_localFieldLift_cover]

variable [Fact (0 < P)]

theorem coverVelocity_trace_zero (u : LiftL2 P)
    (hu : u ∈ divergenceFreeSpace P κ m)
    (hrep : (u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] g)
    (hg : ∀ q, ContDiff ℝ ∞ (localFieldLift P g q)) (z : LiftTangent) :
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (coverVelocity P κ m g) z).toLinearMap = 0 := by
  rw [coverVelocity_trace P κ m g hg]
  exact divergenceFree_classical_divergence_zero P κ m u hu g hrep hg _

end EulerLiftedTransportTrace
