/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionGeometry

/-! # Reflection Weak Equation -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {m : ℤ} {F : Vec d → ℝ}

/-- The centered all-face reflection weak equation may be read on the next
larger centered cube at the level of set integrals. This avoids the false
shortcut of claiming an `H¹` parent-domain object before proving the weak
gradient gluing across the internal faces. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnParent_originCube
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage (originCube d m) F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d (m + 1)),
        cubeCoordinateFoldReflectedScalar (originCube d m) F x * φ x
          ∂MeasureTheory.volume := by
  rw [
    setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
      (m := m)
      (f := fun x =>
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x)),
    setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
      (m := m)
      (f := fun x =>
        cubeCoordinateFoldReflectedScalar (originCube d m) F x * φ x)]
  exact
    W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnBlock_of_compactSupport_of_memLp_normalizedCubeMeasure
      hφ hφs hmean hF

/-- If the reflected vector field has already been realized as the weak
gradient of an `H¹` function on the centered parent cube, the parent integral
identity becomes the standard `WeakPoissonEquationOn` interface. This theorem
isolates the remaining gluing task to constructing that `H1Function`. -/
theorem cubeFaceReflectionParent_weakPoissonEquationOn_originCube_of_grad_eq
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (huP_grad :
      uP.grad =
        cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => W.w.toH1Function.grad y))
    (hmean : cubeAverage (originCube d m) F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    WeakPoissonEquationOn (openCubeSet (originCube d (m + 1))) uP
      (cubeCoordinateFoldReflectedScalar (originCube d m) F) := by
  intro φ hφ hφs _hφ_sub
  rw [huP_grad]
  exact
    W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnParent_originCube
      hφ hφs hmean hF

end MeanZeroNeumannPoissonSolution

end

end Homogenization
