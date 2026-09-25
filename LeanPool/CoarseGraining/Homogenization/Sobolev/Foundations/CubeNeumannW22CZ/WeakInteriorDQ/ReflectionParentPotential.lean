/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Hodge
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentL2
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionWeakEquation

/-! # Reflection Parent Potential -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {m : ℤ} {F : Vec d → ℝ}

/-- Hodge-style reduction of the remaining parent-cube reflection gluing task:
it is enough to prove that the reflected Neumann gradient is orthogonal to all
solenoidal zero-normal fields on the centered parent cube. -/
theorem cubeFaceReflectionParent_reflectedGradient_isPotentialOn_originCube_of_orthogonal
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (horth :
      ∀ {g : Vec d → Vec d},
        MemVectorL2 (openCubeSet (originCube d (m + 1))) g →
        IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d (m + 1))) g →
          ∫ x in openCubeSet (originCube d (m + 1)),
            vecDot (g x)
              (cubeCoordinateFoldReflectedVectorField (originCube d m)
                (fun y => W.w.toH1Function.grad y) x)
            ∂MeasureTheory.volume = 0) :
    IsPotentialOn (openCubeSet (originCube d (m + 1)))
      (cubeCoordinateFoldReflectedVectorField (originCube d m)
        (fun y => W.w.toH1Function.grad y)) := by
  let : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet (originCube d (m + 1)))) :=
    (isOpenBoundedConvexDomain_openCubeSet
      (originCube d (m + 1))).isFiniteMeasure_restrict_volume
  have hGopen :
      MemVectorL2 (openCubeSet (originCube d m))
        (fun y => W.w.toH1Function.grad y) := by
    simpa [MemVectorL2, volumeMeasureOn] using
      W.w.toH1Function.grad_memVectorL2
  have hGparent :
      MemVectorL2 (openCubeSet (originCube d (m + 1)))
        (cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => W.w.toH1Function.grad y)) :=
    memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
      hGopen
  exact
    IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain
        (U := openCubeSet (originCube d (m + 1)))
        (isOpenBoundedConvexDomain_openCubeSet (originCube d (m + 1))))
      hGparent horth

/-- Once the parent reflected vector field is known to be a potential, choose
an `H¹` potential and put the parent reflected equation into the
`WeakPoissonEquationOn` interface. -/
theorem exists_cubeFaceReflectionParent_weakPoissonEquationOn_originCube_of_isPotentialOn
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hpot :
      IsPotentialOn (openCubeSet (originCube d (m + 1)))
        (cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => W.w.toH1Function.grad y)))
    (hmean : cubeAverage (originCube d m) F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.grad =
        cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => W.w.toH1Function.grad y) ∧
      WeakPoissonEquationOn (openCubeSet (originCube d (m + 1))) uP
        (cubeCoordinateFoldReflectedScalar (originCube d m) F) := by
  rcases hpot with ⟨uP, huP_grad⟩
  refine ⟨uP, huP_grad, ?_⟩
  exact
    W.cubeFaceReflectionParent_weakPoissonEquationOn_originCube_of_grad_eq
      uP huP_grad hmean hF

end MeanZeroNeumannPoissonSolution

end

end Homogenization
