/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentH1Graph

/-! # Reflection Parent H1 -/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# Parent-cube `H¹` reflection handoff

The all-face coordinate-fold reflection is recovered as an honest parent-cube
`H1Function` by proving that its scalar/vector representatives lie in the
closed weak-gradient graph on the parent cube.
-/

/-- The all-face coordinate-fold reflection on centered cubes is an honest
`H¹` function on the centered parent cube. -/
theorem exists_cubeFaceReflectionParentH1Function_originCube
    {d : ℕ} {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
        cubeCoordinateFoldReflectedScalar (originCube d m) u.toFun ∧
      uP.grad =
        cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => u.grad y) := by
  have huOpen : MemScalarL2 (openCubeSet (originCube d m)) u.toFun := by
    simpa [MemScalarL2, volumeMeasureOn] using u.memL2
  have hGOpen : MemVectorL2 (openCubeSet (originCube d m))
      (fun y => u.grad y) := by
    simpa [MemVectorL2, volumeMeasureOn] using u.grad_memVectorL2
  have hscalar :
      MemScalarL2 (openCubeSet (originCube d (m + 1)))
        (cubeCoordinateFoldReflectedScalar (originCube d m) u.toFun) :=
    memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
      (m := m) huOpen
  have hvector :
      MemVectorL2 (openCubeSet (originCube d (m + 1)))
        (cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => u.grad y)) :=
    memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
      (m := m) hGOpen
  have hgraph :
      (toScalarL2 hscalar, toHilbertVectorL2OfVecField hvector) ∈
        h1GraphClosedSubmodule (U := openCubeSet (originCube d (m + 1))) :=
    mem_h1GraphClosedSubmodule_cubeCoordinateFoldReflection_originCube
      (m := m) u hscalar hvector
  exact
    exists_h1Function_of_toScalarL2_toHilbertVectorL2OfVecField_mem_h1GraphClosedSubmodule
      (U := openCubeSet (originCube d (m + 1)))
      hscalar hvector hgraph

/-- The gradient-only form consumed by the folded-solenoidal Hodge reduction. -/
theorem exists_cubeFaceReflectionParentH1Function_grad_originCube
    {d : ℕ} {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.grad =
        cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => u.grad y) := by
  rcases exists_cubeFaceReflectionParentH1Function_originCube (m := m) u with
    ⟨uP, _huP_toFun, huP_grad⟩
  exact ⟨uP, huP_grad⟩

/-- The exact reflected-test constructor required by
`ReflectionParentOrthogonality`. -/
theorem cubeFaceReflectionParent_reflected_h1_tests_originCube
    {d : ℕ} {m : ℤ} :
    ∀ φ : H1Function (openCubeSet (originCube d m)),
      ∃ ψ : H1Function (openCubeSet (originCube d (m + 1))),
        ψ.grad =
          cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y => φ.grad y) := by
  intro φ
  exact exists_cubeFaceReflectionParentH1Function_grad_originCube (m := m) φ

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {m : ℤ} {F : Vec d → ℝ}

/-- Parent reflected weak equation obtained from the isolated `H¹` reflection
gluing input and the already-proved folded-Hodge bookkeeping. -/
theorem exists_cubeFaceReflectionParent_weakPoissonEquationOn_originCube
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
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
  exact
    W.exists_cubeFaceReflectionParent_weakPoissonEquationOn_originCube_of_parent_reflected_h1_tests
      (cubeFaceReflectionParent_reflected_h1_tests_originCube (d := d) (m := m))
      hmean hF

end MeanZeroNeumannPoissonSolution

end

end Homogenization
