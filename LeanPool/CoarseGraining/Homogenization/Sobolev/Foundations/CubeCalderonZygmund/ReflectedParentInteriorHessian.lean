/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionParentH1Graph
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.LimitHessianPointwise
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ScaledCubeGeometry

/-! # Reflected Parent Interior Hessian -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# Interior Hessian on an odd-reflected Dirichlet parent

This internal assembly fixes the geometric radii needed to construct a weak
Hessian on the half-scaled parent cube.  It retains the exact odd-reflected
parent value, gradient, scalar forcing, and weak Poisson equation supplied by
the Dirichlet reflection construction.
-/

namespace CubeDirichletWeakPoissonProblem

/-- Canonical cutoff from the half parent to the two-thirds parent. -/
noncomputable def reflectedParentHalfTwoThirdCutoff (d : ℕ) (m : ℤ) :
    QuantitativeCubeCutoff
      (originCube d (m + 1)) (1 / 2 : ℝ) (2 / 3 : ℝ) :=
  QuantitativeCubeCutoff.canonical
    (originCube d (m + 1)) (1 / 2 : ℝ) (2 / 3 : ℝ)
    (by norm_num) (by norm_num)

/-- Canonical outer cutoff leaving a strict margin outside the three-quarter
ambient cube. -/
noncomputable def reflectedParentSevenEighthFifteenSixteenthCutoff
    (d : ℕ) (m : ℤ) :
    QuantitativeCubeCutoff
      (originCube d (m + 1)) (7 / 8 : ℝ) (15 / 16 : ℝ) :=
  QuantitativeCubeCutoff.canonical
    (originCube d (m + 1)) (7 / 8 : ℝ) (15 / 16 : ℝ)
    (by norm_num) (by norm_num)

/-- Canonical fixed-radius interior Hessian package for an odd-reflected
Dirichlet solution.

The parent weak equation is returned verbatim.  The restricted `H¹` function
has the same global value and gradient representatives as the parent, and its
weak Hessian retains the explicit sum of smooth-test bounds produced by the
difference-quotient construction. -/
theorem exists_cubeDirichletOddReflectionParent_innerHalf_hasWeakHessianOn
    {d : ℕ} {m : ℤ}
    {u : H10Function (openCubeSet (originCube d m))} {F : Vec d → ℝ}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d m)
            u.toH1Function.toFun ∧
        uP.grad =
            cubeDirichletOddReflectionVectorField (originCube d m)
              (fun y => u.toH1Function.grad y) ∧
          WeakPoissonEquationOn (openCubeSet (originCube d (m + 1))) uP
              (cubeDirichletOddReflectionScalar (originCube d m) F) ∧
            ∃ uS : H1Function
                (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)),
              uS.toFun = uP.toFun ∧
                uS.grad = uP.grad ∧
                  ∃ H : HasWeakHessianOn
                      (scaledOpenCubeSet
                        (originCube d (m + 1)) (1 / 2 : ℝ)) uS,
                    H.hessianCoordL2NormSum ≤
                      ∑ i : Fin d, ∑ _j : Fin d,
                        @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                          d (originCube d (m + 1)) uP
                          (cubeDirichletOddReflectionScalar
                            (originCube d m) F)
                          i (1 / 2 : ℝ) (2 / 3 : ℝ) (7 / 8 : ℝ)
                          (15 / 16 : ℝ)
                          (reflectedParentSevenEighthFifteenSixteenthCutoff
                            d m) := by
  let Qp : TriadicCube d := originCube d (m + 1)
  let V : Set (Vec d) := scaledOpenCubeSet Qp (3 / 4 : ℝ)
  rcases
    hweak.exists_cubeDirichletOddReflectionParent_weakPoissonEquationOn_originCube
      hF with
    ⟨uP, huP_toFun, huP_grad, hweakParent⟩
  have hFopen : MemScalarL2 (openCubeSet (originCube d m)) F := by
    simpa [MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure
        (originCube d m) hF
  have hFparent :
      MemScalarL2 (openCubeSet Qp)
        (cubeDirichletOddReflectionScalar (originCube d m) F) := by
    simpa only [Qp] using
      memScalarL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar
        (m := m) hFopen
  have hV : IsOpenBoundedConvexDomain V := by
    exact isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Qp
      (by norm_num : 0 < (3 / 4 : ℝ))
  have hη_sub :
      tsupport
          (reflectedParentHalfTwoThirdCutoff d m : Vec d → ℝ) ⊆ V := by
    have hclosed :
        tsupport
            (reflectedParentHalfTwoThirdCutoff d m : Vec d → ℝ) ⊆
          scaledClosedCubeSet Qp (2 / 3 : ℝ) :=
      (reflectedParentHalfTwoThirdCutoff d m).tsupport_subset_scaledClosedCubeSet_of_support_subset
    exact hclosed.trans
      (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Qp
        (by norm_num : (2 / 3 : ℝ) < 3 / 4))
  have hinnerV : scaledClosedCubeSet Qp (1 / 2 : ℝ) ⊆ V :=
    scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Qp
      (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hVν : V ⊆ scaledClosedCubeSet Qp (3 / 4 : ℝ) :=
    scaledOpenCubeSet_subset_scaledClosedCubeSet Qp (3 / 4 : ℝ)
  rcases
    hweakParent.exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_strict_inner_margin
      hFparent hV (reflectedParentHalfTwoThirdCutoff d m) hη_sub hinnerV
      (reflectedParentSevenEighthFifteenSixteenthCutoff d m) hVν
      (by norm_num : 0 ≤ (3 / 4 : ℝ))
      (by norm_num : (3 / 4 : ℝ) < 7 / 8)
      (by norm_num : (7 / 8 : ℝ) < 1)
      (by norm_num : 0 ≤ (15 / 16 : ℝ))
      (by norm_num : (15 / 16 : ℝ) < 1)
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) with
    ⟨uS, huS_toFun, huS_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, hweakParent, uS, huS_toFun, huS_grad, H, ?_⟩
  simpa only [Qp, V] using hH

end CubeDirichletWeakPoissonProblem

end

end Homogenization
