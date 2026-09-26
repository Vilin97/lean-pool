/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionHessianRowFiniteP
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1

/-!
# Cellwise H¹ reflection of a weak Hessian row

On a reflection cell, folding the `i`th weak-gradient coordinate and
multiplying it by the mixed sign `S * s_i` produces an `H¹` function. Its
weak gradient is exactly the mixed-parity reflection `S * s_i * s_j` of the
`i`th Hessian row. This file makes only a cellwise assertion; it does not
assert that the global mixed reflection belongs to `H¹`.
-/

@[expose] public section

namespace Homogenization

noncomputable section

namespace HasWeakHessianOn

/-- The mixed-parity reflection of the `i`th weak-gradient coordinate on one
reflection cell. -/
noncomputable def cubeDirichletOddReflectionGradientCoordCellH1Function
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (choice : Fin d → Fin 3) (i : Fin d) :
    H1Function (openCubeSet (cubeFaceReflectionCellCube Q choice)) :=
  cubeDirichletOddReflectionMixedCellSign choice i •
    (H.gradCoordH1Function i).cubeFaceReflectionCellFold choice

/-- The scalar representative is exactly the cellwise mixed reflection of
the source weak-gradient coordinate. -/
@[simp] theorem cubeDirichletOddReflectionGradientCoordCellH1Function_toFun
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (choice : Fin d → Fin 3) (i : Fin d) :
    (H.cubeDirichletOddReflectionGradientCoordCellH1Function choice i).toFun =
      cubeDirichletOddReflectionGradientCoordCellScalar Q choice i
        (fun y ↦ u.grad y i) :=
  rfl

/-- The weak gradient is exactly the cellwise mixed reflection of the `i`th
Hessian row. -/
@[simp] theorem cubeDirichletOddReflectionGradientCoordCellH1Function_grad
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (choice : Fin d → Fin 3) (i : Fin d) :
    (H.cubeDirichletOddReflectionGradientCoordCellH1Function choice i).grad =
      cubeDirichletOddReflectionHessianRowCellVectorField Q choice i
        (fun y j ↦ H.hess i j y) :=
  rfl

/-- The exact cellwise scalar and Hessian-row representatives satisfy the
weak-gradient identity. -/
theorem cubeDirichletOddReflectionGradientCoordCell_hasWeakGradientOn
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (choice : Fin d → Fin 3) (i : Fin d) :
    HasWeakGradientOn
      (openCubeSet (cubeFaceReflectionCellCube Q choice))
      (cubeDirichletOddReflectionGradientCoordCellScalar Q choice i
        (fun y ↦ u.grad y i))
      (cubeDirichletOddReflectionHessianRowCellVectorField Q choice i
        (fun y j ↦ H.hess i j y)) :=
  (H.cubeDirichletOddReflectionGradientCoordCellH1Function choice i).hasWeakGradient

/-- The cellwise reflected Hessian row is a potential field. -/
theorem cubeDirichletOddReflectionHessianRowCellVectorField_isPotentialOn
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (choice : Fin d → Fin 3) (i : Fin d) :
    IsPotentialOn (openCubeSet (cubeFaceReflectionCellCube Q choice))
      (cubeDirichletOddReflectionHessianRowCellVectorField Q choice i
        (fun y j ↦ H.hess i j y)) :=
  (H.cubeDirichletOddReflectionGradientCoordCellH1Function choice i).isPotentialOn

/-- On its reflection cell, the constructed scalar agrees pointwise with the
global mixed scalar representative. -/
theorem cubeDirichletOddReflectionGradientCoordCellH1Function_eq_global_of_mem
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (choice : Fin d → Fin 3) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    H.cubeDirichletOddReflectionGradientCoordCellH1Function choice i x =
      cubeDirichletOddReflectionGradientCoordScalar Q i
        (fun y ↦ u.grad y i) x := by
  change
    cubeDirichletOddReflectionGradientCoordCellScalar Q choice i
        (fun y ↦ u.grad y i) x =
      cubeDirichletOddReflectionGradientCoordScalar Q i
        (fun y ↦ u.grad y i) x
  exact
    (cubeDirichletOddReflectionGradientCoordScalar_eq_cell_of_mem
      Q choice i (fun y ↦ u.grad y i) hx).symm

/-- On its reflection cell, the constructed weak gradient agrees pointwise
with the global mixed Hessian-row representative. -/
theorem cubeDirichletOddReflectionGradientCoordCellH1Function_grad_eq_global_of_mem
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (choice : Fin d → Fin 3) (i : Fin d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    (H.cubeDirichletOddReflectionGradientCoordCellH1Function choice i).grad x =
      cubeDirichletOddReflectionHessianRowVectorField Q i
        (fun y j ↦ H.hess i j y) x := by
  change
    cubeDirichletOddReflectionHessianRowCellVectorField Q choice i
        (fun y j ↦ H.hess i j y) x =
      cubeDirichletOddReflectionHessianRowVectorField Q i
        (fun y j ↦ H.hess i j y) x
  exact
    (cubeDirichletOddReflectionHessianRowVectorField_eq_cell_of_mem
      Q choice i (fun y j ↦ H.hess i j y) hx).symm

/-- The global mixed scalar and Hessian-row representatives satisfy the weak
gradient identity when both are restricted to one reflection cell. -/
theorem cubeDirichletOddReflectionGradientCoord_hasWeakGradientOn_cell
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (choice : Fin d → Fin 3) (i : Fin d) :
    HasWeakGradientOn
      (openCubeSet (cubeFaceReflectionCellCube Q choice))
      (cubeDirichletOddReflectionGradientCoordScalar Q i
        (fun y ↦ u.grad y i))
      (cubeDirichletOddReflectionHessianRowVectorField Q i
        (fun y j ↦ H.hess i j y)) := by
  intro j φ hφ hφ_supp hφ_sub
  let cell : Set (Vec d) :=
    openCubeSet (cubeFaceReflectionCellCube Q choice)
  let v := H.cubeDirichletOddReflectionGradientCoordCellH1Function choice i
  have hweak := v.hasWeakGradient j φ hφ hφ_supp hφ_sub
  calc
    ∫ x in cell,
        cubeDirichletOddReflectionGradientCoordScalar Q i
            (fun y ↦ u.grad y i) x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume =
      ∫ x in cell, v x * (fderiv ℝ φ x) (basisVec j)
          ∂MeasureTheory.volume := by
        refine MeasureTheory.setIntegral_congr_fun
          (measurableSet_openCubeSet
            (cubeFaceReflectionCellCube Q choice)) ?_
        intro x hx
        change
          cubeDirichletOddReflectionGradientCoordScalar Q i
                (fun y ↦ u.grad y i) x *
              (fderiv ℝ φ x) (basisVec j) =
            v x * (fderiv ℝ φ x) (basisVec j)
        apply congrArg (fun z : ℝ ↦ z * (fderiv ℝ φ x) (basisVec j))
        symm
        simpa only [v] using
          H.cubeDirichletOddReflectionGradientCoordCellH1Function_eq_global_of_mem
            choice i hx
    _ = -∫ x in cell, v.grad x j * φ x ∂MeasureTheory.volume := hweak
    _ = -∫ x in cell,
        cubeDirichletOddReflectionHessianRowVectorField Q i
            (fun y k ↦ H.hess i k y) x j * φ x
          ∂MeasureTheory.volume := by
        apply congrArg Neg.neg
        refine MeasureTheory.setIntegral_congr_fun
          (measurableSet_openCubeSet
            (cubeFaceReflectionCellCube Q choice)) ?_
        intro x hx
        change
          v.grad x j * φ x =
            cubeDirichletOddReflectionHessianRowVectorField Q i
                (fun y k ↦ H.hess i k y) x j * φ x
        apply congrArg (fun z : ℝ ↦ z * φ x)
        have hrow :=
          H.cubeDirichletOddReflectionGradientCoordCellH1Function_grad_eq_global_of_mem
            choice i hx
        simpa only [v] using congrArg (fun z : Vec d ↦ z j) hrow

/-- The global mixed Hessian-row representative is potential on each
reflection cell. -/
theorem cubeDirichletOddReflectionHessianRowVectorField_isPotentialOn_cell
    {d : ℕ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (choice : Fin d → Fin 3) (i : Fin d) :
    IsPotentialOn (openCubeSet (cubeFaceReflectionCellCube Q choice))
      (cubeDirichletOddReflectionHessianRowVectorField Q i
        (fun y j ↦ H.hess i j y)) := by
  refine IsPotentialOn.congr_ae ?_
    (H.cubeDirichletOddReflectionHessianRowCellVectorField_isPotentialOn
      choice i)
  filter_upwards
    [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet
        (cubeFaceReflectionCellCube Q choice))]
    with x hx
  exact
    (cubeDirichletOddReflectionHessianRowVectorField_eq_cell_of_mem
      Q choice i (fun y j ↦ H.hess i j y) hx).symm

end HasWeakHessianOn

end

end Homogenization
