/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.Definitions

/-! # Odd Reflection -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-!
# Odd reflection data for cube Dirichlet `H²`

This file contains the pointwise and `H¹` one-cell vocabulary for the odd
reflection argument.  The analytic endpoint will assemble these cells across
the full reflection block and then reuse the interior weak-Hessian estimate.
-/

/-- The scalar sign used for Dirichlet odd reflection on one reflection cell.

Each coordinate outside the original strip contributes a factor `-1`; each
coordinate in the original strip contributes `1`. -/
def cubeDirichletOddReflectionCellSign {d : ℕ}
    (choice : Fin d → Fin 3) : ℝ :=
  ∏ i : Fin d, if choice i = 1 then (1 : ℝ) else -1

@[simp] theorem cubeDirichletOddReflectionCellSign_center {d : ℕ} :
    cubeDirichletOddReflectionCellSign
      (fun _ : Fin d => (1 : Fin 3)) = 1 := by
  simp [cubeDirichletOddReflectionCellSign]

@[simp] theorem cubeDirichletOddReflectionCellSign_mul_self {d : ℕ}
    (choice : Fin d → Fin 3) :
    cubeDirichletOddReflectionCellSign choice *
        cubeDirichletOddReflectionCellSign choice = 1 := by
  classical
  unfold cubeDirichletOddReflectionCellSign
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one ?_
  intro i _hi
  by_cases h : choice i = 1 <;> simp [h]

@[simp] theorem cubeDirichletOddReflectionCellSign_sq {d : ℕ}
    (choice : Fin d → Fin 3) :
    cubeDirichletOddReflectionCellSign choice ^ (2 : ℕ) = 1 := by
  rw [pow_two, cubeDirichletOddReflectionCellSign_mul_self]

theorem cubeDirichletOddReflectionCellSign_ne_zero {d : ℕ}
    (choice : Fin d → Fin 3) :
    cubeDirichletOddReflectionCellSign choice ≠ 0 := by
  intro hzero
  have hsq := cubeDirichletOddReflectionCellSign_mul_self choice
  rw [hzero] at hsq
  norm_num at hsq

/-- The global odd-reflection sign induced by the coordinate fold. -/
def cubeDirichletOddReflectionSign {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) : ℝ :=
  ∏ i : Fin d, cubeCoordinateFoldSign Q x i

@[simp] theorem cubeDirichletOddReflectionSign_mul_self {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) :
    cubeDirichletOddReflectionSign Q x *
        cubeDirichletOddReflectionSign Q x = 1 := by
  classical
  unfold cubeDirichletOddReflectionSign
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one ?_
  intro i _hi
  by_cases hLower : x i < cubeLowerFaceCoord Q i
  · simp [cubeCoordinateFoldSign, hLower]
  · by_cases hUpper : x i < cubeUpperFaceCoord Q i <;>
      simp [cubeCoordinateFoldSign, hLower, hUpper]

@[simp] theorem cubeDirichletOddReflectionSign_sq {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) :
    cubeDirichletOddReflectionSign Q x ^ (2 : ℕ) = 1 := by
  rw [pow_two, cubeDirichletOddReflectionSign_mul_self]

/-- On a reflection cell, the global odd sign is the cell sign. -/
theorem cubeDirichletOddReflectionSign_eq_cellSign_of_mem_cellCube
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    cubeDirichletOddReflectionSign Q x =
      cubeDirichletOddReflectionCellSign choice := by
  classical
  unfold cubeDirichletOddReflectionSign cubeDirichletOddReflectionCellSign
  refine Finset.prod_congr rfl ?_
  intro i _hi
  exact cubeCoordinateFoldSign_eq_cellFoldLinear_sign_of_mem_cellCube
    Q choice hx i

/-- Pointwise scalar odd reflection on one reflection cell. -/
def cubeDirichletOddReflectionCellScalar {d : ℕ} (Q : TriadicCube d)
    (choice : Fin d → Fin 3) (F : Vec d → ℝ) : Vec d → ℝ :=
  fun x =>
    cubeDirichletOddReflectionCellSign choice *
      F (cubeFaceReflectionCellFoldMap Q choice x)

@[simp] theorem cubeDirichletOddReflectionCellScalar_apply {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (F : Vec d → ℝ)
    (x : Vec d) :
    cubeDirichletOddReflectionCellScalar Q choice F x =
      cubeDirichletOddReflectionCellSign choice *
        F (cubeFaceReflectionCellFoldMap Q choice x) :=
  rfl

/-- Pointwise reflected gradient profile corresponding to one scalar odd cell. -/
def cubeDirichletOddReflectionCellVectorField {d : ℕ} (Q : TriadicCube d)
    (choice : Fin d → Fin 3) (G : Vec d → Vec d) : Vec d → Vec d :=
  fun x =>
    cubeDirichletOddReflectionCellSign choice •
      cubeFaceReflectionCellFoldLinear choice
        (G (cubeFaceReflectionCellFoldMap Q choice x))

@[simp] theorem cubeDirichletOddReflectionCellVectorField_apply {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) (G : Vec d → Vec d)
    (x : Vec d) :
    cubeDirichletOddReflectionCellVectorField Q choice G x =
      cubeDirichletOddReflectionCellSign choice •
        cubeFaceReflectionCellFoldLinear choice
          (G (cubeFaceReflectionCellFoldMap Q choice x)) :=
  rfl

/-- Global scalar odd reflection obtained from the coordinate fold. -/
def cubeDirichletOddReflectionScalar {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → ℝ) : Vec d → ℝ :=
  fun x =>
    cubeDirichletOddReflectionSign Q x *
      F (cubeCoordinateFold Q x)

@[simp] theorem cubeDirichletOddReflectionScalar_apply {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → ℝ) (x : Vec d) :
    cubeDirichletOddReflectionScalar Q F x =
      cubeDirichletOddReflectionSign Q x *
        F (cubeCoordinateFold Q x) :=
  rfl

/-- Global reflected gradient profile corresponding to the scalar odd
reflection. -/
def cubeDirichletOddReflectionVectorField {d : ℕ}
    (Q : TriadicCube d) (G : Vec d → Vec d) : Vec d → Vec d :=
  fun x =>
    cubeDirichletOddReflectionSign Q x •
      cubeCoordinateFoldReflectedVectorField Q G x

@[simp] theorem cubeDirichletOddReflectionVectorField_apply {d : ℕ}
    (Q : TriadicCube d) (G : Vec d → Vec d) (x : Vec d) :
    cubeDirichletOddReflectionVectorField Q G x =
      cubeDirichletOddReflectionSign Q x •
        cubeCoordinateFoldReflectedVectorField Q G x :=
  rfl

/-- The global odd scalar agrees with the affine one-cell scalar on a
reflection cell. -/
theorem cubeDirichletOddReflectionScalar_eq_cellScalar_of_mem_cellCube
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (F : Vec d → ℝ) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    cubeDirichletOddReflectionScalar Q F x =
      cubeDirichletOddReflectionCellScalar Q choice F x := by
  rw [cubeDirichletOddReflectionScalar,
    cubeDirichletOddReflectionCellScalar,
    cubeDirichletOddReflectionSign_eq_cellSign_of_mem_cellCube Q choice hx,
    cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube
      Q choice hx]

/-- The global odd vector profile agrees with the affine one-cell vector
profile on a reflection cell. -/
theorem cubeDirichletOddReflectionVectorField_eq_cellVectorField_of_mem_cellCube
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (G : Vec d → Vec d) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    cubeDirichletOddReflectionVectorField Q G x =
      cubeDirichletOddReflectionCellVectorField Q choice G x := by
  rw [cubeDirichletOddReflectionVectorField,
    cubeDirichletOddReflectionCellVectorField,
    cubeDirichletOddReflectionSign_eq_cellSign_of_mem_cellCube Q choice hx,
    cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
      Q choice G hx]

/-- On the original cube, the global odd-reflection sign is `1`. -/
theorem cubeDirichletOddReflectionSign_eq_one_of_mem_openCubeSet
    {d : ℕ} (Q : TriadicCube d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    cubeDirichletOddReflectionSign Q x = 1 := by
  classical
  unfold cubeDirichletOddReflectionSign
  refine Finset.prod_eq_one ?_
  intro i _hi
  exact cubeCoordinateFoldSign_eq_one_of_mem_openCubeSet Q hx i

/-- On the original cube, the odd reflected scalar agrees with the original
scalar. -/
theorem cubeDirichletOddReflectionScalar_eq_self_of_mem_openCubeSet
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → ℝ) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    cubeDirichletOddReflectionScalar Q F x = F x := by
  rw [cubeDirichletOddReflectionScalar,
    cubeDirichletOddReflectionSign_eq_one_of_mem_openCubeSet Q hx,
    cubeCoordinateFold_eq_self_of_mem_openCubeSet Q hx]
  simp

/-- On the original cube, the odd reflected vector field agrees with the
original vector field. -/
theorem cubeDirichletOddReflectionVectorField_eq_self_of_mem_openCubeSet
    {d : ℕ} (Q : TriadicCube d) (G : Vec d → Vec d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    cubeDirichletOddReflectionVectorField Q G x = G x := by
  rw [cubeDirichletOddReflectionVectorField,
    cubeDirichletOddReflectionSign_eq_one_of_mem_openCubeSet Q hx,
    cubeCoordinateFoldReflectedVectorField_eq_self_of_mem_openCubeSet Q G hx]
  simp

/-- Odd scalar reflection has the same square as the unsigned coordinate-fold
scalar reflection. -/
theorem cubeDirichletOddReflectionScalar_mul_self {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → ℝ) (x : Vec d) :
    cubeDirichletOddReflectionScalar Q F x *
        cubeDirichletOddReflectionScalar Q F x =
      cubeCoordinateFoldReflectedScalar Q F x *
        cubeCoordinateFoldReflectedScalar Q F x := by
  simp [cubeDirichletOddReflectionScalar, cubeCoordinateFoldReflectedScalar]
  ring_nf
  rw [cubeDirichletOddReflectionSign_sq]
  ring

/-- Odd vector reflection has the same self-pairing as the unsigned
coordinate-fold vector reflection. -/
theorem cubeDirichletOddReflectionVectorField_self_pairing {d : ℕ}
    (Q : TriadicCube d) (G : Vec d → Vec d) (x : Vec d) :
    vecDot (cubeDirichletOddReflectionVectorField Q G x)
        (cubeDirichletOddReflectionVectorField Q G x) =
      vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
        (cubeCoordinateFoldReflectedVectorField Q G x) := by
  simp [cubeDirichletOddReflectionVectorField, vecDot_smul_left,
    vecDot_smul_right]
  rw [← mul_assoc, cubeDirichletOddReflectionSign_mul_self]
  ring

namespace H1Function

/-- Odd scalar fold of an `H¹` function from the original cube to one
reflection cell. -/
noncomputable def cubeDirichletOddReflectionCellFold {d : ℕ}
    {Q : TriadicCube d} (u : H1Function (openCubeSet Q))
    (choice : Fin d → Fin 3) :
    H1Function (openCubeSet (cubeFaceReflectionCellCube Q choice)) :=
  cubeDirichletOddReflectionCellSign choice •
    u.cubeFaceReflectionCellFold choice

@[simp] theorem cubeDirichletOddReflectionCellFold_toFun {d : ℕ}
    {Q : TriadicCube d} (u : H1Function (openCubeSet Q))
    (choice : Fin d → Fin 3) (x : Vec d) :
    (u.cubeDirichletOddReflectionCellFold choice).toFun x =
      cubeDirichletOddReflectionCellSign choice *
        u.toFun (cubeFaceReflectionCellFoldMap Q choice x) :=
  rfl

@[simp] theorem cubeDirichletOddReflectionCellFold_grad {d : ℕ}
    {Q : TriadicCube d} (u : H1Function (openCubeSet Q))
    (choice : Fin d → Fin 3) (x : Vec d) :
    (u.cubeDirichletOddReflectionCellFold choice).grad x =
      cubeDirichletOddReflectionCellSign choice •
        cubeFaceReflectionCellFoldLinear choice
          (u.grad (cubeFaceReflectionCellFoldMap Q choice x)) :=
  rfl

theorem cubeDirichletOddReflectionCellFold_isPotentialOn {d : ℕ}
    {Q : TriadicCube d} (u : H1Function (openCubeSet Q))
    (choice : Fin d → Fin 3) :
    IsPotentialOn (openCubeSet (cubeFaceReflectionCellCube Q choice))
      (cubeDirichletOddReflectionCellVectorField Q choice (fun y => u.grad y)) :=
  (u.cubeDirichletOddReflectionCellFold choice).isPotentialOn

end H1Function

end

end Homogenization
