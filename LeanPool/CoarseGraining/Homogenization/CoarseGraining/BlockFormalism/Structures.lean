/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.PDE.Harmonic
public import LeanPool.CoarseGraining.Homogenization.Probability.Scalarization
public import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Structures -/

@[expose] public section

namespace Homogenization

/-!
# Block formalism -- structures and private matrix helpers

BlockState structure, constVecField, blockMatrixOfCoeff /
blockCoeffField definitions, plus symmPart / skewPart / inverse / conjugation
helpers used throughout.
-/

structure BlockState (d : ℕ) where
  potential : Vec d → Vec d
  flux : Vec d → Vec d

@[ext] theorem BlockState.ext {d : ℕ} {X Y : BlockState d}
    (hpot : X.potential = Y.potential) (hflux : X.flux = Y.flux) : X = Y := by
  cases X
  cases Y
  cases hpot
  cases hflux
  rfl

instance {d : ℕ} : Add (BlockState d) where
  add X Y :=
    { potential := X.potential + Y.potential
      flux := X.flux + Y.flux }

instance {d : ℕ} : SMul ℝ (BlockState d) where
  smul c X :=
    { potential := c • X.potential
      flux := c • X.flux }

def BlockState.eval {d : ℕ} (X : BlockState d) (x : Vec d) : BlockVec d :=
  (X.potential x, X.flux x)

@[simp] theorem BlockState.eval_add {d : ℕ} (X Y : BlockState d) (x : Vec d) :
    (X + Y).eval x = X.eval x + Y.eval x := by
  rfl

@[simp] theorem BlockState.eval_smul {d : ℕ} (c : ℝ) (X : BlockState d) (x : Vec d) :
    (c • X).eval x = c • X.eval x := by
  rfl

def BlockState.mapMatrix {d : ℕ} (R : Mat d) (X : BlockState d) : BlockState d :=
  { potential := fun x => matVecMul R (X.potential x)
    flux := fun x => matVecMul R (X.flux x) }

@[simp] theorem BlockState.eval_mapMatrix {d : ℕ} (R : Mat d) (X : BlockState d) (x : Vec d) :
    (X.mapMatrix R).eval x = (matVecMul R (X.potential x), matVecMul R (X.flux x)) := by
  rfl

def BlockState.flipFlux {d : ℕ} (X : BlockState d) : BlockState d :=
  { potential := X.potential
    flux := fun x => -X.flux x }

@[simp] theorem BlockState.eval_flipFlux {d : ℕ} (X : BlockState d) (x : Vec d) :
    X.flipFlux.eval x = (X.potential x, -X.flux x) := by
  rfl

def constVecField {d : ℕ} (p : Vec d) : Vec d → Vec d :=
  fun _ => p

noncomputable def blockMatrixOfCoeff {d : ℕ} (A : Mat d) : BlockMat d :=
  let s := symmPart A
  let k := skewPart A
  let sInv := s⁻¹
  { upperLeft := s + (matTranspose k) * sInv * k
    upperRight := -((matTranspose k) * sInv)
    lowerLeft := -(sInv * k)
    lowerRight := sInv }

noncomputable def blockCoeffField {d : ℕ} (a : CoeffField d) : Vec d → BlockMat d :=
  fun x => blockMatrixOfCoeff (a x)

def blockVecConj {d : ℕ} (R : Mat d) (X : BlockVec d) : BlockVec d :=
  (matVecMul R X.1, matVecMul R X.2)

def blockMatConj {d : ℕ} (R : Mat d) (B : BlockMat d) : BlockMat d :=
  { upperLeft := R * B.upperLeft * R
    upperRight := R * B.upperRight * R
    lowerLeft := R * B.lowerLeft * R
    lowerRight := R * B.lowerRight * R }

theorem symmPart_matTranspose {d : ℕ} (A : Mat d) :
    symmPart (matTranspose A) = symmPart A := by
  ext i j
  simp [symmPart, matTranspose, add_comm]

theorem skewPart_matTranspose {d : ℕ} (A : Mat d) :
    skewPart (matTranspose A) = -skewPart A := by
  ext i j
  simp [skewPart, matTranspose]
  ring

theorem matTranspose_mul_mul_of_transpose_eq_self {d : ℕ} {R A : Mat d}
    (hR : matTranspose R = R) :
    matTranspose (R * A * R) = R * matTranspose A * R := by
  have hR' : Matrix.transpose R = R := by
    simpa [matTranspose] using hR
  change Matrix.transpose (R * A * R) = R * Matrix.transpose A * R
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hR']
  simp [Matrix.mul_assoc]

theorem symmPart_mul_mul_of_transpose_eq_self {d : ℕ} {R A : Mat d}
    (hR : matTranspose R = R) :
    symmPart (R * A * R) = R * symmPart A * R := by
  rw [symmPart_eq_smul_add_transpose, symmPart_eq_smul_add_transpose,
    matTranspose_mul_mul_of_transpose_eq_self hR]
  simp [Matrix.mul_add, add_mul, Matrix.mul_assoc]

theorem skewPart_mul_mul_of_transpose_eq_self {d : ℕ} {R A : Mat d}
    (hR : matTranspose R = R) :
    skewPart (R * A * R) = R * skewPart A * R := by
  rw [skewPart_eq_smul_sub_transpose, skewPart_eq_smul_sub_transpose,
    matTranspose_mul_mul_of_transpose_eq_self hR]
  simp [Matrix.mul_sub, sub_mul, Matrix.mul_assoc]

theorem isUnit_det_mul_mul_iff_of_mul_self_eq_one {d : ℕ} {R A : Mat d}
    (hR2 : R * R = 1) :
    IsUnit (R * A * R).det ↔ IsUnit A.det := by
  have hRdetSq : R.det * R.det = 1 := by
    simpa [Matrix.det_mul, Matrix.det_one, mul_assoc] using congrArg Matrix.det hR2
  have hRdetUnit : IsUnit R.det := IsUnit.of_mul_eq_one _ hRdetSq
  constructor
  · intro h
    have hmul : IsUnit (R.det * (R * A * R).det * R.det) := by
      simpa [mul_assoc] using hRdetUnit.mul (h.mul hRdetUnit)
    have hEq : R.det * (R * A * R).det * R.det = A.det := by
      calc
        R.det * (R * A * R).det * R.det
            = R.det * (R.det * A.det * R.det) * R.det := by
                simp [Matrix.det_mul, mul_assoc]
        _ = (R.det * R.det) * A.det * (R.det * R.det) := by ring
        _ = A.det := by simp [hRdetSq]
    rwa [hEq] at hmul
  · intro h
    have hmul : IsUnit (R.det * A.det * R.det) := by
      simpa [mul_assoc] using hRdetUnit.mul (h.mul hRdetUnit)
    simpa [Matrix.det_mul, mul_assoc] using hmul

theorem nonsing_inv_mul_mul_of_mul_self_eq_one {d : ℕ} {R A : Mat d}
    (hR2 : R * R = 1) :
    (R * A * R)⁻¹ = R * A⁻¹ * R := by
  by_cases hA : IsUnit A.det
  · apply Matrix.inv_eq_right_inv
    calc
      (R * A * R) * (R * A⁻¹ * R)
          = R * A * (R * R) * A⁻¹ * R := by
              simp [Matrix.mul_assoc]
      _ = R * A * A⁻¹ * R := by
              simp [hR2, Matrix.mul_assoc]
      _ = R * 1 * R := by
              simpa [Matrix.mul_assoc] using
                congrArg (fun M => R * M * R) (Matrix.mul_nonsing_inv A hA)
      _ = 1 := by rw [Matrix.mul_one, hR2]
  · have hconj : ¬ IsUnit (R * A * R).det := by
      intro hconj
      exact hA ((isUnit_det_mul_mul_iff_of_mul_self_eq_one (R := R) (A := A) hR2).1 hconj)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hconj, Matrix.nonsing_inv_apply_not_isUnit _ hA]
    simp

theorem mul_mul_mul_conj_of_mul_self_eq_one {d : ℕ} {R B C : Mat d}
    (hR2 : R * R = 1) :
    (R * B * R) * (R * C * R) = R * (B * C) * R := by
  calc
    (R * B * R) * (R * C * R) = R * B * (R * R) * C * R := by
      simp [Matrix.mul_assoc]
    _ = R * B * C * R := by
      simp [hR2, Matrix.mul_assoc]
    _ = R * (B * C) * R := by
      simp [Matrix.mul_assoc]

theorem matVecMul_mul_mul_cancel_of_mul_self_eq_one {d : ℕ} {R A : Mat d} {x : Vec d}
    (hR2 : R * R = 1) :
    matVecMul (R * A * R) (matVecMul R x) = matVecMul R (matVecMul A x) := by
  calc
    matVecMul (R * A * R) (matVecMul R x) = matVecMul ((R * A * R) * R) x := by
      rw [matVecMul_mul]
    _ = matVecMul (R * A) x := by
      simp [Matrix.mul_assoc, hR2]
    _ = matVecMul R (matVecMul A x) := by
      rw [matVecMul_mul]

theorem vecDot_matVecMul_conj_of_transpose_eq_self_of_mul_self_eq_one {d : ℕ}
    {R : Mat d} (hR : matTranspose R = R) (hR2 : R * R = 1) (x y : Vec d) :
    vecDot (matVecMul R x) (matVecMul R y) = vecDot x y := by
  calc
    vecDot (matVecMul R x) (matVecMul R y)
        = vecDot x (matVecMul (matTranspose R) (matVecMul R y)) := by
            rw [← vecDot_matVecMul_transpose x (matVecMul R y) R]
    _ = vecDot x (matVecMul (R * R) y) := by
            rw [hR, matVecMul_mul]
    _ = vecDot x y := by
            rw [hR2]
            unfold matVecMul vecDot
            simp [Matrix.one_apply]

@[simp] theorem blockMatrixOfCoeff_matTranspose_upperLeft {d : ℕ} (A : Mat d) :
    (blockMatrixOfCoeff (matTranspose A)).upperLeft = (blockMatrixOfCoeff A).upperLeft := by
  change
    symmPart (matTranspose A) +
        matTranspose (skewPart (matTranspose A)) * (symmPart (matTranspose A))⁻¹ *
          skewPart (matTranspose A) =
      symmPart A + matTranspose (skewPart A) * (symmPart A)⁻¹ * skewPart A
  rw [symmPart_matTranspose, skewPart_matTranspose]
  simp [Matrix.transpose_neg, matTranspose, Matrix.mul_assoc]

@[simp] theorem blockMatrixOfCoeff_matTranspose_upperRight {d : ℕ} (A : Mat d) :
    (blockMatrixOfCoeff (matTranspose A)).upperRight = -(blockMatrixOfCoeff A).upperRight := by
  change
    -((matTranspose (skewPart (matTranspose A))) * (symmPart (matTranspose A))⁻¹) =
      -(-((matTranspose (skewPart A)) * (symmPart A)⁻¹))
  rw [symmPart_matTranspose, skewPart_matTranspose]
  simp [Matrix.transpose_neg, matTranspose]

@[simp] theorem blockMatrixOfCoeff_matTranspose_lowerLeft {d : ℕ} (A : Mat d) :
    (blockMatrixOfCoeff (matTranspose A)).lowerLeft = -(blockMatrixOfCoeff A).lowerLeft := by
  change
    -((symmPart (matTranspose A))⁻¹ * skewPart (matTranspose A)) =
      -(-((symmPart A)⁻¹ * skewPart A))
  rw [symmPart_matTranspose, skewPart_matTranspose]
  simp

end Homogenization
