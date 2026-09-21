/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Basic -/

open scoped BigOperators

namespace Homogenization

abbrev Vec (d : ℕ) := Fin d → ℝ

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

abbrev BlockVec (d : ℕ) := Vec d × Vec d

structure BlockMat (d : ℕ) where
  upperLeft : Mat d
  upperRight : Mat d
  lowerLeft : Mat d
  lowerRight : Mat d
deriving Inhabited

def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

theorem sq_vecDot_le_vecNormSq_mul_vecNormSq {d : ℕ} (x y : Vec d) :
    vecDot x y ^ 2 ≤ vecNormSq x * vecNormSq y := by
  simpa [vecDot, vecNormSq, pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := x) (g := y))

theorem vecNormSq_nonneg {d : ℕ} (x : Vec d) : 0 ≤ vecNormSq x := by
  unfold vecNormSq vecDot
  refine Finset.sum_nonneg ?_
  intro i hi
  nlinarith [sq_nonneg (x i)]

theorem sq_apply_le_vecNormSq {d : ℕ} (x : Vec d) (i : Fin d) :
    x i ^ (2 : ℕ) ≤ vecNormSq x := by
  let f : Fin d → ℝ := fun j => x j * x j
  have hsingle :
      f i ≤ ∑ j, f j := by
    exact Finset.single_le_sum
      (fun j _ => by
        dsimp [f]
        nlinarith [sq_nonneg (x j)])
      (Finset.mem_univ i)
  simpa [f, vecNormSq, vecDot, pow_two] using hsingle

/-- A real Young inequality packaged for Cauchy-Schwarz consequences. -/
theorem abs_le_add_halves_of_sq_le_mul {u A B : ℝ}
    (hu_sq : u ^ 2 ≤ A * B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |u| ≤ A / 2 + B / 2 := by
  have habsSq : |u| ^ 2 ≤ A * B := by
    simpa [sq_abs] using hu_sq
  have hsumSq : (2 * |u|) ^ 2 ≤ (A + B) ^ 2 := by
    have h0 : 0 ≤ (A - B) ^ 2 := sq_nonneg _
    nlinarith [habsSq, h0]
  have hsum_nonneg : 0 ≤ A + B := add_nonneg hA hB
  have habs2u : 2 * |u| ≤ A + B := le_of_sq_le_sq hsumSq hsum_nonneg
  linarith

/-- Young's inequality for the Euclidean dot product on project vectors. -/
theorem abs_vecDot_le_add_halves_vecNormSq {d : ℕ} (x y : Vec d) :
    |vecDot x y| ≤ vecNormSq x / 2 + vecNormSq y / 2 :=
  abs_le_add_halves_of_sq_le_mul
    (sq_vecDot_le_vecNormSq_mul_vecNormSq x y)
    (vecNormSq_nonneg x) (vecNormSq_nonneg y)

/-- Young's inequality for scalar-weighted Euclidean dot products. -/
theorem abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    {d : ℕ} (a b : ℝ) (x y : Vec d) :
    |a * b * vecDot x y| ≤
      a ^ 2 * vecNormSq x / 2 + b ^ 2 * vecNormSq y / 2 := by
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  have hfactor_nonneg : 0 ≤ a ^ 2 * b ^ 2 :=
    mul_nonneg (sq_nonneg a) (sq_nonneg b)
  have hmul :
      a ^ 2 * b ^ 2 * vecDot x y ^ 2 ≤
        a ^ 2 * b ^ 2 * (vecNormSq x * vecNormSq y) :=
    mul_le_mul_of_nonneg_left hcs hfactor_nonneg
  have hsq :
      (a * b * vecDot x y) ^ 2 ≤
        (a ^ 2 * vecNormSq x) * (b ^ 2 * vecNormSq y) := by
    nlinarith
  exact abs_le_add_halves_of_sq_le_mul hsq
    (mul_nonneg (sq_nonneg a) (vecNormSq_nonneg x))
    (mul_nonneg (sq_nonneg b) (vecNormSq_nonneg y))

theorem vecNormSq_eq_zero {d : ℕ} {x : Vec d} (h : vecNormSq x = 0) : x = 0 := by
  funext i
  let f : Fin d → ℝ := fun j => x j * x j
  have hi_le : x i * x i ≤ vecNormSq x := by
    unfold vecNormSq vecDot
    have hsingle : f i ≤ ∑ j, f j := by
      exact Finset.single_le_sum
        (fun j _ => by nlinarith [sq_nonneg (x j)])
        (Finset.mem_univ i)
    simpa [f] using hsingle
  have hi_zero : x i * x i = 0 := by
    nlinarith [hi_le, h]
  have hsq : x i ^ 2 = 0 := by
    simpa [pow_two] using hi_zero
  exact sq_eq_zero_iff.mp hsq

theorem vecNormSq_eq_zero_iff {d : ℕ} {x : Vec d} : vecNormSq x = 0 ↔ x = 0 := by
  constructor
  · exact vecNormSq_eq_zero
  · intro hx
    rw [hx]
    simp [vecNormSq, vecDot]

theorem vecNormSq_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  unfold vecNormSq vecDot
  calc
    ∑ i, (c • x) i * (c • x) i = ∑ i, c ^ 2 * (x i * x i) := by
      congr with i
      simp [pow_two]
      ring
    _ = c ^ 2 * ∑ i, x i * x i := by
      symm
      simpa using (Finset.mul_sum Finset.univ (fun i => x i * x i) (c ^ 2))
    _ = c ^ 2 * vecNormSq x := by
      rfl

theorem vecNormSq_add_le {d : ℕ} (x y : Vec d) :
    vecNormSq (x + y) ≤ 2 * (vecNormSq x + vecNormSq y) := by
  calc
    vecNormSq (x + y) = ∑ i, (x i + y i) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ i, 2 * (x i ^ 2 + y i ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      nlinarith [sq_nonneg (x i - y i)]
    _ = 2 * ∑ i, (x i ^ 2 + y i ^ 2) := by
      symm
      exact Finset.mul_sum Finset.univ (fun i => x i ^ 2 + y i ^ 2) 2
    _ = 2 * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (vecNormSq x + vecNormSq y) := by
      have hx : ∑ i, x i ^ 2 = ∑ i, x i * x i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [pow_two]
      have hy : ∑ i, y i ^ 2 = ∑ i, y i * y i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [pow_two]
      rw [hx, hy]
      rfl

/-- Four-term Cauchy estimate for the squared Euclidean norm. -/
theorem vecNormSq_four_add_le {d : ℕ} (w x y z : Vec d) :
    vecNormSq (w + x + y + z) ≤
      4 * (vecNormSq w + vecNormSq x + vecNormSq y + vecNormSq z) := by
  have hrewrite : w + x + y + z = (w + x) + (y + z) := by
    ext i
    simp
    ring
  calc
    vecNormSq (w + x + y + z)
        = vecNormSq ((w + x) + (y + z)) := by rw [hrewrite]
    _ ≤ 2 * (vecNormSq (w + x) + vecNormSq (y + z)) :=
        vecNormSq_add_le (w + x) (y + z)
    _ ≤ 4 * (vecNormSq w + vecNormSq x + vecNormSq y + vecNormSq z) := by
        nlinarith [vecNormSq_add_le w x, vecNormSq_add_le y z]

theorem vecNormSq_sub_le {d : ℕ} (x y : Vec d) :
    vecNormSq (x - y) ≤ 2 * (vecNormSq x + vecNormSq y) := by
  calc
    vecNormSq (x - y) = ∑ i, (x i - y i) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ i, 2 * (x i ^ 2 + y i ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      nlinarith [sq_nonneg (x i + y i)]
    _ = 2 * ∑ i, (x i ^ 2 + y i ^ 2) := by
      symm
      exact Finset.mul_sum Finset.univ (fun i => x i ^ 2 + y i ^ 2) 2
    _ = 2 * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (vecNormSq x + vecNormSq y) := by
      have hx : ∑ i, x i ^ 2 = ∑ i, x i * x i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [pow_two]
      have hy : ∑ i, y i ^ 2 = ∑ i, y i * y i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [pow_two]
      rw [hx, hy]
      rfl

def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j

def matTranspose {d : ℕ} (A : Mat d) : Mat d :=
  Matrix.transpose A

def blockVecDot {d : ℕ} (X Y : BlockVec d) : ℝ :=
  vecDot X.1 Y.1 + vecDot X.2 Y.2

def blockMatVecMul {d : ℕ} (A : BlockMat d) (X : BlockVec d) : BlockVec d :=
  ( matVecMul A.upperLeft X.1 + matVecMul A.upperRight X.2
  , matVecMul A.lowerLeft X.1 + matVecMul A.lowerRight X.2 )

@[simp] theorem blockMatVecMul_fst {d : ℕ} (A : BlockMat d) (p q : Vec d) :
    (blockMatVecMul A (p, q)).1 = matVecMul A.upperLeft p + matVecMul A.upperRight q :=
  rfl

@[simp] theorem blockMatVecMul_snd {d : ℕ} (A : BlockMat d) (p q : Vec d) :
    (blockMatVecMul A (p, q)).2 = matVecMul A.lowerLeft p + matVecMul A.lowerRight q :=
  rfl

noncomputable def symmPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j + A j i) / 2

noncomputable def skewPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j - A j i) / 2

theorem symmPart_eq_smul_add_transpose {d : ℕ} (A : Mat d) :
    symmPart A = (1 / 2 : ℝ) • (A + matTranspose A) := by
  ext i j
  simp [symmPart, matTranspose]
  ring

theorem skewPart_eq_smul_sub_transpose {d : ℕ} (A : Mat d) :
    skewPart A = (1 / 2 : ℝ) • (A - matTranspose A) := by
  ext i j
  simp [skewPart, matTranspose]
  ring

@[simp] theorem matTranspose_symmPart {d : ℕ} (A : Mat d) :
    matTranspose (symmPart A) = symmPart A := by
  ext i j
  simp [symmPart, matTranspose, add_comm]

@[simp] theorem matTranspose_skewPart {d : ℕ} (A : Mat d) :
    matTranspose (skewPart A) = -skewPart A := by
  ext i j
  simp [skewPart, matTranspose]
  ring

end Homogenization
