/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data
import LeanPool.TwoColoringOneRound.LowerBound.N1000000ZData
import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000Z
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000Z

open scoped BigOperators
open Matrix

open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000ZData

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Block := Fin 7

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def matGet (M : Array (Array Int)) (i j : Nat) : Int :=
  (M.getD i #[]).getD j 0

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def toMat3Scaled (den : Nat) (M : Array (Array Int)) : Matrix (Fin 3) (Fin 3) Q :=
  fun i j => (matGet M i.1 j.1 : Q) / (den : Q)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def toVec3Scaled (den : Nat) (v : Array Int) : Fin 3 → Q :=
  fun i => (v.getD i.1 0 : Q) / (den : Q)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def Z (r : Block) : Matrix (Fin 3) (Fin 3) Q :=
  toMat3Scaled D (ZBlocks.getD r.1 #[])

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def den (r : Block) : Nat :=
  ZldlDen.getD r.1 1

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def LNum (r : Block) : Array (Array Int) :=
  ZldlLNum.getD r.1 (#[#[], #[], #[]])

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def DNum (r : Block) : Array Int :=
  ZldlDNum.getD r.1 #[]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def L (r : Block) : Matrix (Fin 3) (Fin 3) Q :=
  toMat3Scaled (den r) (LNum r)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def Dvec (r : Block) : Fin 3 → Q :=
  toVec3Scaled (den r) (DNum r)

private def ZNum (r : Block) (i j : Fin 3) : Int :=
  matGet (ZBlocks.getD r.1 #[]) i.1 j.1

private def rhsInt (r : Block) (i j : Fin 3) : Int :=
  (Finset.univ : Finset (Fin 3)).sum fun k =>
    ((DNum r).getD k.1 0) * (matGet (LNum r) i.1 k.1) * (matGet (LNum r) j.1 k.1)

private def den3Int (r : Block) : Int :=
  (den r : Int) * (den r : Int) * (den r : Int)

private theorem cleared_entry_identity (r : Block) (i j : Fin 3) :
    (ZNum r i j) * den3Int r = (D : Int) * (rhsInt r i j) := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide

private theorem den_pos (r : Block) : 0 < den r := by
  fin_cases r <;> decide

private theorem denQ_ne_zero (r : Block) : (den r : Q) ≠ 0 := by
  exact_mod_cast (show den r ≠ 0 by exact Nat.ne_of_gt (den_pos r))

private theorem denQ3_ne_zero (r : Block) : ((den r : Q) * (den r : Q) * (den r : Q)) ≠ 0 := by
  have h : (den r : Q) ≠ 0 := denQ_ne_zero r
  simp [mul_assoc, h]

private lemma mul_diagonal_mul_transpose_apply (L : Matrix (Fin 3) (Fin 3) Q) (d : Fin 3 → Q)
    (i j : Fin 3) :
    (L * Matrix.diagonal d * Lᵀ) i j = ∑ k : Fin 3, L i k * d k * L j k := by
  classical
  -- Expand the matrix products; the diagonal collapses one summation.
  simp [Matrix.mul_apply, Matrix.diagonal, Matrix.transpose, mul_assoc]

private lemma LDL_entry (r : Block) (i j : Fin 3) :
    (((L r) * Matrix.diagonal (Dvec r) * (Matrix.transpose (L r))) i j) =
      ((rhsInt r i j : Q) / ((den r : Q) * (den r : Q) * (den r : Q))) := by
  classical
  have hsum :
      ((L r) * Matrix.diagonal (Dvec r) * (Matrix.transpose (L r))) i j =
        ∑ k : Fin 3, (L r i k) * (Dvec r k) * (L r j k) := by
    simpa [Matrix.mul_assoc] using
      (mul_diagonal_mul_transpose_apply (L := L r) (d := Dvec r) (i := i) (j := j))
  -- Unfold the scaled entries inside the finite sum and factor out the common `den⁻¹` powers.
  have hden : (den r : Q) ≠ 0 := denQ_ne_zero r
  let invDen : Q := (den r : Q)⁻¹
  have hdenProd : ((den r : Q) * (den r : Q) * (den r : Q))⁻¹ = invDen * invDen * invDen := by
    simp [invDen, mul_comm]
  -- Rewrite the LHS using the collapsed sum formula.
  rw [hsum]
  -- Rewrite each term as `numerator * invDen^3`, then factor `invDen^3` out of the sum.
  have hterm :
      (∑ k : Fin 3, (L r i k) * (Dvec r k) * (L r j k)) =
        (invDen * invDen * invDen) *
          ∑ k : Fin 3,
            ((DNum r).getD k.1 0 : Q) *
              ((matGet (LNum r) i.1 k.1 : Q) * (matGet (LNum r) j.1 k.1 : Q)) := by
    -- `simp` on the scaled definitions is now small because it only touches one term at a time.
    simp [L,
      Dvec,
      toMat3Scaled,
      toVec3Scaled,
      invDen,
      div_eq_mul_inv,
      mul_assoc,
      mul_comm,
      mul_left_comm,
      Finset.mul_sum]
  -- Replace the inner sum by `rhsInt` and rewrite `1/den^3` as `invDen^3`.
  have hsumNum :
      (∑ k : Fin 3,
          ((DNum r).getD k.1 0 : Q) *
            ((matGet (LNum r) i.1 k.1 : Q) * (matGet (LNum r) j.1 k.1 : Q)))
        = (rhsInt r i j : Q) := by
    -- This is definitional after unfolding `rhsInt`.
    simp [rhsInt, mul_assoc, mul_comm, mul_left_comm]
  -- Finish.
  calc
    (∑ k : Fin 3, (L r i k) * (Dvec r k) * (L r j k))
        = (invDen * invDen * invDen) *
            ∑ k : Fin 3,
              ((DNum r).getD k.1 0 : Q) *
                ((matGet (LNum r) i.1 k.1 : Q) * (matGet (LNum r) j.1 k.1 : Q)) := hterm
    _ = (invDen * invDen * invDen) * (rhsInt r i j : Q) := by
          -- Avoid cancellation (`simp` would turn this into a disjunction `... ∨ invDen = 0`).
          simpa using congrArg (fun t => (invDen * invDen * invDen) * t) hsumNum
    _ = (rhsInt r i j : Q) * (invDen * invDen * invDen) := by
          ac_rfl
    _ = (rhsInt r i j : Q) * ((den r : Q) * (den r : Q) * (den r : Q))⁻¹ := by
          simp [hdenProd]
    _ = (rhsInt r i j : Q) / ((den r : Q) * (den r : Q) * (den r : Q)) := by
          simp [div_eq_mul_inv]

theorem Z_eq_LDL (r : Block) :
    Z r = (L r) * Matrix.diagonal (Dvec r) * (Matrix.transpose (L r)) := by
  classical
  have hDpos : (D : Q) ≠ 0 := by
    exact_mod_cast (show (D : Nat) ≠ 0 by decide)
  have hdenpos : ((den r : Q) * (den r : Q) * (den r : Q)) ≠ 0 := denQ3_ne_zero r
  ext i j
  have hInt := cleared_entry_identity r i j
  have hQ :
      (ZNum r i j : Q) * ((den r : Q) * (den r : Q) * (den r : Q)) =
        (D : Q) * (rhsInt r i j : Q) := by
    -- `hInt` is an equality in `Int`; casting to `ℚ` preserves multiplication.
    -- We keep the association as `((den)*(den)*(den))` to match `denQ3_ne_zero`.
    exact_mod_cast hInt
  have hEntry :
      (ZNum r i j : Q) / (D : Q) =
        (rhsInt r i j : Q) / ((den r : Q) * (den r : Q) * (den r : Q)) := by
    -- Use cross-multiplication for fractions in a field.
    apply (div_eq_div_iff hDpos hdenpos).2
    -- Arrange both sides to match `hQ`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using hQ
  -- Compare the `Z` entry and the LDL entry via the explicit entry formulas.
  calc
    Z r i j
        = (ZNum r i j : Q) / (D : Q) := by
            simp [Z, toMat3Scaled, ZNum]
    _ = (rhsInt r i j : Q) / ((den r : Q) * (den r : Q) * (den r : Q)) := hEntry
    _ = ((L r) * Matrix.diagonal (Dvec r) * (Matrix.transpose (L r))) i j := by
            simpa using (LDL_entry (r := r) (i := i) (j := j)).symm

theorem Dvec_nonneg (r : Block) : ∀ i : Fin 3, 0 ≤ Dvec r i := by
  intro i
  have hnum : 0 ≤ (DNum r).getD i.1 0 := by
    fin_cases r <;> fin_cases i <;> decide
  have hden : 0 < (den r : Q) := by
    exact_mod_cast (den_pos r)
  -- Division by a positive scalar preserves nonnegativity.
  simpa [Dvec, toVec3Scaled, div_eq_mul_inv] using
    mul_nonneg (show (0 : Q) ≤ (DNum r).getD i.1 0 by exact_mod_cast hnum)
      (inv_nonneg.2 (le_of_lt hden))

theorem Z_posSemidef (r : Block) : (Z r).PosSemidef := by
  classical
  have hD : (Matrix.diagonal (Dvec r)).PosSemidef :=
    Matrix.PosSemidef.diagonal (n := Fin 3) (R := Q) (Dvec_nonneg (r := r))
  have hLDL : ((L r) * Matrix.diagonal (Dvec r) * (Matrix.transpose (L r))).PosSemidef := by
    -- congruence preserves PSD
    have :
        ((L r) * Matrix.diagonal (Dvec r) * (Matrix.conjTranspose (L r))).PosSemidef :=
      Matrix.PosSemidef.mul_mul_conjTranspose_same (A := Matrix.diagonal (Dvec r)) hD (B := L r)
    convert this using 1
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simpa [Z_eq_LDL r] using hLDL

theorem trace_mul_nonneg_of_Z_posSemidef {r : Block} {S : Matrix (Fin 3) (Fin 3) Q}
    (hS : S.PosSemidef) : 0 ≤ ((Z r) * S).trace := by
  classical
  -- Copy the N20 argument: reduce using the LDLᵀ decomposition and diagonal nonnegativity.
  have hZ : Z r = (L r) * Matrix.diagonal (Dvec r) * (Matrix.transpose (L r)) := Z_eq_LDL r
  have hM : ((Matrix.transpose (L r)) * S * (L r)).PosSemidef := by
    have :
        ((Matrix.conjTranspose (L r)) * S * (L r)).PosSemidef :=
      Matrix.PosSemidef.conjTranspose_mul_mul_same (A := S) hS (B := L r)
    convert this using 1
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  have hTrace :
      ((Z r) * S).trace =
        (Matrix.diagonal (Dvec r) * ((Matrix.transpose (L r)) * S * (L r))).trace := by
    calc
      ((Z r) * S).trace
          = ((L r) * Matrix.diagonal (Dvec r) * (Matrix.transpose (L r)) * S).trace := by
            simp [hZ, Matrix.mul_assoc]
      _ = ((Matrix.diagonal (Dvec r) * Matrix.transpose (L r) * S) * (L r)).trace := by
            simpa [Matrix.mul_assoc] using
              (Matrix.trace_mul_comm
                (A := L r)
                (B := Matrix.diagonal (Dvec r) * Matrix.transpose (L r) * S))
      _ = (Matrix.diagonal (Dvec r) * (Matrix.transpose (L r) * S * (L r))).trace := by
            simp [Matrix.mul_assoc]
  have hDiag :
      (Matrix.diagonal (Dvec r) * ((Matrix.transpose (L r)) * S * (L r))).trace =
        ∑ i : Fin 3, (Dvec r i) * (((Matrix.transpose (L r)) * S * (L r)) i i) := by
    classical
    simp [Matrix.trace, Matrix.diag]
  have hterm : ∀ i : Fin 3, 0 ≤ (Dvec r i) * (((Matrix.transpose (L r)) * S * (L r)) i i) := by
    intro i
    have hDi : 0 ≤ Dvec r i := Dvec_nonneg (r := r) i
    have hMii : 0 ≤ ((Matrix.transpose (L r)) * S * (L r)) i i := by
      simpa using (hM.diag_nonneg (i := i))
    exact mul_nonneg hDi hMii
  rw [hTrace, hDiag]
  exact Fintype.sum_nonneg hterm

end N1000000Z

end Distributed2Coloring.LowerBound
