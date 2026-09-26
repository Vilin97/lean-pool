/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.BlockMatrix
public import Mathlib.Analysis.Matrix.Order

/-! # Matrix Order Bridge -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped MatrixOrder

/-!
# Ambient matrix-order bridges

Conversion lemmas between the local quadratic-form order `MatLoewnerLE` used in
the homogenization development and mathlib's matrix order, together with the
basic inverse-antitonicity consequence for positive-definite real matrices.
-/

theorem matLoewnerLE_matrixOrder_of_posSemidef
    {d : ℕ} {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : MatLoewnerLE A B) :
    A ≤ B := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hB.isHermitian.sub hA.isHermitian) ?_
  intro x
  change 0 ≤ dotProduct x (Matrix.mulVec (B - A) x)
  rw [Matrix.sub_mulVec, dotProduct_sub]
  have hAB' :
      (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec A x) ≤
        (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec B x) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec_apply] using hAB x
  nlinarith

theorem matLoewnerLE_of_matrixOrder_of_posSemidef
    {d : ℕ} {A B : Mat d} (_hA : A.PosSemidef) (_hB : B.PosSemidef)
    (hAB : A ≤ B) :
    MatLoewnerLE A B := by
  have hBA : Matrix.PosSemidef (B - A) := (Matrix.le_iff).mp hAB
  intro x
  change (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec A x) ≤
      (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec B x)
  have hnonneg :
      0 ≤ dotProduct x (Matrix.mulVec (B - A) x) := hBA.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hnonneg
  nlinarith

theorem matLoewnerLE_inv_of_posDef
    {d : ℕ} {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : MatLoewnerLE A B) :
    MatLoewnerLE B⁻¹ A⁻¹ := by
  have hAB_order : A ≤ B :=
    matLoewnerLE_matrixOrder_of_posSemidef hA.posSemidef hB.posSemidef hAB
  have hBA_psd : (B - A).PosSemidef := (Matrix.le_iff).mp hAB_order
  let _ := hA.isUnit.invertible
  let _ := hB.isUnit.invertible
  have hBlock :
      (Matrix.fromBlocks B (1 : Mat d) (Matrix.conjTranspose (1 : Mat d)) A⁻¹).PosSemidef := by
    exact
      (Matrix.PosDef.fromBlocks₂₂ (A := B) (B := (1 : Mat d)) (D := A⁻¹) hA.inv).2 <|
        by simpa using hBA_psd
  have hInv_psd : (A⁻¹ - B⁻¹).PosSemidef := by
    simpa using
      (Matrix.PosDef.fromBlocks₁₁ (A := B) (B := (1 : Mat d)) (D := A⁻¹) hB).1 hBlock
  have hInv_order : B⁻¹ ≤ A⁻¹ := (Matrix.le_iff).2 hInv_psd
  exact matLoewnerLE_of_matrixOrder_of_posSemidef hB.inv.posSemidef hA.inv.posSemidef hInv_order

end
