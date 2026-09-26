/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-! # Cauchy Schwarz -/

@[expose] public section

namespace Homogenization

/-!
# Quadratic stability, items B′1 and B′2

Pure-algebra half of Lemma 4.1 (`l.quadratic.stability`) of the high-moment
paper (Armstrong–Kuusi–Loher, to appear).  This file proves the two
pointwise (matrix-level) inequalities, phrased entirely through
`blockVecDot`/`blockMatVecMul` on `BlockVec d`/`BlockMat d`:

* **B′1** (`abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat`): Cauchy–
  Schwarz for a symmetric positive semidefinite block form, proved by the
  discriminant argument on `t ↦ (X + t•Y)·B(X + t•Y)` — no matrix square roots.
* **B′2** (`abs_blockVecDot_sub_le_of_blockMatLoewnerLE`): the mixed-metric
  inequality, from the triangle inequality, B′1 on each of the two forms, and
  the two Loewner hypotheses.

No `EuclideanSpace`.
-/

variable {d : ℕ}

/-! ## B′1 — Cauchy–Schwarz for a positive semidefinite block form -/

/-- The `t`-expansion of the quadratic form `(X + t•Y)·B(X + t•Y)` for a
symmetric block matrix `B`. -/
theorem blockVecDot_blockMatVecMul_add_smul_of_isSymmetricBlockMat
    {B : BlockMat d} (hB : IsSymmetricBlockMat B) (X Y : BlockVec d) (t : ℝ) :
    blockVecDot (X + t • Y) (blockMatVecMul B (X + t • Y)) =
      blockVecDot Y (blockMatVecMul B Y) * (t * t) +
        2 * blockVecDot X (blockMatVecMul B Y) * t +
        blockVecDot X (blockMatVecMul B X) := by
  have hcomm : blockVecDot Y (blockMatVecMul B X) = blockVecDot X (blockMatVecMul B Y) :=
    blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hB Y X
  simp only [blockMatVecMul_add, blockMatVecMul_smul, blockVecDot_add_left,
    blockVecDot_add_right, blockVecDot_smul_left, blockVecDot_smul_right, hcomm]
  ring

/-- **B′1.**  Cauchy–Schwarz for a symmetric positive semidefinite block form:
`|X·BY| ≤ √(X·BX) · √(Y·BY)`.  Proved by the discriminant of the nonnegative
quadratic `t ↦ (X + t•Y)·B(X + t•Y)`. -/
theorem abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat
    {B : BlockMat d} (hB : IsSymmetricBlockMat B)
    (hpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul B Z))
    (X Y : BlockVec d) :
    |blockVecDot X (blockMatVecMul B Y)| ≤
      Real.sqrt (blockVecDot X (blockMatVecMul B X)) *
        Real.sqrt (blockVecDot Y (blockMatVecMul B Y)) := by
  set a := blockVecDot X (blockMatVecMul B X) with ha
  set b := blockVecDot Y (blockMatVecMul B Y) with hb
  set c := blockVecDot X (blockMatVecMul B Y) with hc
  have ha0 : 0 ≤ a := hpsd X
  have hb0 : 0 ≤ b := hpsd Y
  -- discriminant of the nonnegative quadratic `b t² + 2c t + a`
  have hquad : ∀ t : ℝ, 0 ≤ b * (t * t) + 2 * c * t + a := by
    intro t
    have := hpsd (X + t • Y)
    rwa [blockVecDot_blockMatVecMul_add_smul_of_isSymmetricBlockMat hB X Y t] at this
  have hdiscrim : discrim b (2 * c) a ≤ 0 := discrim_le_zero hquad
  have hc2 : c ^ 2 ≤ a * b := by
    have : (2 * c) ^ 2 - 4 * b * a ≤ 0 := hdiscrim
    nlinarith [this]
  -- pass to square roots
  have hab : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha0 b
  calc
    |c| = Real.sqrt (c ^ 2) := (Real.sqrt_sq_eq_abs c).symm
    _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt hc2
    _ = Real.sqrt a * Real.sqrt b := hab

/-! ## B′2 — the mixed-metric inequality -/

/-- Unfold `BlockMatLoewnerLE B̃ (K • B)` to the plain quadratic-form comparison
`X·B̃X ≤ K·(X·BX)`. -/
theorem blockVecDot_le_smul_of_blockMatLoewnerLE {B C : BlockMat d} {K : ℝ}
    (h : BlockMatLoewnerLE B (K • C)) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul B X) ≤ K * blockVecDot X (blockMatVecMul C X) := by
  have hx := h X
  rw [blockMatVecMul_blockSMul, blockVecDot_smul_right] at hx
  linarith

/-- **B′2.**  The mixed-metric inequality.  For symmetric positive semidefinite
`B`, `B̃` with `1 ≤ K`, `B̃ ≤ K•B` and `B ≤ K•B̃` in the block Loewner order,
`|X·B̃Y − X·BY| ≤ 2·√K·√(X·BX)·√(Y·B̃Y)`. -/
theorem abs_blockVecDot_sub_le_of_blockMatLoewnerLE
    {B Bt : BlockMat d} {K : ℝ}
    (hBsymm : IsSymmetricBlockMat B) (hBtsymm : IsSymmetricBlockMat Bt)
    (hBpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul B Z))
    (hBtpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul Bt Z))
    (hK : 1 ≤ K)
    (hBt_le : BlockMatLoewnerLE Bt (K • B)) (hB_le : BlockMatLoewnerLE B (K • Bt))
    (X Y : BlockVec d) :
    |blockVecDot X (blockMatVecMul Bt Y) - blockVecDot X (blockMatVecMul B Y)| ≤
      2 * Real.sqrt K * Real.sqrt (blockVecDot X (blockMatVecMul B X)) *
        Real.sqrt (blockVecDot Y (blockMatVecMul Bt Y)) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  set aB := blockVecDot X (blockMatVecMul B X) with haB
  set aBt := blockVecDot X (blockMatVecMul Bt X) with haBt
  set bB := blockVecDot Y (blockMatVecMul B Y) with hbB
  set bBt := blockVecDot Y (blockMatVecMul Bt Y) with hbBt
  have haB0 : 0 ≤ aB := hBpsd X
  have haBt0 : 0 ≤ aBt := hBtpsd X
  have hbB0 : 0 ≤ bB := hBpsd Y
  have hbBt0 : 0 ≤ bBt := hBtpsd Y
  -- B′1 on each form
  have hcsB : |blockVecDot X (blockMatVecMul B Y)| ≤ Real.sqrt aB * Real.sqrt bB :=
    abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat hBsymm hBpsd X Y
  have hcsBt : |blockVecDot X (blockMatVecMul Bt Y)| ≤ Real.sqrt aBt * Real.sqrt bBt :=
    abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat hBtsymm hBtpsd X Y
  -- Loewner comparisons on the diagonal forms
  have hloBt : aBt ≤ K * aB := blockVecDot_le_smul_of_blockMatLoewnerLE hBt_le X
  have hloB : bB ≤ K * bBt := blockVecDot_le_smul_of_blockMatLoewnerLE hB_le Y
  -- √aBt ≤ √K·√aB, √bB ≤ √K·√bBt
  have hsqrtaBt : Real.sqrt aBt ≤ Real.sqrt K * Real.sqrt aB := by
    calc Real.sqrt aBt ≤ Real.sqrt (K * aB) := Real.sqrt_le_sqrt hloBt
      _ = Real.sqrt K * Real.sqrt aB := Real.sqrt_mul hK0 aB
  have hsqrtbB : Real.sqrt bB ≤ Real.sqrt K * Real.sqrt bBt := by
    calc Real.sqrt bB ≤ Real.sqrt (K * bBt) := Real.sqrt_le_sqrt hloB
      _ = Real.sqrt K * Real.sqrt bBt := Real.sqrt_mul hK0 bBt
  -- nonnegativity of the square roots
  have hsaB : 0 ≤ Real.sqrt aB := Real.sqrt_nonneg _
  have hsbBt : 0 ≤ Real.sqrt bBt := Real.sqrt_nonneg _
  have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  -- bound each term by √K·√aB·√bBt
  have htermBt : |blockVecDot X (blockMatVecMul Bt Y)| ≤
      Real.sqrt K * Real.sqrt aB * Real.sqrt bBt := by
    refine le_trans hcsBt ?_
    have := mul_le_mul_of_nonneg_right hsqrtaBt hsbBt
    nlinarith [this]
  have htermB : |blockVecDot X (blockMatVecMul B Y)| ≤
      Real.sqrt K * Real.sqrt aB * Real.sqrt bBt := by
    refine le_trans hcsB ?_
    have := mul_le_mul_of_nonneg_left hsqrtbB hsaB
    nlinarith [this]
  -- triangle inequality
  calc
    |blockVecDot X (blockMatVecMul Bt Y) - blockVecDot X (blockMatVecMul B Y)|
        ≤ |blockVecDot X (blockMatVecMul Bt Y)| + |blockVecDot X (blockMatVecMul B Y)| :=
          abs_sub _ _
    _ ≤ (Real.sqrt K * Real.sqrt aB * Real.sqrt bBt) +
          (Real.sqrt K * Real.sqrt aB * Real.sqrt bBt) := add_le_add htermBt htermB
    _ = 2 * Real.sqrt K * Real.sqrt aB * Real.sqrt bBt := by ring

end Homogenization
