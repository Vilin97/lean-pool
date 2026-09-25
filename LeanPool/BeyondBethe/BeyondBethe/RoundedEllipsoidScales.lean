/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.RoundedEllipsoid
public import LeanPool.BeyondBethe.BeyondBethe.DyadicMagnitudePrecision
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.Tactic

/-! # Rounded Ellipsoid Scales -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Quantitative bounded-bit ellipsoid scales

The exact determinant defines the least precision needed in the semantic
rounding proof.  We also prove a determinant-free lower bound by clearing
entry denominators.  The final bit-model implementation must use an a-priori
schedule dominating the semantic precision: Mathlib's specification of
`Matrix.det` is not the algorithm used by the optimizer.
-/

/-- A positive rational bound for every absolute matrix entry. -/
def rationalMatrixAbsBound {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) : ℚ :=
  1 + ∑ i, ∑ j, abs (A i j)

theorem rationalMatrixAbsBound_pos {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) : 0 < rationalMatrixAbsBound A := by
  rw [rationalMatrixAbsBound]
  have hsum : 0 ≤ ∑ i, ∑ j, abs (A i j) :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  linarith

theorem abs_entry_lt_rationalMatrixAbsBound {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (i j : Fin d) :
    abs (A i j) < rationalMatrixAbsBound A := by
  rw [rationalMatrixAbsBound]
  have hrow : abs (A i j) ≤ ∑ k, abs (A i k) :=
    Finset.single_le_sum (fun k _ ↦ abs_nonneg (A i k)) (Finset.mem_univ j)
  have hall : (∑ k, abs (A i k)) ≤ ∑ l, ∑ k, abs (A l k) :=
    Finset.single_le_sum
      (fun l _ ↦ Finset.sum_nonneg fun k _ ↦ abs_nonneg (A l k))
      (Finset.mem_univ i)
  linarith

/-- Inflation per rounded update.  Its logarithmic size is polynomial in the
dimension, while its determinant cost is much smaller than the exact
central-cut contraction. -/
def roundedEllipsoidInflation (d : ℕ) : ℚ :=
  1 / (1024 * d ^ 4)

theorem roundedEllipsoidInflation_pos {d : ℕ} (hd : 0 < d) :
    0 < roundedEllipsoidInflation d := by
  rw [roundedEllipsoidInflation]
  positivity

theorem roundedEllipsoidInflation_nonneg (d : ℕ) :
    0 ≤ roundedEllipsoidInflation d := by
  by_cases hd : d = 0
  · simp [roundedEllipsoidInflation, hd]
  · exact (roundedEllipsoidInflation_pos (Nat.pos_of_ne_zero hd)).le

/-- Coefficient multiplying the mesh in the determinant perturbation bound. -/
def roundedDeterminantCoefficient (d : ℕ) (M : ℚ) : ℚ :=
  d.factorial * d * (2 * M) ^ d

/-- Coefficient multiplying the mesh in the adjugate correction bound. -/
def roundedInverseCoefficient (d : ℕ) (M : ℚ) : ℚ :=
  d * (d.factorial * (2 * M) ^ d) * (d + 1)

theorem roundedDeterminantCoefficient_pos {d : ℕ} (hd : 0 < d)
    {M : ℚ} (hM : 0 < M) :
    0 < roundedDeterminantCoefficient d M := by
  rw [roundedDeterminantCoefficient]
  positivity

theorem roundedInverseCoefficient_pos {d : ℕ} (hd : 0 < d)
    {M : ℚ} (hM : 0 < M) :
    0 < roundedInverseCoefficient d M := by
  rw [roundedInverseCoefficient]
  positivity

/-- The allowed mesh for rounding an exact one-step state. -/
def roundedEllipsoidMeshTarget {d : ℕ}
    (U : RationalEllipsoidState d) : ℚ :=
  let M := rationalMatrixAbsBound U.basis
  let Δ := abs (Matrix.det U.basis)
  min
    (Δ / (128 * d ^ 3 * roundedDeterminantCoefficient d M))
    (roundedEllipsoidInflation d * Δ /
      (2 * d * roundedInverseCoefficient d M))

/-- A common denominator dominating both adaptive rounding constraints. -/
def roundedEllipsoidCoarseDenominator (d : ℕ) (M : ℚ) : ℚ :=
  2048 * d ^ 6 * (d + 1) * d.factorial * (2 * M) ^ d

theorem roundedEllipsoidCoarseDenominator_pos {d : ℕ} (hd : 0 < d)
    {M : ℚ} (hM : 0 < M) :
    0 < roundedEllipsoidCoarseDenominator d M := by
  rw [roundedEllipsoidCoarseDenominator]
  positivity

/-- A determinant lower bound computed without evaluating the determinant.
`Matrix.den` is the least common multiple of the entry denominators. -/
def rationalMatrixDeterminantLower {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) : ℚ :=
  1 / (A.den : ℚ) ^ d

theorem rationalMatrixDeterminantLower_pos {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) :
    0 < rationalMatrixDeterminantLower A := by
  rw [rationalMatrixDeterminantLower]
  have hdenNat : 0 < A.den := Nat.pos_of_ne_zero A.den_ne_zero
  have hden : (0 : ℚ) < A.den := by exact_mod_cast hdenNat
  exact div_pos (by norm_num) (pow_pos hden d)

/-- Clearing the common entry denominator turns the determinant into a
nonzero integer.  Hence a nonzero rational determinant has magnitude at least
the reciprocal `d`-th power of that denominator. -/
theorem rationalMatrixDeterminantLower_le_abs_det {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (hdet : Matrix.det A ≠ 0) :
    rationalMatrixDeterminantLower A ≤ abs (Matrix.det A) := by
  have hmatrix := A.inv_denom_smul_num
  have hdetEq := congrArg Matrix.det hmatrix
  rw [Matrix.det_smul, Fintype.card_fin, ← Int.cast_det] at hdetEq
  let z : ℤ := Matrix.det A.num
  have hnumdet : z ≠ 0 := by
    intro hz
    apply hdet
    rw [← hdetEq]
    change (A.den : ℚ)⁻¹ ^ d * (z : ℚ) = 0
    rw [hz]
    simp
  have hint : (1 : ℤ) ≤ abs z := Int.one_le_abs hnumdet
  have hintQ : (1 : ℚ) ≤ ((abs z : ℤ) : ℚ) := by
    exact_mod_cast hint
  rw [rationalMatrixDeterminantLower, ← hdetEq, abs_mul, abs_pow,
    abs_inv, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (A.den : ℚ)),
    ← Int.cast_abs]
  simpa only [one_div, inv_pow, mul_one, z] using
    mul_le_mul_of_nonneg_left hintQ (by positivity :
      0 ≤ ((A.den : ℚ)⁻¹) ^ d)

/-- A positive mesh target computed only from entry arithmetic. -/
def determinantFreeRoundedMeshTarget {d : ℕ}
    (U : RationalEllipsoidState d) : ℚ :=
  rationalMatrixDeterminantLower U.basis /
    roundedEllipsoidCoarseDenominator d
      (rationalMatrixAbsBound U.basis)

theorem determinantFreeRoundedMeshTarget_pos {d : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) :
    0 < determinantFreeRoundedMeshTarget U := by
  rw [determinantFreeRoundedMeshTarget]
  exact div_pos (rationalMatrixDeterminantLower_pos U.basis)
    (roundedEllipsoidCoarseDenominator_pos hd
      (rationalMatrixAbsBound_pos U.basis))

/-- Both determinant and inverse-error constraints are implied by one
coarse lower bound. -/
theorem abs_det_div_coarseDenominator_le_meshTarget {d : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d) :
    abs (Matrix.det U.basis) /
        roundedEllipsoidCoarseDenominator d
          (rationalMatrixAbsBound U.basis) ≤
      roundedEllipsoidMeshTarget U := by
  let M := rationalMatrixAbsBound U.basis
  let Δ := abs (Matrix.det U.basis)
  let Q := roundedEllipsoidCoarseDenominator d M
  have hM : 0 < M := rationalMatrixAbsBound_pos U.basis
  have hQ : 0 < Q := roundedEllipsoidCoarseDenominator_pos hd hM
  have hΔ : 0 ≤ Δ := abs_nonneg _
  rw [roundedEllipsoidMeshTarget]
  apply le_min
  · have hsmallDen :
        128 * (d : ℚ) ^ 3 * roundedDeterminantCoefficient d M ≤ Q := by
      have hfactor : (1 : ℚ) ≤ 16 * d ^ 2 * (d + 1) := by
        have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
        have hd2 : (1 : ℚ) ≤ (d : ℚ) ^ 2 := one_le_pow₀ hdq
        nlinarith
      have hbase : 0 ≤
          128 * (d : ℚ) ^ 3 * roundedDeterminantCoefficient d M := by
        rw [roundedDeterminantCoefficient]
        positivity
      have heq : Q =
          (128 * (d : ℚ) ^ 3 * roundedDeterminantCoefficient d M) *
            (16 * d ^ 2 * (d + 1)) := by
        dsimp only [Q]
        rw [roundedEllipsoidCoarseDenominator,
          roundedDeterminantCoefficient]
        push_cast
        ring
      rw [heq]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hbase
    exact div_le_div_of_nonneg_left hΔ
      (by
        rw [roundedDeterminantCoefficient]
        positivity) hsmallDen
  · have heq :
        roundedEllipsoidInflation d * Δ /
            (2 * d * roundedInverseCoefficient d M) = Δ / Q := by
      dsimp only [Q]
      rw [roundedEllipsoidInflation, roundedInverseCoefficient,
        roundedEllipsoidCoarseDenominator]
      push_cast
      field_simp [Nat.ne_of_gt hd, hM.ne']
      <;> ring
    rw [heq]

theorem determinantFreeRoundedMeshTarget_le {d : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) (hdet : Matrix.det U.basis ≠ 0) :
    determinantFreeRoundedMeshTarget U ≤ roundedEllipsoidMeshTarget U := by
  exact (div_le_div_of_nonneg_right
      (rationalMatrixDeterminantLower_le_abs_det U.basis hdet)
      (roundedEllipsoidCoarseDenominator_pos hd
        (rationalMatrixAbsBound_pos U.basis)).le).trans
    (abs_det_div_coarseDenominator_le_meshTarget hd U)

/-- Mathematical lower bound on the number of fractional bits needed by one
rounded update.  This quantity is used only as a proof specification: the
eventual machine uses an a priori schedule proved to dominate it and does not
evaluate a determinant. -/
def roundedEllipsoidPrecision {d : ℕ}
    (U : RationalEllipsoidState d) : ℕ :=
  positiveDyadicPrecision (roundedEllipsoidMeshTarget U)

theorem dyadicMesh_eq_half_pow (p : ℕ) :
    dyadicMesh p = (1 / 2 : ℚ) ^ p := by
  simp [dyadicMesh, div_pow]

theorem roundedEllipsoidMeshTarget_pos {d : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) (hdet : Matrix.det U.basis ≠ 0) :
    0 < roundedEllipsoidMeshTarget U := by
  let M := rationalMatrixAbsBound U.basis
  have hM : 0 < M := rationalMatrixAbsBound_pos U.basis
  have hΔ : 0 < abs (Matrix.det U.basis) := abs_pos.mpr hdet
  rw [roundedEllipsoidMeshTarget]
  apply lt_min
  · exact div_pos hΔ (by
      have hc := roundedDeterminantCoefficient_pos hd hM
      positivity)
  · exact div_pos
      (mul_pos (roundedEllipsoidInflation_pos hd) hΔ)
      (by
        have hc := roundedInverseCoefficient_pos hd hM
        positivity)

theorem adaptive_dyadicMesh_lt_target {d : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) (hdet : Matrix.det U.basis ≠ 0) :
    dyadicMesh (roundedEllipsoidPrecision U) <
      roundedEllipsoidMeshTarget U := by
  rw [roundedEllipsoidPrecision]
  exact dyadicMesh_positiveDyadicPrecision_lt
    (roundedEllipsoidMeshTarget_pos hd U hdet)

theorem adaptive_dyadicMesh_lt_determinant_threshold {d : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d)
    (hdet : Matrix.det U.basis ≠ 0) :
    dyadicMesh (roundedEllipsoidPrecision U) <
      abs (Matrix.det U.basis) /
        (128 * d ^ 3 * roundedDeterminantCoefficient d
          (rationalMatrixAbsBound U.basis)) := by
  exact (adaptive_dyadicMesh_lt_target hd U hdet).trans_le
    (min_le_left _ _)

theorem adaptive_dyadicMesh_lt_inverse_threshold {d : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d)
    (hdet : Matrix.det U.basis ≠ 0) :
    dyadicMesh (roundedEllipsoidPrecision U) <
      roundedEllipsoidInflation d * abs (Matrix.det U.basis) /
        (2 * d * roundedInverseCoefficient d
          (rationalMatrixAbsBound U.basis)) := by
  exact (adaptive_dyadicMesh_lt_target hd U hdet).trans_le
    (min_le_right _ _)

theorem adaptive_determinant_rounding_loss_lt {d : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d)
    (hdet : Matrix.det U.basis ≠ 0) :
    roundedDeterminantCoefficient d (rationalMatrixAbsBound U.basis) *
        dyadicMesh (roundedEllipsoidPrecision U) <
      abs (Matrix.det U.basis) / (128 * d ^ 3) := by
  let C := roundedDeterminantCoefficient d
    (rationalMatrixAbsBound U.basis)
  have hC : 0 < C := roundedDeterminantCoefficient_pos hd
    (rationalMatrixAbsBound_pos U.basis)
  have hmesh := adaptive_dyadicMesh_lt_determinant_threshold hd U hdet
  have hmul := mul_lt_mul_of_pos_left hmesh hC
  change C * dyadicMesh (roundedEllipsoidPrecision U) < _
  calc
    C * dyadicMesh (roundedEllipsoidPrecision U) <
        C * (abs (Matrix.det U.basis) / (128 * d ^ 3 * C)) := hmul
    _ = abs (Matrix.det U.basis) / (128 * d ^ 3) := by
      field_simp [hC.ne']

theorem adaptive_inverse_rounding_loss_lt {d : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d)
    (hdet : Matrix.det U.basis ≠ 0) :
    roundedInverseCoefficient d (rationalMatrixAbsBound U.basis) *
        dyadicMesh (roundedEllipsoidPrecision U) <
      roundedEllipsoidInflation d * abs (Matrix.det U.basis) /
        (2 * d) := by
  let C := roundedInverseCoefficient d
    (rationalMatrixAbsBound U.basis)
  have hC : 0 < C := roundedInverseCoefficient_pos hd
    (rationalMatrixAbsBound_pos U.basis)
  have hmesh := adaptive_dyadicMesh_lt_inverse_threshold hd U hdet
  have hmul := mul_lt_mul_of_pos_left hmesh hC
  change C * dyadicMesh (roundedEllipsoidPrecision U) < _
  calc
    C * dyadicMesh (roundedEllipsoidPrecision U) <
        C * (roundedEllipsoidInflation d * abs (Matrix.det U.basis) /
          (2 * d * C)) := hmul
    _ = roundedEllipsoidInflation d * abs (Matrix.det U.basis) /
        (2 * d) := by
      field_simp [hC.ne', Nat.ne_of_gt hd]

end BeyondBethe
