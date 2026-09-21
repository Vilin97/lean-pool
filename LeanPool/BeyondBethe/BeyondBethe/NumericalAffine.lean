/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Transfer
import Mathlib.Tactic

/-! # Numerical Affine -/

open scoped BigOperators

namespace BeyondBethe

/-!
# Exact rational coordinates for the Birkhoff affine hull

The upper-left `n`-by-`n` block gives coordinates for matrices of order
`n+1`.  The last row and column are recovered by the sum constraints.  This
file makes the recovery map executable over the rationals and proves, without
any numerical tolerance, that its image has every row and column sum equal to
one.
-/

/-- Recover a matrix of order `n+1` from its upper-left `n`-by-`n` block.
The definition uses only finite sums and ring operations, so in particular it
maps rational coordinates to a rational matrix. -/
def birkhoffAffineMap {n : ℕ} {R : Type*} [CommRing R]
    (Y : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Fin.snoc
    (fun i ↦ Fin.snoc (Y i) (1 - ∑ j, Y i j))
    (Fin.snoc
      (fun j ↦ 1 - ∑ i, Y i j)
      ((∑ i, ∑ j, Y i j) - (n - 1)))

/-- Extract the upper-left affine coordinates from a square matrix of order
`n+1`. -/
def birkhoffAffineCoordinates {n : ℕ} {R : Type*}
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j ↦ X i.castSucc j.castSucc

@[simp] theorem birkhoffAffineMap_castSucc_castSucc
    {n : ℕ} {R : Type*} [CommRing R]
    (Y : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    birkhoffAffineMap Y i.castSucc j.castSucc = Y i j := by
  simp [birkhoffAffineMap]

@[simp] theorem birkhoffAffineMap_castSucc_last
    {n : ℕ} {R : Type*} [CommRing R]
    (Y : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    birkhoffAffineMap Y i.castSucc (Fin.last n) = 1 - ∑ j, Y i j := by
  simp [birkhoffAffineMap]

@[simp] theorem birkhoffAffineMap_last_castSucc
    {n : ℕ} {R : Type*} [CommRing R]
    (Y : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    birkhoffAffineMap Y (Fin.last n) j.castSucc = 1 - ∑ i, Y i j := by
  simp [birkhoffAffineMap]

@[simp] theorem birkhoffAffineMap_last_last
    {n : ℕ} {R : Type*} [CommRing R]
    (Y : Matrix (Fin n) (Fin n) R) :
    birkhoffAffineMap Y (Fin.last n) (Fin.last n) =
      (∑ i, ∑ j, Y i j) - (n - 1) := by
  simp [birkhoffAffineMap]

/-- Every recovered row sums to one, identically over any commutative ring. -/
theorem birkhoffAffineMap_row_sum
    {n : ℕ} {R : Type*} [CommRing R]
    (Y : Matrix (Fin n) (Fin n) R) (i : Fin (n + 1)) :
    ∑ j, birkhoffAffineMap Y i j = 1 := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · rw [Fin.sum_univ_castSucc]
    simp only [birkhoffAffineMap_last_castSucc,
      birkhoffAffineMap_last_last]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Finset.sum_comm]
    ring
  · rw [Fin.sum_univ_castSucc]
    simp

/-- Every recovered column sums to one, identically over any commutative
ring. -/
theorem birkhoffAffineMap_col_sum
    {n : ℕ} {R : Type*} [CommRing R]
    (Y : Matrix (Fin n) (Fin n) R) (j : Fin (n + 1)) :
    ∑ i, birkhoffAffineMap Y i j = 1 := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · rw [Fin.sum_univ_castSucc]
    simp only [birkhoffAffineMap_castSucc_last,
      birkhoffAffineMap_last_last]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  · rw [Fin.sum_univ_castSucc]
    simp

/-- A matrix in the Birkhoff affine hull is recovered exactly from its
upper-left block. -/
theorem birkhoffAffineMap_coordinates_of_unit_sums
    {n : ℕ} {R : Type*} [CommRing R]
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hrow : ∀ i, ∑ j, X i j = 1)
    (hcol : ∀ j, ∑ i, X i j = 1) :
    birkhoffAffineMap (birkhoffAffineCoordinates X) = X := by
  ext i j
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp only [birkhoffAffineMap_last_last, birkhoffAffineCoordinates]
    have hlastCols : ∀ j : Fin n,
        X (Fin.last n) j.castSucc = 1 - ∑ i : Fin n, X i.castSucc j.castSucc := by
      intro j
      have h := hcol j.castSucc
      rw [Fin.sum_univ_castSucc] at h
      rw [← h]
      ring
    have hlastRow := hrow (Fin.last n)
    rw [Fin.sum_univ_castSucc] at hlastRow
    simp_rw [hlastCols] at hlastRow
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hlastRow
    rw [Finset.sum_comm] at hlastRow
    push_cast at hlastRow ⊢
    linear_combination -hlastRow
  · simp only [birkhoffAffineMap_last_castSucc, birkhoffAffineCoordinates]
    have h := hcol j.castSucc
    rw [Fin.sum_univ_castSucc] at h
    rw [← h]
    ring
  · simp only [birkhoffAffineMap_castSucc_last, birkhoffAffineCoordinates]
    have h := hrow i.castSucc
    rw [Fin.sum_univ_castSucc] at h
    rw [← h]
    ring
  · simp [birkhoffAffineCoordinates]

/-- The affine recovery map commutes with matrix segments. -/
theorem birkhoffAffineMap_affineCombination
    {n : ℕ} {t : ℝ} (Y Z : Matrix (Fin n) (Fin n) ℝ) :
    birkhoffAffineMap (fun i j ↦ (1 - t) * Y i j + t * Z i j) =
      fun i j ↦ (1 - t) * birkhoffAffineMap Y i j +
        t * birkhoffAffineMap Z i j := by
  ext i j
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp only [birkhoffAffineMap_last_last,
      Finset.sum_add_distrib]
    have hY :
        (∑ i, ∑ j, (1 - t) * Y i j) =
          (1 - t) * (∑ i, ∑ j, Y i j) := by
      calc
        (∑ i, ∑ j, (1 - t) * Y i j) =
            ∑ i, (1 - t) * ∑ j, Y i j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
        _ = (1 - t) * (∑ i, ∑ j, Y i j) := by
          rw [Finset.mul_sum]
    have hZ :
        (∑ i, ∑ j, t * Z i j) = t * (∑ i, ∑ j, Z i j) := by
      calc
        (∑ i, ∑ j, t * Z i j) = ∑ i, t * ∑ j, Z i j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
        _ = t * (∑ i, ∑ j, Z i j) := by
          rw [Finset.mul_sum]
    rw [hY, hZ]
    ring
  · simp only [birkhoffAffineMap_last_castSucc,
      Finset.sum_add_distrib]
    repeat' rw [← Finset.mul_sum]
    ring
  · simp only [birkhoffAffineMap_castSucc_last,
      Finset.sum_add_distrib]
    repeat' rw [← Finset.mul_sum]
    ring
  · simp

/-- The affine map lands in the Birkhoff affine hull exactly; only
nonnegativity remains to be checked by rational inequalities. -/
theorem birkhoffAffineMap_has_unit_sums
    {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℚ) :
    (∀ i, ∑ j, birkhoffAffineMap Y i j = 1) ∧
      (∀ j, ∑ i, birkhoffAffineMap Y i j = 1) := by
  exact ⟨birkhoffAffineMap_row_sum Y, birkhoffAffineMap_col_sum Y⟩

/-- Rational coordinates are feasible exactly when the recovered entries are
nonnegative. -/
theorem birkhoffAffineMap_doublyStochastic_iff
    {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℚ) :
    IsDoublyStochastic
        (fun i j ↦ ((birkhoffAffineMap Y i j : ℚ) : ℝ)) ↔
      ∀ i j, 0 ≤ birkhoffAffineMap Y i j := by
  constructor
  · intro h i j
    exact_mod_cast h.nonnegative i j
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      change 0 ≤ ((birkhoffAffineMap Y i j : ℚ) : ℝ)
      exact Rat.cast_nonneg.mpr (h i j)
    · intro i
      change ∑ j, ((birkhoffAffineMap Y i j : ℚ) : ℝ) = 1
      rw [← Rat.cast_sum]
      norm_num [birkhoffAffineMap_row_sum]
    · intro j
      change ∑ i, ((birkhoffAffineMap Y i j : ℚ) : ℝ) = 1
      rw [← Rat.cast_sum]
      norm_num [birkhoffAffineMap_col_sum]

/-- Coordinatewise lower bounds make the recovered rational matrix an
interior doubly stochastic point. -/
theorem birkhoffAffineMap_interior
    {n : ℕ} (hn : 0 < n) {Y : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ}
    (hδ : 0 < δ) (hfloor : ∀ i j, δ ≤ birkhoffAffineMap Y i j) :
    IsDoublyStochastic
        (fun i j ↦ ((birkhoffAffineMap Y i j : ℚ) : ℝ)) ∧
      ∀ i, IsInteriorProbabilityVector
        (fun j ↦ ((birkhoffAffineMap Y i j : ℚ) : ℝ)) := by
  have hds := (birkhoffAffineMap_doublyStochastic_iff Y).2
    (fun i j ↦ (hδ.le.trans (hfloor i j)))
  refine ⟨hds, fun i ↦
    ⟨⟨fun j ↦ hds.nonnegative i j, hds.row_sum i⟩,
      fun j ↦ ⟨?_, ?_⟩⟩⟩
  · change 0 < ((birkhoffAffineMap Y i j : ℚ) : ℝ)
    exact Rat.cast_pos.mpr (hδ.trans_le (hfloor i j))
  · exact hds.entry_lt_one_of_positive
      (fun a b ↦ by exact_mod_cast hδ.trans_le (hfloor a b))
      (by simp; omega) i j

/-- In a probability row with at least two coordinates, a common entry floor
also gives the same floor for every complementary coordinate. -/
theorem one_sub_entry_ge_of_common_floor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι) {X : Matrix ι ι ℝ} {δ : ℝ}
    (hX : IsDoublyStochastic X) (hfloor : ∀ i j, δ ≤ X i j)
    (i j : ι) : δ ≤ 1 - X i j := by
  obtain ⟨k, hkj⟩ := Fintype.exists_ne_of_one_lt_card hcard j
  have hkMem : k ∈ Finset.univ.erase j := by
    simp [hkj]
  have hrest : X i k ≤ ∑ l ∈ Finset.univ.erase j, X i l := by
    exact Finset.single_le_sum
      (fun l _ ↦ hX.nonnegative i l) hkMem
  have hsum : ∑ l ∈ Finset.univ.erase j, X i l = 1 - X i j := by
    have htotal := hX.row_sum i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at htotal
    linarith
  rw [← hsum]
  exact (hfloor i k).trans hrest

/-- The uniform point has fixedValue upper-left coordinates. -/
def uniformAffineCoordinates (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun _ _ ↦ 1 / (n + 1)

@[simp] theorem birkhoffAffineMap_uniformAffineCoordinates
    (n : ℕ) (i j : Fin (n + 1)) :
    birkhoffAffineMap (uniformAffineCoordinates n) i j = 1 / (n + 1) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [uniformAffineCoordinates]
    field_simp
    ring
  · simp [uniformAffineCoordinates]
    field_simp
    ring
  · simp [uniformAffineCoordinates]
    field_simp
    ring
  · simp [uniformAffineCoordinates]

/-- In particular, the rational floor body is nonempty whenever its floor is
at most the uniform entry. -/
theorem uniformAffineCoordinates_meets_floor
    (n : ℕ) {δ : ℚ} (hδ : δ ≤ 1 / (n + 1)) :
    ∀ i j, δ ≤ birkhoffAffineMap (uniformAffineCoordinates n) i j := by
  intro i j
  simpa using hδ

/-- Entrywise `ℓ1` distance in the upper-left affine coordinates. -/
def affineCoordinateL1Distance {n : ℕ}
    (Y Z : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, abs (Y i j - Z i j)

theorem affineCoordinateL1Distance_nonneg {n : ℕ}
    (Y Z : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ affineCoordinateL1Distance Y Z := by
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _

theorem affineCoordinate_abs_sub_le_l1 {n : ℕ}
    (Y Z : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    abs (Y i j - Z i j) ≤ affineCoordinateL1Distance Y Z := by
  apply (Finset.single_le_sum
    (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ abs_nonneg (Y a b - Z a b))
    (Finset.mem_univ i)).trans'
  exact Finset.single_le_sum
    (fun b _ ↦ abs_nonneg (Y i b - Z i b)) (Finset.mem_univ j)

theorem affineCoordinate_row_sum_abs_le_l1 {n : ℕ}
    (Y Z : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    abs (∑ j, (Y i j - Z i j)) ≤ affineCoordinateL1Distance Y Z := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.single_le_sum
    (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ abs_nonneg (Y a b - Z a b))
    (Finset.mem_univ i)

theorem affineCoordinate_col_sum_abs_le_l1 {n : ℕ}
    (Y Z : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    abs (∑ i, (Y i j - Z i j)) ≤ affineCoordinateL1Distance Y Z := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ i, abs (Y i j - Z i j) ≤
        ∑ i, ∑ k, abs (Y i k - Z i k) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.single_le_sum
        (fun k _ ↦ abs_nonneg (Y i k - Z i k)) (Finset.mem_univ j)
    _ = affineCoordinateL1Distance Y Z := rfl

theorem affineCoordinate_total_sum_abs_le_l1 {n : ℕ}
    (Y Z : Matrix (Fin n) (Fin n) ℝ) :
    abs (∑ i, ∑ j, (Y i j - Z i j)) ≤
      affineCoordinateL1Distance Y Z := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  exact Finset.abs_sum_le_sum_abs _ _

/-- The affine recovery map is entrywise 1-Lipschitz for the coordinate
`ℓ1` distance.  This single bound covers the upper-left block, recovered
row/column entries, and the corner entry. -/
theorem birkhoffAffineMap_abs_sub_le_l1 {n : ℕ}
    (Y Z : Matrix (Fin n) (Fin n) ℝ) (i j : Fin (n + 1)) :
    abs (birkhoffAffineMap Y i j - birkhoffAffineMap Z i j) ≤
      affineCoordinateL1Distance Y Z := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp only [birkhoffAffineMap_last_last]
    have heq :
        ((∑ i, ∑ j, Y i j) - (n - 1 : ℝ)) -
            ((∑ i, ∑ j, Z i j) - (n - 1 : ℝ)) =
          ∑ i, ∑ j, (Y i j - Z i j) := by
      simp_rw [Finset.sum_sub_distrib]
      ring
    rw [heq]
    exact affineCoordinate_total_sum_abs_le_l1 Y Z
  · simp only [birkhoffAffineMap_last_castSucc]
    have heq :
        (1 - ∑ i, Y i j) - (1 - ∑ i, Z i j) =
          -(∑ i, (Y i j - Z i j)) := by
      rw [Finset.sum_sub_distrib]
      ring
    rw [heq, abs_neg]
    exact affineCoordinate_col_sum_abs_le_l1 Y Z j
  · simp only [birkhoffAffineMap_castSucc_last]
    have heq :
        (1 - ∑ j, Y i j) - (1 - ∑ j, Z i j) =
          -(∑ j, (Y i j - Z i j)) := by
      rw [Finset.sum_sub_distrib]
      ring
    rw [heq, abs_neg]
    exact affineCoordinate_row_sum_abs_le_l1 Y Z i
  · simpa only [birkhoffAffineMap_castSucc_castSucc] using
      affineCoordinate_abs_sub_le_l1 Y Z i j

/-- A weak optimizer may perturb the coordinate vector, but an `ℓ1`
perturbation smaller than half the floor preserves an explicit positive
floor in the recovered matrix. -/
theorem birkhoffAffineMap_floor_of_l1_near
    {n : ℕ} {Y Z : Matrix (Fin n) (Fin n) ℝ} {δ σ : ℝ}
    (hY : ∀ i j, δ ≤ birkhoffAffineMap Y i j)
    (hnear : affineCoordinateL1Distance Y Z ≤ σ)
    (i j : Fin (n + 1)) :
    δ - σ ≤ birkhoffAffineMap Z i j := by
  have habs := (birkhoffAffineMap_abs_sub_le_l1 Y Z i j).trans hnear
  have hupper := (abs_le.mp habs).2
  linarith [hY i j]

end BeyondBethe
