/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import LeanPool.Stafford38.Stafford38.Geometry.PowerSeriesTangentLimit


/-!
# Splitting a rectangular power-series matrix from a selected minor

Let `B` be a matrix whose columns are indexed by `κ`.  An embedding
`rows : κ ↪ ι` selects a square minor of `B`.  If the determinant of that
minor is a unit, its nonsingular inverse, followed by the row-selector matrix,
is an explicit left inverse of `B`.

For matrices over `k[[X]]`, it is enough to assume that the determinant of the
selected minor has nonzero constant coefficient.  This file does not assert
that a suitable minor exists for a geometric tangent family.
-/

@[expose] public section

namespace Stafford38.GeometrySplitTangentMatrix

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

/-- The square submatrix obtained by retaining the explicitly selected rows. -/
def selectedMinor {ι κ : Type*} (B : Matrix ι κ R) (rows : κ ↪ ι) : Matrix κ κ R :=
  fun a b => B (rows a) b

/-- The matrix which restricts a column indexed by `ι` to the selected rows. -/
def rowSelector {ι κ : Type*} [DecidableEq ι] (rows : κ ↪ ι) : Matrix κ ι R :=
  fun a i => if rows a = i then 1 else 0

theorem rowSelector_mul
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι κ R) (rows : κ ↪ ι) :
    rowSelector (R := R) rows * B = selectedMinor B rows := by
  ext a b
  simp [Matrix.mul_apply, rowSelector, selectedMinor]

/--
The constructive left inverse supplied by an invertible selected minor.

The nonsingular inverse is the adjugate divided by the determinant in
Mathlib's matrix API; no inverse of the rectangular matrix is used.
-/
def selectedMinorLeftInverse
    {ι κ : Type*} [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ R) (rows : κ ↪ ι) : Matrix κ ι R :=
  (selectedMinor B rows)⁻¹ * rowSelector (R := R) rows

/-- A unit determinant of the selected square minor makes the construction a
left inverse of the original rectangular matrix. -/
theorem selectedMinorLeftInverse_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ R) (rows : κ ↪ ι)
    (hdet : IsUnit (selectedMinor B rows).det) :
    selectedMinorLeftInverse B rows * B = 1 := by
  rw [selectedMinorLeftInverse, Matrix.mul_assoc, rowSelector_mul]
  exact Matrix.nonsing_inv_mul _ hdet

/-- The selected-minor construction, packaged as an explicit split matrix. -/
theorem exists_leftInverse_of_selectedMinor_det_isUnit
    {ι κ : Type*} [Fintype ι] [Fintype κ]
     [DecidableEq κ]
    (B : Matrix ι κ R) (rows : κ ↪ ι)
    (hdet : IsUnit (selectedMinor B rows).det) :
    ∃ C : Matrix κ ι R, C * B = 1 := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  exact
    ⟨selectedMinorLeftInverse B rows,
        selectedMinorLeftInverse_mul B rows hdet⟩

/-! ## Power-series criterion -/

variable {k : Type v} [Field k]

/-- Over `k[[X]]`, a nonzero constant coefficient makes the selected
determinant a unit and hence gives the same explicit left inverse. -/
theorem powerSeries_selectedMinorLeftInverse_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ (PowerSeries k)) (rows : κ ↪ ι)
    (hconst : PowerSeries.constantCoeff (selectedMinor B rows).det ≠ 0) :
    selectedMinorLeftInverse B rows * B = 1 := by
  apply selectedMinorLeftInverse_mul
  rw [PowerSeries.isUnit_iff_constantCoeff]
  exact isUnit_iff_ne_zero.mpr hconst

/-- Existence form used by the tangent-limit annihilator construction. -/
theorem powerSeries_exists_leftInverse_of_selectedMinor_constantCoeff_ne_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
     [DecidableEq κ]
    (B : Matrix ι κ (PowerSeries k)) (rows : κ ↪ ι)
    (hconst : PowerSeries.constantCoeff (selectedMinor B rows).det ≠ 0) :
    ∃ C : Matrix κ ι (PowerSeries k), C * B = 1 := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  exact
    ⟨selectedMinorLeftInverse B rows,
        powerSeries_selectedMinorLeftInverse_mul B rows hconst⟩

end

end Stafford38.GeometrySplitTangentMatrix
