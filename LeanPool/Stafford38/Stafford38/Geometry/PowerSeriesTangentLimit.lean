/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import LeanPool.Stafford38.Stafford38.Geometry.RetractionSpecialization


/-!
# A power-series tangent-lattice limit

This file isolates an elementary power-series calculation used in a
Grassmannian limit.  A matrix `T` of tangent columns is presented as `X ^ m`
times a matrix `B`.  If one selected coordinate of every column of `T` has a
specified additional positive power of `X`, then the selected row of `B`
vanishes in the residue field.  Consequently the corresponding coordinate
covector annihilates the residue of `B`.

If, as a separate hypothesis, the columns of `B` are split, the retraction
correction from `RetractionSpecialization` lifts that residue row to an exact
annihilator over `k[[X]]`.  This is only the tangent-lattice calculation.  It
does not construct the split lattice from `T`, nor does it construct an arc, a
normalization, a divisor at infinity, or a projective closure.
-/

@[expose] public section

namespace Stafford38.GeometryPowerSeriesTangentLimit

open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u v

variable {k : Type u} [Field k]

/-- The coordinate row selecting `axis`. -/
def axisRow {ι : Type*} [DecidableEq ι] (axis : ι) : ι → k :=
  fun i => if i = axis then 1 else 0

@[simp]
theorem axisRow_apply_same {ι : Type*} [DecidableEq ι] (axis : ι) :
    axisRow (k := k) axis axis = 1 := by
  simp [axisRow]

@[simp]
theorem axisRow_apply_of_ne {ι : Type*} [DecidableEq ι]
    {axis i : ι} (hi : i ≠ axis) : axisRow (k := k) axis i = 0 := by
  simp [axisRow, hi]

/-- `T` is presented as the common power `X ^ m` times `B`.

No maximality of `m` and no splitting of `B` is asserted here.
-/
def HasCommonPowerPresentation {ι κ : Type*}
    (T B : Matrix ι κ (PowerSeries k)) (m : ℕ) : Prop :=
  ∀ i j, T i j = (PowerSeries.X : PowerSeries k) ^ m * B i j

/-- The selected coordinate has order at least `m + gap + 1` in every column. -/
def HasSelectedOrderGap {ι κ : Type*}
    (T : Matrix ι κ (PowerSeries k)) (axis : ι) (m gap : ℕ) : Prop :=
  ∀ j, ∃ u : PowerSeries k,
    T axis j = (PowerSeries.X : PowerSeries k) ^ (m + (gap + 1)) * u

/--
Cancelling the common factor shows that the selected row of the normalized
matrix still contains a positive power of `X`.
-/
theorem normalized_selectedRow_factor
    {ι κ : Type*} (T B : Matrix ι κ (PowerSeries k))
    (axis : ι) (m gap : ℕ)
    (hnorm : HasCommonPowerPresentation T B m)
    (hgap : HasSelectedOrderGap T axis m gap) :
    ∀ j, ∃ u : PowerSeries k,
      B axis j = (PowerSeries.X : PowerSeries k) ^ (gap + 1) * u := by
  intro j
  obtain ⟨u, hu⟩ := hgap j
  refine ⟨u, ?_⟩
  have hpow :
      (PowerSeries.X : PowerSeries k) ^ m * B axis j =
        (PowerSeries.X : PowerSeries k) ^ m *
          ((PowerSeries.X : PowerSeries k) ^ (gap + 1) * u) := by
    rw [← hnorm axis j, hu, pow_add, mul_assoc]
  exact mul_left_cancel₀ (pow_ne_zero m PowerSeries.X_ne_zero) hpow

/-- The strict order gap makes the selected normalized row vanish modulo `X`. -/
theorem residue_normalized_selectedRow_eq_zero
    {ι κ : Type*} (T B : Matrix ι κ (PowerSeries k))
    (axis : ι) (m gap : ℕ)
    (hnorm : HasCommonPowerPresentation T B m)
    (hgap : HasSelectedOrderGap T axis m gap) :
    ∀ j, PowerSeries.constantCoeff (B axis j) = 0 := by
  intro j
  obtain ⟨u, hu⟩ := normalized_selectedRow_factor T B axis m gap hnorm hgap j
  rw [hu]
  simp [pow_succ]

/-- The selected coordinate covector annihilates the residue tangent columns. -/
theorem axisRow_residue_rowMul_eq_zero
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (T B : Matrix ι κ (PowerSeries k))
    (axis : ι) (m gap : ℕ)
    (hnorm : HasCommonPowerPresentation T B m)
    (hgap : HasSelectedOrderGap T axis m gap) :
    rowMul (axisRow (k := k) axis)
      (fun i j => PowerSeries.constantCoeff (B i j)) = 0 := by
  funext j
  simp [rowMul, axisRow,
    residue_normalized_selectedRow_eq_zero T B axis m gap hnorm hgap j]

/--
Tangent-lattice limit with a split power-series column matrix.

The returned row annihilates `B` exactly over `k[[X]]` and specializes to the
selected coordinate covector.  Thus that residue covector is represented by a
genuine power-series annihilator, not merely by a row annihilating the special
fibre.  The left inverse `C` is an independent lattice-splitting hypothesis;
it is not obtained from the common-power presentation.
-/
theorem exists_annihilator_specializing_to_axis
    {ι κ : Type*} [Fintype ι] [Finite κ]
    [DecidableEq ι] [DecidableEq κ]
    (T B : Matrix ι κ (PowerSeries k))
    (C : Matrix κ ι (PowerSeries k))
    (axis : ι) (m gap : ℕ)
    (hnorm : HasCommonPowerPresentation T B m)
    (hgap : HasSelectedOrderGap T axis m gap)
    (hCB : C * B = 1) :
    ∃ a : ι → PowerSeries k,
      rowMul a B = 0 ∧ residueColumn a = axisRow (k := k) axis := by
  classical
  let := Fintype.ofFinite κ
  let a₀ : ι → k := axisRow (k := k) axis
  let a : ι → PowerSeries k :=
    annihilatorLift (constantColumn a₀) B C
  refine ⟨a, ?_⟩
  have hres : residueColumn (constantColumn a₀) = a₀ :=
    residueColumn_constantColumn a₀
  have haxis :
      rowMul a₀ (fun i j => PowerSeries.constantCoeff (B i j)) = 0 :=
    axisRow_residue_rowMul_eq_zero T B axis m gap hnorm hgap
  simpa [a, a₀] using
    (powerSeries_annihilatorLift_spec (constantColumn a₀) a₀ B C hCB hres haxis)


end

end Stafford38.GeometryPowerSeriesTangentLimit
