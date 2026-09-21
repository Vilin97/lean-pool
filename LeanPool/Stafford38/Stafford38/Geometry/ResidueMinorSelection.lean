/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.SplitTangentMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Selecting a nonsingular residue minor

A rectangular matrix over a field with full column rank has a square row minor
with nonzero determinant.  The selected rows are returned as an embedding of
the column index type into the row index type, matching the input expected by
`GeometrySplitTangentMatrix`.
-/

namespace Stafford38.GeometryResidueMinorSelection

noncomputable section

open Stafford38.GeometrySplitTangentMatrix

universe u v w

variable {k : Type u} [Field k]

/-- Full column rank produces an explicitly indexed square row minor with
nonzero determinant. -/
theorem exists_selectedMinor_det_ne_zero_of_rank_eq_card
    {ι : Type v} {κ : Type w} [Finite ι] [Fintype κ]
     [DecidableEq κ]
    (B : Matrix ι κ k) (hrank : B.rank = Fintype.card κ) :
    ∃ rows : κ ↪ ι, (selectedMinor B rows).det ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  let S : Submodule k (κ → k) := Submodule.span k (Set.range B.row)
  have hfinrank : Module.finrank k S = Module.finrank k (κ → k) := by
    rw [← Matrix.rank_eq_finrank_span_row B, hrank, Module.finrank_pi]
  have hS : S = ⊤ := Submodule.eq_top_of_finrank_eq hfinrank
  let b := Module.Basis.ofSpan (K := k) (s := Set.range B.row) (hS.ge)
  let : Fintype ((linearIndepOn_empty k id).extend
      (Set.empty_subset (Set.range B.row))) := Fintype.ofFinite _
  let e : κ ≃ ((linearIndepOn_empty k id).extend
      (Set.empty_subset (Set.range B.row))) :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_basis b, Module.finrank_pi])
  have hb_range (a : κ) : b (e a) ∈ Set.range B :=
    Module.Basis.ofSpan_subset (K := k) (V := κ → k) (hS.ge) ⟨e a, rfl⟩
  let row (a : κ) : ι := Classical.choose (hb_range a)
  have hrow (a : κ) : B (row a) = b (e a) := Classical.choose_spec (hb_range a)
  have hrow_injective : Function.Injective row := by
    intro a₁ a₂ h
    apply e.injective
    apply b.injective
    rw [← hrow a₁, ← hrow a₂, h]
  let rows : κ ↪ ι := ⟨row, hrow_injective⟩
  have hli : LinearIndependent k (fun a : κ => selectedMinor B rows a) := by
    have he : LinearIndependent k (fun a : κ => b (e a)) :=
      b.linearIndependent.comp _ e.injective
    have hfamily : (fun a : κ => selectedMinor B rows a) = fun a => b (e a) := by
      funext a
      exact hrow a
    rw [hfamily]
    exact he
  have hunit : IsUnit (selectedMinor B rows) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hli
  exact ⟨rows, ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero⟩

/-- Injectivity of the residue matrix on column vectors is the usual
hypothesis implying the existence of a nonsingular selected row minor. -/
theorem exists_selectedMinor_det_ne_zero_of_mulVec_injective
    {ι : Type v} {κ : Type w} [Finite ι] [Fintype κ]
     [DecidableEq κ]
    (B : Matrix ι κ k) (hinj : Function.Injective B.mulVec) :
    ∃ rows : κ ↪ ι, (selectedMinor B rows).det ≠ 0 := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let := Fintype.ofFinite ι
  apply exists_selectedMinor_det_ne_zero_of_rank_eq_card B
  have hker : LinearMap.ker B.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hker_finrank : Module.finrank k (LinearMap.ker B.mulVecLin) = 0 := by
    rw [hker]
    exact finrank_bot k (κ → k)
  have hrn := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [hker_finrank, add_zero, Module.finrank_pi] at hrn
  simpa only [Matrix.rank] using hrn

/-! ## Power-series residue matrices -/

/-- Entrywise constant coefficient of a power-series matrix. -/
def residueMatrix
    {ι : Type v} {κ : Type w} (B : Matrix ι κ (PowerSeries k)) : Matrix ι κ k :=
  fun i j => PowerSeries.constantCoeff (B i j)

theorem constantCoeff_selectedMinor_det
    {ι : Type v} {κ : Type w} [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ (PowerSeries k)) (rows : κ ↪ ι) :
    PowerSeries.constantCoeff (selectedMinor B rows).det =
      (selectedMinor (residueMatrix B) rows).det := by
  rw [RingHom.map_det]
  congr 1

/-- Injectivity after reduction to constant coefficients selects a minor whose
power-series determinant is a unit. -/
theorem powerSeries_exists_selectedMinor_constantCoeff_ne_zero_of_residue_mulVec_injective
    {ι : Type v} {κ : Type w} [Finite ι] [Fintype κ]
     [DecidableEq κ]
    (B : Matrix ι κ (PowerSeries k))
    (hinj : Function.Injective (residueMatrix B).mulVec) :
    ∃ rows : κ ↪ ι,
      PowerSeries.constantCoeff (selectedMinor B rows).det ≠ 0 := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let := Fintype.ofFinite ι
  obtain ⟨rows, hrows⟩ :=
    exists_selectedMinor_det_ne_zero_of_mulVec_injective (residueMatrix B) hinj
  exact ⟨rows, by rwa [constantCoeff_selectedMinor_det]⟩

/-- The residue-rank criterion composed with the selected-minor construction:
the power-series matrix has an explicit left inverse. -/
theorem powerSeries_exists_leftInverse_of_residue_mulVec_injective
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
     [DecidableEq κ]
    (B : Matrix ι κ (PowerSeries k))
    (hinj : Function.Injective (residueMatrix B).mulVec) :
    ∃ C : Matrix κ ι (PowerSeries k), C * B = 1 := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  obtain ⟨rows, hrows⟩ :=
    powerSeries_exists_selectedMinor_constantCoeff_ne_zero_of_residue_mulVec_injective B hinj
  exact powerSeries_exists_leftInverse_of_selectedMinor_constantCoeff_ne_zero B rows hrows


end

end Stafford38.GeometryResidueMinorSelection
