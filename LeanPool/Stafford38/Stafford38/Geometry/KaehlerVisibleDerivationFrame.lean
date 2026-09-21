/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
import LeanPool.Stafford38.Stafford38.Geometry.ResidueMinorSelection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Derivation frames visible in residue coordinates

Let `K/k` be a field extension and let `qbar i : K` be a finite family whose
Kähler differentials span `Ω[K/k]`.  A basis can then be selected from that
family.  Its dual coordinate maps correspond, by the universal property of
Kähler differentials, to `k`-derivations of `K`.  These derivations evaluate
on the selected coordinates as the Kronecker delta.

Applying the derivations coefficientwise to power-series lifts of the
coordinates gives a selected residue minor whose determinant has constant
coefficient exactly one.

This file assumes the spanning hypothesis.  In particular, it does not claim
that an arbitrary retained DVR or boundary place supplies it.
-/

namespace Stafford38.Geometry.KaehlerVisibleDerivationFrame

open Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
open Stafford38.GeometryResidueMinorSelection
open Stafford38.GeometrySplitTangentMatrix

noncomputable section

universe u v

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- If finitely many residue coordinates span the Kähler differentials, one
can select a basis among them and choose dual derivations. -/
theorem exists_visible_derivation_frame_of_kaehler_span
    {iota : Type v} [Fintype iota]
    [FiniteDimensional K (Ω[K⁄k])]
    (qbar : iota → K)
    (hspan :
      Submodule.span K
        (Set.range fun i ↦ KaehlerDifferential.D k K (qbar i)) = ⊤) :
    ∃ (rows : Fin (Module.finrank K (Ω[K⁄k])) ↪ iota)
      (D : Fin (Module.finrank K (Ω[K⁄k])) → Derivation k K K),
      ∀ i j, D j (qbar (rows i)) = if i = j then 1 else 0 := by
  let b := Module.Basis.ofSpan (K := K)
    (s := Set.range fun i ↦ KaehlerDifferential.D k K (qbar i)) hspan.ge
  letI : Fintype ((linearIndepOn_empty K (id : Ω[K⁄k] → Ω[K⁄k])).extend
      (Set.empty_subset
        (Set.range fun i ↦ KaehlerDifferential.D k K (qbar i)))) :=
    Fintype.ofFinite _
  let e : Fin (Module.finrank K (Ω[K⁄k])) ≃
      ((linearIndepOn_empty K (id : Ω[K⁄k] → Ω[K⁄k])).extend
        (Set.empty_subset
          (Set.range fun i ↦ KaehlerDifferential.D k K (qbar i)))) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, ← Module.finrank_eq_card_basis b])
  have hb_range (a : Fin (Module.finrank K (Ω[K⁄k]))) :
      b (e a) ∈
        Set.range fun i ↦ KaehlerDifferential.D k K (qbar i) :=
    Module.Basis.ofSpan_subset (K := K) (V := Ω[K⁄k]) hspan.ge ⟨e a, rfl⟩
  let row (a : Fin (Module.finrank K (Ω[K⁄k]))) : iota :=
    Classical.choose (hb_range a)
  have hrow (a : Fin (Module.finrank K (Ω[K⁄k]))) :
      KaehlerDifferential.D k K (qbar (row a)) = b (e a) :=
    Classical.choose_spec (hb_range a)
  have hrow_injective : Function.Injective row := by
    intro a₁ a₂ h
    apply e.injective
    apply b.injective
    rw [← hrow a₁, ← hrow a₂, h]
  let rows : Fin (Module.finrank K (Ω[K⁄k])) ↪ iota :=
    ⟨row, hrow_injective⟩
  let D (j : Fin (Module.finrank K (Ω[K⁄k]))) : Derivation k K K :=
    KaehlerDifferential.linearMapEquivDerivation k K (b.coord (e j))
  refine ⟨rows, D, ?_⟩
  intro i j
  rw [show qbar (rows i) = qbar (row i) by rfl]
  rw [show D j (qbar (row i)) =
      b.coord (e j) (KaehlerDifferential.D k K (qbar (row i))) by
    simp [D]]
  rw [hrow]
  by_cases hij : i = j
  · subst j
    simp
  · have heij : e i ≠ e j := fun h ↦ hij (e.injective h)
    simp [heij, hij]

/-- Coefficientwise application of a family of residue-field derivations to
power-series coordinates. -/
noncomputable def coefficientwiseTangentMatrix
    {iota kappa : Type*}
    (q : iota → PowerSeries K) (D : kappa → Derivation k K K) :
    Matrix iota kappa (PowerSeries K) :=
  fun i j ↦ coefficientwiseDerivation (D j) (q i)

@[simp]
theorem constantCoeff_coefficientwiseTangentMatrix
    {iota kappa : Type*}
    (q : iota → PowerSeries K) (D : kappa → Derivation k K K)
    (i : iota) (j : kappa) :
    PowerSeries.constantCoeff (coefficientwiseTangentMatrix q D i j) =
      D j (PowerSeries.constantCoeff (q i)) := by
  rw [coefficientwiseTangentMatrix,
    ← PowerSeries.coeff_zero_eq_constantCoeff]
  exact coeff_coefficientwiseDerivation (D j) (q i) 0

/-- Under the Kähler-span hypothesis, coefficientwise derivations furnish a
selected power-series minor with constant coefficient exactly one. -/
theorem exists_coefficientwise_selectedMinor_constantCoeff_eq_one_of_kaehler_span
    {iota : Type v} [Fintype iota]
    [FiniteDimensional K (Ω[K⁄k])]
    (q : iota → PowerSeries K)
    (hspan :
      Submodule.span K
        (Set.range fun i ↦ KaehlerDifferential.D k K
          (PowerSeries.constantCoeff (q i))) = ⊤) :
    ∃ (rows : Fin (Module.finrank K (Ω[K⁄k])) ↪ iota)
      (D : Fin (Module.finrank K (Ω[K⁄k])) → Derivation k K K),
      (∀ i j,
        D j (PowerSeries.constantCoeff (q (rows i))) =
          if i = j then 1 else 0) ∧
      PowerSeries.constantCoeff
        (selectedMinor (coefficientwiseTangentMatrix q D) rows).det = 1 := by
  obtain ⟨rows, D, hD⟩ :=
    exists_visible_derivation_frame_of_kaehler_span
      (fun i ↦ PowerSeries.constantCoeff (q i)) hspan
  refine ⟨rows, D, hD, ?_⟩
  rw [constantCoeff_selectedMinor_det]
  have hmatrix :
      selectedMinor
          (residueMatrix (coefficientwiseTangentMatrix q D)) rows =
        (1 : Matrix (Fin (Module.finrank K (Ω[K⁄k])))
          (Fin (Module.finrank K (Ω[K⁄k]))) K) := by
    ext i j
    simpa [selectedMinor, residueMatrix, Matrix.one_apply,
      constantCoeff_coefficientwiseTangentMatrix] using hD i j
  rw [hmatrix, Matrix.det_one]


end

end Stafford38.Geometry.KaehlerVisibleDerivationFrame
