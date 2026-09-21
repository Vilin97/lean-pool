/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornC1AssemblyStrong
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornNormalizedC1Assembly

/-!
# Wedhorn Normalized Strong C1 Assembly

Strengthened analogue of
`WedhornNormalizedC1Assembly.exists_per_D_finset_via_normalized_C1_supplier`
(commit landed by Secondary): wraps
`WedhornC1AssemblyStrong.exists_per_D_finset_via_C1Strong_supplier_and_compactness`
(commit `e7a86bb`) behind the cover-level `RationalCoveringData.insertDenom`
normalization (`WedhornCoverNormalization.lean`).

The result is a per-D Finset existential that:
* does NOT require the artificial
  `h_normalized : ∀ D ∈ C.covers, D.s ∈ D.T` hypothesis (supplied
  internally via `RationalCoveringData.insertDenom_normalized`);
* carries the strengthened coverage clause `¬ v.vle f 0`, ready for
  consumption by
  `WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`
  (commit `63c8ecd`) at the `h_cover_D_nonzero` argument WITHOUT an
  abstract nonzero-cover supplier.

## What this file provides

* `exists_per_D_finset_via_normalized_C1Strong_supplier` — the
  strengthened normalized assembly. Sorry-free, axiom-clean. Given only
  `C : RationalCoveringData A` and `C1SupplierStrong_local C.insertDenom`,
  produces a total `mk_S_D : RationalLocData A → Finset A` whose
  per-D coverage clause carries `¬ v.vle f 0`.

## Notes

* No root import; this file is leaf-level.
* No edits to `WedhornC1AssemblyStrong.lean`,
  `WedhornNormalizedC1Assembly.lean`, `WedhornCoverNormalization.lean`,
  `WedhornStrengthenedC1.lean`,
  `WedhornStrengthenedCompactExtraction.lean`,
  `WedhornCompactExtraction.lean` (Secondary), or
  `WedhornStandardCoverRefinement.lean` (Tertiary).
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness content.
* No compactness proof duplication: this file uses
  `exists_per_D_finset_via_C1Strong_supplier_and_compactness` directly
  (which itself wraps `mk_S_D_of_C1Strong_and_compactness`).
* The third coverage clause `¬ v.vle f 0` is invariant under the
  insert-denominator translation because the valuation `v` and the
  cover-base element `f` are unchanged across the transform; only
  `D.T` and `C.base.T` are augmented with their respective
  denominators, and the rational opens at the augmented sets agree
  with the originals on the same `v` (Wedhorn 7.30(3)). -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [DecidableEq A]

/-- **Strong C1-supplier normalization wrapper** — strengthened analogue
of `exists_per_D_finset_via_normalized_C1_supplier` at the strong-supplier
level.

Takes only `C : RationalCoveringData A` and a strong C1 supplier on the
normalized cover `C.insertDenom`; produces per-D Finset data on the
original `C` with **both**:

1. **Containment** — `∀ f ∈ mk_S_D D, R(insert f C.base.T, C.base.s)
   ⊆ R(D.T, D.s)`.
2. **Strengthened coverage** — `∀ v ∈ R(D.T, D.s), ∃ f ∈ mk_S_D D,
   v ∈ R(insert f C.base.T, C.base.s) ∧ ¬ v.vle f 0`.

The output shape exactly matches the `h_cover_D_nonzero` input expected
by
`WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue`,
so consumers wiring this into the final/base-Spa bridge no longer need
an abstract `h_cover_D_nonzero` supplier.

**Internal use:**

* `RationalCoveringData.insertDenom_normalized` discharges `D.s ∈ D.T` for
  `C.insertDenom`.
* `RationalLocData.rationalOpen_insertDenom` translates the per-piece
  rational opens.
* `rationalOpen_insert_base_insertDenom_eq` (already in
  `WedhornNormalizedC1Assembly.lean`) translates the per-`f`
  plus-piece on the cover base.

The output `mk_S_D` equals `mk_S_D' ∘ insertDenom` on `C.covers` (where
`mk_S_D'` comes from
`exists_per_D_finset_via_C1Strong_supplier_and_compactness` applied to
`C.insertDenom`), and `∅` outside `C.covers`. -/
theorem exists_per_D_finset_via_normalized_C1Strong_supplier
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A)
    (h_C1_strong : C1SupplierStrong_local C.insertDenom) :
    ∃ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D,
          v ∈ rationalOpen (insert f C.base.T) C.base.s ∧ ¬ v.vle f 0) := by
  classical
  -- Apply the existing strong assembly theorem to the normalized cover.
  obtain ⟨mk_S_D', h_in_D', h_cover_D'⟩ :=
    exists_per_D_finset_via_C1Strong_supplier_and_compactness P hA₀_le π hI hπ_tn
      hπ_unit hArch C.insertDenom h_C1_strong
      (RationalCoveringData.insertDenom_normalized C)
  -- Translate to the original cover via D ↦ D.insertDenom.
  let mk_S_D : RationalLocData A → Finset A := fun D =>
    if hD : D ∈ C.covers then mk_S_D' D.insertDenom else ∅
  refine ⟨mk_S_D, ?_, ?_⟩
  · -- Containment.
    intro D hD f hf
    rw [show mk_S_D D = mk_S_D' D.insertDenom from by simp [mk_S_D, hD]] at hf
    have hD' : D.insertDenom ∈ C.insertDenom.covers :=
      Finset.mem_image.mpr ⟨D, hD, rfl⟩
    rw [← rationalOpen_insert_base_insertDenom_eq,
      ← RationalLocData.rationalOpen_insertDenom D]
    exact h_in_D' D.insertDenom hD' f hf
  · -- Strengthened coverage (with `¬ v.vle f 0` clause).
    intro D hD v hv
    have hD' : D.insertDenom ∈ C.insertDenom.covers :=
      Finset.mem_image.mpr ⟨D, hD, rfl⟩
    have hv' : v ∈ rationalOpen D.insertDenom.T D.insertDenom.s := by
      rwa [RationalLocData.rationalOpen_insertDenom D]
    obtain ⟨f, hf, hv_f, hv_nonzero⟩ := h_cover_D' D.insertDenom hD' v hv'
    rw [show mk_S_D D = mk_S_D' D.insertDenom from by simp [mk_S_D, hD]]
    exact ⟨f, hf, (rationalOpen_insert_base_insertDenom_eq C f).symm ▸ hv_f, hv_nonzero⟩

end ValuationSpectrum
