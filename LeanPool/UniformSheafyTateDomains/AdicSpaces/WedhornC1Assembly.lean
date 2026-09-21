/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StandardCoverConditionalBridge
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCompactExtraction

/-!
# Wedhorn C1 Assembly: composition of conditional-bridge + compactness layers

Composes the three pieces currently in flight on the Wedhorn 8.34(ii)
standard-cover refinement chain into a single per-D Finset existential
and a per-E `hZavyalov_per_E` discharge:

* `StandardCoverConditionalBridge.exists_single_f_refining_point_in_D_via_C1Supplier`
  — the bridge from Tertiary's abstract `C1Supplier_local` to the
  pointwise C1 single-`f` form (mine, commit 240b682).
* `WedhornCompactExtraction.mk_S_D_of_C1_and_compactness` — Secondary's
  finite-subcover extraction for a single cover piece `D`.
* `StandardCover.hZavyalov_per_E_of_per_D_construction` — existing
  per-E wrapper consuming `(mk_S_D, h_in_D, h_cover_D, h_span)`.

## What this file provides

* `exists_per_D_finset_via_C1_supplier_and_compactness` (theorem A) —
  given the abstract `C1Supplier_local` + the Wedhorn 7.30(3)-respecting
  normalization `D.s ∈ D.T` for each `D ∈ C.covers`, produce a total
  function `mk_S_D : RationalLocData A → Finset A` with the per-D
  containment and coverage clauses required by
  `hZavyalov_per_E_of_per_D_construction`.

* `hZavyalov_per_E_via_C1_supplier_and_compactness_with_h_span`
  (theorem B) — composes theorem A with
  `hZavyalov_per_E_of_per_D_construction` under an explicit
  `h_span_extractor` hypothesis. Sorry-free; the `h_span_extractor`
  is the precise Stage-2 obstruction (Spa-level no-common-zero on the
  union family) that requires either Tertiary's helper to expose
  `¬ v.vle f 0` or a separate global-rescue argument.

## Notes

* No root import: this file is leaf-level; not imported by
  `Adic spaces.lean`.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness content.
* Axioms used (after compilation): only `propext`, `Classical.choice`,
  `Quot.sound`. Verified via `#print axioms`.
* `mk_S_D` is built by `Classical.dec` dispatch on `D ∈ C.covers`
  (no project-level `DecidableEq` for `RationalLocData A`); on
  out-of-cover inputs `mk_S_D D = ∅`. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Theorem A** — assembly of the C1 supplier + compactness extraction
into a per-D Finset.

For each `D ∈ C.covers`, the abstract `C1Supplier_local` together with
the Wedhorn 7.30(3) normalization `D.s ∈ D.T` (so that the supplier's
`t ∈ D.T` slot can be filled with `D.s`) produces a pointwise
single-`f` refinement at every `v ∈ rationalOpen D.T D.s`. Secondary's
`mk_S_D_of_C1_and_compactness` then extracts a finite `S_D : Finset A`
covering `rationalOpen D.T D.s` via plus-pieces and contained inside it.

This theorem aggregates these per-D Finsets into a single total function
`mk_S_D : RationalLocData A → Finset A` (defaulting to `∅` on cover
pieces outside `C.covers`) and exposes the resulting `h_in_D` /
`h_cover_D` clauses in the shape consumed by
`hZavyalov_per_E_of_per_D_construction` (`StandardCover.lean:292`). -/
theorem exists_per_D_finset_via_C1_supplier_and_compactness
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A)
    (h_C1 : C1Supplier_local C)
    (h_normalized : ∀ D ∈ C.covers, D.s ∈ D.T) :
    ∃ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) := by
  classical
  -- Step 1: per-D pointwise C1 via the conditional bridge.
  have hC1_pointwise : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ v ∈ rationalOpen D.T D.s, ∃ f : A,
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s := by
    intro D hD v hv
    exact exists_single_f_refining_point_in_D_via_C1Supplier C h_C1 D hD
      (h_normalized D hD) v hv
  -- Step 2: per-D Finset via Secondary's compactness extraction.
  have hPerD : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∃ S : Finset A,
        (∀ f ∈ S,
          rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
        (∀ v ∈ rationalOpen D.T D.s,
          ∃ f ∈ S, v ∈ rationalOpen (insert f C.base.T) C.base.s) := by
    intro D hD
    exact mk_S_D_of_C1_and_compactness P hA₀_le π hI hπ_tn hπ_unit hArch C D
      (hC1_pointwise D hD)
  -- Step 3: aggregate per-D Finsets into a total function via Classical.dec.
  let mk_S_D : RationalLocData A → Finset A := fun D ↦
    if hD : D ∈ C.covers then Classical.choose (hPerD D hD) else ∅
  refine ⟨mk_S_D, ?_, ?_⟩
  · -- h_in_D: containment per D, per f.
    intro D hD f hf
    have h_unfold : mk_S_D D = Classical.choose (hPerD D hD) := by
      simp [mk_S_D, hD]
    rw [h_unfold] at hf
    exact (Classical.choose_spec (hPerD D hD)).1 f hf
  · -- h_cover_D: coverage per D, per v.
    intro D hD v hv
    have h_unfold : mk_S_D D = Classical.choose (hPerD D hD) := by
      simp [mk_S_D, hD]
    rw [h_unfold]
    exact (Classical.choose_spec (hPerD D hD)).2 v hv

/-- **Theorem B** — composition into `hZavyalov_per_E` under an
explicit span extractor.

Theorem A produces the per-D Finset data `(mk_S_D, h_in_D, h_cover_D)`;
the existing `hZavyalov_per_E_of_per_D_construction`
(`StandardCover.lean:292`) consumes that triple plus an `h_span` witness
for the union family. The latter remains the **Stage-2 obstruction**
documented in the assembly audit: deriving `Ideal.span (biUnion mk_S_D)
= ⊤` requires either Tertiary's helper to expose a third clause
`¬ v.vle f 0` (and then a global-rescue argument for points outside
`rationalOpen C.base.T C.base.s`) or an externally-supplied
`h_span_extractor` hypothesis. This theorem takes the latter and
discharges the rest. -/
theorem hZavyalov_per_E_via_C1_supplier_and_compactness_with_h_span
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A)
    (h_C1 : C1Supplier_local C)
    (h_normalized : ∀ D ∈ C.covers, D.s ∈ D.T)
    (h_span_extractor : ∀ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) →
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) →
      Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  obtain ⟨mk_S_D, h_in_D, h_cover_D⟩ :=
    exists_per_D_finset_via_C1_supplier_and_compactness P hA₀_le π hI hπ_tn hπ_unit
      hArch C h_C1 h_normalized
  exact hZavyalov_per_E_of_per_D_construction C mk_S_D h_in_D h_cover_D
    (h_span_extractor mk_S_D h_in_D h_cover_D)

end ValuationSpectrum
