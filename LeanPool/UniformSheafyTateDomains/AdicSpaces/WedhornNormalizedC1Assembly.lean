/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornC1Assembly
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCoverNormalization

/-!
# Wedhorn Normalized C1 Assembly

Wraps `WedhornC1Assembly.exists_per_D_finset_via_C1_supplier_and_compactness`
behind the cover-level `RationalCoveringData.insertDenom` normalization
(`WedhornCoverNormalization.lean`). The result is a per-D Finset existential
that does NOT require the artificial
`h_normalized : ∀ D ∈ C.covers, D.s ∈ D.T` hypothesis: it is supplied
internally via `RationalCoveringData.insertDenom_normalized`.

## What this file provides

* `rationalOpen_insert_base_insertDenom_eq` — the cover-base analog of
  Wedhorn 7.30(3) at insert-denom: for any `f : A`,
  `rationalOpen (insert f C.insertDenom.base.T) C.insertDenom.base.s =
    rationalOpen (insert f C.base.T) C.base.s`. Composes
  `Finset.insert_comm` with `rationalOpen_insert_s`.

* `exists_per_D_finset_via_normalized_C1_supplier` — the **C1-supplier
  normalization wrapper**: takes only `C : RationalCoveringData A` and
  `C1Supplier_local C.insertDenom` (no `h_normalized` hypothesis), produces
  per-D Finset data on the original `C`.

* `hZavyalov_per_E_via_normalized_C1_supplier_with_h_span` — composes the
  per-D wrapper with `hZavyalov_per_E_of_per_D_construction` under an
  explicit `h_span_extractor` hypothesis. The Stage-2 span obstruction is
  unchanged from `WedhornC1Assembly`'s version; only the `h_normalized`
  hypothesis is removed.

## Notes

* No root import; this file is leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  content.
* Axioms used: `propext`, `Classical.choice`, `Quot.sound` only.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [DecidableEq A]

/-- **Cover-base analog of Wedhorn 7.30(3) at insert-denom**: adding a fresh
`f` to `C.insertDenom.base.T` produces the same rational open as adding `f`
to the original `C.base.T`. Composes `Finset.insert_comm` (to swap `f` and
`C.base.s` in the insert chain) with `rationalOpen_insert_s` (to drop the
`C.base.s` insertion). -/
theorem rationalOpen_insert_base_insertDenom_eq
    (C : RationalCoveringData A) (f : A) :
    rationalOpen (insert f C.insertDenom.base.T) C.insertDenom.base.s =
      rationalOpen (insert f C.base.T) C.base.s := by
  show rationalOpen (insert f (insert C.base.s C.base.T)) C.base.s =
    rationalOpen (insert f C.base.T) C.base.s
  rw [Finset.insert_comm]
  exact rationalOpen_insert_s _ _

/-- **C1-supplier normalization wrapper** — Theorem A on the unnormalized
side. Takes only `C : RationalCoveringData A` and a C1 supplier on the
normalized cover `C.insertDenom`; produces per-D Finset data on the original
`C` without requiring the `D.s ∈ D.T` hypothesis as an external input.

Internal use:

* `RationalCoveringData.insertDenom_normalized` discharges the required
  normalization hypothesis for `C.insertDenom`.
* `RationalLocData.rationalOpen_insertDenom` translates the per-piece
  rational opens (`rationalOpen D.insertDenom.T D.insertDenom.s =
  rationalOpen D.T D.s`).
* `rationalOpen_insert_base_insertDenom_eq` translates the per-`f`
  plus-piece on the cover base.

The output `mk_S_D` equals `mk_S_D' ∘ insertDenom` on `C.covers` (where
`mk_S_D'` comes from the underlying assembly applied to `C.insertDenom`),
and `∅` outside `C.covers`. -/
theorem exists_per_D_finset_via_normalized_C1_supplier
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A)
    (h_C1 : C1Supplier_local C.insertDenom) :
    ∃ mk_S_D : RationalLocData A → Finset A,
      (∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
        rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s) ∧
      (∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
        ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s) := by
  classical
  -- Apply the existing assembly theorem to the normalized cover.
  obtain ⟨mk_S_D', h_in_D', h_cover_D'⟩ :=
    exists_per_D_finset_via_C1_supplier_and_compactness P hA₀_le π hI hπ_tn hπ_unit
      hArch C.insertDenom h_C1 (RationalCoveringData.insertDenom_normalized C)
  -- Translate to the original cover via D ↦ D.insertDenom.
  let mk_S_D : RationalLocData A → Finset A := fun D =>
    if hD : D ∈ C.covers then mk_S_D' D.insertDenom else ∅
  refine ⟨mk_S_D, ?_, ?_⟩
  · -- Containment.
    intro D hD f hf
    rw [show mk_S_D D = mk_S_D' D.insertDenom from by simp [mk_S_D, hD]] at hf
    have hD' : D.insertDenom ∈ C.insertDenom.covers :=
      Finset.mem_image.mpr ⟨D, hD, rfl⟩
    have hContain := h_in_D' D.insertDenom hD' f hf
    rwa [rationalOpen_insert_base_insertDenom_eq,
      RationalLocData.rationalOpen_insertDenom D] at hContain
  · -- Coverage.
    intro D hD v hv
    have hD' : D.insertDenom ∈ C.insertDenom.covers :=
      Finset.mem_image.mpr ⟨D, hD, rfl⟩
    have hv' : v ∈ rationalOpen D.insertDenom.T D.insertDenom.s := by
      rwa [RationalLocData.rationalOpen_insertDenom D]
    obtain ⟨f, hf, hv_f⟩ := h_cover_D' D.insertDenom hD' v hv'
    rw [show mk_S_D D = mk_S_D' D.insertDenom from by simp [mk_S_D, hD]]
    exact ⟨f, hf, by rwa [← rationalOpen_insert_base_insertDenom_eq C f]⟩

/-- **`hZavyalov_per_E` via normalized C1 supplier under explicit span
extractor** — composes the normalized per-D wrapper with
`hZavyalov_per_E_of_per_D_construction`. The `h_normalized` hypothesis from
`WedhornC1Assembly.hZavyalov_per_E_via_C1_supplier_and_compactness_with_h_span`
is removed; only the Stage-2 span obstruction `h_span_extractor` remains
external. -/
theorem hZavyalov_per_E_via_normalized_C1_supplier_with_h_span
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A)
    (h_C1 : C1Supplier_local C.insertDenom)
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
    exists_per_D_finset_via_normalized_C1_supplier P hA₀_le π hI hπ_tn hπ_unit
      hArch C h_C1
  exact hZavyalov_per_E_of_per_D_construction C mk_S_D h_in_D h_cover_D
    (h_span_extractor mk_S_D h_in_D h_cover_D)

end ValuationSpectrum
