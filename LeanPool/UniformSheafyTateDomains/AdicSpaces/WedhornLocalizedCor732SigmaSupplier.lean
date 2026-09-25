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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornC1SigmaImageAlignment
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCor732ToFactoredChain

/-!
# Wedhorn 8.34(ii) — Localized Cor 7.32 σ-supplier for the actual C1 route (T065)

T058 + T062 closed the Lemma 8.33 multi-piece collapse and the
σ-shift exact-alignment bridge. The remaining theorem-level work for
the Wedhorn 8.34(ii) C1 supplier route is the **σ-supplier**: produce
the dominating unit `σ_loc : (Localization.Away s)ˣ` and the
t-indexed Laurent cover hypothesis in the exact shape consumed by
T062's `rationalOpen_global_subset_via_sigma_shift_t_indexed`.

## What this file provides

* `cor732_laurent_piece_membership_t_indexed` — generic re-indexing of
  the existing `cor732_laurent_piece_membership_at` output from
  `(τ ∈ T_test, w ∈ R({1}, σ⁻¹ * τ))` to
  `(t ∈ T_test.image (σ⁻¹ * ·), w ∈ R({1}, t))`. Mathlib-style
  primitive: produces the **t-indexed** form expected by T062's
  consumer directly from Cor 7.32 σ-strict-domination.

* `localizedCor732_sigma_supplier_for_actual_C1` — **main theorem**
  (T065 ticket-named target): from the localized Wedhorn-Tate
  hypotheses, produce `σ_loc : (Localization.Away s)ˣ` and the
  σ-rescaled image cover hypothesis
  `∀ w ∈ Spa, ∃ t ∈ D_T_loc, w ∈ rationalOpen ({1}) t`
  with `D_T_loc := (localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·)`,
  i.e., the **exact t-indexed Laurent cover input** that T062's
  σ-shifted consumer consumes for the actual C1 target
  `rationalOpen D_T_loc D_s`.

* `localizedCor732_sigma_supplier_t_indexed_cover_at` — the
  per-piece-membership packaging of the supplier output: for each
  `w ∈ Spa(Localization.Away s, …)`, the t-indexed Laurent piece
  membership directly.

* `rationalOpen_global_subset_via_localizedCor732_sigma_supplier`
  — **end-to-end consumer**: composes the localized Cor 7.32
  σ-supplier with T062's
  `rationalOpen_global_subset_via_sigma_shift_t_indexed` to produce
  the C1 supplier's clause 2 conclusion
  `rationalOpen (insert f T_base) s_base ⊆ rationalOpen D_T_loc D_s`
  on the localized side, modulo only the per-piece subset
  hypothesis.

## How this closes the Wedhorn 8.34(ii) C1 chain

Combining T053 / T054 (per-piece data), T056 (per-piece source-
restricted reroute), T058 (Lemma 8.33 collapse for σ-rescaled image),
T062 (σ-shift exact alignment with t-indexed consumer), and T065 (this
file's supplier), the C1 supplier's clause 2 conclusion at the
**actual cover-piece denominator target** `rationalOpen D_T_loc D_s`
is dischargeable from:

* the localized Wedhorn-Tate / pseudouniformizer / Archimedean
  hypotheses (already established as the input of
  `exists_dominating_unit_in_localization`),
* the per-piece subset inclusions deliverable from T056 +
  `per_piece_singleton_subset_via_laurent_membership`.

No remaining theorem-level Wedhorn 8.34(ii) cover-assembly residual
beyond the localized hypotheses — the σ and Laurent cover are
mechanical from this T065 supplier.

## Notes

* No root import; leaf-level file.
* Imports `WedhornC1SigmaImageAlignment` (T062) and
  `WedhornLocalCor732ToFactoredChain` (existing localized Cor 7.32
  application).
* No edits to T031–T064 accepted leaves, root imports, or final
  theorem signatures.
* Disjoint write set from `WedhornC1CoverAssemblyClosure.lean` (T060),
  `WedhornTateAcyclicityFinalClosure.lean` (T061), and any
  consumer-side integration files (T064).
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32 / Jacobson, faithful-flatness, Zavyalov, global universal
  Spa bound, or bivariate-overlap content.
* All declarations are fully proven, depend only on the standard
  Lean kernel postulates, and avoid native compilation and unchecked
  tactics.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **τ-indexed → t-indexed re-indexing of `cor732_laurent_piece_membership_at`**
(T065 reusable primitive).

Generic re-indexing: from the existing
`cor732_laurent_piece_membership_at` output
`∃ τ ∈ T, w ∈ rationalOpen ({1}) (σ⁻¹ * τ)`, produce the
**t-indexed** form
`∃ t ∈ T.image (σ⁻¹ * ·), w ∈ rationalOpen ({1}) t`
needed by T062's `rationalOpen_global_subset_via_sigma_shift_t_indexed`
consumer.

Mathlib-style primitive — fully general re-indexing using
`Finset.mem_image_of_mem`. -/
theorem cor732_laurent_piece_membership_t_indexed
    [DecidableEq A]
    {σ : Aˣ} {T : Finset A}
    (hσ_dom :
      ∀ v ∈ Spa A A⁺, ∃ τ ∈ T, v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A)) :
    ∀ w ∈ Spa A A⁺,
      ∃ t ∈ T.image (fun τ ↦ ((σ⁻¹ : Aˣ) : A) * τ),
        w ∈ rationalOpen ({(1 : A)} : Finset A) t := by
  intro w hw
  obtain ⟨τ, hτ_mem, hw_in_piece⟩ :=
    cor732_laurent_piece_membership_at hσ_dom hw
  refine ⟨((σ⁻¹ : Aˣ) : A) * τ, ?_, hw_in_piece⟩
  exact Finset.mem_image_of_mem _ hτ_mem

omit [PlusSubring A] in
/-- **Localized Cor 7.32 σ-supplier for the actual C1 route**
(T065 main theorem — ticket-named target).

From the localized Wedhorn-Tate hypotheses (`π_loc`, `T_D`, `s_D`,
Archimedean, etc.), produce `σ_loc : (Localization.Away s)ˣ` and the
**σ-rescaled image cover hypothesis** in the exact shape consumed by
T062's `rationalOpen_global_subset_via_sigma_shift_t_indexed` with
`D_T_loc := (localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·)`:

```
∀ w ∈ Spa(Localization.Away s, locSubring P T s),
  ∃ t ∈ (localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·),
    w ∈ rationalOpen ({1}) t
```

**Substantive composition** of:

* `exists_dominating_unit_in_localization` (existing localized
  Cor 7.32 σ-supplier in `WedhornLocalizedCor732Application`),
* `cor732_laurent_piece_membership_at` (existing per-`w` Laurent piece
  membership in `WedhornStandardCoverRefinement`),
* the τ → t re-indexing helper above.

The resulting σ_loc and cover form are the **exact T062 consumer
inputs** for the actual C1 cover-piece denominator target
`rationalOpen D_T_loc D_s` — closing the localized Cor 7.32 →
σ-shifted t-indexed Lemma 8.33 cover-assembly chain.

The non-vanishing hypothesis `hT_loc` is the standard "no common zero
of the test family on the localized Spa" precondition for Cor 7.32. -/
theorem localizedCor732_sigma_supplier_for_actual_C1
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ (π_loc : (locPairOfDefinition P T s hopen).A₀)
      (_hI_loc : (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away s),
        letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)))
      (T_D : Finset A) (s_D : A)
      (_hT_loc : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D, ¬ w.vle τ 0),
    ∃ σ_loc : (Localization.Away s)ˣ,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ t ∈ (localizedTestFamily s T_D s_D).image
          (fun τ ↦ ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
            Localization.Away s) * τ),
          w ∈ rationalOpen
            ({(1 : Localization.Away s)} :
              Finset (Localization.Away s)) t := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
  -- Step 1: extract σ_loc via the existing localized Cor 7.32 supplier.
  obtain ⟨σ_loc, hσ_loc_dom⟩ :=
    exists_dominating_unit_in_localization P T s hopen
      π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc
      (localizedTestFamily s T_D s_D) hT_loc
  refine ⟨σ_loc, ?_⟩
  -- Step 2: re-index the Laurent piece membership to t-indexed form.
  exact cor732_laurent_piece_membership_t_indexed hσ_loc_dom

omit [PlusSubring A] in
/-- **Per-`w` packaging of the localized Cor 7.32 σ-supplier output**
(T065 single-`w` form).

For a fixed σ_loc supplied by `localizedCor732_sigma_supplier_for_actual_C1`
(or directly by `exists_dominating_unit_in_localization`), at every
`w ∈ Spa(Localization.Away s, locSubring P T s)` produce a
**t-indexed Laurent piece witness**: `∃ t ∈ D_T_loc, w ∈
rationalOpen ({1}) t` with `D_T_loc := (localizedTestFamily s T_D s_D).image
(σ_loc⁻¹ * ·)`.

Per-`w` form of the supplier; useful for callers that already hold a
σ_loc (e.g., constructed by hand or via a different σ-strict-dom
route) and only need the t-indexed reformulation. -/
theorem localizedCor732_sigma_supplier_t_indexed_cover_at
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      ∃ t ∈ (localizedTestFamily s T_D s_D).image
        (fun τ ↦ ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
          Localization.Away s) * τ),
        w ∈ rationalOpen
          ({(1 : Localization.Away s)} :
            Finset (Localization.Away s)) t := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  exact cor732_laurent_piece_membership_t_indexed hσ_loc_dom

omit [PlusSubring A] in
/-- **End-to-end localized Cor 7.32 → C1 supplier clause 2**
(T065 final consumer).

End-to-end consumer for the C1 supplier's clause 2 conclusion on the
localized side: combines T065's σ-supplier with T062's
`rationalOpen_global_subset_via_sigma_shift_t_indexed`.

**Inputs**:

* Localized Wedhorn-Tate hypotheses (the standard preconditions
  for `exists_dominating_unit_in_localization`).

* `T_D : Finset A`, `s_D : A` — the cover-piece denominator family
  and main denominator (used to construct the localized test family).

* `T_base_loc : Finset (Localization.Away s)`, `s_base_loc f_loc D_s :
  Localization.Away s` — the C1 supplier's source-side rational subset
  data on the localization (`R(insert f_loc T_base_loc) s_base_loc`).

* `h_per_piece_subset` — the per-piece subset inclusions on each
  σ-rescaled Laurent piece, deliverable from T056's per-piece source-
  restricted reroute.

**Output**: the global subset
`rationalOpen (insert f_loc T_base_loc) s_base_loc ⊆ rationalOpen
((localizedTestFamily s T_D s_D).image (σ_loc⁻¹ * ·)) D_s`,
i.e., the C1 supplier's clause 2 conclusion at the σ-rescaled image
target. The σ_loc is **internally extracted** via T065's σ-supplier;
the user does not supply a σ.

This theorem **closes the Wedhorn 8.34(ii) C1 cover-assembly route**
on the localized side modulo only the per-piece subset inclusions.
The C1 supplier's clause 2 is no longer the bottleneck; remaining
theorem-level work is the per-piece bound deliverable from T056. -/
theorem rationalOpen_global_subset_via_localizedCor732_sigma_supplier
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ (π_loc : (locPairOfDefinition P T s hopen).A₀)
      (_hI_loc : (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away s),
        letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)))
      (T_D : Finset A) (s_D : A)
      (_hT_loc : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D, ¬ w.vle τ 0)
      (T_base_loc : Finset (Localization.Away s))
      (s_base_loc D_s f_loc : Localization.Away s)
      (_h_per_piece_subset_at_supplied_sigma :
        ∀ (σ_loc : (Localization.Away s)ˣ),
          ∀ t ∈ (localizedTestFamily s T_D s_D).image
              (fun τ ↦ ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
                Localization.Away s) * τ),
            rationalOpen (insert f_loc T_base_loc) s_base_loc ∩
                rationalOpen
                  ({(1 : Localization.Away s)} :
                    Finset (Localization.Away s)) t ⊆
              rationalOpen
                ({t} : Finset (Localization.Away s)) D_s),
    ∃ σ_loc : (Localization.Away s)ˣ,
      rationalOpen (insert f_loc T_base_loc) s_base_loc ⊆
        rationalOpen
          ((localizedTestFamily s T_D s_D).image
            (fun τ ↦ ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
              Localization.Away s) * τ))
          D_s := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
    T_base_loc s_base_loc D_s f_loc h_per_piece_subset_at_supplied_sigma
  -- Extract σ_loc and the t-indexed cover from the supplier.
  obtain ⟨σ_loc, h_cover_t⟩ :=
    localizedCor732_sigma_supplier_for_actual_C1 P T s hopen
      π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_D s_D hT_loc
  refine ⟨σ_loc, ?_⟩
  -- Restrict the cover from Spa to the source rationalOpen.
  have h_cover_source :
      ∀ w ∈ rationalOpen (insert f_loc T_base_loc) s_base_loc,
        ∃ t ∈ (localizedTestFamily s T_D s_D).image
          (fun τ ↦ ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
            Localization.Away s) * τ),
          w ∈ rationalOpen
            ({(1 : Localization.Away s)} :
              Finset (Localization.Away s)) t := by
    intro w hw_source
    have hw_spa : w ∈ Spa (Localization.Away s)
        (Localization.Away s)⁺ := rationalOpen_subset_spa hw_source
    exact h_cover_t w hw_spa
  -- Apply T062's σ-shift t-indexed consumer.
  exact rationalOpen_global_subset_via_sigma_shift_t_indexed σ_loc
    ((localizedTestFamily s T_D s_D).image
      (fun τ ↦ ((σ_loc⁻¹ : (Localization.Away s)ˣ) :
        Localization.Away s) * τ))
    T_base_loc s_base_loc D_s f_loc
    (h_per_piece_subset_at_supplied_sigma σ_loc)
    h_cover_source

end ValuationSpectrum
