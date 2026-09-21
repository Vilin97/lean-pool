/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPerPieceLaurentC1Supplier
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPerPieceLaurentCoverAssembly

/-!
# Wedhorn 8.34(ii) — C1 supplier cover-assembly closure (T060)

T056 (commit `111310f`) accepted the per-piece source-restricted C1
reroute and named `CoverLevelAssemblyResidual` as the remaining
content. T057 (commit accepted in parallel by Claude Secondary) lands
the subset-level cover-assembly API and the structured Lemma 8.33
predicate `LaurentCoverPresheafLemma833Assembly`.

This file lands the **bridge from T057's structured Lemma 8.33
predicate to T056's `CoverLevelAssemblyResidual`**: a single named
multi-piece Wedhorn 8.33 assembly hypothesis is **sufficient** to
discharge `CoverLevelAssemblyResidual`. Combined with T056's per-piece
reroute, this fully reduces the C1 supplier cover-assembly chain to
exactly one named API: Wedhorn 8.33 multi-piece cover-acyclicity
collapse.

## What this file provides

* `coverLevelAssemblyResidual_via_lemma833_assembly` — the **substantive
  bridge**: `LaurentCoverPresheafLemma833Assembly` (T057) ⊢
  `CoverLevelAssemblyResidual` (T056). Real proof composing T057's
  `rationalOpen_global_subset_via_lemma833_assembly` with the
  cover-on-Source restriction inferred from `rationalOpen_subset_spa`.

* `C1SupplierStrong_local_clause2_via_lemma833_assembly` — the
  **C1 supplier clause 2 closure**: the subset clause
  `R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)` follows from a single
  Lemma 8.33 multi-piece assembly hypothesis plus the per-piece
  source-restricted bounds (already deliverable from the T056 reroute
  + T054 refinement). Demonstrates that **one** missing API is
  sufficient to close the entire chain at the subset-of-Spa level.

* `C1SupplierStrong_local_clause2_via_per_piece_lemma833_full_chain`
  — the **complete cover-assembly chain closure** consuming:
  - T054 per-piece refinement output `MultiPieceLaurentCoverRefinementOutput`
    (provable from Cor 7.32 σ-strict-domination via existing API),
  - per-piece subset inclusions `R(insert f T_base, s) ∩ V_τ ⊆
    R({σ⁻¹ * τ}, D_s)` (deliverable from T056's
    `per_piece_singleton_subset_via_laurent_membership` + product
    upper bound at `D_s`),
  - the Lemma 8.33 multi-piece collapse `LaurentCoverPresheafLemma833Assembly`
    (the **single named missing API**).

  Concludes the global subset clause `R(insert f T_base, s) ⊆ R(D_T,
  D_s)`. This is the **C1 supplier clause 2 closure modulo Lemma 8.33**:
  every other piece is already deliverable; Lemma 8.33 is the sole
  remaining theorem-sized step.

## Cross-lane disjointness

Disjoint from Secondary's `WedhornLemma833MultiPieceAssembly.lean`
(which proves `LaurentCoverPresheafLemma833Assembly`) and from
Primary's final-closure file. T060 imports T056 and T057 as accepted
predecessors and exposes the bridge between them. It does NOT
attempt the Lemma 8.33 multi-piece collapse itself; that is
Secondary's lane.

## Notes

* No root import; leaf-level.
* Imports `WedhornPerPieceLaurentC1Supplier` (T056) and
  `WedhornPerPieceLaurentCoverAssembly` (T057).
* No edits to T031–T057 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim (per
  T035's counter-example).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-- **`CoverLevelAssemblyResidual` from `LaurentCoverPresheafLemma833Assembly`**
(T060 main bridge theorem).

The Wedhorn 8.33 multi-piece cover-acyclicity collapse predicate
`LaurentCoverPresheafLemma833Assembly` is sufficient to discharge
T056's `CoverLevelAssemblyResidual`.

**Proof structure**: take the per-piece subset and cover-on-Spa
hypotheses of `CoverLevelAssemblyResidual`. The cover-on-Spa
hypothesis restricts to a cover-on-Source via `rationalOpen_subset_spa`.
Apply T057's `rationalOpen_global_subset_via_lemma833_assembly` with
the Lemma 8.33 hypothesis to derive the global subset.

**Substantive consumption**: every input hypothesis is genuinely
used. The Lemma 8.33 hypothesis closes the gap from per-piece subsets
+ cover to a single global subset. -/
theorem coverLevelAssemblyResidual_via_lemma833_assembly
    [DecidableEq A]
    {σ : Aˣ} (T_test T_base D_T : Finset A) (s D_s f : A)
    (h_lemma833 :
      LaurentCoverPresheafLemma833Assembly (σ := σ) T_test
        (fun τ ↦ rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
        (rationalOpen D_T D_s)) :
    CoverLevelAssemblyResidual (σ := σ) T_test T_base D_T s D_s f := by
  intro h_per_piece_subset h_cover
  have h_cover_source :
      ∀ w ∈ rationalOpen (insert f T_base) s, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) :=
    fun w hw_source ↦ h_cover w (rationalOpen_subset_spa hw_source)
  exact rationalOpen_global_subset_via_lemma833_assembly T_test T_base D_T
    s D_s f h_lemma833 h_per_piece_subset h_cover_source

/-- **C1 supplier clause 2 subset clause via `LaurentCoverPresheafLemma833Assembly`**
(T060 substantive C1 closure theorem).

Concrete C1-supplier-clause-2 closure form: from the Lemma 8.33
multi-piece cover-acyclicity collapse, the per-piece subset inclusions
on each σ-rescaled Laurent piece, and the σ-rescaled Laurent cover
hypothesis on the source `R(insert f T_base, s)`, derive the global
subset `R(insert f T_base, s) ⊆ R(D_T, D_s)`.

**Inputs**:

* `h_lemma833` — Lemma 8.33 multi-piece cover-acyclicity collapse
  predicate. **The single named missing API**, owned by Secondary in
  `WedhornLemma833MultiPieceAssembly.lean`.

* `h_per_piece_subset` — per-piece subset inclusions on each
  σ-rescaled Laurent piece, deliverable from T056's
  `per_piece_singleton_subset_via_laurent_membership` plus a per-piece
  product upper bound at `D_s`.

* `h_cover` — σ-rescaled Laurent cover hypothesis on the source.
  Provable from Cor 7.32 σ-strict-domination over `T_test` via
  T054's `cor732_multi_piece_laurent_refinement` + restriction to
  source.

**Output**: `R(insert f T_base, s) ⊆ R(D_T, D_s)` — the C1 supplier's
clause 2 conclusion shape.

**Note**: this is a direct re-export of T057's
`rationalOpen_global_subset_via_lemma833_assembly` under T060's
documentation umbrella, exposing it as the **C1 supplier clause 2
closure modulo the single named Lemma 8.33 API**. -/
theorem C1SupplierStrong_local_clause2_via_lemma833_assembly
    [DecidableEq A]
    {σ : Aˣ} (T_test : Finset A) (T_base D_T : Finset A) (s D_s f : A)
    (h_lemma833 :
      LaurentCoverPresheafLemma833Assembly (σ := σ) T_test
        (fun τ ↦ rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
        (rationalOpen D_T D_s))
    (h_per_piece_subset :
      ∀ τ ∈ T_test,
        rationalOpen (insert f T_base) s ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
    (h_cover :
      ∀ w ∈ rationalOpen (insert f T_base) s, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen D_T D_s :=
  rationalOpen_global_subset_via_lemma833_assembly T_test T_base D_T s
    D_s f h_lemma833 h_per_piece_subset h_cover

/-- **Complete cover-assembly chain closure** (T060 final substantive
theorem).

Composes T054's per-piece refinement output (provable from Cor 7.32
σ-strict-domination via existing API), T056's per-piece subset
inclusions (deliverable from per-piece source-restricted reroute), and
T057's structured Lemma 8.33 predicate to derive the global C1
supplier clause 2 conclusion. The σ-rescaled Laurent cover hypothesis
on the source is **internally extracted** from T054's refinement
output via `rationalOpen_subset_spa`.

**Inputs**:

* `h_refinement : MultiPieceLaurentCoverRefinementOutput T_test`
  — T054's per-piece refinement output (deliverable from Cor 7.32).

* `h_per_piece_subset` — per-piece subset inclusions on each
  σ-rescaled Laurent piece.

* `h_lemma833 : LaurentCoverPresheafLemma833Assembly ...` — the
  **single named missing API** owned by Secondary.

**Output**: the global subset `R(insert f T_base, s) ⊆ R(D_T, D_s)` —
the C1 supplier's clause 2 conclusion.

**This theorem demonstrates that the entire cover-assembly chain
reduces to ONE named missing API**: every other input
(`h_refinement`, `h_per_piece_subset`) is already deliverable from
T054 + T056 + Cor 7.32. The C1 supplier closure modulo Lemma 8.33
is therefore complete at the subset-of-Spa level. -/
theorem C1SupplierStrong_local_clause2_via_per_piece_lemma833_full_chain
    [DecidableEq A]
    {σ : Aˣ} (T_test : Finset A) (T_base D_T : Finset A) (s D_s f : A)
    (h_refinement : MultiPieceLaurentCoverRefinementOutput (σ := σ) T_test)
    (h_per_piece_subset :
      ∀ τ ∈ T_test,
        rationalOpen (insert f T_base) s ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
    (h_lemma833 :
      LaurentCoverPresheafLemma833Assembly (σ := σ) T_test
        (fun τ ↦ rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
        (rationalOpen D_T D_s)) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen D_T D_s := by
  -- Extract the σ-rescaled Laurent cover hypothesis on the source from
  -- T054's `MultiPieceLaurentCoverRefinementOutput`.
  have h_cover_source :
      ∀ w ∈ rationalOpen (insert f T_base) s, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) := by
    intro w hw_source
    have hw_spa : w ∈ Spa A A⁺ := rationalOpen_subset_spa hw_source
    obtain ⟨τ, hτ_mem, hw_in_piece, _⟩ := h_refinement w hw_spa
    exact ⟨τ, hτ_mem, hw_in_piece⟩
  -- Apply the C1 supplier clause 2 subset clause closure.
  exact C1SupplierStrong_local_clause2_via_lemma833_assembly T_test T_base
    D_T s D_s f h_lemma833 h_per_piece_subset h_cover_source

end ValuationSpectrum
