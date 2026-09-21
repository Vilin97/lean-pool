/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornVKMaxElementComparisonDischarge

/-!
# Wedhorn 8.34(ii) — Base rational-subset comap residual via Wedhorn
7.45 base refinement (T048)

T047 (commit `a9dfc9a`) reduced the T046 max-element comparison residual
to a single source-restricted base rational-subset comap residual:

```
∀ w ∈ Spa(Loc s, ⁺), source-restrictions →
  comap (algebraMap A (Loc s)) w ∈ rationalOpen D.T D.s on Spa(A, A⁺)
```

This file lands the **Wedhorn 7.45 base refinement reduction** of
that residual: T047's comap residual follows from a single base
rational-open inclusion `rationalOpen (insert f C.base.T) C.base.s ⊆
rationalOpen D.T D.s` on `Spa(A, A⁺)` — the natural Wedhorn 7.45
cover-refinement statement — composed with the `locSubring` form
of `comap_mem_rationalOpen_iff` (`rationalOpen_transfer_via_
localization_locSubring`) to translate the source-restricted LHS
rationalOpen conditions on `w` to a base rationalOpen membership of
`comap w` in `R(insert f C.base.T, C.base.s)`.

## Proof outline (sole reduction step)

At every `w ∈ Spa(Loc s, ⁺)` satisfying the LHS rationalOpen
conditions for `(insert f T_base, s)` — i.e., per-`c` bound at
`algebraMap s` for `c ∈ insert f T_base` AND non-vanishing of
`algebraMap s` — the locSubring transfer
(`rationalOpen_transfer_via_localization_locSubring`) gives
`comap w ∈ rationalOpen (insert f T_base) s` on `Spa(A, A⁺)`. Apply
the base refinement inclusion `R(insert f T_base, s) ⊆ R(T_D, s_D)`
to obtain `comap w ∈ rationalOpen T_D s_D` on `Spa(A, A⁺)`.
Translate back to the localized side via `comap_vle` to extract the
per-`t` upper bound `∀ t ∈ T_D, w.vle (algMap t) (algMap s_D)` and
non-vanishing of `algMap s_D` — exactly T043's predicate
`WedhornCoverPieceCovPlusPieceLiftPerTBound`.

## What this file provides

* `WedhornCoverPieceCovPlusPieceLiftPerTBound_via_base_refinement`
  — the main discharge: T043's source-restricted comap-lift
  predicate follows from a single Wedhorn 7.45 base rational-open
  refinement inclusion. Uses
  `rationalOpen_transfer_via_localization_locSubring` for the
  LHS-to-comap direction and `comap_vle` for the RHS-to-localized
  translation.

* `C1SupplierStrong_local_via_Wedhorn745_refinement` — top-level C1
  supplier wrapper composing T048's discharge with T044's
  `C1SupplierStrong_local_via_cov_plus_piece_lift_supplier` (which
  consumes T043's predicate as `WedhornC1PerCallSupplyCovPlusPieceLift`'s
  central piece). Produces `C1SupplierStrong_local C` from per-call
  delivery of `f`, the base refinement inclusion, the rationalOpen
  membership of `v`, and `f`-non-degeneracy of `v`.

## Why this is the natural Wedhorn 7.45 reduction

The base rational-open inclusion `R(insert f T_base, s) ⊆ R(T_D, s_D)`
on `Spa(A, A⁺)` IS Wedhorn 7.45's exact cover-refinement statement.
T048 reduces the entire T044 → T045 → T046 → T047 chain residuals
to this single base-side statement, exposing the actual Wedhorn 7.45
cover-refinement deduction as the sole remaining mathematical
content for the C1 supplier.

The reduction is **not source-restricting**: it preserves T043's
LHS-restricted predicate and exposes the base inclusion as the
single Wedhorn 7.45 residual. The reduction is also strictly closer
to Wedhorn 7.45 than T047's comap residual: T047's residual is at
the localized side conditioned on σ-construction premises; T048's
residual is at the **base** side, **without** σ-construction
premises, matching Wedhorn 7.45's exact statement.

## Notes

* No root import; leaf-level.
* Imports only `WedhornVKMaxElementComparisonDischarge` (T047, commit
  `a9dfc9a`), which transitively brings in
  `rationalOpen_transfer_via_localization_locSubring`, T043's
  predicate, and the `comap_vle` / `rationalOpen` API.
* No edits to T031–T047 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* The reduction REQUIRES the additional standing hypothesis
  `(A⁺ : Set A) ⊆ P.A₀` (the converse direction to the C1 supplier's
  `P.A₀ ≤ A⁺`), needed by `localizationLocSubring_aplus_le_comap`.
  In Wedhorn-Tate rings this gives `A⁺ = A₀` (the standard setting).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Discharge of T043's source-restricted comap-lift predicate from
Wedhorn 7.45 base refinement** (T048 main theorem).

From a base rational-open refinement inclusion
`rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D` on
`Spa(A, A⁺)` (Wedhorn 7.45's exact cover-refinement statement),
derive T043's source-restricted comap-lift predicate
`WedhornCoverPieceCovPlusPieceLiftPerTBound`.

**Proof**: take `w ∈ Spa(Loc s, locSubring)` satisfying the LHS
rationalOpen conditions for `(insert f T_base, s)` (per-`c` bound
at `algebraMap s` for `c ∈ insert f T_base` AND non-vanishing of
`algebraMap s`). The locSubring transfer
(`rationalOpen_transfer_via_localization_locSubring`) gives
`comap (algebraMap A _) w ∈ rationalOpen (insert f T_base) s` on
`Spa(A, A⁺)`. Apply the base refinement inclusion: `comap w ∈
rationalOpen T_D s_D`. Unfold `rationalOpen` to extract the per-`t`
bound `∀ t ∈ T_D, comap w.vle t s_D` and non-vanishing
`¬ comap w.vle s_D 0`. Translate via `comap_vle` to get the
localized per-`t` bound and non-vanishing required by T043's
predicate.

The base refinement inclusion `h_base_refinement` is the **single
named non-tautological residual** — exactly Wedhorn 7.45's
cover-refinement statement at the base. -/
theorem WedhornCoverPieceCovPlusPieceLiftPerTBound_via_base_refinement
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (T_base T_D : Finset A) (s_D : A) (f : A)
    (h_base_refinement :
      rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D) :
    WedhornCoverPieceCovPlusPieceLiftPerTBound P T s hopen
      T_base T_D s_D f := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro w hw_spa hw_LHS hw_s_ne
  -- Apply locSubring transfer at (insert f T_base, s) to get comap w ∈ R(insert f T_base, s).
  have h_comap_in :
      comap (algebraMap A (Localization.Away s)) w ∈
        rationalOpen (insert f T_base) s := by
    rw [rationalOpen_transfer_via_localization_locSubring P T s hopen
        hAplus_le_A₀ (insert f T_base) s hw_spa]
    exact ⟨hw_LHS, hw_s_ne⟩
  -- Apply base refinement inclusion.
  have h_comap_RHS :
      comap (algebraMap A (Localization.Away s)) w ∈ rationalOpen T_D s_D :=
    h_base_refinement h_comap_in
  -- Unfold rationalOpen to extract per-t bound + non-vanishing on the base side.
  obtain ⟨_hw_spa_base, h_per_t_base, h_s_D_ne_base⟩ := h_comap_RHS
  -- Translate to localized side via comap_vle.
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · have h_comap_t : (comap (algebraMap A (Localization.Away s)) w).vle t s_D :=
      h_per_t_base t ht
    rwa [comap_vle] at h_comap_t
  · intro hw_s_D
    apply h_s_D_ne_base
    rw [comap_vle, map_zero]
    exact hw_s_D

/-- **Top-level: `C1SupplierStrong_local C` via Wedhorn 7.45 base
refinement** (T048 final deliverable).

Caller theorem producing `C1SupplierStrong_local C` from per-call
delivery of `f`, the base refinement inclusion (Wedhorn 7.45's
cover-refinement statement), the rationalOpen membership of `v`,
and `f`-non-degeneracy of `v`. Composes T048's discharge with
T044's `C1SupplierStrong_local_via_cov_plus_piece_lift_supplier`.

**The single named non-tautological residual** is
`h_base_refinement : rationalOpen (insert f C.base.T) C.base.s ⊆
rationalOpen D.T D.s` — Wedhorn 7.45's exact cover-refinement
statement at the base `Spa(A, A⁺)`. All max-element, per-`t`
upper-bound, V_K-nonempty, and σ-construction residuals from
T044–T047 are dispatched via this single base inclusion.

This is the **shortest path** from the C1 supplier's per-call
input to the canonical Wedhorn 7.45 base statement. -/
theorem C1SupplierStrong_local_via_Wedhorn745_refinement
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_components :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (f : A),
        rationalOpen (insert f C.base.T) C.base.s ⊆
            rationalOpen D.T D.s ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_cov_plus_piece_lift_supplier
    P hA₀_le C hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨f, h_base_refinement, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  refine ⟨f, ?_, hv_in_plus, hvf_nz⟩
  exact WedhornCoverPieceCovPlusPieceLiftPerTBound_via_base_refinement
    P C.base.T C.base.s hopen_base hAplus_le_A₀ C.base.T D.T D.s f
    h_base_refinement

end ValuationSpectrum
