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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStrengthenedC1
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornNormalizedC1Assembly
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedMultiPieceLaurentRefinement

/-!
# Strong-supplier insertDenom-lift bridge

The downstream Wedhorn 8.34(ii) assembly chain consumes
`C1SupplierStrong_local C.insertDenom` (e.g.,
`WedhornBaseSpaFinalBridgeStrong.lean:98`,
`WedhornNormalizedC1AssemblyStrong.lean:105`). This file lands the
**structural lift** from `C1SupplierStrong_local C` to
`C1SupplierStrong_local C.insertDenom`, the largest compileable
theorem-level bridge toward producing the strong supplier on the
normalized cover from one on the original.

## Why this lift

`C.insertDenom`'s pieces have `D.s ∈ D.T` (the normalization). The
downstream consumers
(`WedhornStrengthenedC1.exists_single_f_refining_point_in_D_via_C1SupplierStrong`,
`WedhornNormalizedC1AssemblyStrong.exists_per_D_finset_via_normalized_C1Strong_supplier`)
exploit this normalization. But producing
`C1SupplierStrong_local C.insertDenom` directly from Tate hypotheses
requires the full Wedhorn 8.34(ii) σ-construction (still external; see
`WedhornStandardCoverRefinement.lean:91` target signature). The
structural lift here turns an abstract `C1SupplierStrong_local C`
(potentially supplied by Tertiary) into the consumer-ready form on the
normalized cover, modulo the mild non-emptiness hypothesis on cover-piece
test families documented below.

## What this file provides

`C1SupplierStrong_local_insertDenom_lift` — given:

1. `C1SupplierStrong_local C` — abstract strong supplier on the original
   cover.
2. `h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty` — every cover-piece
   test family is non-empty (mild restriction; cover pieces with
   `D.T = ∅` are basic-opens-at-`D.s`, an unusual degenerate case).

Produces `C1SupplierStrong_local C.insertDenom`, the consumer-ready
strong supplier on the normalized cover.

## Why the non-emptiness hypothesis

For `D ∈ C.covers` with `D.T = ∅`: the corresponding `D.insertDenom`
has `D.insertDenom.T = {D.s}` (non-empty), and the strong supplier on
`C.insertDenom` would receive `t = D.s` as the test element. There is
no element of `D.T` to substitute in the underlying
`C1SupplierStrong_local C` call (which requires `t ∈ D.T`), so the
`D.T = ∅` case is uncovered by this lift. The hypothesis
`h_covers_nonempty` rules out this degenerate subcase, which is harmless
for typical rational coverings.

## Documented residual: producing `C1SupplierStrong_local C` from Tate hypotheses

The genuine remaining work toward Wedhorn 8.34(ii) is producing
`C1SupplierStrong_local C` from concrete Tate/noetherian/pseudouniformizer
hypotheses. The exact missing target signature is:

```
theorem produce_C1SupplierStrong_local_via_Wedhorn_834
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCoveringData A)
    -- Localization-topology openness data for the rational-open transfer
    -- (`rationalOpen_transfer_via_localization`):
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s) :
    C1SupplierStrong_local C
```

The proof would (canonically) proceed via:
1. Pre-localise `A` at `C.base.s` to obtain `(A_loc, A_loc⁺_image)`
   (`localizationAwayPlusSubring`).
2. Apply `Cor732.exists_dominating_unit` inside
   `Spa(A_loc, A_loc⁺_image)` (where `C.base.s` is invertible, so the
   test family is unconstrained) to extract `σ_loc : (A_loc)ˣ`.
3. Clear denominators: `σ_loc * (algebraMap C.base.s)^M = algebraMap σ`
   for some `σ : A` and `M : ℕ`.
4. Set `f := σ * t * D.s ^ N` per Wedhorn's construction.
5. Verify the three C1 clauses via `rationalOpen_transfer_via_localization`
   plus the σ-domination output.

Steps 2-5 are the genuinely Wedhorn 8.34(ii)-specific content; this
file's structural lift is independent of them.

## Notes

* No root import; leaf-level file.
* No edits to `WedhornStrengthenedC1.lean`,
  `WedhornCoverNormalization.lean`, `WedhornNormalizedC1Assembly.lean`,
  or any other Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness
  / final-acyclicity file.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Structural lift: `C1SupplierStrong_local C → C1SupplierStrong_local
C.insertDenom`** (mod cover-piece non-emptiness).

Given an abstract strong C1 supplier on the original cover `C` plus the
mild non-emptiness condition `∀ D ∈ C.covers, D.T.Nonempty`, the lift to
the normalized cover `C.insertDenom` is straightforward: invoke the
supplier on the underlying `D` (using a substitute test element from
`D.T`) and translate the rational-open clauses through the
`rationalOpen_insertDenom` and `rationalOpen_insert_base_insertDenom_eq`
identities. The conclusion's `f` is independent of `t` (only depends on
`D` and `v`), so the substitution is invisible to the user.

**Use case**: feed this into
`WedhornNormalizedC1AssemblyStrong.exists_per_D_finset_via_normalized_C1Strong_supplier`
and onward into `WedhornBaseSpaFinalBridgeStrong`. -/
theorem C1SupplierStrong_local_insertDenom_lift
    [DecidableEq A] (C : RationalCoveringData A)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1 : C1SupplierStrong_local C) :
    C1SupplierStrong_local C.insertDenom := by
  classical
  intro D' hD' v hv t _ht _hvt hvD_s
  -- D' = D.insertDenom for some D ∈ C.covers.
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hD'
  -- Pick a substitute test element from D.T (non-empty by hypothesis).
  obtain ⟨t', ht'_mem⟩ := h_covers_nonempty D hD
  -- Translate hypotheses on D.insertDenom back to D.
  rw [RationalLocData.rationalOpen_insertDenom] at hv
  rw [RationalLocData.insertDenom_s] at hvD_s
  -- Inputs to the underlying supplier on C, using t' ∈ D.T.
  have hvt' : v.vle t' D.s := hv.2.1 t' ht'_mem
  obtain ⟨f, hv_in, hsub, hnonzero⟩ :=
    h_C1 D hD v hv t' ht'_mem hvt' hvD_s
  refine ⟨f, ?_, ?_, hnonzero⟩
  · -- v ∈ rationalOpen (insert f C.insertDenom.base.T) C.insertDenom.base.s
    rw [rationalOpen_insert_base_insertDenom_eq]
    exact hv_in
  · -- subset translation
    rw [rationalOpen_insert_base_insertDenom_eq,
      RationalLocData.rationalOpen_insertDenom]
    exact hsub

/-! ### T178: produce `C1SupplierStrong_local C` via T177's per-call localized
multi-piece supply

T177 (commit `09a84d9`,
`WedhornLocalizedMultiPieceLaurentRefinement.lean`) provides
`C1SupplierStrong_local_via_localized_multi_piece_data`, which produces
`C1SupplierStrong_local C` from per-call delivery of
`WedhornC1PerCallSupplyLocalizedMultiPiece` — the natural Wedhorn
cover-piece structural data (cover-refinement element identity,
cover-base factorization, ring-of-definition membership, source-side
clauses).

This section attacks the documented residual
`produce_C1SupplierStrong_local_via_Wedhorn_834` by lowering it to
T177's clean per-call supply boundary.

**Status: caller-facing reduction (acceptable fallback)**. The full
discharge from concrete Tate / pseudouniformizer hypotheses to the
per-call supply requires the Wedhorn 8.34(ii) σ-construction
(localized Cor 7.32 σ-strict-dominating unit, denominator-clearing
construction `f := σ · t · D.s ^ N`, and source-side rational-open
membership transfer) — the genuinely missing per-call structural
producer. T178's reduction theorem isolates that per-call producer
as the single open input.

Provided:

* `produce_C1SupplierStrong_local_via_Wedhorn_834_via_per_call_supply` —
  caller-facing reduction theorem. Takes the natural cover-base
  structural data (`P`, `hA₀_le`, `C`, `hopen_base`) plus T177's
  `WedhornC1PerCallSupplyLocalizedMultiPiece` per-call supply, and
  produces `C1SupplierStrong_local C` via
  `C1SupplierStrong_local_via_localized_multi_piece_data`.

The Tate / noetherian / pseudouniformizer hypotheses listed in the
documented residual signature are not required by this reduction —
they belong to a future per-call supply producer (Wedhorn 8.34(ii)
σ-construction at the per-call level), which is outside T178's scope. -/

/-- **T178 caller-facing reduction**: produce `C1SupplierStrong_local C`
from T177's per-call localized multi-piece supply.

Reduces the documented residual
`produce_C1SupplierStrong_local_via_Wedhorn_834` (in this file's
docstring) to T177's clean per-call boundary
`WedhornC1PerCallSupplyLocalizedMultiPiece`. The per-call supply is
the **genuine missing per-call structural producer**: the Wedhorn
8.34(ii) σ-construction packaged as `(σ_loc, f, h_alg, h_s_factor,
hT_D_le_A₀, hv_in_plus, hvf_nz)` per `(D, v, t)`. Its discharge from
concrete Tate / pseudouniformizer hypotheses is the next theorem-level
ticket beyond T178.

Composition: applies
`C1SupplierStrong_local_via_localized_multi_piece_data` (T177).
Clauses 1, 2, 3 of `C1SupplierStrong_local` are dispatched through
T172/T173/T175/T176 producers internally to T177; T178 only handles
the per-call delivery layer. -/
theorem produce_C1SupplierStrong_local_via_Wedhorn_834_via_per_call_supply
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_supply :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1PerCallSupplyLocalizedMultiPiece P C hopen_base D v) :
    C1SupplierStrong_local C :=
  C1SupplierStrong_local_via_localized_multi_piece_data
    P hA₀_le C hopen_base h_per_call_supply

/-! ### T179: per-call localized multi-piece supply producer

T178 (commit `d33b428`, this file) reduces the documented residual
`produce_C1SupplierStrong_local_via_Wedhorn_834` to T177's per-call
boundary `WedhornC1PerCallSupplyLocalizedMultiPiece`. T179 attacks the
**per-call producer** itself: how to construct that supply from
concrete Wedhorn 8.34(ii) Tate setup data.

**Decomposition of the per-call supply**:

The 8 fields of `WedhornC1PerCallSupplyLocalizedMultiPiece`:
* (1) `σ_loc : (Loc C.base.s)ˣ`,
* (2) `f : A`,
* (3) `hσ_loc_dom` — σ-strict-dom over `localizedTestFamily`,
* (4) `h_alg` — `algebraMap f = σ_loc · ∏ D.T.image`,
* (5) `h_s_factor` — `C.base.s = D.s · f`,
* (6) `hT_D_le_A₀` — `∀ t ∈ D.T, t ∈ P.A₀`,
* (7a) `hv_in_plus` — `v ∈ rationalOpen (insert f C.base.T) C.base.s`,
* (7b) `hvf_nz` — `¬ v.vle f 0`,

split naturally into:

* **Cover structural data**: `hT_covers_le_A₀ : ∀ D ∈ C.covers, ∀ t ∈ D.T, t ∈ P.A₀`
  — a cover-piece structural condition not present in
  `RationalCoveringData`'s definition; must be supplied explicitly.

* **σ/denominator/factorization construction (the genuinely missing
  per-call structural lemma)**: at each per-call `(D, v, t)`, construct
  `σ_loc, f` together with `hσ_loc_dom`, `h_alg`, `h_s_factor`,
  `hv_in_plus`, `hvf_nz`. This is Wedhorn 8.34(ii)'s explicit
  σ-construction `f := σ · t · D.s ^ N`, with σ chosen via
  `Cor732.exists_dominating_unit` (the localized
  `exists_dominating_unit_in_localization` API requires lifting the
  global pseudouniformizer `π : P.A₀` to a localized `π_loc` plus the
  Tate transfer of pseudouniformizer hypotheses; that lifting is the
  inner content of the missing structural lemma).

**T179 deliverable shape (acceptable fallback)**: a compiled,
caller-facing per-call reduction theorem that names
`h_dom_factorization` (the σ/denominator/factorization construction)
as the genuinely missing structural lemma and consumes
`hT_D_le_A₀` from the cover structural data, producing the per-call
`WedhornC1PerCallSupplyLocalizedMultiPiece`. A top-level theorem
composes with T178 to produce `C1SupplierStrong_local C`.

Provided:

* `produce_WedhornC1PerCallSupplyLocalizedMultiPiece_via_factorization_and_dom_supply`
  — per-call reduction theorem.
* `produce_C1SupplierStrong_local_via_Wedhorn_834_via_factorization_and_dom_supply`
  — top-level theorem composing the per-call reduction with T178. -/

/-- **T179 per-call reduction**: produce
`WedhornC1PerCallSupplyLocalizedMultiPiece P C hopen_base D v` from
the σ/denominator/factorization construction supplier plus the
cover-piece structural hypothesis `hT_D_le_A₀`.

The construction supplier `h_dom_factorization` packages five of the
six per-call fields:

* `σ_loc, f` (the constructed unit and cover-refinement element);
* `hσ_loc_dom`, `h_alg`, `h_s_factor` (Wedhorn cover-piece factorization
  identities);
* `hv_in_plus`, `hvf_nz` (source-side rational-open transfer).

The remaining `hT_D_le_A₀` is supplied separately as a cover-piece
structural hypothesis (the natural Wedhorn `D.T ⊆ P.A₀` condition;
explicitly required since `RationalCoveringData` does not embed it).

This is the **first compiled boundary** for the per-call supply
construction: the manageable inputs are isolated as cover structural
data, and the genuinely Wedhorn 8.34(ii)-specific content is named
exactly as the σ/denominator/factorization construction supplier. -/
theorem produce_WedhornC1PerCallSupplyLocalizedMultiPiece_via_factorization_and_dom_supply
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A)
    (hT_D_le_A₀ : ∀ τ ∈ D.T, τ ∈ P.A₀)
    (h_dom_factorization :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
        (∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
            ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
              w.vle (σ_loc : Localization.Away C.base.s) τ ∧
                ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
        (algebraMap A (Localization.Away C.base.s) f =
          (σ_loc : Localization.Away C.base.s) *
            (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)),
              τ)) ∧
        C.base.s = D.s * f ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    WedhornC1PerCallSupplyLocalizedMultiPiece P C hopen_base D v := by
  obtain ⟨σ_loc, f, hσ_dom, h_alg, h_s_factor, hv_in, hvf_nz⟩ :=
    h_dom_factorization
  exact ⟨σ_loc, f, hσ_dom, h_alg, h_s_factor, hT_D_le_A₀, hv_in, hvf_nz⟩

/-- **T179 top-level reduction**: produce `C1SupplierStrong_local C`
from per-call σ/denominator/factorization construction supplier plus
cover-piece structural data, composing T179's per-call reduction with
T178's caller-facing reduction.

**Inputs**:
* `P`, `hA₀_le`, `C`, `hopen_base` — natural cover-base structural data.
* `hT_covers_le_A₀ : ∀ D ∈ C.covers, ∀ t ∈ D.T, t ∈ P.A₀` —
  cover-piece structural condition (the natural Wedhorn `D.T ⊆ P.A₀`
  condition; explicit since `RationalCoveringData` does not embed it).
* `h_per_call_construction` — per-call σ/denominator/factorization
  construction supplier (the genuinely missing Wedhorn 8.34(ii) per-call
  structural lemma).

**Output**: `C1SupplierStrong_local C`.

After T179, the documented residual
`produce_C1SupplierStrong_local_via_Wedhorn_834` is reduced to a single
named per-call structural lemma `h_per_call_construction` plus the
cover structural hypothesis. The Wedhorn 8.34(ii) σ-construction at
the per-call level is the only remaining input. -/
theorem produce_C1SupplierStrong_local_via_Wedhorn_834_via_factorization_and_dom_supply
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (hT_covers_le_A₀ : ∀ D ∈ C.covers, ∀ τ ∈ D.T, τ ∈ P.A₀)
    (h_per_call_construction :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
          (∀ w ∈ Spa (Localization.Away C.base.s)
                (Localization.Away C.base.s)⁺,
              ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
                w.vle (σ_loc : Localization.Away C.base.s) τ ∧
                  ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
          (algebraMap A (Localization.Away C.base.s) f =
            (σ_loc : Localization.Away C.base.s) *
              (∏ τ ∈ D.T.image
                (algebraMap A (Localization.Away C.base.s)), τ)) ∧
          C.base.s = D.s * f ∧
          v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
          ¬ v.vle f 0) :
    C1SupplierStrong_local C :=
  produce_C1SupplierStrong_local_via_Wedhorn_834_via_per_call_supply
    P hA₀_le C hopen_base
    (fun D hD v hv t ht hvt hvD_s =>
      produce_WedhornC1PerCallSupplyLocalizedMultiPiece_via_factorization_and_dom_supply
        P C hopen_base D v (hT_covers_le_A₀ D hD)
        (h_per_call_construction D hD v hv t ht hvt hvD_s))

/-! ### T180: σ-strict-domination supplier via `exists_dominating_unit_in_localization`

T179's per-call construction supplier `h_per_call_construction` packages
together five outputs:

* `σ_loc, hσ_loc_dom` — the localized Cor 7.32 σ-strict-domination unit;
* `f, h_alg, h_s_factor` — Wedhorn 8.34(ii) cover-refinement element
  `f := σ · t · D.s ^ N` with N chosen via denominator clearing;
* `hv_in_plus, hvf_nz` — source-side rational-open transfer for `v`.

T180 lands the **first real mathematical component** of this bundle:
the σ-strict-domination output, by **direct application** of the
existing `exists_dominating_unit_in_localization` API (in
`Adic spaces/WedhornLocalizedCor732Application.lean:87`) at the
canonical localized test family `localizedTestFamily C.base.s D.T D.s`.

**Inputs**: the localized pseudouniformizer data
`(π_loc, hI_loc, hπ_loc_tn, hπ_loc_unit, hArch_loc)` — these are the
**localized** versions of the global Tate hypotheses
`(π, hI, hπ_tn, hπ_unit, hArch)` from the documented T178 residual
signature; lifting global → localized is the deferred Tate-side
content (see e.g.
`Adic spaces/WedhornLocalizedCor732Application.lean`'s docstring).
The non-vanishing supplier `hT_loc_ne` for
`localizedTestFamily C.base.s D.T D.s` is also taken as input;
deriving it from the cover plus-piece structure is a separate
structural lemma.

**Output**: `σ_loc + hσ_loc_dom` — the first two of T179's five
construction outputs.

**Next missing piece** for T179's full per-call construction
supplier (after T180):

* **Denominator-clearing / `f` construction**: given `σ_loc` from
  T180 + `(D, v, t)`, produce `f : A` with
  `algebraMap f = σ_loc · ∏ D.T.image (algebraMap)` and
  `C.base.s = D.s · f`. Wedhorn 8.34(ii)'s explicit construction
  is `f := σ · t · D.s ^ (N - 1)` for some `σ : A` lifting `σ_loc`
  modulo the localization and `N : ℕ` chosen large enough to clear
  denominators. The σ ↦ σ_loc lifting is non-trivial: σ_loc lives
  in `(Loc C.base.s)ˣ`, and σ : A would need
  `algebraMap σ = σ_loc · (algebraMap C.base.s)^M` for some M.

* **Source-side transfer**: with `f` constructed, derive
  `v ∈ rationalOpen (insert f C.base.T) C.base.s` from `v`'s
  rational-open membership in `D` and the f-construction; derive
  `¬ v.vle f 0` from `f`'s explicit form. -/

/-- **T180 σ-strict-domination supplier** (first real component of
T179's per-call construction supplier).

Applies `exists_dominating_unit_in_localization` at the canonical
localized test family `localizedTestFamily C.base.s D.T D.s` to
produce the σ-strict-dominating unit `σ_loc : (Loc C.base.s)ˣ` with
the per-`w` strict-domination output consumed by T177/T179.

The localized pseudouniformizer data `(π_loc, hI_loc, hπ_loc_tn,
hπ_loc_unit, hArch_loc)` is supplied as explicit hypotheses; lifting
from the global `(π, hI, hπ_tn, hπ_unit, hArch)` of the documented
T178 residual is the deferred Tate-side construction. The
non-vanishing supplier `hT_loc_ne` for the localized test family is
also supplied as a hypothesis.

This delivers exactly the σ-strict-domination subset of T179's
construction bundle — the first real mathematical component
discharged from existing API. The remaining `(f, h_alg, h_s_factor,
hv_in_plus, hvf_nz)` components require the Wedhorn 8.34(ii)
denominator-clearing construction, which is the next theorem-level
ticket. -/
theorem wedhorn_834_per_call_dom_supplier
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    ∀ (π_loc : (locPairOfDefinition P C.base.T C.base.s hopen_base).A₀)
      (_hI_loc : (locPairOfDefinition P C.base.T C.base.s hopen_base).I =
        Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P C.base.T C.base.s hopen_base).A₀.subtype
          π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P C.base.T C.base.s hopen_base).A₀.subtype
          π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away C.base.s),
        letI : ValuativeRel (Localization.Away C.base.s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero
          (Localization.Away C.base.s)))
      (_hT_loc_ne :
        ∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s, ¬ w.vle τ 0),
      ∃ σ_loc : (Localization.Away C.base.s)ˣ,
        ∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
              ¬ w.vle τ (σ_loc : Localization.Away C.base.s) := by
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc hT_loc_ne
  exact exists_dominating_unit_in_localization P C.base.T C.base.s hopen_base
    π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc
    (localizedTestFamily C.base.s D.T D.s) hT_loc_ne

/-! ### T181: localized test-family non-vanishing supplier from `α D.s`

T180 takes the per-`w` non-vanishing supplier `hT_loc_ne` for
`localizedTestFamily C.base.s D.T D.s` as an explicit input. T181 lands
the natural reduction: from the simpler per-cover non-vanishing
hypothesis `h_α_D_s_ne` (asserting `¬ w.vle (algebraMap D.s) 0` at every
`w ∈ Spa(Loc C.base.s, ⁺)`), produce the localized test-family
non-vanishing supplier.

The reduction picks `τ := algebraMap A (Loc C.base.s) D.s` (always in
`localizedTestFamily C.base.s D.T D.s` via `Finset.mem_insert_self`)
and forwards the per-cover non-vanishing hypothesis at each `w`.

This isolates the **α D.s non-vanishing** as the weakest cover-piece
structural hypothesis sufficient to discharge `hT_loc_ne` at the T180
boundary. The full discharge of `h_α_D_s_ne` from concrete cover data
(e.g., from `D.s ∈ A` being a unit modulo the localization, or from
the per-`w` rational-open / valuative restriction structure) is a
separate cover-piece structural lemma; deriving it from existing
codebase APIs requires the localized rational-open transfer
(see `WedhornStrengthenedC1` / `rationalOpen_transfer_via_localization`),
which is outside T181's scope.

Provided:

* `wedhorn_834_localizedTestFamily_nonvanishing_supplier` — produces
  the T180 `hT_loc_ne` shape from `h_α_D_s_ne`.

* `wedhorn_834_per_call_dom_supplier_via_α_D_s_ne` — caller composing
  T181's supplier with T180's `wedhorn_834_per_call_dom_supplier`. -/

/-- **T181 localized test-family non-vanishing supplier**.

Produces the T180 `hT_loc_ne` hypothesis shape from the simpler
per-cover non-vanishing condition `h_α_D_s_ne`: at every
`w ∈ Spa(Loc C.base.s, ⁺)`, `¬ w.vle (algebraMap D.s) 0`.

**Proof**: at each `w`, return `τ := algebraMap A (Loc C.base.s) D.s`
(in `localizedTestFamily C.base.s D.T D.s` by `Finset.mem_insert_self`,
since `localizedTestFamily = insert (algebraMap D.s) (D.T.image (algebraMap))`),
with the supplied non-vanishing witness.

This is a strict reduction: the multi-element `localizedTestFamily`
non-vanishing reduces to the single-element α D.s non-vanishing — the
weakest sufficient cover-piece structural condition. -/
theorem wedhorn_834_localizedTestFamily_nonvanishing_supplier
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    ∀ (_h_α_D_s_ne :
        ∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
          ¬ w.vle (algebraMap A (Localization.Away C.base.s) D.s) 0),
      ∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s, ¬ w.vle τ 0 := by
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  intro h_α_D_s_ne w hw_spa
  refine ⟨algebraMap A (Localization.Away C.base.s) D.s, ?_,
    h_α_D_s_ne w hw_spa⟩
  unfold localizedTestFamily
  exact Finset.mem_insert_self _ _

/-- **T181 caller**: σ-strict-domination supplier with the localized
test-family non-vanishing hypothesis discharged from α D.s
non-vanishing.

Composes T181's `wedhorn_834_localizedTestFamily_nonvanishing_supplier`
with T180's `wedhorn_834_per_call_dom_supplier`, producing the
σ-strict-dominating unit + per-`w` strict-domination output from:

* localized pseudouniformizer data (`π_loc`, `hI_loc`, `hπ_loc_tn`,
  `hπ_loc_unit`, `hArch_loc`) — same as T180;
* `h_α_D_s_ne` — per-`w` non-vanishing of `algebraMap D.s` (cover-piece
  structural condition).

After T181, the remaining inputs for the σ-strict-domination supplier
beyond standard pseudouniformizer data are reduced to the cleanest
per-cover non-vanishing condition on α D.s. -/
theorem wedhorn_834_per_call_dom_supplier_via_α_D_s_ne
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    ∀ (π_loc : (locPairOfDefinition P C.base.T C.base.s hopen_base).A₀)
      (_hI_loc : (locPairOfDefinition P C.base.T C.base.s hopen_base).I =
        Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P C.base.T C.base.s hopen_base).A₀.subtype
          π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P C.base.T C.base.s hopen_base).A₀.subtype
          π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away C.base.s),
        letI : ValuativeRel (Localization.Away C.base.s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero
          (Localization.Away C.base.s)))
      (_h_α_D_s_ne :
        ∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
          ¬ w.vle (algebraMap A (Localization.Away C.base.s) D.s) 0),
      ∃ σ_loc : (Localization.Away C.base.s)ˣ,
        ∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
              ¬ w.vle τ (σ_loc : Localization.Away C.base.s) := by
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc h_α_D_s_ne
  exact wedhorn_834_per_call_dom_supplier P C hopen_base D
    π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc
    (wedhorn_834_localizedTestFamily_nonvanishing_supplier
      P C hopen_base D h_α_D_s_ne)

/-! ### T182: α D.s non-vanishing from base factorization `C.base.s = D.s · f`

T181 reduces the localized test-family non-vanishing input at the T180
boundary to the per-`w` non-vanishing of `algebraMap D.s`. T182
discharges this directly from the natural Wedhorn cover-base
factorization `h_s_factor : C.base.s = D.s · f` (the same factorization
already consumed by T173/T176 for the α_T_D / α_s_D branch closures).

**Math**:
* `algebraMap A (Loc C.base.s) C.base.s` is a **unit** in
  `Loc C.base.s` (by `IsLocalization.Away.algebraMap_isUnit`, since
  `C.base.s` is inverted there).
* By `h_s_factor` and `RingHom.map_mul`,
  `algebraMap C.base.s = algebraMap D.s · algebraMap f`.
* So `algebraMap D.s · algebraMap f` is a unit in `Loc C.base.s`.
* In a commutative monoid, the **left factor of a unit product is a
  unit** (`isUnit_of_mul_isUnit_left`); hence `algebraMap D.s` is a
  unit.
* Units in commutative rings are non-vanishing at every valuation
  (`not_vle_zero_of_isUnit`), so `¬ w.vle (algebraMap D.s) 0` at
  every `w ∈ Spa(Loc C.base.s, ⁺)`.

Provided:

* `wedhorn_834_alpha_D_s_nonvanishing_of_base_factorization` —
  produces the per-`w` `α D.s` non-vanishing from `h_s_factor` alone.

* `wedhorn_834_per_call_dom_supplier_via_base_factorization` —
  caller composing T182 with T181's
  `wedhorn_834_per_call_dom_supplier_via_α_D_s_ne`, producing the
  σ-strict-domination output from localized pseudouniformizer data
  + `h_s_factor`. -/

/-- **T182 α D.s non-vanishing from base factorization**.

From the natural Wedhorn cover-base factorization
`h_s_factor : C.base.s = D.s * f` and the unit-of-product factorization,
derive `¬ w.vle (algebraMap A (Loc C.base.s) D.s) 0` at every
`w ∈ Spa(Loc C.base.s, ⁺)`.

**Proof**: `algebraMap C.base.s` is a unit in `Loc C.base.s` (since
`C.base.s` is inverted); by `h_s_factor` + `map_mul`, this unit equals
`algebraMap D.s * algebraMap f`; `isUnit_of_mul_isUnit_left` extracts
the left-factor unit; `not_vle_zero_of_isUnit` gives non-vanishing at
every `w`. -/
theorem wedhorn_834_alpha_D_s_nonvanishing_of_base_factorization
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (f : A)
    (h_s_factor : C.base.s = D.s * f) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    ∀ w ∈ Spa (Localization.Away C.base.s)
          (Localization.Away C.base.s)⁺,
      ¬ w.vle (algebraMap A (Localization.Away C.base.s) D.s) 0 := by
  -- α C.base.s is a unit in Loc C.base.s (since C.base.s is inverted).
  have h_α_C_base_s_unit :
      IsUnit (algebraMap A (Localization.Away C.base.s) C.base.s) :=
    IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away C.base.s) C.base.s
  -- Lift h_s_factor through algebraMap (avoid motive failure on Loc C.base.s).
  have h_α_eq :
      algebraMap A (Localization.Away C.base.s) C.base.s =
        algebraMap A (Localization.Away C.base.s) (D.s * f) :=
    congr_arg (algebraMap A (Localization.Away C.base.s)) h_s_factor
  rw [h_α_eq, map_mul] at h_α_C_base_s_unit
  -- α D.s is the left factor of a unit product, hence a unit.
  have h_α_D_s_unit :
      IsUnit (algebraMap A (Localization.Away C.base.s) D.s) :=
    isUnit_of_mul_isUnit_left h_α_C_base_s_unit
  -- Non-vanishing at every w follows from unit-ness.
  intro w _hw_spa
  exact not_vle_zero_of_isUnit h_α_D_s_unit w

/-- **T182 caller**: σ-strict-domination supplier with α D.s
non-vanishing discharged from base factorization.

Composes T182's `wedhorn_834_alpha_D_s_nonvanishing_of_base_factorization`
with T181's `wedhorn_834_per_call_dom_supplier_via_α_D_s_ne`,
producing σ_loc + per-`w` strict-domination output from:

* localized pseudouniformizer data (`π_loc`, `hI_loc`, `hπ_loc_tn`,
  `hπ_loc_unit`, `hArch_loc`) — same as T180/T181;
* `h_s_factor : C.base.s = D.s * f` — the natural Wedhorn cover-base
  factorization (the same one consumed by T173/T176 for the
  α_T_D / α_s_D branch closures).

After T182, the σ-strict-domination supplier at the T180 boundary is
discharged from purely Tate-side localized pseudouniformizer data
plus the cover-base factorization — no remaining cover-piece
non-vanishing residual. -/
theorem wedhorn_834_per_call_dom_supplier_via_base_factorization
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (f : A)
    (h_s_factor : C.base.s = D.s * f) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    ∀ (π_loc : (locPairOfDefinition P C.base.T C.base.s hopen_base).A₀)
      (_hI_loc : (locPairOfDefinition P C.base.T C.base.s hopen_base).I =
        Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P C.base.T C.base.s hopen_base).A₀.subtype
          π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P C.base.T C.base.s hopen_base).A₀.subtype
          π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away C.base.s),
        letI : ValuativeRel (Localization.Away C.base.s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero
          (Localization.Away C.base.s))),
      ∃ σ_loc : (Localization.Away C.base.s)ˣ,
        ∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
              ¬ w.vle τ (σ_loc : Localization.Away C.base.s) := by
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc
  exact wedhorn_834_per_call_dom_supplier_via_α_D_s_ne P C hopen_base D
    π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc
    (wedhorn_834_alpha_D_s_nonvanishing_of_base_factorization
      P C hopen_base D f h_s_factor)

/-! ### T183: per-call construction packaging with `¬ v.vle f 0` from source-side

T182 supplies σ_loc + σ-strict-dom for the σ-strict-dom subset of T179's
per-call construction supplier, from `h_s_factor : C.base.s = D.s * f`
plus localized pseudouniformizer data. T183 attacks the **packaging**
of T179's six-clause per-call construction bundle, deriving the
**source-side `¬ v.vle f 0`** clause automatically from the
rational-open membership `v ∈ rationalOpen (insert f C.base.T) C.base.s`
and the cover-base factorization `h_s_factor : C.base.s = D.s * f`.

**Cycle-breaking analysis** (per the ticket's directive):

The σ-strict-dom subset of T179's bundle (T180/T181/T182 chain) and
the algebraic-factorization subset (clauses h_alg, h_s_factor) both
consume `h_s_factor` as a structural input. There is **no circular
dependency**: T183 takes `f`, `h_alg`, `h_s_factor`, σ_loc, σ-strict-dom,
and source-side `hv_in_plus` all as **explicit inputs**, packages them
into T179's existential bundle, and **derives** `¬ v.vle f 0` (the
sixth clause) from `hv_in_plus` + `h_s_factor`. The σ_loc in `h_alg`
matches the σ_loc supplied separately; T183 does not need to extract
σ_loc from T180/T181/T182's existential.

**Key algebraic content (cycle-breaking)**:

The lemma `not_vle_zero_left_of_mul_eq_of_not_vle_zero` derives
`¬ v.vle f 0` from `h_s_factor : C.base.s = D.s * f` and
`¬ v.vle (C.base.s) 0`: if `v.vle f 0`, then by `mul_vle_mul_right`
multiplying by `D.s` on the left, `v.vle (D.s * f) (D.s * 0) = 0`;
substituting `h_s_factor` gives `v.vle (C.base.s) 0`, contradicting
`hv_in_plus.2.2`. This is purely algebraic, no Wedhorn-specific
content — reusable as a standalone valuation identity.

**Source-side membership `hv_in_plus`** (`v ∈ rationalOpen (insert f
C.base.T) C.base.s`) is the genuinely missing per-call structural
input that T183 does not derive. Its discharge requires the Wedhorn
8.34(ii) f-construction `f := σ · t · D.s ^ (N-1)` plus per-call
verification that `v.vle f C.base.s` (cover refinement at `v`); this
is the next theorem-level ticket.

Provided:

* `not_vle_zero_left_of_mul_eq_of_not_vle_zero` — generic algebraic
  cycle-breaking lemma.

* `wedhorn_834_per_call_construction_via_factorization` — T183 main
  theorem packaging T179's six-clause per-call construction bundle
  with `¬ v.vle f 0` derived. -/

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Generic algebraic non-vanishing lemma**: from `c = a * b` and
`¬ v.vle c 0`, derive `¬ v.vle b 0`.

Proof: assume `v.vle b 0`; multiply on the left by `a` via
`ValuativeRel.mul_vle_mul_right` to get `v.vle (a * b) (a * 0) = 0`;
substituting `c = a * b` gives `v.vle c 0`, contradicting `¬ v.vle c 0`.

This is a reusable mathlib-style algebraic lemma — purely valuation
arithmetic, no Wedhorn-specific content. Applied at T183 to derive
`¬ v.vle f 0` from `h_s_factor : C.base.s = D.s * f` and the
denominator non-vanishing of `C.base.s` at `v` (the third component of
`v ∈ rationalOpen (insert f C.base.T) C.base.s`). -/
theorem not_vle_zero_left_of_mul_eq_of_not_vle_zero
    (v : Spv A) {a b c : A}
    (h_eq : c = a * b)
    (h_c_ne : ¬ v.vle c 0) :
    ¬ v.vle b 0 := by
  intro h_b_zero
  apply h_c_ne
  rw [h_eq]
  letI : ValuativeRel A := v.toValuativeRel
  have h_step : v.vle (a * b) (a * 0) :=
    ValuativeRel.mul_vle_mul_right h_b_zero a
  rwa [mul_zero] at h_step

/-- **T183 per-call construction packaging via factorization**.

Packages T179's six-clause per-call construction bundle from explicit
data:

* `σ_loc, hσ_loc_dom` — the σ-strict-dominating unit and the per-`w`
  strict-domination output (the σ-strict-dom subset, supplied by
  T180/T181/T182 chain or directly).
* `f, h_alg` — the cover-refinement element and the algebraic
  identity `algebraMap f = σ_loc · ∏ D.T.image (algebraMap)`.
* `h_s_factor : C.base.s = D.s * f` — the cover-base factorization
  in `A`.
* `hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s` — the
  source-side rational-open membership (the genuinely missing Wedhorn
  8.34(ii) f-construction content; its discharge requires the next
  theorem-level ticket).

T183 **derives** `¬ v.vle f 0` (the sixth clause of the bundle)
automatically from `hv_in_plus` + `h_s_factor`, via the generic
algebraic lemma `not_vle_zero_left_of_mul_eq_of_not_vle_zero`.

Output: T179's six-clause existential bundle, ready to feed
`produce_WedhornC1PerCallSupplyLocalizedMultiPiece_via_factorization_and_dom_supply`. -/
theorem wedhorn_834_per_call_construction_via_factorization
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A)
    (σ_loc : (Localization.Away C.base.s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      ∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s))
    (f : A)
    (h_alg :
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      algebraMap A (Localization.Away C.base.s) f =
        (σ_loc : Localization.Away C.base.s) *
          (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)),
            τ))
    (h_s_factor : C.base.s = D.s * f)
    (hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
    ∃ (σ_loc' : (Localization.Away C.base.s)ˣ) (f' : A),
      (∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc' : Localization.Away C.base.s) τ ∧
              ¬ w.vle τ (σ_loc' : Localization.Away C.base.s)) ∧
      (algebraMap A (Localization.Away C.base.s) f' =
        (σ_loc' : Localization.Away C.base.s) *
          (∏ τ ∈ D.T.image
              (algebraMap A (Localization.Away C.base.s)), τ)) ∧
      C.base.s = D.s * f' ∧
      v ∈ rationalOpen (insert f' C.base.T) C.base.s ∧
      ¬ v.vle f' 0 := by
  refine ⟨σ_loc, f, hσ_loc_dom, h_alg, h_s_factor, hv_in_plus, ?_⟩
  -- Derive ¬ v.vle f 0 from hv_in_plus + h_s_factor.
  -- hv_in_plus : v ∈ Spa A A⁺ ∧ (∀ x, v.vle x C.base.s) ∧ ¬ v.vle (C.base.s) 0.
  exact not_vle_zero_left_of_mul_eq_of_not_vle_zero v h_s_factor
    hv_in_plus.2.2

/-! ### T184: source-side membership bridge from `f`-bound and cover refinement

T183 packages T179's per-call construction bundle taking the source-side
rational-open membership `hv_in_plus : v ∈ rationalOpen (insert f C.base.T)
C.base.s` as an explicit input. T184 **derives** that membership from the
weaker hypothesis `h_f_bound : v.vle f C.base.s` combined with the
cover refinement structure `C.hsubset D hD hv`, eliminating
`hv_in_plus` from the input list.

**Proof structure**:

* `v ∈ rationalOpen (insert f C.base.T) C.base.s` unfolds to:
  - `v ∈ Spa A A⁺` (from `v ∈ rationalOpen D.T D.s`);
  - `∀ x ∈ insert f C.base.T, v.vle x C.base.s` — split into `x = f`
    (from `h_f_bound`) and `x ∈ C.base.T` (from `C.hsubset` applied
    to the cover refinement);
  - `¬ v.vle (C.base.s) 0` (from `C.hsubset` applied to the cover
    refinement; equivalently from the base rational-open membership).

The cover refinement `C.hsubset D hD : rationalOpen D.T D.s ⊆ rationalOpen
C.base.T C.base.s` is an axiom of `RationalCoveringData` itself.

Provided:

* `wedhorn_834_v_in_plus_of_f_bound_and_cover` — source-side membership
  bridge.

* `wedhorn_834_per_call_construction_via_factorization_and_f_bound` —
  composes T184's bridge with T183, eliminating `hv_in_plus` from the
  input list. -/

/-- **T184 source-side membership bridge**: derive
`v ∈ rationalOpen (insert f C.base.T) C.base.s` from `h_f_bound :
v.vle f C.base.s` and the cover refinement `v ∈ rationalOpen D.T D.s`
for `D ∈ C.covers`.

**Proof**: unfold the rationalOpen membership into three components:
* `v ∈ Spa A A⁺` and `¬ v.vle (C.base.s) 0` come from
  `C.hsubset D hD hv` (the base rational-open membership).
* `∀ x ∈ insert f C.base.T, v.vle x C.base.s` splits via
  `Finset.mem_insert.mp`: at `x = f`, use `h_f_bound`; at
  `x ∈ C.base.T`, use the second component of `C.hsubset D hD hv`. -/
theorem wedhorn_834_v_in_plus_of_f_bound_and_cover
    [DecidableEq A]
    (C : RationalCoveringData A)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s)
    (f : A) (h_f_bound : v.vle f C.base.s) :
    v ∈ rationalOpen (insert f C.base.T) C.base.s := by
  -- Cover refinement: v lies in the base rational subset; unfold membership.
  obtain ⟨hv_spa, hv_T_bound, hv_C_base_s_ne⟩ := C.hsubset D hD hv
  refine ⟨hv_spa, ?_, hv_C_base_s_ne⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx_in_T
  · exact h_f_bound
  · exact hv_T_bound x hx_in_T

/-- **T184 per-call construction packaging from f-bound** (composed
with T183).

Composes T184's source-side membership bridge with T183's
`wedhorn_834_per_call_construction_via_factorization`, producing
T179's six-clause per-call construction bundle with the source-side
membership `hv_in_plus` **eliminated** from the input list — replaced
by the weaker `h_f_bound : v.vle f C.base.s` plus the cover refinement
`hD : D ∈ C.covers` and `hv : v ∈ rationalOpen D.T D.s`.

**Inputs**:
* `σ_loc : (Loc C.base.s)ˣ` + `hσ_loc_dom` — σ-strict-dom (T180-T182
  chain).
* `f : A` + `h_alg` + `h_s_factor : C.base.s = D.s * f` — algebraic
  factorization data.
* `h_f_bound : v.vle f C.base.s` — the source-side `f`-bound
  (the actual remaining structural input; replaces `hv_in_plus`).

**Output**: T179's six-clause existential bundle.

After T184, the per-call construction bundle is reduced to:
* σ-strict-dom subset (4 fields via T180-T182 chain);
* `f, h_alg, h_s_factor, h_f_bound` (algebraic + source-bound);
* (`v ∈ rationalOpen (insert f C.base.T) C.base.s` and `¬ v.vle f 0`
  derived).

The remaining genuinely-Wedhorn input is the explicit `f` construction
satisfying `h_alg, h_s_factor, h_f_bound` simultaneously — the next
theorem-level ticket. -/
theorem wedhorn_834_per_call_construction_via_factorization_and_f_bound
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s)
    (σ_loc : (Localization.Away C.base.s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      ∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s))
    (f : A)
    (h_alg :
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      algebraMap A (Localization.Away C.base.s) f =
        (σ_loc : Localization.Away C.base.s) *
          (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)),
            τ))
    (h_s_factor : C.base.s = D.s * f)
    (h_f_bound : v.vle f C.base.s) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
    ∃ (σ_loc' : (Localization.Away C.base.s)ˣ) (f' : A),
      (∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc' : Localization.Away C.base.s) τ ∧
              ¬ w.vle τ (σ_loc' : Localization.Away C.base.s)) ∧
      (algebraMap A (Localization.Away C.base.s) f' =
        (σ_loc' : Localization.Away C.base.s) *
          (∏ τ ∈ D.T.image
              (algebraMap A (Localization.Away C.base.s)), τ)) ∧
      C.base.s = D.s * f' ∧
      v ∈ rationalOpen (insert f' C.base.T) C.base.s ∧
      ¬ v.vle f' 0 :=
  wedhorn_834_per_call_construction_via_factorization
    P C hopen_base D v σ_loc hσ_loc_dom f h_alg h_s_factor
    (wedhorn_834_v_in_plus_of_f_bound_and_cover C D hD v hv f h_f_bound)

/-! ### T185: power-cleared `h_alg` and the exact-lift gap

Manager's hypothesis (T185 directive): standard denominator clearing
for `(σ_loc : Loc C.base.s) * ∏ D.T.image (algebraMap)` only produces
a **power-cleared** identity, not the exact `h_alg` target.

**Verification (this section)**: `exists_away_denominator_cleared`
applied at `x := (σ_loc : Loc C.base.s) * ∏ D.T.image (algebraMap)`
gives:

```
∃ (a : A) (n : ℕ),
  algebraMap A (Loc C.base.s) a =
    ((σ_loc : Loc C.base.s) *
      (∏ τ ∈ D.T.image (algebraMap A (Loc C.base.s)), τ)) *
      (algebraMap A (Loc C.base.s) C.base.s) ^ n
```

The factor `(algebraMap C.base.s) ^ n` on the RHS is the
**denominator-clearing power**. The exact `h_alg` target consumed by
T179/T183 is the `n = 0` case — i.e., the additional condition that
the chosen `(σ_loc, ∏ D.T.image)` lifts to `algebraMap` of an
A-element directly, with no power-clearing required.

**Precise gap (the missing exact-lift hypothesis)**:

```
∃ a : A, algebraMap A (Loc C.base.s) a =
  (σ_loc : Loc C.base.s) *
    (∏ τ ∈ D.T.image (algebraMap A (Loc C.base.s)), τ)
```

This is **not** derivable from `exists_away_denominator_cleared` alone;
the existing API yields only the power-cleared variant above.

**Mathematical interpretation**: Wedhorn 8.34(ii)'s explicit
`f := σ · t · D.s ^ (N - 1)` construction sidesteps this issue by
choosing `f` of a specific algebraic form — the resulting `algebraMap f`
matches `σ_loc · t · (algebraMap D.s) ^ (N - 1)` (a single-`t` form,
not the multi-element `∏ D.T.image` form). Thus the current
`h_alg` target's multi-element shape is what's mismatched: the
denominator-clearing route naturally produces `h_alg` for a
**singleton** `D.T = {t}` (with `∏ D.T.image = algebraMap t`) plus
power-clearing factor; the multi-element shape requires either
exact-lift or a different algebraic identity (e.g.,
`f := σ · ∏ t · D.s ^ (N - |D.T|)`).

**Issue type**: this is **mathematical**, not API-level — the
exact-lift hypothesis is a genuine extra structural condition. The
correct `h_alg` shape consumed by downstream T179/T183 is either:
(a) the `n = 0` exact-lift case (a structural condition), or
(b) a power-cleared form `algebraMap f = σ_loc · ∏ · (algebraMap C.base.s) ^ n`
(requires reformulating downstream T179/T183 consumers).

Provided:

* `wedhorn_834_power_cleared_h_alg_for_unit_product` — strongest
  honest power-cleared identity from `exists_away_denominator_cleared`.

* `wedhorn_834_exact_h_alg_target` — Prop-valued statement of the
  exact `h_alg` target (the existential for `f` matching the n = 0
  case), exposed as a precise Lean type. -/

/-- **T185 power-cleared `h_alg`** — strongest honest denominator-
clearing identity for `(σ_loc : Loc C.base.s) * ∏ D.T.image
(algebraMap)`.

Direct application of `exists_away_denominator_cleared` at
`x := (σ_loc : Loc) * ∏ D.T.image (algebraMap)`. Produces `(a, n)`
with `algebraMap a = x * (algebraMap C.base.s) ^ n`.

The exact `h_alg` target consumed by T179/T183 is the `n = 0`
specialisation; for `n > 0`, the power factor `(algebraMap C.base.s)^n`
remains on the RHS and the exact `h_alg` shape requires the
exact-lift hypothesis stated by `wedhorn_834_exact_h_alg_target`. -/
theorem wedhorn_834_power_cleared_h_alg_for_unit_product
    [DecidableEq A]
    (C : RationalCoveringData A)
    (D : RationalLocData A)
    (σ_loc : (Localization.Away C.base.s)ˣ) :
    letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
    ∃ (a : A) (n : ℕ),
      algebraMap A (Localization.Away C.base.s) a =
        ((σ_loc : Localization.Away C.base.s) *
          (∏ τ ∈ D.T.image
              (algebraMap A (Localization.Away C.base.s)), τ)) *
          (algebraMap A (Localization.Away C.base.s) C.base.s) ^ n := by
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  obtain ⟨a, n, h⟩ := exists_away_denominator_cleared C.base.s
    ((σ_loc : Localization.Away C.base.s) *
      (∏ τ ∈ D.T.image
          (algebraMap A (Localization.Away C.base.s)), τ))
  exact ⟨a, n, h.symm⟩

/-- **T185 exact `h_alg` target** — precise Lean statement of the
genuinely missing exact-lift hypothesis for the T179/T183 `h_alg`
shape.

The existential `∃ a : A, algebraMap a = σ_loc · ∏ D.T.image
(algebraMap)` is the `n = 0` specialisation of T185's power-cleared
identity. **It is not derivable from
`exists_away_denominator_cleared` alone** — the existing API yields
only the power-cleared variant.

This statement is the **exact missing Lean type** for the upstream
T179/T183 `h_alg` consumer. Discharging it requires either:

(a) the structural condition that the chosen `(σ_loc, ∏ D.T.image)`
    pair satisfies the exact-lift `n = 0` case, or

(b) reformulating downstream T179/T183 consumers to accept the
    power-cleared form (a separate signature-level refactor).

The mathematical content of (a) is Wedhorn 8.34(ii)-specific: the
`σ_loc` chosen via Cor 7.32 + the `∏ D.T.image` cover-piece product
must combine into a "denominator-free" `Loc C.base.s`-element for the
exact h_alg shape to hold without power factors. -/
def wedhorn_834_exact_h_alg_target
    [DecidableEq A]
    (C : RationalCoveringData A)
    (D : RationalLocData A)
    (σ_loc : (Localization.Away C.base.s)ˣ) : Prop :=
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  ∃ a : A,
    algebraMap A (Localization.Away C.base.s) a =
      (σ_loc : Localization.Away C.base.s) *
        (∏ τ ∈ D.T.image
            (algebraMap A (Localization.Away C.base.s)), τ)

/-! ### T187: single-`t` per-call supply boundary (replacing multi-product)

T185/T186 confirmed that the existing multi-product `h_alg` target
(from `WedhornC1PerCallSupplyLocalizedMultiPiece`) is misframed: it
asks for an exact lift of `(σ_loc : Loc) * ∏ D.T.image (algebraMap)`,
which standard denominator clearing does not provide (only the
power-cleared variant). T186's analysis showed that recovering the
exact form requires `n = 0` in the power-cleared exponent, equivalent
to T185's `wedhorn_834_exact_h_alg_target`, which is itself the
genuine missing structural condition not derivable from existing
denominator-clearing API.

T187 corrects the per-call boundary by **dropping the multi-product
shape** and aligning with Wedhorn 8.34(ii)'s natural single-`t`
construction `f := σ · t · D.s ^ N`. The C1 supplier
(`C1SupplierStrong_local`) is already per `(D, v, t)` with selected
`t ∈ D.T`, so the single-`t` shape matches the consumer interface
directly — no multi-product is independently justified by the proof.

Provided:

* `WedhornC1PerCallSupplyLocalizedSingleT` — single-`t` per-call
  supply Prop. Data: `(σ : A, N : ℕ)` parameterising
  `f := σ · t · D.s ^ N` plus the three C1 verifications (source
  membership, target-side rational-open inclusion, source
  non-vanishing). NO multi-product `∏ D.T.image (algebraMap)`.

* `C1SupplierStrong_local_via_single_t_supply` — direct reduction:
  per-call `WedhornC1PerCallSupplyLocalizedSingleT` data → C1 output.
  The reduction is trivial because the single-`t` data is exactly
  the C1 output bundled at the natural Wedhorn level.

The discharge of `WedhornC1PerCallSupplyLocalizedSingleT` from
concrete Wedhorn 8.34(ii) Tate / pseudouniformizer setup data is the
next theorem-level ticket. Required ingredients:

1. **σ-construction**: from Cor 7.32 in `Loc C.base.s` + denominator
   clearing, produce `σ : A` such that `algebraMap σ` is `σ_loc · ?`
   for an appropriate σ_loc with σ-strict-domination over a test
   family.

2. **N-choice**: pick `N : ℕ` large enough that `f := σ · t · D.s ^ N`
   satisfies the source-side bound `v.vle f C.base.s` (Spa-
   quasi-compactness + topological nilpotence of σ at the localized
   level).

3. **Clause-2 inclusion**: prove
   `rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`
   directly via Wedhorn 8.34(ii)'s σ-strict-dom branch-clearing on
   the single-`t` form (NOT via T176's multi-product chain — that
   chain consumes a different algebraic identity).

4. **Source clauses**: derive `v ∈ rationalOpen (insert f C.base.T)
   C.base.s` from cover refinement + the f-bound + h_s_factor
   structural data; derive `¬ v.vle f 0` from non-vanishing of
   constituents.

These are genuinely Wedhorn 8.34(ii)-content lemmas, not yet present
in the codebase. -/

/-- **T187 single-`t` per-call C1 supply Prop**.

Per-call data and clauses for `C1SupplierStrong_local C` at a
single `(D, v, t)`. The data is the natural Wedhorn 8.34(ii)
parameters `(σ : A, N : ℕ)` defining
`f := σ · t · D.s ^ N`; the clauses are the three C1 outputs at
this `f`:

* `v ∈ rationalOpen (insert f C.base.T) C.base.s` — source
  rational-open membership.
* `rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`
  — clause 2 (rational-open inclusion).
* `¬ v.vle f 0` — source non-vanishing.

**No multi-product** `∏ D.T.image (algebraMap)` appears in this
shape; the algebraic data `(σ, N)` is single-`t`, matching Wedhorn's
natural `f := σ · t · D.s ^ N` construction.

This Prop is the corrected boundary replacing the misframed
`WedhornC1PerCallSupplyLocalizedMultiPiece` (which required an exact
lift of the multi-product, not derivable from standard denominator
clearing per T185/T186). -/
def WedhornC1PerCallSupplyLocalizedSingleT
    [DecidableEq A]
    (C : RationalCoveringData A)
    (D : RationalLocData A) (v : Spv A) (t : A) : Prop :=
  ∃ (σ : A) (N : ℕ),
    v ∈ rationalOpen (insert (σ * t * D.s ^ N) C.base.T) C.base.s ∧
    rationalOpen (insert (σ * t * D.s ^ N) C.base.T) C.base.s ⊆
      rationalOpen D.T D.s ∧
    ¬ v.vle (σ * t * D.s ^ N) 0

/-- **T187 C1 supplier reduction via single-`t` per-call supply**.

Direct reduction: per-call `WedhornC1PerCallSupplyLocalizedSingleT`
data produces `C1SupplierStrong_local C`. The reduction is trivial
because the single-`t` data `(σ, N)` is exactly the Wedhorn 8.34(ii)
construction at the natural level matching the C1 consumer
interface.

**No multi-product** is required: the single-`t` boundary aligns
with `C1SupplierStrong_local`'s per-`(D, v, t)` interface directly,
avoiding the misframed multi-product `h_alg` from T177/T179. -/
theorem C1SupplierStrong_local_via_single_t_supply
    [DecidableEq A]
    (C : RationalCoveringData A)
    (h_per_call :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1PerCallSupplyLocalizedSingleT C D v t) :
    C1SupplierStrong_local C := by
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ, N, hv_in, h_subset, hvf_nz⟩ :=
    h_per_call D hD v hv t ht hvt hvD_s
  exact ⟨σ * t * D.s ^ N, hv_in, h_subset, hvf_nz⟩

/-! ### T188: single-`t` clause-2 inclusion from `h_s_factor` + `T_D ⊆ A⁺`

T187's `WedhornC1PerCallSupplyLocalizedSingleT` requires the clause-2
inclusion `rationalOpen (insert (σ * t * D.s ^ N) C.base.T) C.base.s ⊆
rationalOpen D.T D.s` per `(D, v, t)`. T188 attacks this inclusion
directly.

**Key mathematical observation**: the single-`t` clause-2 inclusion is
provable from purely structural data — **σ-strict-domination is not
required**. The natural Wedhorn 8.34-style structural inputs are:

1. `h_s_factor : C.base.s = D.s * (σ * t * D.s ^ N)` — the cover-base
   factorization for the chosen `f := σ * t * D.s ^ N`.

2. `h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ A⁺` — the natural Tate condition
   that all generators of `D.T` lie in the plus-subring (equivalently,
   are bounded by `1` at every Spa point).

**Proof outline** (purely valuation arithmetic):

* From `h_s_factor` + denominator non-vanishing on `R(insert f C.base.T,
  C.base.s)`: `¬ w.vle f 0` and `¬ w.vle D.s 0` (via T183's generic
  `not_vle_zero_left_of_mul_eq_of_not_vle_zero` applied twice — once
  to `C.base.s = D.s * f` for `f`-non-vanishing, once after
  commutation for `D.s`-non-vanishing).

* From `h_s_factor` + `f`-bound `w.vle f C.base.s`: substituting
  `C.base.s = D.s * f` gives `w.vle (1 * f) (D.s * f)`; cancellation
  via `w.vle_mul_cancel` (using `f`-non-vanishing) yields `w.vle 1 D.s`.

* From `h_T_D_in_plus` + `vle_one_of_mem_spa`: `w.vle t' 1` for each
  `t' ∈ D.T`.

* Transitivity `w.vle t' 1 ≤ w.vle 1 D.s` gives `w.vle t' D.s`.

The σ-strict-domination data plays NO role in this proof — the
multiplicative structure of valuations + the Tate-style A⁺ condition
on `D.T` is enough. This is the **honest single-t clause-2 inclusion**
under the natural Wedhorn 8.34-style structural data.

Provided:

* `rationalOpen_subset_via_single_t_h_s_factor_and_T_D_in_plus` — the
  single-`t` clause-2 inclusion theorem, with no multi-product, no
  σ-strict-dom hypothesis, and no exact-lift `n = 0` assumption.

* `WedhornC1PerCallSupplyLocalizedSingleT_via_h_s_factor_and_T_D_in_plus`
  — caller producing T187's per-call supply Prop from structural data
  and the T188 inclusion. -/

/-- **T188 single-`t` clause-2 inclusion from `h_s_factor` + Tate
condition on `D.T`**.

Proves the single-`t` rational-open inclusion
`rationalOpen (insert (σ * t * D.s ^ N) T_base) C.base.s ⊆
rationalOpen D.T D.s` from the natural Wedhorn 8.34-style structural
data, without requiring σ-strict-domination, multi-product exact-lift,
or N-choice arguments.

The σ-strict-domination data is **not needed** at this level: the
multiplicative structure of valuations on `Spa A A⁺` plus the
`T_D ⊆ A⁺` Tate condition is sufficient. -/
theorem rationalOpen_subset_via_single_t_h_s_factor_and_T_D_in_plus
    [DecidableEq A]
    (D : RationalLocData A) (σ : A) (t : A) (N : ℕ)
    (T_base : Finset A) (C_base_s : A)
    (h_s_factor : C_base_s = D.s * (σ * t * D.s ^ N))
    (h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) :
    rationalOpen (insert (σ * t * D.s ^ N) T_base) C_base_s ⊆
      rationalOpen D.T D.s := by
  intro w hw
  obtain ⟨hw_spa, hw_bound, hw_C_base_s_ne⟩ := hw
  letI : ValuativeRel A := w.toValuativeRel
  -- f-bound at w (the inserted element).
  have hw_f_bound : w.vle (σ * t * D.s ^ N) C_base_s :=
    hw_bound _ (Finset.mem_insert_self _ _)
  -- ¬ w.vle f 0 from h_s_factor (right factor) + ¬ w.vle C_base_s 0.
  have hw_f_ne : ¬ w.vle (σ * t * D.s ^ N) 0 :=
    not_vle_zero_left_of_mul_eq_of_not_vle_zero w h_s_factor hw_C_base_s_ne
  -- ¬ w.vle D.s 0 from h_s_factor (commuted, then right factor).
  have hw_D_s_ne : ¬ w.vle D.s 0 := by
    apply not_vle_zero_left_of_mul_eq_of_not_vle_zero w
      (h_s_factor.trans (mul_comm _ _)) hw_C_base_s_ne
  -- w.vle 1 D.s from f-bound + h_s_factor + ¬ w.vle f 0 (cancellation).
  have h_one_le_D_s : w.vle (1 : A) D.s := by
    have h_chain : w.vle ((1 : A) * (σ * t * D.s ^ N))
        (D.s * (σ * t * D.s ^ N)) := by
      rw [one_mul, ← h_s_factor]
      exact hw_f_bound
    exact w.vle_mul_cancel hw_f_ne h_chain
  -- Now reassemble the rational-open membership at D.T D.s.
  refine ⟨hw_spa, ?_, hw_D_s_ne⟩
  intro t' ht'
  -- t' ∈ D.T → t' ∈ A⁺ (hypothesis) → w.vle t' 1 (by vle_one_of_mem_spa).
  have h_t'_le_one : w.vle t' (1 : A) :=
    vle_one_of_mem_spa hw_spa (h_T_D_in_plus t' ht')
  -- Transitivity: w.vle t' 1 ≤ w.vle 1 D.s ⟹ w.vle t' D.s.
  exact w.vle_trans h_t'_le_one h_one_le_D_s

/-- **T188 caller**: produce T187's `WedhornC1PerCallSupplyLocalizedSingleT`
from structural data alone.

Given:
* `f := σ * t * D.s ^ N` (the Wedhorn single-`t` form);
* `h_s_factor : C.base.s = D.s * f`;
* `h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ A⁺` (Tate condition);
* `hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s`;
* `hvf_nz : ¬ v.vle f 0`;

produce `WedhornC1PerCallSupplyLocalizedSingleT C D v t`.

The clause-2 inclusion is dispatched via T188's
`rationalOpen_subset_via_single_t_h_s_factor_and_T_D_in_plus`; clauses
1 (`hv_in_plus`) and 3 (`hvf_nz`) are passed through unchanged. -/
theorem WedhornC1PerCallSupplyLocalizedSingleT_via_h_s_factor_and_T_D_in_plus
    [DecidableEq A]
    (C : RationalCoveringData A)
    (D : RationalLocData A) (v : Spv A) (t : A)
    (σ : A) (N : ℕ)
    (h_s_factor : C.base.s = D.s * (σ * t * D.s ^ N))
    (h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A))
    (hv_in_plus :
      v ∈ rationalOpen (insert (σ * t * D.s ^ N) C.base.T) C.base.s)
    (hvf_nz : ¬ v.vle (σ * t * D.s ^ N) 0) :
    WedhornC1PerCallSupplyLocalizedSingleT C D v t :=
  ⟨σ, N, hv_in_plus,
    rationalOpen_subset_via_single_t_h_s_factor_and_T_D_in_plus
      D σ t N C.base.T C.base.s h_s_factor h_T_D_in_plus,
    hvf_nz⟩

/-! ### T189: per-call supply from honest structural data only

Composes T184's source-side membership bridge, T183's
non-vanishing lemma, and T188's per-call caller into a single theorem
producing `WedhornC1PerCallSupplyLocalizedSingleT C D v t` from
honest Wedhorn 8.34-style structural data **alone** — no `hv_in_plus`,
no `hvf_nz`, no clause-2 inclusion taken as input.

Inputs:

* `hD : D ∈ C.covers` and `hv : v ∈ rationalOpen D.T D.s` — the
  cover-piece refinement at `(D, v)`;
* `σ : A` and `N : ℕ` — the Wedhorn 8.34(ii) parameters
  (Cor 7.32 σ-construction + N-choice; deferred upstream);
* `h_s_factor : C.base.s = D.s * (σ * t * D.s ^ N)` — cover-base
  factorization for the chosen `f := σ * t * D.s ^ N`;
* `h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ A⁺` — Tate condition on `D.T`;
* `h_f_bound : v.vle (σ * t * D.s ^ N) C.base.s` — the source-side
  `f`-bound at `v`.

Output: `WedhornC1PerCallSupplyLocalizedSingleT C D v t`.

Composition chain:

* T184 (`wedhorn_834_v_in_plus_of_f_bound_and_cover`) lifts
  `h_f_bound` + cover refinement to
  `hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s`.
* The third component of `hv_in_plus` is `¬ v.vle (C.base.s) 0`; T183's
  `not_vle_zero_left_of_mul_eq_of_not_vle_zero` then produces
  `hvf_nz : ¬ v.vle f 0` from `h_s_factor`.
* T188's
  `WedhornC1PerCallSupplyLocalizedSingleT_via_h_s_factor_and_T_D_in_plus`
  packages the data into the per-call supply Prop. -/

/-- **T189 per-call supply from honest structural data**.

Produces `WedhornC1PerCallSupplyLocalizedSingleT C D v t` from the
honest Wedhorn 8.34-style structural data
`(σ, N, h_s_factor, h_T_D_in_plus, h_f_bound)` plus cover-refinement
data `(hD, hv)`. Composes T184 + T183 + T188.

This eliminates `hv_in_plus`, `hvf_nz`, and the clause-2 inclusion
from the input list — they are derived from `h_s_factor +
h_T_D_in_plus + h_f_bound + hD + hv` via the T184/T183/T188 chain.

The remaining inputs are the genuinely Wedhorn-content
`(σ, N, h_s_factor, h_T_D_in_plus, h_f_bound)`: the σ-construction +
N-choice + cover-base factorization + Tate condition + source f-bound.
Their discharge from concrete Tate / pseudouniformizer data is the
next theorem-level ticket. -/
theorem WedhornC1PerCallSupplyLocalizedSingleT_via_h_s_factor_T_D_in_plus_and_f_bound
    [DecidableEq A]
    (C : RationalCoveringData A)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s)
    (t : A)
    (σ : A) (N : ℕ)
    (h_s_factor : C.base.s = D.s * (σ * t * D.s ^ N))
    (h_T_D_in_plus : ∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A))
    (h_f_bound : v.vle (σ * t * D.s ^ N) C.base.s) :
    WedhornC1PerCallSupplyLocalizedSingleT C D v t := by
  -- Source-side membership via T184.
  have hv_in_plus :
      v ∈ rationalOpen (insert (σ * t * D.s ^ N) C.base.T) C.base.s :=
    wedhorn_834_v_in_plus_of_f_bound_and_cover C D hD v hv
      (σ * t * D.s ^ N) h_f_bound
  -- Source-side non-vanishing of f via T183 + denominator non-vanishing.
  have hvf_nz : ¬ v.vle (σ * t * D.s ^ N) 0 :=
    not_vle_zero_left_of_mul_eq_of_not_vle_zero v h_s_factor hv_in_plus.2.2
  -- Package via T188's caller.
  exact WedhornC1PerCallSupplyLocalizedSingleT_via_h_s_factor_and_T_D_in_plus
    C D v t σ N h_s_factor h_T_D_in_plus hv_in_plus hvf_nz

/-- **T190 C1-level consumer**: produce `C1SupplierStrong_local C`
from a per-call provider of the honest single-`t` structural inputs.

Composes T189's
`WedhornC1PerCallSupplyLocalizedSingleT_via_h_s_factor_T_D_in_plus_and_f_bound`
with T187's `C1SupplierStrong_local_via_single_t_supply` to produce
`C1SupplierStrong_local C` directly from the genuinely
Wedhorn 8.34-style per-call structural data:

* `σ : A` and `N : ℕ` (Wedhorn parameters);
* `C.base.s = D.s * (σ * t * D.s ^ N)` (cover-base factorization);
* `∀ t' ∈ D.T, t' ∈ A⁺` (Tate condition on D.T);
* `v.vle (σ * t * D.s ^ N) C.base.s` (source f-bound at v).

Inputs `hD`, `hv`, `t`, `ht`, `hvt`, `hvD_s` come from the C1
consumer's per-`(D, v, t)` quantification.

After T190, the C1-level reduction is reduced to the genuinely
Wedhorn-content per-call provider (deferred upstream): producing
`(σ, N, h_s_factor, h_T_D_in_plus, h_f_bound)` from concrete
Tate / pseudouniformizer setup data. -/
theorem C1SupplierStrong_local_via_single_t_structural_data
    [DecidableEq A]
    (C : RationalCoveringData A)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s) :
    C1SupplierStrong_local C := by
  apply C1SupplierStrong_local_via_single_t_supply
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ, N, h_s_factor, h_T_D_in_plus, h_f_bound⟩ :=
    h_struct D hD v hv t ht hvt hvD_s
  exact WedhornC1PerCallSupplyLocalizedSingleT_via_h_s_factor_T_D_in_plus_and_f_bound
    C D hD v hv t σ N h_s_factor h_T_D_in_plus h_f_bound

/-- **T191 normalized-cover consumer**: produce
`C1SupplierStrong_local C.insertDenom` from per-call honest single-`t`
structural data.

Composes T190's
`C1SupplierStrong_local_via_single_t_structural_data` (which produces
`C1SupplierStrong_local C` from the per-call structural provider)
with the existing structural lift `C1SupplierStrong_local_insertDenom_lift`
(which lifts `C1SupplierStrong_local C` to
`C1SupplierStrong_local C.insertDenom` modulo the cover-piece
non-emptiness condition).

This delivers the consumer-ready strong C1 supplier on the normalized
cover from honest Wedhorn 8.34-style structural per-call data plus the
mild non-emptiness condition `∀ D ∈ C.covers, D.T.Nonempty`. -/
theorem C1SupplierStrong_local_insertDenom_via_single_t_structural_data
    [DecidableEq A]
    (C : RationalCoveringData A)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s) :
    C1SupplierStrong_local C.insertDenom :=
  C1SupplierStrong_local_insertDenom_lift C h_covers_nonempty
    (C1SupplierStrong_local_via_single_t_structural_data C h_struct)

end ValuationSpectrum
