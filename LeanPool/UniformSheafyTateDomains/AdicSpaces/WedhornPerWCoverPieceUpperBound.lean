/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornC1PerWCoverPieceSupplier

/-!
# Wedhorn 8.34(ii) — Per-`w` cover-piece upper-bound supplier (T040)

T040 owns the genuine theorem-level residual isolated by T039
(`WedhornC1PerWCoverPieceSupplier`, commit `4512f6a`):

```
∀ w ∈ Spa (Localization.Away C.base.s) (Localization.Away C.base.s)⁺,
  w.vle ((σ_loc : Localization.Away C.base.s) *
    (∏ t ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), t))
    (algebraMap A (Localization.Away C.base.s) C.base.s) →
  ∀ τ ∈ localizedTestFamily C.base.s D.T D.s,
    w.vle (σ_loc : Localization.Away C.base.s) τ ∧
    ¬ w.vle τ (σ_loc : Localization.Away C.base.s) →
    ∀ t ∈ D.T.image (algebraMap A (Localization.Away C.base.s)),
      w.vle t (algebraMap A (Localization.Away C.base.s) D.s)
```

i.e., component 5 of `WedhornC1PerCallSupplyPerWCoverPiece`.

## Source-restricted predicate

The genuine mathematical content of the per-`w` upper-bound supplier is
the **localized analog of Wedhorn Lemma 7.45's cover-refinement
inclusion** restricted to the cover plus-piece via the f-membership
premise. That is, the **localized rational-subset condition under
f-membership**:

```
∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
  w.vle (σ_loc * ∏ T_D.image (algebraMap)) (algebraMap s) →
  ∀ t ∈ T_D.image (algebraMap), w.vle t (algebraMap s_D)
```

This is the natural localized form of Wedhorn 7.45's set-level
cover refinement `R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)`,
restricted to the cover plus-piece via the f-membership premise. The
σ-strict-domination premise of the T039 supplier is **dropped** here
because the per-`t` upper bound is a pure rational-subset condition,
not a domination assertion — the σ-strict-domination by some
`τ ∈ localizedTestFamily` is only a consumer-side bookkeeping marker
for T037's structural-data shape and is not used in the conclusion.

## Why this predicate is the genuine residual

Per T035's analysis (`WedhornMaxElementSDComparison`, commit `8ffad58`),
the rational-subset condition `∀ t ∈ T_D.image, w.vle t (algebraMap s_D)`
is **mathematically false uniformly on `Spa(Localization.Away s, ⁺)`**
for arbitrary `(T_D, s_D)`: see the explicit counter-example at
`A = ℚ_p, T_D = {1}, s_D = p` where the standard p-adic valuation
violates the bound. The natural setting where the bound holds is
**at `w` in the cover plus-piece** — the f-membership premise is
exactly the cover-plus-piece source-restriction.

This source-restricted predicate is the localized analog of Wedhorn's
set-level cover refinement, and its honest discharge is the genuine
remaining mathematical content for Wedhorn 8.34(ii) Step 2. The
existing local data (Cor 7.32, Laurent-piece membership, σ-strict-
domination, the V_K decomposition of T031, the α_T_D arithmetic of
T033, the max-element bridge of T035, etc.) does not supply the
predicate without an additional honest valuation-arithmetic step
corresponding to Wedhorn 7.45's deduction at the localized side.

## What this file provides

* `WedhornCoverPieceLocRationalBound` — the source-restricted
  predicate. Captures the localized analog of Wedhorn 7.45's cover
  refinement, restricted to the cover plus-piece via f-membership.
  σ-strict-domination is intentionally not in the predicate (the per-`t`
  bound is a pure rational-subset condition, independent of
  σ-domination data).

* `c1PerWUpperBoundSupplier_of_loc_rational_bound` — bridge promoting
  the predicate to the T039 per-`w` supplier residual shape (with the
  σ-strict-domination premise as an unused premise, kept for
  signature symmetry with T037 / T039).

* `WedhornC1PerCallSupplyPerWCoverPiece_of_loc_rational_bound` — per-
  call assembly: produces `WedhornC1PerCallSupplyPerWCoverPiece` from
  the seven natural components (σ_loc, f, h_alg, h_dom, the predicate
  `h_loc_bound`, hv_in_plus, hvf_nz). Trivial existential constructor
  composing the bridge above with the unchanged remaining six
  components.

* `C1SupplierStrong_local_via_loc_rational_bound` — top-level C1
  caller producing `C1SupplierStrong_local C` from a per-call function
  delivering the seven components for every
  `(D ∈ C.covers, v ∈ rationalOpen D.T D.s, t ∈ D.T)` triple. Composes
  with T039's `C1SupplierStrong_local_via_per_w_cover_piece_supplier`.

## Notes

* No root import; leaf-level.
* Imports only `WedhornC1PerWCoverPieceSupplier` (T039, commit
  `4512f6a`), which transitively brings in T037 / T038 and the local
  per-branch chain APIs.
* No edits to T027–T039 accepted files, root imports, or final
  theorem signatures.
* No revival of global universal-over-Spa rational-bound claims,
  M-power-decay, σ-power-decay, T001/Lane-B, Cor 8.32/Jacobson,
  faithful-flatness, Zavyalov, or bivariate-overlap content.
* The localized rational-bound predicate is the **single explicit
  remaining mathematical residual** for Wedhorn 8.34(ii) Step 2 at
  the C1 layer; its honest discharge corresponds to the localized
  analog of Wedhorn Lemma 7.45 and is genuine downstream content.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Cover-piece localized rational-bound predicate** (T040 source-
restricted structural predicate).

At every `w ∈ Spa(Localization.Away s, ⁺)` satisfying the f-membership
premise `w.vle (σ_loc * ∏ T_D.image (algebraMap)) (algebraMap s)`,
every element of `T_D.image (algebraMap)` is bounded above by
`algebraMap s_D` at `w`.

This is the **localized analog of Wedhorn Lemma 7.45's cover refinement
`R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)`**, restricted to the
cover plus-piece via the f-membership premise. Mathematically TRUE
under the cover refinement (which is the σ-construction's goal in
Wedhorn 8.34(ii)), and the natural `∀ w in cover plus-piece` shape of
the rational-subset condition required by T037's source-restricted
structural data.

The σ-strict-domination premise of T039's per-`w` supplier residual is
**not in this predicate**: it is bookkeeping symmetry with T037, but
the per-`t` upper bound is a pure rational-subset condition that does
not depend on the σ-strict-domination witness. Dropping it yields the
cleanest source-restricted predicate. -/
def WedhornCoverPieceLocRationalBound
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle t (algebraMap A (Localization.Away s) s_D)

omit [PlusSubring A] in
/-- **Bridge: localized rational-bound predicate → T039 per-`w`
upper-bound supplier residual** (T040 main bridge).

Promotes `WedhornCoverPieceLocRationalBound` to the per-`w` supplier
residual shape consumed by component 5 of
`WedhornC1PerCallSupplyPerWCoverPiece`. The σ-strict-domination
premise `∀ τ ∈ localizedTestFamily, w.vle σ_loc τ ∧ ¬ w.vle τ σ_loc`
is **unused** in the conclusion: the per-`t` upper bound is a pure
rational-subset condition, independent of the τ-quantifier. The
premise is kept on the supplier signature for symmetry with T037's
structural-data shape; the bridge discards it. -/
theorem c1PerWUpperBoundSupplier_of_loc_rational_bound
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_loc_bound :
      WedhornCoverPieceLocRationalBound P T s hopen T_D s_D σ_loc) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
        ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t (algebraMap A (Localization.Away s) s_D) := by
  intro w hw_spa hw_f _τ _hτ _hστ t ht
  exact h_loc_bound w hw_spa hw_f t ht

/-- **Per-call assembly: `WedhornC1PerCallSupplyPerWCoverPiece` via
the cover-piece localized rational-bound predicate** (T040 composed
deliverable).

Given the seven natural components — σ_loc, f, h_alg
(denominator-clearing identity), h_dom (Cor 7.32 σ-strict-domination),
h_loc_bound (the T040 source-restricted localized rational-bound
predicate), hv_in_plus (source-side rational-open membership),
hvf_nz (non-degeneracy of f at v) — produce
`WedhornC1PerCallSupplyPerWCoverPiece P C hopen_base D v` (T039,
commit `4512f6a`).

The localized rational-bound predicate `h_loc_bound` is the single
mathematical residual; the other six components are routine Cor 7.32 /
denominator-clearing / base-side data. Trivial existential constructor
composing `c1PerWUpperBoundSupplier_of_loc_rational_bound` with the
unchanged remaining six components. -/
theorem WedhornC1PerCallSupplyPerWCoverPiece_of_loc_rational_bound
    [DecidableEq A]
    (P : PairOfDefinition A) (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
    ∀ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A)
      (_h_alg : algebraMap A (Localization.Away C.base.s) f =
        (σ_loc : Localization.Away C.base.s) *
          (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ))
      (_h_dom : ∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s))
      (_h_loc_bound :
        WedhornCoverPieceLocRationalBound P C.base.T C.base.s hopen_base
          D.T D.s σ_loc)
      (_hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s)
      (_hvf_nz : ¬ v.vle f 0),
      WedhornC1PerCallSupplyPerWCoverPiece P C hopen_base D v := by
  intro σ_loc f h_alg h_dom h_loc_bound hv_in_plus hvf_nz
  exact ⟨σ_loc, f, h_alg, h_dom,
    c1PerWUpperBoundSupplier_of_loc_rational_bound P C.base.T C.base.s
      hopen_base D.T D.s σ_loc h_loc_bound, hv_in_plus, hvf_nz⟩

/-- **Top-level: `C1SupplierStrong_local C` via cover-piece localized
rational-bound predicate** (T040 final deliverable).

Identical caller signature to T039's
`C1SupplierStrong_local_via_per_w_cover_piece_supplier`, modulo the
per-call supply: each per-call delivery provides the source-restricted
predicate `WedhornCoverPieceLocRationalBound` in place of T039's
explicit per-`w` upper-bound supplier (the σ-strict-domination premise
is unused at this layer and discharged automatically by the bridge).

Composes
`WedhornC1PerCallSupplyPerWCoverPiece_of_loc_rational_bound` with
T039's `C1SupplierStrong_local_via_per_w_cover_piece_supplier`. The
localized rational-bound predicate is the **single explicit
mathematical residual** for Wedhorn 8.34(ii) Step 2 at the C1 layer;
its honest discharge corresponds to the localized analog of Wedhorn
Lemma 7.45 and is genuine downstream content. -/
theorem C1SupplierStrong_local_via_loc_rational_bound
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_components :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
        algebraMap A (Localization.Away C.base.s) f =
          (σ_loc : Localization.Away C.base.s) *
            (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ) ∧
        (∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
        WedhornCoverPieceLocRationalBound P C.base.T C.base.s hopen_base
          D.T D.s σ_loc ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_per_w_cover_piece_supplier P hA₀_le C
    hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_loc_bound, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  exact WedhornC1PerCallSupplyPerWCoverPiece_of_loc_rational_bound P C
    hopen_base D v σ_loc f h_alg h_dom h_loc_bound hv_in_plus hvf_nz

end ValuationSpectrum
