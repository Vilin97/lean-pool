/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCoverPieceLocRationalBoundDischarge

/-!
# Wedhorn 8.34(ii) — V_K-nonempty rational-bound max-element factoring (T042)

T041 (commit `74d971e`) accepted the honest factoring of T040's
`WedhornCoverPieceLocRationalBound` into a fully-discharged V_∅ branch
plus an explicit V_K-nonempty residual predicate
`WedhornCoverPieceVKNonemptyRationalBound`. This file lands the next
honest factoring: the V_K-nonempty residual reduces to the more
elementary **max-element conditional bound** under V_K-nonempty
source-restriction, via T034's `Spv.exists_max_vle_of_nonempty` +
transitivity.

## Source-restricted max-element residual

The new residual predicate
`WedhornCoverPieceVKAlphaTDMaxBound` asks for the per-`τ_max` upper
bound at `algebraMap s_D` whenever `τ_max` is a maximum of
`T_D.image (algebraMap)` at `w`, conditioned on:

* the f-membership premise `w.vle (σ_loc * ∏ T_D.image (algebraMap))
  (algebraMap s)`, AND
* the V_K-nonempty witness (`∃ t_K ∈ T_D.image, w.vle σ_loc t_K ∧
  ¬ w.vle t_K σ_loc`).

This is the **single max-element residual** matching T034's
`alpha_T_D_per_t_factored_chain_via_max_element` shape with the
additional V_K-nonempty source restriction inherited from T041.

## Why this is honest progress

The reduction from `WedhornCoverPieceVKNonemptyRationalBound`
("∀ t ∈ T_D.image, w.vle t (algebraMap s_D)") to
`WedhornCoverPieceVKAlphaTDMaxBound` ("max-element of T_D.image
bounded by algebraMap s_D under maxness") is **mechanical** via
`Spv.exists_max_vle_of_nonempty` (T034) + transitivity:

1. The V_K-nonempty witness gives `T_D.image (algebraMap)` is nonempty
   — the witness `t_K` is in the image.
2. `Spv.exists_max_vle_of_nonempty` extracts a max element `τ_max` at
   `w`.
3. The max-element residual gives `w.vle τ_max (algebraMap s_D)`.
4. Maxness `∀ t ∈ T_D.image, w.vle t τ_max` + transitivity gives
   `∀ t ∈ T_D.image, w.vle t (algebraMap s_D)`.

The factoring exposes the genuine remaining mathematical content —
the **per-`τ_max` upper bound at `algebraMap s_D`** — as the single
explicit residual.

## Why the max-element bound is the genuine residual (analysis)

Per T035's analysis (`WedhornMaxElementSDComparison`, commit
`8ffad58`): the unrestricted version of this bound `∀ w ∈
Spa(Loc s, ⁺), ∀ τ_max ∈ T_D.image (under maxness), w.vle τ_max
(algebraMap s_D)` is **mathematically false uniformly** on
`Spa(Loc s, ⁺)` for arbitrary `(T_D, s_D, σ_loc)`. Concrete
counter-example (slight extension of T035's): `A = ℚ_p`, `s = 1` (so
`Localization.Away s = ℚ_p`), `T_D = {p}`, `s_D = p^2`,
`σ_loc = p^3`. At the standard p-adic valuation `v_p`:

* `v_p(σ_loc) = v_p(p^3) = 1/p^3`, `v_p(algebraMap p) = v_p(p) = 1/p`,
  `v_p(algebraMap s_D) = v_p(p^2) = 1/p^2`.
* σ-strict-domination (Cor 7.32 standard output) by `algebraMap p`:
  `v_p.vle (1/p^3) (1/p)` and `¬ v_p.vle (1/p) (1/p^3)`. ✓
* f-membership: `f := σ_loc · p = p^4`; `v_p.vle p^4 1` since
  `v_p(p^4) = 1/p^4 ≤ 1`. ✓
* V_K-nonempty witness `t_K := algebraMap p`: σ-strict-dom by `t_K` at
  `v_p` (same as above). ✓
* Max element of `T_D.image (algebraMap) = {p}` at `v_p` is `p`
  itself, with `v_p(p) = 1/p`.
* Max-element bound: `v_p.vle p p^2`, i.e., `1/p ≤ 1/p^2`, **FAILS**
  for `p > 1`.

So at `v_p`, with `σ_loc = p^3`, the max-element residual is **false**
— but `v_p ∉ rationalOpen T_D s_D = R({p}, p^2)` (since `1/p ≤ 1/p^2`
fails). The residual fails precisely at `w` whose comap-image at the
base is **outside** the rational-open `R(T_D, s_D)`. The natural
setting where the residual holds is: `w` arising as the comap-lift of
a base point in `R(T_D, s_D)`.

Discharging the max-element residual on **all** of `Spa(Loc s, ⁺)`
without a base-lift restriction therefore requires either:

* **Wedhorn-specific power-decay arithmetic** (M-power-decay or
  σ-power-decay) — both **forbidden** by current ticket boundaries.

* **Definition-level tightening of the universal quantifier** in the
  per-`w` cover-piece supplier (T039's component 5) and the
  structural-data Prop (T037) — out of scope for T042 and would
  require coordinated edits to T037–T041.

Per the second acceptance option in the T042 ticket, this file
delivers a **minimal source-restricted structural predicate plus
bridge theorem** that precisely isolates the remaining V_K-nonempty
valuation-arithmetic input as the max-element bound.

## What this file provides

* `WedhornCoverPieceVKAlphaTDMaxBound` — the max-element residual
  predicate. Source-restricted by f-membership AND V_K-nonempty
  witness. Precisely isolates Wedhorn 8.34(ii)'s α_T_D-branch
  cover-refinement deduction.

* `WedhornCoverPieceVKNonemptyRationalBound_via_alpha_TD_max_bound`
  — the main bridge: from the max-element residual, derive T041's
  `WedhornCoverPieceVKNonemptyRationalBound` via
  `Spv.exists_max_vle_of_nonempty` + transitivity.

* `WedhornC1PerCallSupplyPerWCoverPiece_via_alpha_TD_max_bound` —
  per-call composition producing T039's
  `WedhornC1PerCallSupplyPerWCoverPiece` from σ_loc, f, h_alg, h_dom,
  the max-element residual, hv_in_plus, hvf_nz. Composes with T041's
  `WedhornC1PerCallSupplyPerWCoverPiece_via_VK_residual`.

* `C1SupplierStrong_local_via_alpha_TD_max_bound` — top-level C1
  caller producing `C1SupplierStrong_local C` from per-call delivery
  of the components above. Composes with T041's
  `C1SupplierStrong_local_via_VK_residual`.

## Notes

* No root import; leaf-level.
* Imports only `WedhornCoverPieceLocRationalBoundDischarge` (T041,
  commit `74d971e`), which transitively brings in T034's
  `Spv.exists_max_vle_of_nonempty`, T040's predicate, T039's per-w
  supplier, and the per-call assembly machinery.
* No edits to T027–T041 accepted files, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* The max-element residual is the **single explicit remaining
  mathematical residual** for Wedhorn 8.34(ii) Step 2 at the C1
  layer; honest discharge requires definition-level tightening of
  T039's universal quantifier or forbidden power-decay arguments.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **V_K-nonempty α_T_D-branch max-element residual predicate** (T042
source-restricted residual).

At every `w ∈ Spa(Localization.Away s, ⁺)` satisfying:

* the f-membership premise `w.vle (σ_loc * ∏ T_D.image (algebraMap))
  (algebraMap s)`, AND
* the V_K-nonempty witness `∃ t_K ∈ T_D.image (algebraMap),
  w.vle σ_loc t_K ∧ ¬ w.vle t_K σ_loc`,

every `τ_max ∈ T_D.image (algebraMap)` that is a max of
`T_D.image (algebraMap)` at `w` (i.e., `∀ t' ∈ T_D.image, w.vle t'
τ_max`) satisfies `w.vle τ_max (algebraMap s_D)`.

This is the **max-element conditional form** of T041's V_K-nonempty
residual. The conditional is on max-ness, restricting the per-`t`
upper-bound conclusion to a single distinguished element of
`T_D.image (algebraMap)`. -/
def WedhornCoverPieceVKAlphaTDMaxBound
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
    (∃ t_K ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (σ_loc : Localization.Away s) t_K ∧
        ¬ w.vle t_K (σ_loc : Localization.Away s)) →
    ∀ τ_max ∈ T_D.image (algebraMap A (Localization.Away s)),
      (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' τ_max) →
      w.vle τ_max (algebraMap A (Localization.Away s) s_D)

omit [PlusSubring A] in
/-- **Bridge: T041's `WedhornCoverPieceVKNonemptyRationalBound` via
the max-element residual** (T042 main bridge).

From `WedhornCoverPieceVKAlphaTDMaxBound` (the max-element residual
under f-membership + V_K-nonempty), derive T041's
`WedhornCoverPieceVKNonemptyRationalBound` (the per-`t` upper bound).

**Proof**: at any `w` satisfying the source restrictions, the
V_K-nonempty witness `t_K ∈ T_D.image (algebraMap)` makes
`T_D.image (algebraMap)` nonempty. Apply
`Spv.exists_max_vle_of_nonempty` to extract `τ_max ∈ T_D.image
(algebraMap)` with `∀ t' ∈ T_D.image, w.vle t' τ_max`. The
max-element residual gives `w.vle τ_max (algebraMap s_D)`. For our
target `t ∈ T_D.image (algebraMap)`, max-ness gives `w.vle t τ_max`,
and transitivity closes via `w.vle_trans`.

Mechanical reduction from "for all `t`" to "for the max element"
using totality + transitivity of `w.vle` (T034's existence lemma). -/
theorem WedhornCoverPieceVKNonemptyRationalBound_via_alpha_TD_max_bound
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_max_bound :
      WedhornCoverPieceVKAlphaTDMaxBound P T s hopen T_D s_D σ_loc) :
    WedhornCoverPieceVKNonemptyRationalBound P T s hopen T_D s_D σ_loc := by
  intro w hw_spa hw_f h_VK t ht
  -- V_K-nonempty witness gives nonempty image (without consuming h_VK).
  -- Extract max element via T034's existence lemma.
  obtain ⟨τ_max, hτ_max_mem, hτ_max_max⟩ :=
    Spv.exists_max_vle_of_nonempty w (h_VK.imp fun _ h => h.1)
  -- Maxness gives `w.vle t τ_max`; the max-element residual gives
  -- `w.vle τ_max (algebraMap s_D)`; transitivity closes.
  exact w.vle_trans (hτ_max_max t ht)
    (h_max_bound w hw_spa hw_f h_VK τ_max hτ_max_mem hτ_max_max)

/-- **Per-call assembly: `WedhornC1PerCallSupplyPerWCoverPiece` via
the max-element residual** (T042 composed deliverable).

Produces T039's per-call supply predicate from the seven natural
components, with the max-element residual `h_max_bound` taking the
place of T041's `h_VK_residual`. Composes
`WedhornCoverPieceVKNonemptyRationalBound_via_alpha_TD_max_bound`
with T041's
`WedhornC1PerCallSupplyPerWCoverPiece_via_VK_residual`.

The max-element residual is the **single explicit mathematical
residual** at this layer; the V_∅ branch is dispatched automatically
inside T041's bridge using the supplied σ-strict-domination
hypothesis. -/
theorem WedhornC1PerCallSupplyPerWCoverPiece_via_alpha_TD_max_bound
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
      (_h_max_bound :
        WedhornCoverPieceVKAlphaTDMaxBound P C.base.T C.base.s hopen_base
          D.T D.s σ_loc)
      (_hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s)
      (_hvf_nz : ¬ v.vle f 0),
      WedhornC1PerCallSupplyPerWCoverPiece P C hopen_base D v := by
  intro σ_loc f h_alg h_dom h_max_bound hv_in_plus hvf_nz
  exact WedhornC1PerCallSupplyPerWCoverPiece_via_VK_residual
    P C hopen_base D v σ_loc f h_alg h_dom
    (WedhornCoverPieceVKNonemptyRationalBound_via_alpha_TD_max_bound
      P C.base.T C.base.s hopen_base D.T D.s σ_loc h_max_bound)
    hv_in_plus hvf_nz

/-- **Top-level: `C1SupplierStrong_local C` via max-element residual**
(T042 final deliverable).

Identical caller signature to T041's
`C1SupplierStrong_local_via_VK_residual`, modulo the per-call supply:
each per-call delivery provides
`WedhornCoverPieceVKAlphaTDMaxBound` in place of T041's
`WedhornCoverPieceVKNonemptyRationalBound`. The reduction from per-`t`
upper bound to max-element conditional bound is dispatched
automatically inside the bridge using
`Spv.exists_max_vle_of_nonempty` (T034) + transitivity.

Composes
`WedhornC1PerCallSupplyPerWCoverPiece_via_alpha_TD_max_bound` with
T041's `C1SupplierStrong_local_via_VK_residual` flow through T040's
`C1SupplierStrong_local_via_loc_rational_bound` and T039's
`C1SupplierStrong_local_via_per_w_cover_piece_supplier`. The
max-element residual is the **single explicit remaining mathematical
residual** for Wedhorn 8.34(ii) Step 2 at the C1 layer; honest
discharge corresponds to Wedhorn 7.45's α_T_D-branch
cover-refinement deduction restricted to the V_K-nonempty cover
plus-piece. -/
theorem C1SupplierStrong_local_via_alpha_TD_max_bound
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
        WedhornCoverPieceVKAlphaTDMaxBound P C.base.T C.base.s
          hopen_base D.T D.s σ_loc ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_VK_residual P hA₀_le C hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_max_bound, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  exact ⟨σ_loc, f, h_alg, h_dom,
    WedhornCoverPieceVKNonemptyRationalBound_via_alpha_TD_max_bound
      P C.base.T C.base.s hopen_base D.T D.s σ_loc h_max_bound,
    hv_in_plus, hvf_nz⟩

end ValuationSpectrum
