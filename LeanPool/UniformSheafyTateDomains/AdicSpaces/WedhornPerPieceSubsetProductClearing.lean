/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornActualC1PerCallClosure
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLaurentLocalBoundsFromCor732

/-!
# Wedhorn 8.34(ii) — Per-piece subset via product clearing (T067)

T064 (commit `d5e2abe`) accepted the actual C1 per-call consumer:
`C1SupplierStrong_local_via_t_indexed_direct` reduces the strong C1
supplier to per-call σ-free t-indexed inputs over `D.T`. The two
remaining inputs are:

* **Per-piece subset** (this file's lane): for each `t' ∈ D.T`,
  `rationalOpen (insert f C.base.T) C.base.s ∩ rationalOpen ({1}) t' ⊆
  rationalOpen ({t'}) D.s`.

* **Laurent cover witness** (T065 / Secondary's lane): the σ-rescaled
  Laurent cover hypothesis at the source.

This file lands the **per-piece subset arithmetic supplier**: the
strongest theorem reducing T064's per-piece subset input to an exact
named pointwise valuation-clearing residual, with all non-arithmetic
content (Spa membership threading, non-vanishing derivation,
rationalOpen assembly) discharged.

## Mathematical content

At any `v ∈ Spa(A, A⁺)` satisfying the LHS intersection
`v ∈ R(insert f T_base, s) ∩ R({1}, t')`, we have:

* `v.vle f s` (from `f ∈ insert f T_base`'s per-element bound).
* `v.vle (1 : A) t'` (from `R({1}, t')`'s per-element bound at 1).
* `¬ v.vle t' 0` (from `R({1}, t')`'s non-vanishing).
* `∀ c ∈ T_base, v.vle c s` and `¬ v.vle s 0` (from
  `R(insert f T_base, s)`'s remaining structure).

The RHS `v ∈ R({t'}, D_s)` requires:

* `v.vle t' D_s` — the **per-element upper bound at `D_s`**, the
  Wedhorn 8.34(ii) per-piece arithmetic content.
* `¬ v.vle D_s 0` — non-vanishing of `D_s`, **derivable** from the
  upper bound `v.vle t' D_s` plus the LHS lower bound `v.vle 1 t'`
  via transitivity + `Spv.not_vle_one_zero`.

T067 isolates the **pointwise clearing** `v.vle t' D_s` as the exact
named arithmetic residual, with all surrounding rationalOpen / Spa
membership / non-vanishing assembly discharged. The pointwise
clearing is the genuine Wedhorn 8.34(ii) σ-product-clearing content
arising from the σ-construction algebraic identity
`f := σ * (D.T.prod or t') * D.s^N` plus σ-strict-domination at `v`.

## What this file provides

* `per_piece_subset_via_pointwise_clearing` — substantive reduction:
  from a per-`v` pointwise clearing hypothesis `v.vle f s ∧ v.vle 1 t'
  ∧ ¬ v.vle t' 0 → v.vle t' D_s` (at v ∈ Spa A A⁺ in the intersection),
  derive T064's per-piece subset for the specific `t'`. The non-
  vanishing of `D_s` is auto-derived via `not_vle_zero_of_one_vle`
  (T053 reusable primitive).

* `per_piece_subset_supplier_via_pointwise_clearing` — uniform-over-
  `t' ∈ D.T` version of the above. Direct supplier for T064's
  per-call hypothesis shape.

* `per_piece_subset_via_corrected_multi_clearing_at_v` — alternative
  reduction route via the existing
  `vle_of_dominating_unit_multi_corrected_at` (`WedhornDominatingUnitInequality.lean`):
  takes a per-`v` product upper bound + per-element lower bound for
  ALL of `D.T` (a stronger hypothesis than the per-`t'` pointwise
  clearing, but uses the existing corrected multi-clearing primitive).

## Why the pointwise clearing is the natural Wedhorn 8.34(ii) residual

The Wedhorn 8.34(ii) σ-construction picks `f` and `σ` such that on
the Laurent piece `V_t'` (where `v.vle 1 t'` holds), the algebraic
identity
`f = σ * (multi-element factor) * D.s^N`
plus σ-strict-domination at `v` clears to give `v.vle t' D.s`. The
exact form of the factor depends on the σ-construction's specific
choice; T067 exposes this clearing as a named residual without
committing to a particular factor structure, leaving room for the
σ-construction's natural choice.

## Notes

* No root import; leaf-level.
* Imports T064 (`WedhornActualC1PerCallClosure`) for the per-call
  consumer signature and T053 (`WedhornLaurentLocalBoundsFromCor732`)
  for the `not_vle_zero_of_one_vle` primitive.
* No edits to T031–T065 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-- **Per-piece subset via pointwise clearing residual** (T067 main
substantive theorem).

From a per-`v` pointwise clearing hypothesis — at every `v ∈ Spa A A⁺`
satisfying `v.vle f s` (the f-bound from the LHS rationalOpen) AND
`v.vle 1 t'` (from `V_t' = R({1}, t')`) AND `¬ v.vle t' 0` (from
`V_t'`), supply the per-element upper bound `v.vle t' D_s` —
derive T064's per-piece subset
`rationalOpen (insert f T_base) s ∩ rationalOpen ({1}) t' ⊆
rationalOpen ({t'}) D_s` for the specific `t'`.

**Proof structure**: take `v` in the LHS intersection. Extract the
four pieces of LHS data. Apply the pointwise clearing to obtain
`v.vle t' D_s`. Derive `¬ v.vle D_s 0` from `v.vle 1 t'` + `v.vle t'
D_s` via transitivity + `not_vle_zero_of_one_vle` (T053 reusable
primitive). Assemble the RHS rationalOpen membership.

**Substantive consumption**: every input is genuinely used. The
pointwise clearing is the **single named arithmetic residual** for
T067. -/
theorem per_piece_subset_via_pointwise_clearing
    [DecidableEq A]
    (T_base : Finset A) (s D_s f t' : A)
    (h_clearing :
      ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        v.vle t' D_s) :
    rationalOpen (insert f T_base) s ∩
        rationalOpen ({(1 : A)} : Finset A) t' ⊆
      rationalOpen ({t'} : Finset A) D_s := by
  intro v ⟨⟨hv_spa, hv_per_c, _⟩, _, hv_per_one, hv_t_ne⟩
  have hv_one_t : v.vle (1 : A) t' :=
    hv_per_one (1 : A) (Finset.mem_singleton.mpr rfl)
  have hv_t_D_s : v.vle t' D_s :=
    h_clearing v hv_spa (hv_per_c f (Finset.mem_insert_self f T_base)) hv_one_t hv_t_ne
  exact ⟨hv_spa, fun t'' ht'' => Finset.mem_singleton.mp ht'' ▸ hv_t_D_s,
    not_vle_zero_of_one_vle (v.vle_trans hv_one_t hv_t_D_s)⟩

/-- **Per-piece subset supplier — uniform-over-`t' ∈ D.T` form** (T067
direct T064 supplier).

Uniform-over-`t' ∈ D_T` version of `per_piece_subset_via_pointwise_clearing`,
matching T064's per-call hypothesis shape exactly. From a uniform
pointwise clearing hypothesis, derive T064's per-piece subset for
every `t' ∈ D_T`. -/
theorem per_piece_subset_supplier_via_pointwise_clearing
    [DecidableEq A]
    (T_base D_T : Finset A) (s D_s f : A)
    (h_clearing_uniform :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        v.vle t' D_s) :
    ∀ t' ∈ D_T,
      rationalOpen (insert f T_base) s ∩
          rationalOpen ({(1 : A)} : Finset A) t' ⊆
        rationalOpen ({t'} : Finset A) D_s :=
  fun t' ht' =>
    per_piece_subset_via_pointwise_clearing T_base s D_s f t'
      (h_clearing_uniform t' ht')

/-- **Per-piece subset via the corrected multi-clearing primitive**
(T067 alternative route via `vle_of_dominating_unit_multi_corrected_at`).

Alternative reduction route consuming the existing
`vle_of_dominating_unit_multi_corrected_at`
(`WedhornDominatingUnitInequality.lean:280`). From a per-`v` product
upper bound `v.vle (D_T.prod id) D_s` AND a per-`v` per-element lower
bound for **ALL of `D_T`** `∀ t_i ∈ D_T, v.vle 1 t_i`, derive T064's
per-piece subset for any `t' ∈ D_T`.

**Trade-off** vs `per_piece_subset_via_pointwise_clearing`: this
route uses the existing corrected multi-clearing primitive directly,
but the per-element lower bound input is **uniform over `D_T`**
(stronger hypothesis than per-`t'` pointwise). In the Wedhorn
8.34(ii) per-piece structure, the per-`t'` pointwise hypothesis is
the natural per-piece data; the uniform-over-`D_T` hypothesis is
universally false on `Spa A A⁺` (per T035's counter-example) and
must itself be source-restricted to a Laurent piece V_τ.

Useful when the per-call delivery has the corrected-multi-clearing
input shape natively (e.g., from upstream consumers that already
package the product + per-element lower bound together). -/
theorem per_piece_subset_via_corrected_multi_clearing_at_v
    [DecidableEq A]
    (T_base D_T : Finset A) (s D_s f : A) (t' : A) (ht' : t' ∈ D_T)
    (h_per_v :
      ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (D_T.prod id) D_s ∧ ∀ t_i ∈ D_T, v.vle (1 : A) t_i) :
    rationalOpen (insert f T_base) s ∩
        rationalOpen ({(1 : A)} : Finset A) t' ⊆
      rationalOpen ({t'} : Finset A) D_s := by
  refine per_piece_subset_via_pointwise_clearing T_base s D_s f t' ?_
  intro v hv_spa hv_f _hv_one_t _hv_t_ne
  obtain ⟨h_prod, h_lower⟩ := h_per_v v hv_spa hv_f
  exact (vle_of_dominating_unit_multi_corrected_at v h_prod h_lower).1 t' ht'

end ValuationSpectrum
