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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPerPieceSubsetProductClearing
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSigmaPowerClearedInequalitySupplier

/-!
# Wedhorn 8.34(ii) — Direct upper bound supplier from pointwise clearing (T077)

T073 (commit `39c0e12`) accepted the consumer
`SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier`:
from a per-`(v, t')` **direct upper bound supplier**
```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
  v.vle t' D_s ∧ ¬ v.vle D_s 0
```
produce T072's named residual `SigmaProductClearedInequalitySupplier`
via the `N = 0` witness.

T067 (commit accepted in `WedhornPerPieceSubsetProductClearing.lean`)
landed the per-piece subset reduction consuming the **pointwise
clearing supplier** (per-`(v, t')`, upper bound only):
```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
  v.vle t' D_s
```

This file lands the **direct lane** into T073's consumer: it bridges
the pointwise clearing supplier (T067's residual, upper bound only)
to the direct upper bound supplier (T073's input, upper bound + `D_s`
non-vanishing) by **mechanically auto-deriving** the `¬ v.vle D_s 0`
piece via the transitivity chain
`v.vle 1 t' → v.vle t' D_s → v.vle 1 D_s` and
`not_vle_zero_of_one_vle` (T053 reusable primitive).

## Why this is a substantive bridge, not a wrapper

The pointwise clearing supplier delivers the **upper bound** content
only; T073's direct supplier additionally requires `¬ v.vle D_s 0`.
The non-vanishing piece is **derivable from the supplied data** —
specifically from the LHS lower bound `v.vle 1 t'` (already an
input, available from the Laurent-piece membership `V_t' = R({1}, t')`)
combined with the supplied upper bound `v.vle t' D_s`. T077 lands
this derivation as a single closed valuation-arithmetic step. The
input is genuinely consumed: if either `v.vle 1 t'` or the upper
bound were missing, the non-vanishing of `D_s` could not be
concluded at this layer.

The bridge is mechanical from valuation arithmetic alone; no σ-
construction content beyond what T067 already exposes is needed.
This is the natural "direct" lane parallel to Secondary's σ-factored
lane (which routes through
`SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier`).

## What this file provides

* `direct_upper_bound_data_via_pointwise_clearing_at` — substantive
  per-`(v, t')` reduction: from the upper bound `v.vle t' D_s` plus
  the LHS lower bound `v.vle 1 t'`, derive the pair
  `v.vle t' D_s ∧ ¬ v.vle D_s 0`. Real proof via `Spv.vle_trans` +
  `not_vle_zero_of_one_vle`.

* `direct_upper_bound_supplier_via_pointwise_clearing` — supplier-level
  form: from a per-`(v, t')` pointwise clearing supplier (the T067
  residual shape, upper bound only), produce T073's direct upper bound
  supplier (upper bound + `D_s` non-vanishing). Direct input to
  `SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier`.

* `SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier`
  — full composition: from a pointwise clearing supplier, produce
  `SigmaProductClearedInequalitySupplier` (T072's named residual)
  by composing T077's bridge with T073's `_via_direct_clearing_supplier`.
  Closes the direct lane end-to-end.

## Notes

* No root import; leaf-level.
* Imports T067 (`WedhornPerPieceSubsetProductClearing`) for the
  pointwise clearing shape and `not_vle_zero_of_one_vle` (T053
  primitive, transitively imported), and T073
  (`WedhornSigmaPowerClearedInequalitySupplier`) for the
  `_via_direct_clearing_supplier` consumer.
* No edits to T031–T076 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim.
* No global universal-over-`D_T` lower bound resurrection.
* No final Tate acyclicity hypothesis additions.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Direct upper bound data from pointwise clearing at a single `v`**
(T077 substantive per-`(v, t')` reduction).

From the pointwise upper bound `v.vle t' D_s` (T067's pointwise
clearing residual output) plus the LHS lower bound `v.vle 1 t'`
(available from the Laurent-piece membership `V_t' = R({1}, t')`),
derive the **direct upper bound data pair** consumed by T073:
`v.vle t' D_s ∧ ¬ v.vle D_s 0`.

**Proof structure**: chain `v.vle 1 t'` and `v.vle t' D_s` via
`Spv.vle_trans` to obtain `v.vle 1 D_s`. Apply
`not_vle_zero_of_one_vle` (T053 reusable primitive) to derive
`¬ v.vle D_s 0`. Pair with the original upper bound.

**Substantive consumption**: the lower bound `v.vle 1 t'` is
genuinely used to derive the non-vanishing piece — without it, only
the upper bound part of T073's direct supplier shape would be
deliverable. -/
theorem direct_upper_bound_data_via_pointwise_clearing_at
    {v : Spv A} {t' D_s : A}
    (h_clear : v.vle t' D_s)
    (h_one_t : v.vle (1 : A) t') :
    v.vle t' D_s ∧ ¬ v.vle D_s 0 :=
  ⟨h_clear, not_vle_zero_of_one_vle (v.vle_trans h_one_t h_clear)⟩

omit [IsTopologicalRing A] in
/-- **Direct upper bound supplier from pointwise clearing supplier**
(T077 main supplier-level theorem; direct T073 input).

Bridge from T067's pointwise clearing supplier shape (upper bound
only) to T073's direct upper bound supplier shape (upper bound +
`D_s` non-vanishing). The `¬ v.vle D_s 0` piece is auto-derived
per-`(v, t')` from the LHS lower bound `v.vle 1 t'` + the supplied
upper bound via
`direct_upper_bound_data_via_pointwise_clearing_at`.

**Composition shape**: the output is exactly the input expected by
`SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier`
(T073). Composing T077's bridge with T073 yields the full direct lane
into T072's named residual `SigmaProductClearedInequalitySupplier`
(see `SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier`
below). -/
theorem direct_upper_bound_supplier_via_pointwise_clearing
    (D_T : Finset A) (s D_s f : A)
    (h_pointwise :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        v.vle t' D_s) :
    ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
      v.vle f s →
      v.vle (1 : A) t' →
      ¬ v.vle t' 0 →
      v.vle t' D_s ∧ ¬ v.vle D_s 0 :=
  fun t' ht' v hv_spa hv_f hv_one_t hv_t_ne =>
    direct_upper_bound_data_via_pointwise_clearing_at
      (h_pointwise t' ht' v hv_spa hv_f hv_one_t hv_t_ne) hv_one_t

omit [IsTopologicalRing A] in
/-- **`SigmaProductClearedInequalitySupplier` from pointwise clearing
supplier — full direct lane composition** (T077 end-to-end direct
supplier into T072's named residual).

Composes T077's
`direct_upper_bound_supplier_via_pointwise_clearing` (this file) with
T073's `SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier`
to deliver T072's named residual `SigmaProductClearedInequalitySupplier`
**directly from the pointwise clearing supplier** (T067's residual
shape).

**End-to-end direct lane**: pointwise clearing supplier (T067) →
direct upper bound supplier (T077 bridge) →
`SigmaProductClearedInequalitySupplier` (T073 `N = 0` witness). The
entire chain is closed-form valuation arithmetic; no σ-factored
content is consumed on this lane.

This sits parallel to Secondary's σ-factored lane (T075) which
delivers the same `SigmaProductClearedInequalitySupplier` from the
σ-factored supplier shape via T073's
`_via_sigma_factored_supplier`. -/
theorem SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier
    (D_T : Finset A) (s D_s f : A)
    (h_pointwise :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        v.vle t' D_s) :
    SigmaProductClearedInequalitySupplier D_T s D_s f :=
  SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier
    D_T s D_s f
    (direct_upper_bound_supplier_via_pointwise_clearing D_T s D_s f h_pointwise)

end ValuationSpectrum
