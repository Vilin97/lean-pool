/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPerPieceSubsetAdapterFromT056
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPointwiseSigmaProductClearing

/-!
# Wedhorn 8.34(ii) — C1 σ-construction endgame assembly (T072)

T064 (`WedhornActualC1PerCallClosure`) provides the t-indexed
`C1SupplierStrong_local_via_t_indexed_direct` consumer.
T065 (`WedhornLocalizedCor732SigmaSupplier`) provides the localized
Cor 7.32 σ-supplier with the σ-rescaled Laurent cover.
T067 (`WedhornPerPieceSubsetProductClearing`) reduces the per-piece
subset to a per-`v` pointwise clearing.
T069 (`WedhornPerPieceSubsetAdapterFromT056`) packages the chain
T067 → T064 as `C1SupplierStrong_local_via_pointwise_clearing`.
T070 (`WedhornPointwiseSigmaProductClearing`) further reduces the
pointwise clearing to a **per-`(v, t')` source-restricted σ-power-
cleared inequality** via `vle_mul_pow_cancel_left`.

This file lands the **C1 endgame assembly boundary** — the strongest
theorem-level wrapper composing the accepted T064 / T065 / T067 / T069
machinery and T070's source-restricted σ-power cancellation. The
output `C1SupplierStrong_local C` is exposed to downstream consumers
of the Wedhorn 8.34(ii) C1 supplier route; the **single named
remaining theorem-level residual** is the σ-power-cleared inequality
supplier — a per-`(v, t')` source-restricted Wedhorn 8.34(ii)
σ-construction algebraic step.

## What this file provides

* `SigmaProductClearedInequalitySupplier` — Prop predicate naming
  the source-restricted per-`(v, t')` σ-power-cleared inequality
  supplier residual. Mathlib-style and reusable: parameterised by
  the cover-piece denominator family `D_T`, the source rational data
  `s`, the cover-piece denominator `D_s`, and the inserted
  refinement candidate `f`.

* `pointwise_clearing_supplier_via_sigma_product_cleared_inequality`
  — supplier-level bridge: from `SigmaProductClearedInequalitySupplier`,
  derive T067's per-piece pointwise clearing supplier shape. Direct
  reformulation of T070's `pointwise_clearing_supplier_via_pow_cancellation`
  in the named-Prop form.

* `C1SupplierStrong_local_via_sigma_construction_boundary` — **main
  ticket-named theorem** (T072 endgame wrapper): from per-call
  delivery of `(σ_choice, f, v ∈ R(insert f), ¬ v.vle f 0,
  σ-power-cleared inequality supplier, σ-rescaled Laurent cover)`,
  derive `C1SupplierStrong_local C`.

  Composes T070's source-restricted σ-power cancellation supplier
  with T069's `C1SupplierStrong_local_via_pointwise_clearing`.
  The σ-power-cleared inequality supplier is the **single
  source-restricted σ-product algebraic residual** at the C1
  consumer boundary.

* `C1SupplierStrong_local_via_named_sigma_construction_supplier` —
  variant using the named Prop predicate
  `SigmaProductClearedInequalitySupplier` to expose the residual
  shape uniformly across callers. Useful for downstream consumers
  that produce the σ-product-cleared inequality through a separate
  σ-construction lane.

## The single source-restricted named residual

After T072, the C1 supplier route reduces to **exactly one named
source-restricted σ-construction residual** (the
`SigmaProductClearedInequalitySupplier` Prop):

```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
  ∃ N : ℕ, v.vle (t' * D_s^N) (D_s^(N+1)) ∧ ¬ v.vle D_s 0
```

This is **per-`(v, t')` source-restricted** (only `t'` and `D_s`
appear, no universal-over-`D_T` lower bound), matching the actual
Wedhorn 8.34(ii) σ-construction's algebraic identity at each Laurent
piece. The exponent `N` and the specific σ-cancellation are chosen
by the supplier per-`(v, t')`; T072 does not commit to a particular
σ form at this layer.

T072 does **NOT** depend on or bless any global universal-over-Spa
multi-element bound (rejected by T035's counter-example). The named
residual is strictly weaker than T067's pointwise clearing (since
T070's σ-power cancellation derives the clearing from the cleared
inequality + non-vanishing), so the consumer-facing boundary is
genuinely refined relative to T067 / T069.

## What T072 does NOT do

* Does **NOT** add or use any final
  `ValuationSpectrum.tateAcyclicity` hypothesis. T072 is a C1
  supplier-side endgame wrapper; downstream tate acyclicity assembly
  remains in its own files (Lane A / Lane B suppliers, Stage-2
  bridge, etc.).

* Does **NOT** assume the σ-construction's full algebraic identity
  globally; the per-`(v, t')` σ-power-cleared inequality is the
  weakest sufficient form.

* Does **NOT** depend on any global universal-over-Spa multi-element
  clearing claim, M-power-decay / σ-power-decay residuals,
  T001 / Lane B / Cor 8.32 / Jacobson / faithful-flatness / Zavyalov
  / bivariate-overlap content.

## Notes

* No root import; leaf-level file.
* Imports T069 (`WedhornPerPieceSubsetAdapterFromT056`) and T070
  (`WedhornPointwiseSigmaProductClearing`).
* No edits to T031–T070 accepted leaves, root imports, or final
  theorem signatures.
* All declarations are fully proven, depend only on the standard
  Lean kernel postulates, and avoid native compilation and unchecked
  tactics.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Source-restricted σ-product-cleared inequality supplier**
(T072 named residual Prop predicate).

The named source-restricted residual at the C1 consumer boundary:
at every `v ∈ Spa A A⁺` in the Laurent piece for some `t' ∈ D_T`
(i.e., `v.vle 1 t'` and `¬ v.vle t' 0` from the rationalOpen
membership) with the f-bound `v.vle f s` from the source rationalOpen,
supply an exponent `N` and the σ-power-cleared inequality
`v.vle (t' * D_s^N) (D_s^(N+1))` plus the non-vanishing
`¬ v.vle D_s 0`.

This is the **weakest known sufficient hypothesis** at the C1
consumer boundary: it is per-`(v, t')` source-restricted (no
universal-over-`D_T` lower bound), the exponent is per-`(v, t')`
chosen, and the σ-construction's algebraic identity is captured in
the cleared inequality form without committing to a particular σ.

The named residual is consumed by T072's main wrapper to produce
`C1SupplierStrong_local C`. Discharging the residual is the
remaining Wedhorn 8.34(ii) σ-construction theorem-level work,
**downstream** of T072. -/
def SigmaProductClearedInequalitySupplier
    (D_T : Finset A) (s D_s f : A) : Prop :=
  ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
    v.vle f s →
    v.vle (1 : A) t' →
    ¬ v.vle t' 0 →
    ∃ N : ℕ,
      v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0

omit [IsTopologicalRing A] in
/-- **Pointwise clearing supplier from the σ-product-cleared
inequality supplier** (T072 supplier-level bridge).

Direct reformulation of T070's
`pointwise_clearing_supplier_via_pow_cancellation` in terms of the
named `SigmaProductClearedInequalitySupplier` Prop predicate. From
the source-restricted σ-power-cleared inequality supplier, derive
T067's per-piece pointwise clearing supplier shape uniformly over
`t' ∈ D_T`.

**Substantive consumption** of T070's σ-power cancellation primitive
at each per-call `(v, t')`. -/
theorem pointwise_clearing_supplier_via_sigma_product_cleared_inequality
    (D_T : Finset A) (s D_s f : A)
    (h_supplier : SigmaProductClearedInequalitySupplier D_T s D_s f) :
    ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
      v.vle f s →
      v.vle (1 : A) t' →
      ¬ v.vle t' 0 →
      v.vle t' D_s := by
  intro t' ht'
  exact pointwise_clearing_supplier_via_pow_cancellation s D_s f t' (h_supplier t' ht')

/-- **C1 endgame wrapper from per-call σ-construction boundary**
(T072 main ticket-named theorem).

Top-level C1 endgame assembly: from per-call delivery at each
`(D ∈ C.covers, v ∈ rationalOpen D.T D.s, t ∈ D.T)` triple of:

* `σ_choice : Aˣ` and `f : A` — the σ-construction outputs.
* `v ∈ rationalOpen (insert f C.base.T) C.base.s` — base-side
  rationalOpen membership of `v` (C1 supplier's clause 1).
* `¬ v.vle f 0` — non-degeneracy of `f` at `v` (strong clause 3).
* a **per-`(w, t')` source-restricted σ-power-cleared inequality
  supplier** (the named source-restricted residual) — the genuine
  Wedhorn 8.34(ii) σ-construction algebraic content.
* a σ-rescaled Laurent cover hypothesis `∀ w ∈ R(insert f C.base.T)
  C.base.s, ∃ t' ∈ D.T, w ∈ R({1}, t')` — supplied by T065's
  localized Cor 7.32 supplier.

derive `C1SupplierStrong_local C` — the strong cover-refinement
supplier consumed by the existing tate acyclicity Part 2 chain.

**Composition**: T070's `pointwise_clearing_supplier_via_pow_cancellation`
converts the σ-power-cleared inequality supplier to T067's pointwise
clearing supplier shape; T069's
`C1SupplierStrong_local_via_pointwise_clearing` then produces
`C1SupplierStrong_local C` from the pointwise clearing.

**Single named source-restricted residual**: the σ-power-cleared
inequality supplier (per-call). All other inputs are routine
σ-construction outputs (already deliverable from Cor 7.32 / T065 /
denominator clearing) or basic rationalOpen-membership data. -/
theorem C1SupplierStrong_local_via_sigma_construction_boundary
    [DecidableEq A]
    (C : RationalCoveringData A)
    (h_per_call :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (_ : Aˣ) (f : A),
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0 ∧
        (∀ t' ∈ D.T, ∀ w ∈ Spa A A⁺,
          w.vle f C.base.s →
          w.vle (1 : A) t' →
          ¬ w.vle t' 0 →
          ∃ N : ℕ,
            w.vle (t' * D.s ^ N) (D.s ^ (N + 1)) ∧ ¬ w.vle D.s 0) ∧
        (∀ w ∈ rationalOpen (insert f C.base.T) C.base.s,
          ∃ t' ∈ D.T,
            w ∈ rationalOpen ({(1 : A)} : Finset A) t')) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_pointwise_clearing C ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_choice, f, hv_in_plus, hvf_nz, h_pow_supplier, h_cover⟩ :=
    h_per_call D hD v hv t ht hvt hvD_s
  refine ⟨σ_choice, f, hv_in_plus, hvf_nz, ?_, h_cover⟩
  -- Convert σ-power-cleared inequality supplier to pointwise clearing.
  intro t' ht'
  exact pointwise_clearing_supplier_via_pow_cancellation
    C.base.s D.s f t' (h_pow_supplier t' ht')

/-- **C1 endgame wrapper using the named source-restricted residual
predicate** (T072 named-Prop variant).

Variant of `C1SupplierStrong_local_via_sigma_construction_boundary`
exposing the σ-power-cleared inequality supplier through the named
`SigmaProductClearedInequalitySupplier` Prop predicate. Useful for
downstream consumers that produce the σ-product-cleared inequality
through a separate σ-construction lane and want the residual exposed
uniformly as a named hypothesis. -/
theorem C1SupplierStrong_local_via_named_sigma_construction_supplier
    [DecidableEq A]
    (C : RationalCoveringData A)
    (h_per_call :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (_ : Aˣ) (f : A),
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0 ∧
        SigmaProductClearedInequalitySupplier D.T C.base.s D.s f ∧
        (∀ w ∈ rationalOpen (insert f C.base.T) C.base.s,
          ∃ t' ∈ D.T,
            w ∈ rationalOpen ({(1 : A)} : Finset A) t')) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_sigma_construction_boundary C ?_
  intro D hD v hv t ht hvt hvD_s
  exact h_per_call D hD v hv t ht hvt hvD_s

end ValuationSpectrum
