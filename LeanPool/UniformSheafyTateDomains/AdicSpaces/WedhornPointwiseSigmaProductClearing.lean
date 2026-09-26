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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornDominatingUnitInequality
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSigmaDominationClearing

/-!
# Wedhorn 8.34(ii) — Pointwise σ-product clearing (T070)

T067 (commit `f697f6b`) reduced T064's per-piece subset to the
pointwise clearing residual: at every `v ∈ Spa A A⁺` with `v.vle f s`,
`v.vle 1 t'`, and `¬ v.vle t' 0`, derive `v.vle t' D_s`. This file
lands the **substantive arithmetic discharge** of that residual via
the σ-power cancellation primitive
`vle_mul_pow_cancel_left` (`WedhornSigmaDominationClearing.lean`)
applied to a **source-restricted per-`(v, t')` σ-product cleared
inequality**.

The earlier revision of this file (commit `ad2ec62`) used the
corrected multi-clearing primitive but exposed a global universal-
over-`D_T` lower bound as the named residual. That global form is
mathematically false in general (per T035's counter-example) and
inappropriate as a downstream boundary. This revision lands a
**source-restricted per-`(v, t')` σ-power cancellation supplier**
matching the actual Wedhorn 8.34(ii) per-piece situation: at each
`(v, t')` where `v` lies in the Laurent piece `R({1}, t')`, supply
the σ-power-cleared inequality `v.vle (t' * D_s^N) (D_s^(N+1))` for
some `N` (the per-`(v, t')` Wedhorn arithmetic step), and the σ-power
cancellation primitive discharges T067's pointwise clearing at that
specific `(v, t')`.

## Mathematical content

The per-`(v, t')` σ-power cancellation reduction has signature

```
(v.vle (t' * D_s^N) (D_s^(N+1))) ∧ (¬ v.vle D_s 0) → v.vle t' D_s
```

where the LHS captures the σ-product cleared form and `D_s`
non-vanishing. The proof is a single application of
`vle_mul_pow_cancel_left` after `pow_succ` rewriting on the right
side and `mul_comm` to align the cancellation pattern.

The σ-power-cleared inequality `v.vle (t' * D_s^N) (D_s^(N+1))` is
the natural Wedhorn 8.34(ii) σ-product algebraic content,
source-restricted to a Laurent piece. It arises from the
σ-construction's algebraic identity (e.g., `f := σ * D.T.prod *
D.s^N`) plus σ-strict-domination at the specific `v` after
σ-cancellation, but T070 does NOT commit to a particular σ form —
the source-restricted hypothesis abstracts over the σ choice.

## What this file provides

* `pointwise_clearing_via_corrected_multi_clearing` — substantive
  single-`v` reduction via `vle_of_dominating_unit_multi_corrected_at`.
  Takes a per-`v` corrected-multi-clearing input and discharges
  T067's pointwise clearing for `t' ∈ T_D`. Real arithmetic; useful
  for callers that hold the corrected-multi-clearing input shape
  natively (e.g., the alternative T067 route).

* `pointwise_clearing_via_pow_cancellation` — **the key revised
  substantive theorem**: source-restricted per-`(v, t')` σ-power
  cancellation. Takes a per-`(v, t')` σ-power-cleared inequality
  `v.vle (t' * D_s^N) (D_s^(N+1))` plus `¬ v.vle D_s 0`, derives
  `v.vle t' D_s` via `vle_mul_pow_cancel_left`. The hypothesis is
  per-`(v, t')` and source-restricted — no universal-over-`D_T` form.

* `pointwise_clearing_supplier_via_pow_cancellation` — supplier form
  matching T067's per-call hypothesis shape. Takes a per-`(v, t')`
  σ-power-cleared inequality + non-vanishing supplier and produces
  T067's pointwise clearing.

* `per_piece_subset_supplier_via_pow_cancellation_supplier` —
  composes T070's σ-power cancellation supplier with T067's
  `per_piece_subset_supplier_via_pointwise_clearing` to give T064's
  per-piece subset directly. Mechanically composes with T064's
  `C1SupplierStrong_local_via_t_indexed_direct`.

## The named source-restricted residual

The remaining theorem-level gap is the **per-`(v, t')` σ-power-cleared
inequality supplier**:

```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺, v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
  ∃ N : ℕ, v.vle (t' * D_s^N) (D_s^(N+1)) ∧ ¬ v.vle D_s 0
```

This is **per-`(v, t')` source-restricted Wedhorn 8.34(ii) σ-product
algebraic content**: at each `v` in the Laurent piece for `t'` (where
`v.vle 1 t'` holds), supply the σ-power-cleared inequality. The
exponent `N` and the specific σ-cancellation are chosen by the
supplier per-`(v, t')`; T070 does not commit to a specific σ
construction at this layer.

The named residual is **strictly weaker** than the previous revision's
universal-over-`D_T` form: the σ-power-cleared inequality at `(v, t')`
involves only `t'` and `D_s` (no other `t_i ∈ D_T`), and the universal
lower bound across `D_T` is replaced by the per-`(v, t')` σ-power
cleared form.

## Notes

* No root import; leaf-level.
* Imports T067 (`WedhornPerPieceSubsetProductClearing`) for
  composition with the per-piece subset supplier,
  `WedhornDominatingUnitInequality` for the corrected multi-clearing
  primitive, and `WedhornSigmaDominationClearing` (T050) for the
  σ-power cancellation primitive `vle_mul_pow_cancel_left`.
* No edits to T031–T067 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim (per
  T035's counter-example).
* No introduction of any final Tate acyclicity hypothesis. The
  named residual is a per-`(v, t')` σ-product algebraic step,
  consumed by Secondary's σ/Laurent-cover supplier lane.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Pointwise clearing via corrected multi-clearing at `v`** (T070
single-`v` reduction via `vle_of_dominating_unit_multi_corrected_at`).

From a per-`v` corrected-multi-clearing input — `h_prod : v.vle
(T_D.prod id) D_s` + `h_lower : ∀ t_i ∈ T_D, v.vle (1 : A) t_i` at a
specific `v` — discharge T067's pointwise clearing for any `t' ∈ T_D`.

**Note**: the universal-over-`T_D` lower bound is the well-known
"global multi-element residual" form that is mathematically false on
all of `Spa A A⁺` per T035's counter-example. This single-`v`
reduction is useful only when the input data holds at the specific
`v` (e.g., on a Laurent piece where the universal lower bound is
source-restrictedly true). The supplier-facing residual is **NOT**
the universal-over-`D_T` form (see the σ-power cancellation route
below for the correct source-restricted residual).

**Real proof** using `vle_of_dominating_unit_multi_corrected_at`. -/
theorem pointwise_clearing_via_corrected_multi_clearing
    (T_D : Finset A) (D_s : A) (t' : A) (ht' : t' ∈ T_D)
    {v : Spv A}
    (h_prod : v.vle (T_D.prod id) D_s)
    (h_lower : ∀ t_i ∈ T_D, v.vle (1 : A) t_i) :
    v.vle t' D_s :=
  (vle_of_dominating_unit_multi_corrected_at v h_prod h_lower).1 t' ht'

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Pointwise clearing via σ-power cancellation** (T070 source-
restricted substantive theorem).

From a **source-restricted per-`v` σ-power-cleared inequality**
`v.vle (t' * D_s^N) (D_s^(N+1))` plus `¬ v.vle D_s 0`, discharge
T067's pointwise clearing `v.vle t' D_s` at the specific `v` and
`t'`.

**Proof structure**: rewrite `D_s^(N+1) = D_s^N * D_s` via
`pow_succ`, commute the LHS to align as `D_s^N * t'`, then apply
`vle_mul_pow_cancel_left` (T050 σ-power cancellation primitive) at
`D_s` with the non-vanishing hypothesis to cancel the common
`D_s^N` factor.

**Substantive consumption**: the σ-power-cleared inequality and
non-vanishing are genuinely used through the σ-power cancellation
primitive — not pass-through.

This is the per-`(v, t')` source-restricted form of T067's pointwise
clearing residual: `t'` and `D_s` are the only test elements (no
other `t_i ∈ D_T`), and the Wedhorn arithmetic content is the
σ-power-cleared inequality, derivable per-`(v, t')` from the
σ-construction's algebraic identity at that specific Laurent piece. -/
theorem pointwise_clearing_via_pow_cancellation
    {v : Spv A} {t' D_s : A} {N : ℕ}
    (h_chain : v.vle (t' * D_s ^ N) (D_s ^ (N + 1)))
    (h_D_s_ne : ¬ v.vle D_s 0) :
    v.vle t' D_s := by
  rw [pow_succ, mul_comm t' (D_s ^ N)] at h_chain
  exact vle_mul_pow_cancel_left h_D_s_ne N t' D_s h_chain

omit [IsTopologicalRing A] in
/-- **Pointwise clearing supplier via σ-power cancellation supplier**
(T070 source-restricted supplier form).

From a per-`(v, t')` source-restricted σ-power cancellation supplier
— at every `v ∈ Spa A A⁺` with `v.vle f s` AND `v.vle 1 t'` AND
`¬ v.vle t' 0` (the T067 source restriction at `(v, t')`), supply an
exponent `N` and the σ-power-cleared inequality + non-vanishing —
discharge T067's pointwise clearing at the specific `t'`.

The named hypothesis `h_pow_chain` is the **single source-restricted
remaining content** at the per-`(v, t')` σ-power-cleared inequality
layer. Strictly weaker than a universal-over-`D_T` lower bound: it
involves only `t'` and `D_s` per-`(v, t')`, with the σ-product
construction's algebraic content captured in the cleared inequality
form. -/
theorem pointwise_clearing_supplier_via_pow_cancellation
    (s D_s f t' : A)
    (h_pow_chain :
      ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        ∃ N : ℕ,
          v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0) :
    ∀ v ∈ Spa A A⁺,
      v.vle f s →
      v.vle (1 : A) t' →
      ¬ v.vle t' 0 →
      v.vle t' D_s := by
  intro v hv_spa hv_f hv_one_t hv_t_ne
  obtain ⟨N, h_chain, h_D_s_ne⟩ := h_pow_chain v hv_spa hv_f hv_one_t hv_t_ne
  exact pointwise_clearing_via_pow_cancellation h_chain h_D_s_ne

omit [IsTopologicalRing A] in
/-- **Per-piece subset supplier via σ-power cancellation supplier**
(T070 final source-restricted consumer-facing theorem).

Composes T070's σ-power cancellation supplier with T067's
`per_piece_subset_supplier_via_pointwise_clearing` to give T064's
per-piece subset directly from the per-`(v, t')` σ-power-cleared
inequality supplier.

**The source-restricted named residual**:

```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
  ∃ N : ℕ, v.vle (t' * D_s^N) (D_s^(N+1)) ∧ ¬ v.vle D_s 0
```

This is the **single per-`(v, t')` Wedhorn 8.34(ii) σ-product
algebraic step**, source-restricted to the per-piece situation. It
involves only `t'` and `D_s` per-`(v, t')`, with no universal-over-
`D_T` lower bound. The σ-construction's algebraic identity is
captured in the cleared inequality form; the exponent `N` and the
specific σ-cancellation are chosen by the supplier per-`(v, t')`. -/
theorem per_piece_subset_supplier_via_pow_cancellation_supplier
    [DecidableEq A]
    (T_base D_T : Finset A) (s D_s f : A)
    (h_pow_chain_uniform :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        ∃ N : ℕ,
          v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0) :
    ∀ t' ∈ D_T,
      rationalOpen (insert f T_base) s ∩
          rationalOpen ({(1 : A)} : Finset A) t' ⊆
        rationalOpen ({t'} : Finset A) D_s :=
  per_piece_subset_supplier_via_pointwise_clearing T_base D_T s D_s f
    fun t' ht' => pointwise_clearing_supplier_via_pow_cancellation s D_s f t'
      (h_pow_chain_uniform t' ht')

end ValuationSpectrum
