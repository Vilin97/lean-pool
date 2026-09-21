/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornDominatingBranchInequality
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizationDenominatorUnit

/-!
# Wedhorn multi-branch subset inequality (algebraic core)

Multi-`t'` valuation inequality on the Wedhorn 8.34(ii) lane: from a
per-`t'` σ-domination chain plus an explicit σ-power-decay hypothesis
on `C_base_s`, derive the subset-side conclusion
`(∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0`.

This file lands the **algebraic core** of the σ-clearing transfer at a
fixed Spa-point `w`: with the σ-power-decay condition `w.vle C_base_s
((σ : A) * D_s ^ (N + 1))` supplied as an explicit hypothesis (the
Wedhorn 8.34(ii) / Cor 7.32 input), the transfer is pure
unit-cancellation + power-cancellation arithmetic.

## Honest hypothesis discussion

The full subset-side σ-clearing
`R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)` requires per-`w` case
analysis on which `τ ∈ T_D ∪ {D_s}` wins σ-domination at `w`, and the
specific Cor 7.32 σ-power-decay structure. This file does **not**
attempt to derive the σ-power-decay; it consumes it as an explicit
input. The genuinely-new Wedhorn content is the Cor 7.32 σ-construction
plus the choice of `N`, both upstream of the algebraic step here.

The chosen-form per-`t'` chain hypothesis
`w.vle ((σ : A) * t' * D_s ^ N) C_base_s` corresponds to the candidate
shape `f := (σ : A) * t' * D_s ^ N` in the **single-`t'`** Wedhorn
8.34(ii) candidate; for the multi-`t'` candidate `f := (σ : A) *
(T_D.prod id) * D_s ^ N`, the per-`t'` chain is recovered via
factor-extraction from `∏ T_D` after a separate boundedness argument
(also genuinely Wedhorn content, residual recorded below).

## What this file provides

* `vle_iff_mul_unit_right` — `v.vle (a * σ) (b * σ) ↔ v.vle a b`
  (cancellation of a unit factor on the right).
* `vle_iff_mul_unit_left` — `v.vle (σ * a) (σ * b) ↔ v.vle a b`
  (cancellation of a unit factor on the left).
* `vle_t_D_s_of_sigma_decay_chain_at` — single-`t'` transfer: the
  algebraic core, given a chain through C_base_s and an explicit
  σ-power-decay hypothesis.
* `subset_inequality_via_per_t_sigma_decay` — multi-`t'` wrapper:
  iterates the single-`t'` transfer over a finite `T_D`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit `WedhornLocalizationLiftContinuity.lean`,
  `WedhornValuationLocalizationLift.lean`,
  `WedhornC1StrongSupplierCore.lean`, or any in-flight file.
* Imports only `WedhornDominatingBranchInequality` (for branch
  primitives) and `WedhornLocalizationDenominatorUnit` (for
  `not_vle_zero_pow`).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **Right-cancellation iff for a unit factor**. For any unit
`σ : Aˣ`, the `vle`-relation is preserved on both sides under
multiplication by `(σ : A)` on the right: `v.vle (a * σ) (b * σ) ↔
v.vle a b`. -/
theorem vle_iff_mul_unit_right
    (v : Spv A) (σ : Aˣ) (a b : A) :
    v.vle (a * (σ : A)) (b * (σ : A)) ↔ v.vle a b := by
  letI : ValuativeRel A := v.toValuativeRel
  exact ValuativeRel.mul_vle_mul_iff_left (not_vle_zero_of_isUnit σ.isUnit v)

/-- **Left-cancellation iff for a unit factor**. For any unit
`σ : Aˣ`, the `vle`-relation is preserved on both sides under
multiplication by `(σ : A)` on the left: `v.vle (σ * a) (σ * b) ↔
v.vle a b`. -/
theorem vle_iff_mul_unit_left
    (v : Spv A) (σ : Aˣ) (a b : A) :
    v.vle ((σ : A) * a) ((σ : A) * b) ↔ v.vle a b := by
  letI : ValuativeRel A := v.toValuativeRel
  exact ValuativeRel.mul_vle_mul_iff_right (not_vle_zero_of_isUnit σ.isUnit v)

/-- **Single-`t'` σ-decay chain transfer** (algebraic core of the
Wedhorn 8.34(ii) subset-side inequality at a fixed Spa-point).

Given:
* a chain `w.vle ((σ : A) * t' * D_s ^ N) C_base_s` (membership in
  the plus-piece-at-`f` for `f := (σ : A) * t' * D_s ^ N`);
* an explicit σ-power-decay hypothesis
  `w.vle C_base_s ((σ : A) * D_s ^ (N + 1))` (the Wedhorn 8.34(ii)
  / Cor 7.32 input);
* a non-zero denominator hypothesis `¬ w.vle D_s 0`,

derive `w.vle t' D_s`. The proof composes transitivity, σ-cancellation
on the left, and `D_s ^ N`-cancellation on the right. -/
theorem vle_t_D_s_of_sigma_decay_chain_at
    (w : Spv A) {σ : Aˣ} {t' D_s C_base_s : A} (N : ℕ)
    (h_D_s_ne : ¬ w.vle D_s 0)
    (h_w_f : w.vle ((σ : A) * t' * D_s ^ N) C_base_s)
    (h_C_decay : w.vle C_base_s ((σ : A) * D_s ^ (N + 1))) :
    w.vle t' D_s := by
  letI : ValuativeRel A := w.toValuativeRel
  have h_combined := w.vle_trans h_w_f h_C_decay
  rwa [mul_assoc, ValuativeRel.mul_vle_mul_iff_right (not_vle_zero_of_isUnit σ.isUnit w),
    pow_succ, mul_comm (D_s ^ N) D_s,
    ValuativeRel.mul_vle_mul_iff_left (not_vle_zero_pow h_D_s_ne N)] at h_combined

/-- **Multi-`t'` subset-inequality wrapper** (Wedhorn 8.34(ii) target
shape).

Iterates `vle_t_D_s_of_sigma_decay_chain_at` over a finite `T_D`,
using the same C_base_s / σ / N / σ-decay data: given the per-`t'`
chain hypothesis `∀ t' ∈ T_D, w.vle ((σ : A) * t' * D_s ^ N)
C_base_s` and the σ-power-decay `w.vle C_base_s ((σ : A) * D_s ^ (N + 1))`,
derive the universal subset inequality. -/
theorem subset_inequality_via_per_t_sigma_decay
    (w : Spv A) {σ : Aˣ} {T_D : Finset A} {D_s C_base_s : A} (N : ℕ)
    (h_D_s_ne : ¬ w.vle D_s 0)
    (h_per_t : ∀ t' ∈ T_D, w.vle ((σ : A) * t' * D_s ^ N) C_base_s)
    (h_C_decay : w.vle C_base_s ((σ : A) * D_s ^ (N + 1))) :
    (∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0 :=
  ⟨fun t' ht' ↦
      vle_t_D_s_of_sigma_decay_chain_at w N h_D_s_ne (h_per_t t' ht') h_C_decay,
    h_D_s_ne⟩

/-! ### Residual (recorded for the next ticket)

The remaining genuinely-new Wedhorn content for the multi-`t'`
candidate `f := (σ : A) * (T_D.prod id) * D_s ^ N` is **factor
extraction**: deriving the per-`t'` chain
`∀ t' ∈ T_D, w.vle ((σ : A) * t' * D_s ^ N) C_base_s` from the
single multi-element chain `w.vle f C_base_s` plus the boundedness
of the OTHER factors `∏ T_D \ {t'}`. The exact target signature:

```
theorem per_t_chain_of_multi_chain
    {A : Type*} [CommRing A] (w : Spv A) {σ : Aˣ}
    {T_D : Finset A} {D_s C_base_s : A} (N : ℕ)
    {f : A} (hf : f = (σ : A) * (T_D.prod id) * D_s ^ N)
    (h_w_f : w.vle f C_base_s)
    (h_T_D_bounded : ∀ t' ∈ T_D, w.vle t' 1)  -- T_D ⊆ A° at w
    (h_T_D_ne : ∀ t' ∈ T_D, ¬ w.vle t' 0) :
    ∀ t' ∈ T_D, w.vle ((σ : A) * t' * D_s ^ N) C_base_s
```

The `h_T_D_bounded` (or analogous `T_D ⊆ A°` / `T_D ⊆ A⁺`) and
`h_T_D_ne` premises are the additional Wedhorn 8.34(ii) inputs not
present in the abstract σ-domination signature; they would come from
the rational-open structure on `D` or from the ring-of-integers
context. Verifying their availability and proving this factor
extraction is the next ticket on this lane.

Equally, the σ-power-decay `w.vle C_base_s ((σ : A) * D_s ^ (N + 1))`
consumed here as `h_C_decay` is the Cor 7.32 / Wedhorn 8.34(ii) input
proper; it is established by Wedhorn's choice of `N` once the ratio
construction is set up, and is not derivable from purely algebraic
material. -/

end ValuationSpectrum
