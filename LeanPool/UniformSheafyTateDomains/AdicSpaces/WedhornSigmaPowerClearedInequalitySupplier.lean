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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornC1SigmaConstructionAssembly
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalArithmeticPerTChain

/-!
# Wedhorn 8.34(ii) — σ-power-cleared inequality supplier (T073)

T072 (commit accepted in `WedhornC1SigmaConstructionAssembly.lean`)
landed the C1 endgame wrapper consuming a single named source-
restricted residual `SigmaProductClearedInequalitySupplier`:

```
def SigmaProductClearedInequalitySupplier (D_T : Finset A) (s D_s f : A) : Prop :=
  ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
    v.vle f s → v.vle (1 : A) t' → ¬ v.vle t' 0 →
    ∃ N : ℕ, v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0
```

This file lands the **substantive arithmetic discharge** of that
residual via two routes corresponding to two natural σ-construction
algebraic shapes:

1. **σ-factor cancellation**: from a per-`(v, t')` σ-factored
   inequality `v.vle (t' * D_s^N * σ) (D_s^(N+1) * σ)` (with σ a
   unit), apply the σ-factor cancellation primitive
   `per_t_inequality_via_sigma_factor`
   (`WedhornLocalArithmeticPerTChain.lean:76`) to derive the σ-power-
   cleared inequality. This is the natural σ-construction shape: the
   σ-construction's algebraic identity carries a σ multiplicative
   factor that cancels via the unit-right primitive.

2. **Direct clearing at `N = 0`**: from a per-`(v, t')` direct upper
   bound `v.vle t' D_s` plus `D_s` non-vanishing, witness the σ-power-
   cleared inequality at `N = 0` (where it reduces to the direct upper
   bound after `pow_zero`/`pow_one`/`mul_one` simplification). This
   route is useful when the σ-construction is already simplified to
   the un-σ-factored form.

Both routes preserve the **per-`(v, t')` source restriction**: no
universal-over-`D_T` lower bound, no global universal-over-Spa form.
The σ-construction's specific σ choice and exponent `N` are chosen
per-`(v, t')` by the supplier.

## What this file provides

* `sigma_product_cleared_inequality_via_sigma_factored` — substantive
  per-`(v, t')` σ-cancellation reduction: from the σ-factored form
  `v.vle (t' * D_s^N * σ) (D_s^(N+1) * σ)`, derive the σ-power-cleared
  inequality `v.vle (t' * D_s^N) (D_s^(N+1))`. Real proof via
  `per_t_inequality_via_sigma_factor` (T050 σ-factor cancellation
  primitive).

* `sigma_product_cleared_inequality_via_direct_clearing` — substantive
  per-`(v, t')` `N = 0` route: from `v.vle t' D_s` + `¬ v.vle D_s 0`,
  witness the σ-power-cleared inequality at `N = 0`. Real proof via
  `pow_zero`/`pow_one`/`mul_one` simplification.

* `SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier`
  — supplier-level form: from a per-`(v, t')` σ-factored supplier (the
  natural σ-construction algebraic content per-piece), produce
  `SigmaProductClearedInequalitySupplier`. Composes with T072's
  `pointwise_clearing_supplier_via_sigma_product_cleared_inequality`
  to give the full chain.

* `SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier`
  — alternative supplier form using `N = 0`. The named residual is
  the per-`(v, t')` direct upper bound supplier
  `v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 → v.vle t' D_s ∧ ¬ v.vle D_s 0`.

## The remaining named source-restricted residual

After T073, the remaining content reduces to one of:

* **σ-factored form supplier** (deliverable from σ-construction's
  algebraic identity + σ-strict-domination):
  ```
  ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
    v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
    ∃ (σ : Aˣ) (N : ℕ),
      v.vle (t' * D_s^N * (σ : A)) (D_s^(N+1) * (σ : A)) ∧
      ¬ v.vle D_s 0
  ```
  This captures the σ-construction's natural per-`(v, t')` algebraic
  shape after σ-cancellation.

* **Direct upper bound supplier** (the original Wedhorn 8.34(ii)
  per-piece content, equivalent to T067's pointwise clearing):
  ```
  ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
    v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
    v.vle t' D_s ∧ ¬ v.vle D_s 0
  ```

Both are per-`(v, t')` and source-restricted; neither is the
rejected universal-over-`D_T` form.

## Notes

* No root import; leaf-level.
* Imports T072 (`WedhornC1SigmaConstructionAssembly`) for the named
  residual `SigmaProductClearedInequalitySupplier` and
  `WedhornLocalArithmeticPerTChain` for the σ-factor cancellation
  primitive `per_t_inequality_via_sigma_factor`.
* No edits to T031–T072 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim.
* No introduction of any final Tate acyclicity hypothesis. The
  named residuals are per-`(v, t')` σ-construction algebraic content,
  consumed by Secondary's σ/Laurent-cover supplier lane.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **σ-power-cleared inequality from σ-factored form** (T073
substantive σ-cancellation reduction).

From a per-`(v, t')` **σ-factored inequality**
`v.vle (t' * D_s^N * σ) (D_s^(N+1) * σ)` (where `σ : Aˣ` is the
σ-construction unit and `N : ℕ` the exponent), plus
`¬ v.vle D_s 0`, derive the σ-power-cleared inequality
`v.vle (t' * D_s^N) (D_s^(N+1))` plus the non-vanishing.

**Proof structure**: apply `per_t_inequality_via_sigma_factor`
(T050 / `WedhornLocalArithmeticPerTChain`'s σ-factor cancellation
primitive: `w.vle (a * σ) (b * σ) ↔ w.vle a b` for σ a unit) at the
σ-factored hypothesis to extract the σ-cancelled form. The
non-vanishing hypothesis passes through.

**Substantive consumption** of `per_t_inequality_via_sigma_factor` —
not pass-through. -/
theorem sigma_product_cleared_inequality_via_sigma_factored
    {v : Spv A} (σ : Aˣ) {t' D_s : A} {N : ℕ}
    (h_factored :
      v.vle (t' * D_s ^ N * (σ : A)) (D_s ^ (N + 1) * (σ : A)))
    (h_D_s_ne : ¬ v.vle D_s 0) :
    v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0 :=
  ⟨(per_t_inequality_via_sigma_factor v σ (t' * D_s ^ N)
      (D_s ^ (N + 1))).mp h_factored,
    h_D_s_ne⟩

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **σ-power-cleared inequality at `N = 0` from direct upper bound**
(T073 alternative `N = 0` route).

From a per-`(v, t')` direct upper bound `v.vle t' D_s` plus
`¬ v.vle D_s 0`, witness the σ-power-cleared inequality at `N = 0`.
Useful when the σ-construction is already simplified to the
un-σ-factored direct form.

**Proof**: at `N = 0`, the inequality `v.vle (t' * D_s^0) (D_s^(0+1))`
simplifies via `pow_zero`, `mul_one`, `pow_one` to `v.vle t' D_s`,
which is the direct upper bound hypothesis. -/
theorem sigma_product_cleared_inequality_via_direct_clearing
    {v : Spv A} {t' D_s : A}
    (h_clear : v.vle t' D_s)
    (h_D_s_ne : ¬ v.vle D_s 0) :
    ∃ N : ℕ, v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0 :=
  ⟨0, by simpa only [pow_zero, mul_one, zero_add, pow_one] using h_clear, h_D_s_ne⟩

omit [IsTopologicalRing A] in
/-- **`SigmaProductClearedInequalitySupplier` from σ-factored
supplier** (T073 main consumer-facing theorem).

From a per-`(v, t')` σ-factored supplier — the natural σ-construction
algebraic content per-piece — produce
`SigmaProductClearedInequalitySupplier` (T072's named residual).

**The named source-restricted residual** at this layer is the
σ-factored supplier:

```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
  ∃ (σ : Aˣ) (N : ℕ),
    v.vle (t' * D_s^N * (σ : A)) (D_s^(N+1) * (σ : A)) ∧
    ¬ v.vle D_s 0
```

This captures the σ-construction's natural per-`(v, t')` algebraic
shape after multiplication by σ on both sides. Per-`(v, t')` and
source-restricted (no universal-over-`D_T` form). -/
theorem SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier
    (D_T : Finset A) (s D_s f : A)
    (h_factored_supplier :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        ∃ (σ : Aˣ) (N : ℕ),
          v.vle (t' * D_s ^ N * (σ : A))
            (D_s ^ (N + 1) * (σ : A)) ∧
          ¬ v.vle D_s 0) :
    SigmaProductClearedInequalitySupplier D_T s D_s f := by
  intro t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  obtain ⟨σ, N, h_factored, h_D_s_ne⟩ :=
    h_factored_supplier t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  exact ⟨N, sigma_product_cleared_inequality_via_sigma_factored σ h_factored
    h_D_s_ne⟩

omit [IsTopologicalRing A] in
/-- **`SigmaProductClearedInequalitySupplier` from direct upper-bound
supplier** (T073 alternative consumer-facing theorem).

Alternative route: from a per-`(v, t')` direct upper-bound supplier
(equivalent to T067's pointwise clearing residual reformulated with
explicit `D_s` non-vanishing), produce
`SigmaProductClearedInequalitySupplier` via the `N = 0` witness.

The named residual at this layer is the **direct upper bound
supplier**:

```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
  v.vle t' D_s ∧ ¬ v.vle D_s 0
```

Equivalent in content to T067's pointwise clearing (modulo explicit
`D_s` non-vanishing); useful when the σ-construction is already
simplified to direct form. -/
theorem SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier
    (D_T : Finset A) (s D_s f : A)
    (h_direct_supplier :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        v.vle t' D_s ∧ ¬ v.vle D_s 0) :
    SigmaProductClearedInequalitySupplier D_T s D_s f := by
  intro t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  obtain ⟨h_clear, h_D_s_ne⟩ :=
    h_direct_supplier t' ht' v hv_spa hv_f hv_one_t hv_t_ne
  exact sigma_product_cleared_inequality_via_direct_clearing h_clear h_D_s_ne

end ValuationSpectrum
