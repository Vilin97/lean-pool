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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationSpectrum

/-!
# Wedhorn dominating-unit valuation-inequality core

Pure valuation-inequality building blocks for the Wedhorn 8.34(ii)
σ-clearing argument. These are point-level lemmas that combine
`ValuativeRel.mul_vle_mul`, `ValuativeRel.pow_vle_pow`, and
transitivity of `vle` into reusable shapes that consumers (notably
`WedhornC1StrongSupplierCore.lean`) can apply repeatedly when chaining
through

```
v(f) = v(σ) * v(t) * v(D.s)^N ≤ v(C.base.s)
```

at a fixed Spa-point `v`.

## Strategy

The full multi-element σ-clearing lemma
(`vle_of_dominating_unit_multi`, target signature documented at
`WedhornStandardCoverRefinement.lean:301`) is genuinely a per-Spa-point
case analysis on which `τ ∈ T_test ∪ {D_s}` wins σ-domination. This
file does **not** attempt that full case analysis; it provides the
two algebraic building blocks that participate in any branch of that
case analysis:

1. **σ-monotonicity at a constant**: from `v.vle (σ : A) τ`, deduce
   `v.vle ((σ : A) * c) (τ * c)` and the power version
   `v.vle ((σ : A)^N * c) (τ^N * c)`.
2. **σ-replacement via transitivity**: from `v.vle (σ : A) τ` and
   `v.vle (τ * a) b`, deduce `v.vle ((σ : A) * a) b`. Power version
   analogous.

Together these compose into the pointwise candidate inequality
`v.vle f C.base.s` once the user supplies the per-`τ`-branch
intermediate `v.vle (τ^N * intermediate) C.base.s`.

## What this file provides

* `vle_mul_const_of_dominating_at` — σ-domination → product inequality
  with a constant right factor.
* `vle_pow_mul_const_of_dominating_at` — power σ-domination version
  using `ValuativeRel.pow_vle_pow`.
* `vle_replace_dominating_at` — σ-replacement via transitivity:
  `v.vle σ τ → v.vle (τ * a) b → v.vle (σ * a) b`.
* `vle_replace_pow_dominating_at` — power version of replacement.
* `vle_pow_mul_pow_const_of_dominating_at` — bilinear σ-power and
  τ-power product inequality (the Wedhorn-shape `σ^N * t^M ≤ τ^N * t^M`
  appearing in Step 3 of the dominating-unit argument).

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit `WedhornLocalizationLiftContinuity.lean`,
  `WedhornValuationLocalizationLift.lean`,
  `WedhornC1StrongSupplierCore.lean`, or any in-flight file.
* Imports only `«Adic spaces».ValuationSpectrum` plus its transitive
  closure (Spv, vle, ValuativeRel infrastructure).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **σ-domination at a constant right factor**. For a Spa-point `v`
and σ-domination `v.vle (σ : A) τ`, multiplying both sides by a constant
`c : A` preserves the inequality: `v.vle ((σ : A) * c) (τ * c)`. -/
theorem vle_mul_const_of_dominating_at
    (v : Spv A) {σ : Aˣ} {τ : A} (hστ : v.vle (σ : A) τ) (c : A) :
    v.vle ((σ : A) * c) (τ * c) := by
  let : ValuativeRel A := v.toValuativeRel
  exact ValuativeRel.mul_vle_mul hστ ((v.vle_total c c).elim id id)

/-- **σ-domination at a power constant**. Power-product version of
`vle_mul_const_of_dominating_at`: σ-domination raised to the `N`-th
power transfers to a product with any constant `c : A`. -/
theorem vle_pow_mul_const_of_dominating_at
    (v : Spv A) {σ : Aˣ} {τ : A} (hστ : v.vle (σ : A) τ) (c : A) (N : ℕ) :
    v.vle ((σ : A) ^ N * c) (τ ^ N * c) := by
  let : ValuativeRel A := v.toValuativeRel
  exact ValuativeRel.mul_vle_mul (ValuativeRel.pow_vle_pow hστ N)
    ((v.vle_total c c).elim id id)

/-- **σ-replacement via transitivity** (point-level Wedhorn 8.34(ii)
Step 3 building block). From σ-domination `v.vle (σ : A) τ` and a
known intermediate inequality `v.vle (τ * a) b`, deduce
`v.vle ((σ : A) * a) b`. -/
theorem vle_replace_dominating_at
    (v : Spv A) {σ : Aˣ} {τ a b : A} (hστ : v.vle (σ : A) τ)
    (h_chain : v.vle (τ * a) b) :
    v.vle ((σ : A) * a) b := by
  let : ValuativeRel A := v.toValuativeRel
  exact v.vle_trans
    (ValuativeRel.mul_vle_mul hστ ((v.vle_total a a).elim id id)) h_chain

/-- **Power version of σ-replacement**. From σ-domination
`v.vle (σ : A) τ` and an intermediate `v.vle (τ ^ N * a) b`, deduce
`v.vle ((σ : A) ^ N * a) b`. Used when the candidate carries a σ-power
factor `σ^N`. -/
theorem vle_replace_pow_dominating_at
    (v : Spv A) {σ : Aˣ} {τ a b : A} (hστ : v.vle (σ : A) τ) (N : ℕ)
    (h_chain : v.vle (τ ^ N * a) b) :
    v.vle ((σ : A) ^ N * a) b := by
  let : ValuativeRel A := v.toValuativeRel
  exact v.vle_trans
    (ValuativeRel.mul_vle_mul (ValuativeRel.pow_vle_pow hστ N)
      ((v.vle_total a a).elim id id)) h_chain

/-- **Bilinear σ-power / τ-power inequality**. From σ-domination
`v.vle (σ : A) τ` and an unrelated `v.vle a b`, deduce the bilinear
power-product inequality
`v.vle ((σ : A) ^ N * a ^ M) (τ ^ N * b ^ M)`. The exact algebraic
shape appearing in Wedhorn 8.34(ii)'s Step 3 chain
`v(σ)^N * v(t)^M ≤ v(τ)^N * v(D.s)^M` after picking
`a := t, b := D.s`. -/
theorem vle_pow_mul_pow_const_of_dominating_at
    (v : Spv A) {σ : Aˣ} {τ a b : A} (hστ : v.vle (σ : A) τ)
    (hab : v.vle a b) (N M : ℕ) :
    v.vle ((σ : A) ^ N * a ^ M) (τ ^ N * b ^ M) := by
  let : ValuativeRel A := v.toValuativeRel
  exact ValuativeRel.mul_vle_mul (ValuativeRel.pow_vle_pow hστ N)
    (ValuativeRel.pow_vle_pow hab M)

/-! ### Algebraic decomposition for the corrected branch-clearing target

The documented `vle_of_dominating_unit_multi` target at
`WedhornStandardCoverRefinement.lean:301` is **mathematically false**
uniformly on `Spa A A⁺` for arbitrary `(T_D, D_s, σ, f, s)`.

**Concrete counter-example** (verifies the falsity of the documented
target): take `A = ℚ_p⟨T⟩` (a Tate ring), `T_D = {1}`, `D_s = p`,
`σ = p^M` (M ≥ 2). Form `f := σ * 1 * p^0 = p^M`, take `s := p^M`.
At the Gauss valuation `v` on `A`:
* `v(σ) = p^(-M) < 1 = v(1)` and `v(σ) = p^(-M) < p^(-1) = v(D_s)`,
  so σ-strict-domination over `insert D_s T_D = {p, 1}` holds at `v`.
* `v(f) = p^(-M) ≤ p^(-M) = v(s)`, so f-membership holds at `v`.
* But the conclusion `v.vle 1 p` requires `v(1) = 1 ≤ p^(-1) = v(p)`,
  which is **FALSE** for `p > 1`.

The conclusion `(∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0` only holds
on the Laurent piece `V_{D_s} = {w | ∀ t ∈ insert D_s T_D, w.vle t D_s}`
(where `D_s` is the maximum of the test family at `w`). Outside this
piece, the conclusion is false, even when σ-strict-dom and f-membership
hold.

**Corrected hypotheses**: replace σ-strict-dom + f-membership with the
**multi-element rational-subset bound** `w.vle (T_D.prod id) D_s` and
the **per-element lower bound** `∀ t' ∈ T_D, w.vle 1 t'`. Together these
are the weakest sufficient hypotheses for the conclusion: the
multi-element bound is the genuine Wedhorn-content fact (NOT derivable
from σ-strict-dom + f-membership alone, per T023's blocker), and the
per-element lower bound is the natural Tate-style condition that each
test-family element has valuation ≥ 1 at `w`.

The two helpers below are pure algebraic decomposition primitives
matching the structure of `Spv.vle_prod_of_pointwise`
(`WedhornMultiDominatingUnit.lean`) and `Finset.mul_prod_erase`. -/

/-- **Product lower bound from pointwise lower bound**. From
`∀ t ∈ T, w.vle 1 t` (each element of `T` has valuation at least 1 at
`w`), deduce `w.vle 1 (T.prod id)` (the product has valuation at least
1 at `w`).

The dual of `Spv.vle_prod_of_pointwise` (`WedhornMultiDominatingUnit.lean`)
applied to the constant function `1` on the LHS. Proven by
`Finset.induction_on` using `ValuativeRel.mul_vle_mul`. -/
theorem one_vle_prod_of_pointwise_lower_bound
    (w : Spv A) {T : Finset A}
    (h_lower : ∀ t ∈ T, w.vle (1 : A) t) :
    w.vle (1 : A) (T.prod id) := by
  classical
  let : ValuativeRel A := w.toValuativeRel
  induction T using Finset.induction_on with
  | empty =>
      exact (w.vle_total 1 1).elim id id
  | insert a T' ha ih =>
      rw [Finset.prod_insert ha]
      have h_a : w.vle (1 : A) (id a) :=
        h_lower a (Finset.mem_insert_self a T')
      have h_T' : w.vle (1 : A) (T'.prod id) :=
        ih (fun t ht => h_lower t (Finset.mem_insert_of_mem ht))
      exact (one_mul (1 : A)).symm ▸ ValuativeRel.mul_vle_mul h_a h_T'

/-- **Per-element extraction from a multi-element product upper bound**.

From `w.vle (T.prod id) D` (the product of `T` is bounded above by `D`
at `w`) and `∀ t' ∈ T, w.vle 1 t'` (each factor has valuation at least
1 at `w`), conclude `∀ t' ∈ T, w.vle t' D` (each factor is individually
bounded above by `D`).

Proof: decompose `T.prod id = t' * (T.erase t').prod id` via
`Finset.mul_prod_erase`. Then `(T.erase t').prod id` has valuation
at least 1 at `w` by `one_vle_prod_of_pointwise_lower_bound`. Hence
`w.vle (t' * 1) (t' * (T.erase t').prod id)` by left-multiplication,
which simplifies to `w.vle t' (t' * (T.erase t').prod id)`. Chaining
through `h_prod` via `vle_trans` gives `w.vle t' D`.

This is the **algebraic core** of the per-`t'` extraction step in
Wedhorn 8.34(ii) Route B's branch-clearing argument. The hypothesis
`w.vle (T.prod id) D` itself is the **multi-element rational-subset
condition** — the genuinely-Wedhorn structural fact NOT derivable from
σ-strict-domination plus f-membership alone (per T023's blocker on
`sigma_power_decay_of_cor732`). -/
theorem vle_per_t_of_prod_vle_of_lower_bound
    (w : Spv A) {T : Finset A} {D : A}
    (h_prod : w.vle (T.prod id) D)
    (h_lower : ∀ t' ∈ T, w.vle (1 : A) t') :
    ∀ t' ∈ T, w.vle t' D := by
  classical
  let : ValuativeRel A := w.toValuativeRel
  intro t' ht'
  have h_split : T.prod id = t' * ((T.erase t').prod id) :=
    (Finset.mul_prod_erase T id ht').symm
  rw [h_split] at h_prod
  have h_others_lower : w.vle (1 : A) ((T.erase t').prod id) :=
    one_vle_prod_of_pointwise_lower_bound w
      (fun t'' ht'' => h_lower t'' (Finset.mem_of_mem_erase ht''))
  have h_step : w.vle (t' * (1 : A)) (t' * ((T.erase t').prod id)) :=
    ValuativeRel.mul_vle_mul_right h_others_lower t'
  rw [mul_one] at h_step
  exact w.vle_trans h_step h_prod

/-- **Corrected `vle_of_dominating_unit_multi`** — the per-`w`
branch-clearing theorem with the documented target's hypotheses
replaced by the **weakest sufficient pair**.

The documented `vle_of_dominating_unit_multi` target at
`WedhornStandardCoverRefinement.lean:301` (with σ-strict-domination
+ f-membership as hypotheses) is mathematically false uniformly on
`Spa A A⁺`; see the file's section docstring for a concrete
counter-example.

This corrected form replaces those weak hypotheses with:

* `h_prod : w.vle (T_D.prod id) D_s` — the **multi-element rational-
  subset bound** at `w`, capturing exactly the cover-refinement content
  needed (NOT derivable from σ-strict-dom + f-membership alone, per
  T023's blocker).
* `h_lower : ∀ t' ∈ T_D, w.vle 1 t'` — the **per-element lower bound**,
  the natural Tate-style condition that each `t' ∈ T_D` has valuation
  at least 1 at `w` (corresponds to `T_D ⊆ A°°` at `w` in valuation
  terms).

From these:
* The per-`t'` upper bound `∀ t' ∈ T_D, w.vle t' D_s` follows by
  `vle_per_t_of_prod_vle_of_lower_bound`.
* `D_s` non-vanishing follows by chaining
  `1 ≤ (T_D.prod id) ≤ D_s` (so `w(D_s) ≥ 1 > 0`); contradiction
  with `w.vle D_s 0` via `not_vle_one_zero`. **No σ-strict-dom is
  needed** — the multi-element bound + lower bound suffice for both
  conjuncts.

## Replacing T021's σ-power-decay residual

The localized T021 chain's residuals `AlphaS_DBranchPerTSigmaPowerDecay`
and `AlphaT_DBranchPerTSigmaPowerDecay` (parked at commit `1cdea0d`)
depend on a uniform σ-power-decay shape that T023's blocker showed is
mathematically false. To replace them, the localized chain should be
refactored to consume the **multi-element bound** + **per-element lower
bound** at each `w` in the cover plus-piece, then apply this corrected
lemma to derive the per-`t'` conclusion.

The remaining content for unblocking T021 is then **the producer for
the multi-element bound** `w.vle (T_D.prod id) D_s` per `w` in the
cover plus-piece — this corresponds to Wedhorn's actual Laurent cover
refinement (PDF Lemma 8.34(ii), page 84), where the Laurent cover
generated by `σ⁻¹ f_i` partitions Spa into pieces, and on each piece
the multi-element bound holds by construction. -/
theorem vle_of_dominating_unit_multi_corrected_at
    (w : Spv A) {T_D : Finset A} {D_s : A}
    (h_prod : w.vle (T_D.prod id) D_s)
    (h_lower : ∀ t' ∈ T_D, w.vle (1 : A) t') :
    (∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0 := by
  refine ⟨vle_per_t_of_prod_vle_of_lower_bound w h_prod h_lower, ?_⟩
  intro h_D_s_zero
  exact w.not_vle_one_zero (w.vle_trans (w.vle_trans
    (one_vle_prod_of_pointwise_lower_bound w h_lower) h_prod) h_D_s_zero)

end ValuationSpectrum
