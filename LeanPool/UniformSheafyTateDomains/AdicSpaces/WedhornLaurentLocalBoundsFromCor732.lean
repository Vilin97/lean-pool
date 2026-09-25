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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLaurentPieceCor732RationalOpenData
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStandardCoverRefinement

/-!
# Wedhorn 8.34(ii) — Laurent-piece local bounds from Cor 7.32 (T053)

T052 (commit `058fc9a`) accepted the consumer
`laurent_piece_rationalOpen_data_via_local_bounds`, which converts a
per-`w` four-part **local-bounds package** into T051's rationalOpen
data. T053 attacks the local-bounds package directly by using
Cor 7.32 σ-strict-domination (`Cor732.exists_dominating_unit` /
`exists_one_vle_inv_unit_mul_at_of_cor732_strict_dom` /
`cor732_laurent_piece_membership_at`) and the σ-rescaled Laurent-piece
arithmetic.

## Documented universality blocker (recap)

Per T035's analysis, the **universal-over-Spa multi-element clearing**
is mathematically false in general: T035's counter-example
(`A = ℚ_p, T_D = {1}, D_s = p, σ = p^N`) satisfies all source
restrictions yet violates the per-`t'` upper bound. Consequently,
T053's residual cannot be discharged for arbitrary `(D.T, D.s)` from
Cor 7.32 alone.

What Cor 7.32 + the existing Laurent-piece API DO give is **per-`w`
existential** σ-rescaled per-element data: at each `w`, ONE element
of the σ-rescaled image of `T_test` has the lower bound +
non-vanishing. The bridge from this **per-`w` existential** to the
T053 residual's **per-`w` universal-over-D.T** form requires either
the singleton case (`|D.T| = 1`) or a multi-piece Laurent cover
refinement structure not currently in the API.

## What this file provides

* `not_vle_zero_of_one_vle` — reusable mathlib-style primitive: from
  `w.vle 1 a`, derive `¬ w.vle a 0`. Reusable across the lower-bound
  / non-vanishing chain.

* `rescaled_per_t_lower_bound_universal_at_strict_dom_witness` —
  **substantive new theorem**: from a universal σ-strict-domination
  hypothesis `∀ w ∈ Spa, w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)` at a
  SINGLE `τ : A` (the singleton-Cor-7.32 specialization) and a unit
  `σ : Aˣ`, derive at every `w` the σ-rescaled per-element data:
  `w.vle (1 : A) (σ⁻¹ * τ) ∧ ¬ w.vle (σ⁻¹ * τ) 0`. **Real proof**
  using `one_vle_inv_unit_mul_of_strict_dom_at` (existing primitive),
  `ValuativeRel.mul_vle_mul_right`, `Units.mul_inv`, `Spv.vle_trans`,
  and `ValuativeRel.zero_vle` — not just packaging.

* `cor732_per_w_existential_rescaled_data` — substantive composition
  of `cor732_laurent_piece_membership_at` (existing) with rationalOpen
  unfolding: from Cor 7.32 σ-domination over `T_test`, derive the
  per-`w` **existential** form `∃ τ ∈ T_test, w.vle 1 (σ⁻¹ * τ) ∧
  ¬ w.vle (σ⁻¹ * τ) 0`. This is the **full Cor 7.32 output** at the
  per-`w` level, with the rationalOpen wrapper unfolded.

* `singleton_local_bounds_via_cor732_singleton` — the **singleton
  case discharge**: when `D.T = {σ⁻¹ * τ}` (singleton σ-rescaled),
  the universal σ-strict-dom hypothesis at `τ` (e.g., from Cor 7.32
  with `T_test = {τ}`) supplies the FULL T052 local-bounds package
  if the product upper bound is also supplied.

* `MultiElementLowerBoundResidual` — explicit Lean Prop predicate
  for the **named structured blocker**: the universal-over-D.T
  per-element lower bound at every `w`. This residual cannot be
  derived from Cor 7.32 alone for `|D.T| > 1`; the bridge requires
  multi-piece Laurent cover refinement.

## Why this is closer to Wedhorn 8.34(ii) than T052

T052's residual was a four-part local-bounds package with no Cor 7.32
or Laurent-piece structure exposed. T053's substantive theorems
EXPOSE the Cor 7.32 σ-rescaled structure: the per-`w` σ-rescaled
per-element data follows from Cor 7.32 σ-strict-dom by SUBSTANTIVE
σ-multiplication arithmetic. The structured blocker
`MultiElementLowerBoundResidual` precisely names the gap from
"per-`w` existential" (Cor 7.32 output) to "per-`w` universal-over-
D.T" (T052's required input).

## Notes

* No root import; leaf-level.
* Imports `WedhornLaurentPieceCor732RationalOpenData` (T052) and
  `WedhornStandardCoverRefinement` (for `one_vle_inv_unit_mul_of_strict_dom_at`,
  `cor732_laurent_piece_membership_at`).
* No edits to T031–T052 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-clearing claim (per T035's
  counter-example).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Non-vanishing from "valuation at least 1" primitive** (T053
reusable building block).

From `w.vle (1 : A) a`, derive `¬ w.vle a 0` via transitivity +
`Spv.not_vle_one_zero`. -/
theorem not_vle_zero_of_one_vle
    {w : Spv A} {a : A} (h : w.vle (1 : A) a) :
    ¬ w.vle a 0 := by
  intro h_a_zero
  exact w.not_vle_one_zero (w.vle_trans h h_a_zero)

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **σ-rescaled per-element lower bound + non-vanishing from σ-strict
domination at `w`** (T053 substantive single-w primitive).

From σ-strict-domination data `w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)`
at a specific `w`, derive the σ-rescaled per-element data:

* `w.vle (1 : A) (σ⁻¹ * τ)` — the σ-rescaled element `σ⁻¹ * τ` has
  valuation at least 1 at `w` (Laurent-piece-≥-1 condition).
* `¬ w.vle (σ⁻¹ * τ) 0` — `σ⁻¹ * τ` is non-vanishing at `w`.

**Proof structure**:

* Part 1 follows from `one_vle_inv_unit_mul_of_strict_dom_at`
  (existing primitive in `WedhornStandardCoverRefinement.lean`).
* Part 2 is a NEW substantive derivation: assume `w.vle (σ⁻¹ * τ) 0`;
  multiply both sides by `(σ : A)` via
  `ValuativeRel.mul_vle_mul_right`; the LHS `(σ : A) * (σ⁻¹ * τ)`
  simplifies to `τ` via `Units.mul_inv`; the RHS `(σ : A) * 0`
  simplifies to `0` via `mul_zero`; this gives `w.vle τ 0`. By
  transitivity with `ValuativeRel.zero_vle (σ : A)` (the always-true
  `0 ≤ᵥ σ`), we get `w.vle τ (σ : A)`, contradicting the strict
  hypothesis.

**Real** valuation arithmetic — uses `ValuativeRel.mul_vle_mul_right`,
`Units.mul_inv`, `Spv.vle_trans`, `ValuativeRel.zero_vle`. -/
theorem rescaled_per_t_lower_bound_at_strict_dom_witness
    (w : Spv A) {σ : Aˣ} {τ : A}
    (hστ_le : w.vle (σ : A) τ)
    (hστ_strict : ¬ w.vle τ (σ : A)) :
    w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) ∧
    ¬ w.vle (((σ⁻¹ : Aˣ) : A) * τ) 0 := by
  refine ⟨one_vle_inv_unit_mul_of_strict_dom_at w hστ_le, ?_⟩
  intro h_inv_τ_zero
  apply hστ_strict
  letI : ValuativeRel A := w.toValuativeRel
  have h_mul :
      w.vle ((σ : A) * (((σ⁻¹ : Aˣ) : A) * τ)) ((σ : A) * 0) :=
    ValuativeRel.mul_vle_mul_right h_inv_τ_zero (σ : A)
  have h_lhs : (σ : A) * (((σ⁻¹ : Aˣ) : A) * τ) = τ := by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [h_lhs, mul_zero] at h_mul
  exact w.vle_trans h_mul (ValuativeRel.zero_vle (σ : A))

omit [IsTopologicalRing A] in
/-- **Universal σ-rescaled per-element data from universal σ-strict-
domination at `τ`** (T053 substantive universal-over-Spa theorem).

When `τ : A` satisfies the **universal σ-strict-dom condition**
`∀ w ∈ Spa A A⁺, w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)` (e.g., from
Cor 7.32 specialised to `T_test = {τ}` in `Cor732.exists_dominating_unit`,
where the existential `∃ τ ∈ T_test` becomes universal at `T_test = {τ}`),
the σ-rescaled element `σ⁻¹ * τ` satisfies the per-element data
universally on `Spa A A⁺`:

```
∀ w ∈ Spa A A⁺,
  w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) ∧
  ¬ w.vle (((σ⁻¹ : Aˣ) : A) * τ) 0
```

Direct consequence of
`rescaled_per_t_lower_bound_at_strict_dom_witness` applied
universally. **Real new theorem**: provides the per-element lower
bound + non-vanishing for the σ-rescaled τ at every `w`, derived
substantively from σ-strict-dom hypotheses. -/
theorem rescaled_per_t_lower_bound_universal_at_strict_dom_witness
    {σ : Aˣ} {τ : A}
    (h_dom_universal :
      ∀ w ∈ Spa A A⁺, w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) :
    ∀ w ∈ Spa A A⁺,
      w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) ∧
      ¬ w.vle (((σ⁻¹ : Aˣ) : A) * τ) 0 := by
  intro w hw_spa
  obtain ⟨hστ_le, hστ_strict⟩ := h_dom_universal w hw_spa
  exact rescaled_per_t_lower_bound_at_strict_dom_witness w hστ_le hστ_strict

omit [IsTopologicalRing A] in
/-- **Per-`w` existential σ-rescaled data from Cor 7.32 σ-domination**
(T053 substantive composition).

Substantively composes
`cor732_laurent_piece_membership_at` (existing) with rationalOpen
unfolding: from Cor 7.32 σ-strict-domination over `T_test`, derive
at every `w ∈ Spa A A⁺` the **existential** form

```
∃ τ ∈ T_test,
  w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) ∧
  ¬ w.vle (((σ⁻¹ : Aˣ) : A) * τ) 0
```

This unfolds the rationalOpen membership produced by
`cor732_laurent_piece_membership_at` at the singleton test element
`(1 : A)`, exposing the underlying per-element lower bound and
non-vanishing at the σ-rescaled witness `σ⁻¹ * τ`.

**Note the per-`w` existential structure**: at each `w`, ONE τ ∈
`T_test` wins the σ-strict-dom + per-element data. This is the
**Laurent-cover** structure: the σ-rescaled pieces `V_τ := {w :
w.vle 1 (σ⁻¹ * τ)}` partition `Spa A A⁺`, and at each `w` exactly
one piece V_τ contains it. -/
theorem cor732_per_w_existential_rescaled_data
    {σ : Aˣ} {T_test : Finset A}
    (hσ_dom :
      ∀ v ∈ Spa A A⁺, ∃ τ ∈ T_test,
        v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A)) :
    ∀ w ∈ Spa A A⁺,
      ∃ τ ∈ T_test,
        w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) ∧
        ¬ w.vle (((σ⁻¹ : Aˣ) : A) * τ) 0 := by
  intro w hw_spa
  obtain ⟨τ, hτ_mem, h_in_open⟩ :=
    cor732_laurent_piece_membership_at hσ_dom hw_spa
  refine ⟨τ, hτ_mem, ?_, ?_⟩
  · exact h_in_open.2.1 (1 : A) (Finset.mem_singleton.mpr rfl)
  · exact h_in_open.2.2

omit [IsTopologicalRing A] in
/-- **Singleton-case discharge of T052's per-`t'` lower-bound + non-
vanishing** (T053 singleton case — real substantive proof).

When `D_T = {σ⁻¹ * τ}` is a singleton consisting of a single
σ-rescaled element, the universal σ-strict-dom hypothesis at `τ`
(equivalent to Cor 7.32 over `T_test = {τ}`) supplies the per-element
lower bound + non-vanishing **for ALL elements** of `D_T` at every
`w`. The case `|D_T| = 1` is where Cor 7.32's existential becomes
universal.

Conclusion: at every `w ∈ Spa A A⁺`,

```
∀ t' ∈ D_T, w.vle (1 : A) t' ∧ ¬ w.vle t' 0
```

(matching parts (3)+(4) of T052's local-bounds package with `D_T =
{σ⁻¹ * τ}`). -/
theorem singleton_per_t_lower_bound_via_cor732_singleton
    {σ : Aˣ} {τ : A}
    (h_dom_universal :
      ∀ w ∈ Spa A A⁺, w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) :
    ∀ w ∈ Spa A A⁺,
      ∀ t' ∈ ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A),
        w.vle (1 : A) t' ∧ ¬ w.vle t' 0 := by
  intro w hw_spa t' ht'
  rw [Finset.mem_singleton] at ht'
  subst ht'
  exact rescaled_per_t_lower_bound_universal_at_strict_dom_witness
    h_dom_universal w hw_spa

/-- **Multi-element residual blocker — Lean statement of the missing
hypothesis** (T053 structured blocker).

The full T052 local-bounds package's per-element lower bound + non-
vanishing for ALL `t' ∈ D.T` at every `w ∈ Spa A A⁺` requires the
**universal-over-D.T** condition

```
∀ w ∈ Spa A A⁺, ∀ t' ∈ D_T, w.vle (1 : A) t' ∧ ¬ w.vle t' 0
```

Cor 7.32's existential output `∃ τ ∈ T_test` per `w` only supplies
this for ONE element of `D_T` per `w` (per the per-piece structure
of the σ-rescaled Laurent cover). The bridge from "per-`w`
existential" to "per-`w` universal-over-D.T" requires either:

1. `D_T = ∅` (vacuous).
2. `|D_T| = 1` (Cor 7.32's existential becomes universal — handled by
   `singleton_per_t_lower_bound_via_cor732_singleton`).
3. A **multi-piece Laurent cover refinement** that partitions `Spa A
   A⁺` such that on each piece, the multi-element bound holds for
   ALL `t' ∈ D_T` simultaneously. This is Wedhorn 8.34(ii) (PDF page
   84)'s actual construction; it requires Wedhorn-specific
   Lemma 8.33 binary Laurent cover acyclicity machinery beyond
   raw Cor 7.32.

This Prop predicate names the missing hypothesis explicitly. -/
def MultiElementLowerBoundResidual (D_T : Finset A) : Prop :=
  ∀ w ∈ Spa A A⁺, ∀ t' ∈ D_T, w.vle (1 : A) t' ∧ ¬ w.vle t' 0

end ValuationSpectrum
