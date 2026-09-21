/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornFullLaurentAlphaTDBranch

/-!
# Wedhorn 8.34(ii) α_T_D branch comparison supplier (T034)

α_T_D-branch consumer/supplier interface for T033's
`alpha_T_D_per_t_factored_chain_via_intermediate` (commit `f0d15c8`).

T033 reduces the α_T_D branch per-`t'` σ-factored chain to two
explicit comparisons for an intermediate `τ`:

1. `h_τ_le_s_D : w.vle τ (algebraMap A (Localization.Away s) s_D)`.
2. `h_t_le_τ : ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
   w.vle t' τ`.

The natural choice for `τ` is the **maximum element** of
`T_D.image (algebraMap)` at `w`, which automatically satisfies (2) by
construction. This file provides the **finite-max-element lemma**
making (2) mechanical, plus an α_T_D wrapper consuming only the
genuine residual (1) for that max element.

## Orientation audit

T031 supplies the V_K-nonempty σ-strict-dom witness
`t_0 ∈ T_D.image (algebraMap)` with `w.vle σ_loc t_0` and
`¬ w.vle t_0 σ_loc`. **`t_0` is NOT necessarily a maximum element**:
σ-strict-domination only orders `t_0` above `σ_loc`, not above other
`t' ∈ T_D.image`. Consequently:

* The natural intermediate `τ` for T033's input is NOT the V_K-nonempty
  witness `t_0`; it is the **max element** `τ_max` of
  `T_D.image (algebraMap)` at `w`. By max-ness, `w.vle t' τ_max` for
  every `t'`, satisfying T033's hypothesis (2) automatically.
* T033's hypothesis (1) `w.vle τ_max (algebraMap s_D)` does **NOT**
  follow from σ-strict-domination, V_K-nonempty witness, or the
  Laurent-piece membership at `t_0`. It is the **genuine remaining
  T021 residual** for the α_T_D branch.

## What this file provides

* `Spv.exists_max_vle_of_nonempty` — generic finite-max-element lemma
  in the valuation total preorder. For any `w : Spv X` and finite
  nonempty `S : Finset X`, ∃ `x_max ∈ S, ∀ y ∈ S, w.vle y x_max`.
  Reusable mathlib-style API; not specific to the Wedhorn chain.

* `alpha_T_D_per_t_factored_chain_via_max_element` — α_T_D branch
  wrapper consuming **only** the genuine residual: the max-element
  comparison `∀ τ_max maximal in T_D.image, w.vle τ_max (algebraMap s_D)`.
  Internally extracts the max via `Spv.exists_max_vle_of_nonempty`,
  then plugs into T033's `alpha_T_D_per_t_factored_chain_via_intermediate`.

## The remaining T021 dependency

The α_T_D branch's remaining genuine Wedhorn-content residual is:

```
∀ τ_max ∈ T_D.image (algebraMap),
  (∀ t' ∈ T_D.image (algebraMap), w.vle t' τ_max) →
  w.vle τ_max (algebraMap A (Localization.Away s) s_D)
```

i.e., **whenever an element of `T_D.image (algebraMap)` is a max of
`T_D.image (algebraMap)` at `w`, it is bounded above by
`algebraMap s_D` at `w`**. This is the per-w content of "the largest
T_D-element does not exceed `s_D`", which is the precise localized
counterpart of the base rational-open inclusion `v ∈ rationalOpen T_D
s_D ⇒ v(t) ≤ v(s_D)`. It is NOT supplied by:

* Cor 7.32 σ-strict-domination (orders σ_loc vs `τ_supp`, not `τ_max`
  vs `algebraMap s_D`).
* T027 Laurent-piece membership (gives `w.vle σ_loc τ_w` for some
  `τ_w`, not a comparison with `algebraMap s_D` for arbitrary
  T_D-elements).
* T031 V_K-nonempty witness (orders σ_loc vs `t_0`, not `t_0` vs
  `algebraMap s_D`).
* f-membership `w.vle (σ_loc * ∏ T_D.image) (algebraMap s)` (relates
  the full T_D product to `s`, not max-T_D vs `s_D`).

The natural source is the base rational covering data lifted via
comap, but the structural supplier is uniform over all `w` in the
localized Spa. Discharging this residual on every `w` requires either:

* tightening the structural supplier's universality to `w`s arising
  via comap from `v ∈ rationalOpen T_D s_D` (a definition-level
  change to `WedhornMPowerStructuralDataHonest`), OR
* a Wedhorn-specific argument tying the `(σ_loc, ∏ T_D, s)`
  f-membership to per-`t'` bounds via the Cor 7.32 σ-construction's
  internal pseudo-uniformizer power (the parked sigma-power-decay
  route was an attempt at this and was shown false).

## Notes

* No root import; leaf-level.
* Imports only `WedhornFullLaurentAlphaTDBranch` (T033, commit
  `f0d15c8`) and its transitive closure.
* No edits to T027/T028/T029/T030/T031/T032/T033 files.
* No revival of σ-power-decay, T001 / Lane-B, Cor832/Jacobson,
  faithful-flatness, Zavyalov, or bivariate-overlap content.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Finite-max-element lemma in the Spv valuation total preorder**.

For any `w : Spv X` (with `X` a commutative ring) and any finite
nonempty `S : Finset X`, there exists `x_max ∈ S` such that
`w.vle y x_max` for every `y ∈ S`.

Proof: induction on `S` via `Finset.Nonempty.cons_induction`,
case-splitting on `w.vle x_max a` (using totality `w.vle_total`) at
each cons step.

This is reusable mathlib-style API: the only structure used is the
totality and transitivity of `w.vle` (inherited from `ValuativeRel`).
Not specific to the Wedhorn 8.34(ii) chain. -/
theorem Spv.exists_max_vle_of_nonempty
    {X : Type*} [CommRing X] (w : Spv X) {S : Finset X} (hS : S.Nonempty) :
    ∃ x_max ∈ S, ∀ y ∈ S, w.vle y x_max := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton x =>
      refine ⟨x, Finset.mem_singleton.mpr rfl, fun y hy ↦ ?_⟩
      rw [Finset.mem_singleton] at hy
      subst hy
      exact (w.vle_total y y).elim id id
  | cons a S _ha _hSne ih =>
      obtain ⟨x_max, hx_max_mem, h_max⟩ := ih
      rcases w.vle_total x_max a with h_x_le_a | h_a_le_x
      · refine ⟨a, Finset.mem_cons.mpr (Or.inl rfl), fun y hy ↦ ?_⟩
        rcases Finset.mem_cons.mp hy with rfl | hy'
        · exact (w.vle_total y y).elim id id
        · exact w.vle_trans (h_max y hy') h_x_le_a
      · refine ⟨x_max, Finset.mem_cons.mpr (Or.inr hx_max_mem), fun y hy ↦ ?_⟩
        rcases Finset.mem_cons.mp hy with rfl | hy'
        · exact h_a_le_x
        · exact h_max y hy'

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **α_T_D per-`t'` σ-factored chain via max-element comparison**
(T034 main composed deliverable).

Combines `Spv.exists_max_vle_of_nonempty` (for the max-element of
`T_D.image (algebraMap)` at `w`) with T033's
`alpha_T_D_per_t_factored_chain_via_intermediate`. Consumes:

* `hT_D_image_ne` — `(T_D.image (algebraMap A (Localization.Away s))).Nonempty`,
  i.e., `T_D` has at least one element with non-trivial image (the V_K-
  nonempty branch automatically gives this; see T031);
* `h_max_le_s_D` — the **max-element comparison residual**: whenever
  `τ_max ∈ T_D.image (algebraMap)` is a max of `T_D.image (algebraMap)`
  at `w`, `w.vle τ_max (algebraMap s_D)`.

Output: per-`t'` σ-factored chain
`w.vle (t' * σ_loc) ((algebraMap s_D) * σ_loc)` for every
`t' ∈ T_D.image (algebraMap)`, the α_T_D branch piece needed by
T028's `PerLaurentPieceFactoredChain` and ultimately T021's honest
structural supplier.

`h_max_le_s_D` is the **single remaining mathematical residual** for
the α_T_D branch chain; the rest is mechanical (max extraction +
σ-cancellation). -/
theorem alpha_T_D_per_t_factored_chain_via_max_element
    {s : A} (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (hT_D_image_ne :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      (T_D.image (algebraMap A (Localization.Away s))).Nonempty)
    (h_max_le_s_D :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ_max ∈ T_D.image (algebraMap A (Localization.Away s)),
        (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle t' τ_max) →
        w.vle τ_max (algebraMap A (Localization.Away s) s_D)) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (t' * (σ_loc : Localization.Away s))
        ((algebraMap A (Localization.Away s) s_D) *
          (σ_loc : Localization.Away s)) := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  obtain ⟨τ_max, hτ_max_mem, hτ_max_max⟩ :=
    Spv.exists_max_vle_of_nonempty w hT_D_image_ne
  have h_τ_le_s_D : w.vle τ_max (algebraMap A (Localization.Away s) s_D) :=
    h_max_le_s_D τ_max hτ_max_mem hτ_max_max
  exact alpha_T_D_per_t_factored_chain_via_intermediate T_D s_D σ_loc w τ_max
    h_τ_le_s_D hτ_max_max

end ValuationSpectrum
