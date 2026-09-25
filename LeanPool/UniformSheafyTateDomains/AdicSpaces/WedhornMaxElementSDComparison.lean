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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornAlphaTDComparisonSupplier

/-!
# Wedhorn 8.34(ii) max-element ≤ s_D comparison supplier (T035)

T035 isolates the **genuine remaining mathematical residual** for
T034's α_T_D-branch comparison supplier
(`alpha_T_D_per_t_factored_chain_via_max_element`, commit `58a85b5`):
the per-`w` comparison `w.vle τ_max (algebraMap s_D)` for the maximum
element of `T_D.image (algebraMap)` at `w`.

## Orientation audit (per the T034 docstring)

T034's residual is restated:

```
∀ τ_max ∈ T_D.image (algebraMap),
  (∀ t' ∈ T_D.image (algebraMap), w.vle t' τ_max) →
  w.vle τ_max (algebraMap A (Localization.Away s) s_D)
```

i.e., whenever an element of `T_D.image (algebraMap)` is a max of
`T_D.image (algebraMap)` at `w`, it is bounded above by `algebraMap s_D`
at `w`.

**This residual is mathematically FALSE uniformly over `Spa(Loc s, ⁺)`**
for arbitrary `(T_D, s_D)`. Concrete counter-example: take `A = ℚ_p`,
`s = 1` (so `Localization.Away s = ℚ_p`), `T_D = {(1 : A)}`, `s_D = p`.
Then `T_D.image (algebraMap) = {1}` and `algebraMap s_D = p`. At the
standard p-adic valuation `v` on `ℚ_p`:

* `v(1) = 1` and `v(p) = 1/p < 1`;
* The unique max of `T_D.image (algebraMap)` at `v` is `τ_max = 1`
  with `v(1) = 1`;
* `v.vle τ_max (algebraMap s_D) = v.vle 1 p` requires `v(1) ≤ v(p)`,
  i.e., `1 ≤ 1/p`, which is **FALSE** for `p > 1`.

Hence the universal-over-Spa statement of T034's residual cannot hold
without an additional hypothesis ruling out such valuations.

## Why existing T027/T031/T034 data does not supply the residual

Per T034's own analysis, none of the following supplies the comparison:

* **Cor 7.32 σ-strict-domination**: orders σ_loc vs τ_supp, NOT τ_max
  vs algebraMap s_D.
* **T027 Laurent-piece membership**: gives `w.vle σ_loc τ_w` for some
  τ_w, not a comparison with algebraMap s_D for arbitrary T_D-elements.
* **T031 V_K-nonempty witness**: orders σ_loc vs t_0, not t_0 vs
  algebraMap s_D.
* **f-membership** `w.vle (σ_loc * ∏ T_D.image) (algebraMap s)`:
  relates the full T_D product to s, not max-T_D vs s_D.

The natural source is the **base rational-subset condition**
`v ∈ rationalOpen T_D s_D`, which directly gives
`∀ t ∈ T_D, v.vle t s_D` (the rational subset's defining bound). At
the localized level, this becomes
`w ∈ rationalOpen (T_D.image (algebraMap)) (algebraMap s_D)`, i.e.,
`∀ t ∈ T_D.image (algebraMap), w.vle t (algebraMap s_D)`.

## What this file provides

This file lands a **reusable bridge theorem** (option (2) per T035's
ticket preferences) deriving T034's residual from the explicit
augmented branch predicate `∀ t ∈ T_D.image (algebraMap), w.vle t
(algebraMap s_D)`. The augmented predicate corresponds to `w` being in
the rational subset `R(T_D.image (algebraMap), algebraMap s_D)`.

The bridge isolates the universal-quantification mismatch:

* T034's universal-over-Spa supplier obligation needs the comparison
  at every `w ∈ Spa(Loc s, ⁺)`.
* The augmented predicate is naturally available **only at `w` in
  the rational open** `rationalOpen (T_D.image (algMap)) (algMap s_D)`,
  not at every `w ∈ Spa`.

This mismatch is the **structural blocker** identified by T034's
analysis: T021's `WedhornMPowerStructuralDataHonest` is universal over
Spa, but the natural rational-subset-condition source is restricted to
the cover plus-piece. Either (a) tighten T021's universal quantifier
to range over the cover plus-piece (definition-level change, out of
scope for T035), or (b) supply the rational-subset condition via some
other Wedhorn-specific argument (the parked σ-power-decay route was an
attempt and was shown false in T023).

## What this file provides — theorems

* `max_element_le_s_D_of_laurent_branch` — the bridge: from
  `∀ t ∈ T_D.image (algMap), w.vle t (algMap s_D)`, derive T034's
  max-element residual. The maxness premise of T034's residual is
  NOT used; the rational-subset condition over the entire image
  trivially implies the bound for any element (max or otherwise).

* `alpha_T_D_per_t_factored_chain_via_rational_open` — top-level
  composed wrapper: takes the rational-subset condition + nonemptiness,
  composes via `max_element_le_s_D_of_laurent_branch` and
  `alpha_T_D_per_t_factored_chain_via_max_element` (T034) to produce
  the per-`t'` σ-factored chain consumed by T028's
  `PerLaurentPieceFactoredChain`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap content.
* No σ-power-decay revival.
* Imports only T034's committed `WedhornAlphaTDComparisonSupplier`,
  which transitively brings in T033/T031/T030/T029/T028/T027 and the
  rational-open / σ-cancellation API.
* Does NOT edit T027/T028/T031/T032/T033/T034 accepted files.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Bridge from rational-subset condition to T034's max-element
residual** (T035 main deliverable).

From the rational-subset condition `∀ t ∈ T_D.image (algebraMap A
(Localization.Away s)), w.vle t (algebraMap s_D)` (i.e., `w ∈
rationalOpen (T_D.image (algMap)) (algMap s_D)`'s per-element bound
component), derive T034's α_T_D-branch max-element residual:

```
∀ τ_max ∈ T_D.image (algebraMap),
  (∀ t' ∈ T_D.image (algebraMap), w.vle t' τ_max) →
  w.vle τ_max (algebraMap s_D)
```

**Proof**: the rational-subset condition over the entire image
trivially implies the bound for any element of the image (max or
otherwise); the maxness premise `∀ t' ∈ T_D.image, w.vle t' τ_max` is
unused.

**Hypotheses consumed**:

* `h_per_t_le_s_D` — per-`t` rational-subset-condition bound: every
  element of `T_D.image (algebraMap)` is bounded above by `algebraMap
  s_D` at `w`. Naturally available when `w ∈ rationalOpen
  (T_D.image (algMap)) (algMap s_D)` (the cover-refinement target).

**Why the maxness premise is unused**: T034's residual is phrased with
a max-ness conditional `(∀ t', w.vle t' τ_max) → ...`, but the
rational-subset condition gives the bound for ALL elements, so τ_max's
maxness is not required to apply it. The bridge is a one-line
projection. -/
theorem max_element_le_s_D_of_laurent_branch
    {s : A} (T_D : Finset A) (s_D : A)
    (w : Spv (Localization.Away s))
    (h_per_t_le_s_D :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t (algebraMap A (Localization.Away s) s_D)) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ_max ∈ T_D.image (algebraMap A (Localization.Away s)),
      (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' τ_max) →
      w.vle τ_max (algebraMap A (Localization.Away s) s_D) :=
  fun τ_max hτ_max _ ↦ h_per_t_le_s_D τ_max hτ_max

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Top-level composed wrapper: α_T_D per-`t'` σ-factored chain via
rational-subset condition** (T035 composed deliverable).

Composes the bridge `max_element_le_s_D_of_laurent_branch` with
T034's `alpha_T_D_per_t_factored_chain_via_max_element` to produce the
per-`t'` σ-factored chain consumed by T028's
`PerLaurentPieceFactoredChain` from two natural inputs:

* `hT_D_image_ne` — `(T_D.image (algMap)).Nonempty` (automatic in the
  V_K-nonempty branch from T031);
* `h_per_t_le_s_D` — the rational-subset condition `∀ t ∈ T_D.image
  (algMap), w.vle t (algMap s_D)` (the explicit augmented branch
  predicate identified by this T035 ticket).

This is the **strongest theorem-level α_T_D consumer** achievable from
existing API: it unifies the max-element-extraction (T034's mechanical
reducer) and the explicit residual (T035's bridge) into a single
caller-friendly signature parameterised by the genuine missing
content — the rational-subset condition. -/
theorem alpha_T_D_per_t_factored_chain_via_rational_open
    {s : A} (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s))
    (hT_D_image_ne :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      (T_D.image (algebraMap A (Localization.Away s))).Nonempty)
    (h_per_t_le_s_D :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t (algebraMap A (Localization.Away s) s_D)) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (t' * (σ_loc : Localization.Away s))
        ((algebraMap A (Localization.Away s) s_D) *
          (σ_loc : Localization.Away s)) :=
  alpha_T_D_per_t_factored_chain_via_max_element T_D s_D σ_loc w hT_D_image_ne
    (max_element_le_s_D_of_laurent_branch T_D s_D w h_per_t_le_s_D)

end ValuationSpectrum
