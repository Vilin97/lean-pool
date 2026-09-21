/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalSubsets

/-!
# Wedhorn 8.34(ii) pre-localisation transfer (Route B audit + first lemma)

The per-`t'` half of the Wedhorn multi-element σ-clearing obligation
identified in `WedhornMultiDominatingUnit.lean` does NOT yield to direct
σ-domination over `Spa(A, A⁺)` (verified by tracing the τ-case-analysis
under the proposed canonical test family). The standard Wedhorn 8.34(ii)
proof instead **pre-localises at `C.base.s`** and runs the σ-construction
on `Spa(A_loc, A_loc⁺)` where `A_loc := Localization.Away C.base.s`.
This file isolates the **transfer-of-rational-opens** API needed to
implement that route.

## API audit (state of the repository as of this file)

### Available (`Spv` / `Spa` comap infrastructure)

* `ValuationSpectrum.comap : (A →+* B) → Spv B → Spv A` — contravariant
  Spv map for any ring hom (`Adic spaces/ValuationSpectrum.lean:88`).
* `ValuationSpectrum.comap_vle` — `(comap φ v).vle a₁ a₂ = v.vle (φ a₁)
  (φ a₂)` (`Adic spaces/ValuationSpectrum.lean:92`).
* `ValuationSpectrum.comap_preimage_basicOpen` — pullback formula
  `comap φ ⁻¹' basicOpen f s = basicOpen (φ f) (φ s)`
  (`Adic spaces/ValuationSpectrum.lean:101`).
* `ValuationSpectrum.comap_continuous` — Spv comap is continuous
  (`Adic spaces/ValuationSpectrum.lean:107`).
* `ValuationSpectrum.comap_mem_spa` and `spa_comap_mapsTo`,
  `spaComap` — Spa-level comap, requires `Continuous φ` plus
  `A⁺ ≤ (B⁺).comap φ` (`Adic spaces/AdicSpectrum.lean:256-274`).

### Available (`Localization.Away` infrastructure)

* `LocalizationTopology.locSubring P T s` — ring of definition
  `D = A₀[t₁/s, …, tₙ/s]` inside `Localization.Away s`
  (`Adic spaces/LocalizationTopology.lean:52`).
* `LocalizationTopology.locTopology P T s` — non-archimedean topology
  on `Localization.Away s`
  (`Adic spaces/LocalizationTopology.lean:~150` — `RingSubgroupsBasis`
  + `topology` instance).
* `LocalizationTopology.divByS t s` — the element `t/s ∈
  Localization.Away s` (`Adic spaces/LocalizationTopology.lean:38`).

### Missing (this file lands the first piece)

* **`comap_preimage_rationalOpen`** — analog of
  `comap_preimage_basicOpen` for rational opens. Lands below as
  `comap_mem_rationalOpen_iff`. The cleanest formulation avoids
  `Finset.image` (which forces `[DecidableEq B]`) by stating the
  rational-open membership condition pointwise via `comap φ`.

* **`PlusSubring (Localization.Away s)` instance** — NOT formalised.
  The standard Wedhorn 7.30 / 8.1 construction requires a designated
  plus subring on `A_loc` so that `Spa(A_loc, A_loc⁺)` is well-defined.
  No canonical choice has been instantiated in the project. Documented
  as the blocking structural API below.

* **Continuity of `algebraMap A → Localization.Away C.base.s` under
  `locTopology`** — likely embedded in `LocalizationTopology`'s
  topology construction; needs explicit extraction.

* **Plus-subring containment `A⁺ ≤ (A_loc⁺).comap (algebraMap A
  A_loc)`** — depends on the choice of `(A_loc⁺)` (plus subring
  instance above).

## What this file provides

1. `comap_mem_rationalOpen_iff` — the pointwise rational-open
   pullback formula under any ring hom `φ : A →+* B`. The smallest
   genuinely-new transfer building block: it does not depend on the
   `Localization.Away` infrastructure or the missing `PlusSubring`
   instance, but is the necessary pullback law for any pre-localisation
   transfer of rational opens. Reusable for any `φ`, including the
   eventual `algebraMap A → Localization.Away C.base.s`.

2. Documented target signature (`rationalOpen_transfer_via_localization`)
   plus the precise list of upstream API gaps that prevent the full
   transfer from compiling now.

No Lane B / Cor 8.32 / Jacobson / faithful-flatness / T001 content.
No new final acyclicity hypotheses. -/

namespace ValuationSpectrum

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B]
  [PlusSubring A] [PlusSubring B]

/-- **Rational-open pullback under a Spv-comap**: for any ring hom
`φ : A →+* B` continuous with `A⁺ ≤ (B⁺).comap φ`, and any `w ∈ Spa B B⁺`,
the comap `comap φ w` lies in `rationalOpen T s` iff the pointwise
inequalities `w.vle (φ t) (φ s)` (for each `t ∈ T`) and the
non-degeneracy `¬ w.vle (φ s) 0` hold.

**Proof**: unfold `rationalOpen` and apply `comap_vle` pointwise; the
Spa-membership clause is discharged by `comap_mem_spa` from the
continuity + plus-subring-containment hypotheses.

**Use case**: this is the rational-open analog of
`Spv.comap_preimage_basicOpen` — it lifts the membership-of-rational-open
question across `comap φ` to a pointwise question in the codomain `B`.
For the Wedhorn 8.34(ii) pre-localisation route, instantiate with
`φ := algebraMap A (Localization.Away C.base.s)` (after providing a
`PlusSubring (Localization.Away C.base.s)` instance and verifying
continuity + plus-subring containment, both currently missing — see
file docblock). The result then transfers any rational-open membership
on `Spa(A, A⁺)` to a pointwise condition on `Spa(A_loc, A_loc⁺)`.

The lemma is stated WITHOUT `Finset.image`, so it does not require
`[DecidableEq B]`; this gives the cleanest reusable formulation. -/
lemma comap_mem_rationalOpen_iff
    {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ)
    (T : Finset A) (s : A) {w : Spv B} (hw : w ∈ Spa B B⁺) :
    comap φ w ∈ rationalOpen T s ↔
      (∀ t ∈ T, w.vle (φ t) (φ s)) ∧ ¬ w.vle (φ s) 0 := by
  refine ⟨fun ⟨_, hvT, hvs⟩ => ⟨fun t ht => by simpa only [comap_vle] using hvT t ht,
      fun hws => hvs (by rwa [comap_vle, map_zero])⟩, fun ⟨hwT, hws⟩ =>
    ⟨comap_mem_spa hφ hAB hw, fun t ht => by simpa only [comap_vle] using hwT t ht,
      fun hvs => hws (by rwa [comap_vle, map_zero] at hvs)⟩⟩

/-! ## Target signature: full pre-localisation transfer

The next layer above `comap_mem_rationalOpen_iff` packages the transfer
through the SPECIFIC ring hom `algebraMap A → Localization.Away
C.base.s`. The exact missing target signature is:

```
theorem rationalOpen_transfer_via_localization
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    -- Plus subring on the localisation:
    [PlusSubring (Localization.Away s)]
    -- Continuity + plus-subring containment for `algebraMap`:
    (h_cont : Continuous (algebraMap A (Localization.Away s)))
    (h_plus : (A⁺ : Set A) ≤
      ((Localization.Away s)⁺ : Set (Localization.Away s)).comap
        (algebraMap A (Localization.Away s))) :
    -- Transfer at the rational open `R(T, s)`:
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      comap (algebraMap A (Localization.Away s)) w ∈ rationalOpen T s ↔
        (∀ t ∈ T, w.vle (algebraMap A _ t) (algebraMap A _ s)) ∧
          ¬ w.vle (algebraMap A _ s) 0
```

**Status**: directly available from `comap_mem_rationalOpen_iff` (this
file) once `[PlusSubring (Localization.Away s)]` is supplied. The
remaining obligations are:

### Upstream API gaps (precise, ordered by priority)

1. **`PlusSubring (Localization.Away s)` instance / construction**.
   This is the genuinely missing structural API. The canonical Wedhorn
   choice is the integral closure of `image (A⁺)` inside
   `Localization.Away s`, or equivalently the subring generated by `A⁺`
   plus the `s/s = 1`-style fractions. No `instance` or `def` for this
   exists in the codebase (`grep -rn "instance.*PlusSubring.*Localization"`
   returns empty).

2. **Continuity of `algebraMap A → Localization.Away s` under
   `locTopology`**. The relevant topology on `Localization.Away s` is
   `LocalizationTopology.locTopology P T s` (`Adic spaces/LocalizationTopology.lean`).
   Continuity should follow from the construction but needs an explicit
   continuity lemma. May already exist — needs grep for
   `Continuous.*algebraMap.*Localization` (returns empty under default
   form; might be present under different naming).

3. **Plus-subring containment**. Once (1) is supplied, the containment
   `(A⁺ : Set A) ≤ ((Localization.Away s)⁺).comap (algebraMap A _)`
   should follow from the canonical choice of `(A_loc⁺)` as the
   integral-closure-of-image construction.

### Why `[DecidableEq B]` is not required

`comap_mem_rationalOpen_iff` deliberately states the conclusion via
the pointwise predicate `∀ t ∈ T, w.vle (φ t) (φ s)` rather than via
`Finset.image φ T` (which would need `[DecidableEq B]` to even define
the image). This keeps the lemma usable in callsites where
`B = Localization.Away s` lacks `[DecidableEq]` instances — the typical
case for Tate / non-discrete rings.

### Where the full transfer slots in

After upstream gaps (1)-(3) close, the transfer
`rationalOpen_transfer_via_localization` is a one-liner application
of `comap_mem_rationalOpen_iff`. The full Wedhorn 8.34(ii) Route B
proof then proceeds:

1. Pre-localise `A` at `C.base.s` to obtain `(A_loc, A_loc⁺)`.
2. Apply Cor 7.32 in `Spa(A_loc, A_loc⁺)` (where `C.base.s` is now
   invertible, so the test family choice is unconstrained).
3. The σ-domination output transfers back to `Spa(A, A⁺)` via
   `comap_mem_rationalOpen_iff`, yielding the per-`t'` inequalities
   needed to discharge `hT_test_compat` for the multi-element case.

### Status

This file lands the SMALLEST genuinely-new transfer lemma
(`comap_mem_rationalOpen_iff`) and pins the precise upstream API
gaps blocking the full transfer. The file is structural Wedhorn-route
content: no faithful-flatness / Cor 8.32 / Jacobson / T001 detours. -/

end ValuationSpectrum
