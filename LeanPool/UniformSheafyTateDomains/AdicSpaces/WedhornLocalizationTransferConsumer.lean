/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizationContinuity
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizationPlus
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPrelocalizationTransfer

/-!
# Wedhorn 8.34(ii) rational-open transfer consumer

The full Route B pre-localisation rational-open transfer law,
packaged as a single theorem.

## Composition

This file packages the one-line composition of the three landed
upstream APIs:

* `locTopology_algebraMap_continuous`
  (`Adic spaces/WedhornLocalizationContinuity.lean`) — continuity of
  `algebraMap A (Localization.Away s)` for `locTopology P T s hopen`.
* `localizationAwayPlusSubring_aplus_le_comap`
  (`Adic spaces/WedhornLocalizationPlus.lean`) — plus-subring
  containment for the canonical image-form
  `localizationAwayPlusSubring`.
* `comap_mem_rationalOpen_iff`
  (`Adic spaces/WedhornPrelocalizationTransfer.lean`) — the
  rational-open pullback law for any continuous ring hom with
  plus-subring containment.

The combined transfer is the prerequisite for the Wedhorn 8.34(ii)
Route B per-`t'` discharge: pre-localise to `Spa(A_loc, A_loc⁺)` (where
`C.base.s` is invertible), apply Cor 7.32 there, transfer the σ-domination
output back to `Spa(A, A⁺)` via this consumer.

## What this file provides

`rationalOpen_transfer_via_localization` — for any pair-of-definition
`P`, finite test family `T`, and denominator `s` on `A`, plus the
`hopen` boundedness hypothesis defining `locTopology P T s hopen`, and
for any `w` on the localisation lying in
`Spa (Localization.Away s) (localizationAwayPlusSubring s).toSubring`,
the rational-open membership transfers via the localisation map:
```
comap (algebraMap A (Localization.Away s)) w ∈ rationalOpen T' s' ↔
  (∀ t ∈ T', w.vle (algebraMap A _ t) (algebraMap A _ s')) ∧
    ¬ w.vle (algebraMap A _ s') 0
```

The theorem deliberately uses the explicit `Spa _ subring` form (rather
than the `(Localization.Away s)⁺` notation) to avoid global
`PlusSubring (Localization.Away s)` instance issues — consumers can
either supply their own plus-subring or use the canonical image form
documented inline.

No Lane B / Cor 8.32 / Jacobson / faithful-flatness / T001 content. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Wedhorn 8.34(ii) rational-open transfer consumer**.

For a `PairOfDefinition P` on `A`, a `(T, s)`-witnessed `locTopology` on
`Localization.Away s`, and a Spa-point `w` on the localisation w.r.t.
the canonical image-form plus-subring, the rational-open membership
of `comap (algebraMap A _) w` transfers to a pointwise condition on
`w` via the algebra map.

**Hypotheses**:
* `(P, T, s, hopen)` — `locTopology` data on `Localization.Away s`.
* `(T', s')` — the rational open `R(T', s')` on `Spa A A⁺` to test.
* `hw : w ∈ Spa (Localization.Away s) (localizationAwayPlusSubring s).toSubring`
  — Spa-membership on the localisation w.r.t. the image plus-subring.

**Conclusion**: `comap (algebraMap A _) w ∈ R(T', s') ↔ (pointwise
inequalities on `w`)`.

**Proof**: one-line composition of `locTopology_algebraMap_continuous`,
`localizationAwayPlusSubring_aplus_le_comap`, and
`comap_mem_rationalOpen_iff`. Uses `letI` locally to introduce the
`locTopology` and `localizationAwayPlusSubring` typeclasses for the
`comap_mem_rationalOpen_iff` application. -/
theorem rationalOpen_transfer_via_localization
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T' : Finset A) (s' : A) {w : Spv (Localization.Away s)}
    (hw : w ∈ @Spa (Localization.Away s) _ (locTopology P T s hopen)
      (localizationAwayPlusSubring s).toSubring) :
    comap (algebraMap A (Localization.Away s)) w ∈ rationalOpen T' s' ↔
      (∀ t ∈ T', w.vle (algebraMap A (Localization.Away s) t)
        (algebraMap A (Localization.Away s) s')) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s') 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
  exact comap_mem_rationalOpen_iff
    (locTopology_algebraMap_continuous P T s hopen)
    (localizationAwayPlusSubring_aplus_le_comap s) T' s' hw

end ValuationSpectrum
