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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LocalizationTopology
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPrelocalizationTransfer

/-!
# Plus-subring construction on `Localization.Away s` (Wedhorn 8.34(ii) Route B)

The upstream blocker identified in `WedhornPrelocalizationTransfer.lean`'s
docblock — the missing `PlusSubring (Localization.Away s)` instance — is
the structural API needed to form `Spa (Localization.Away s) (Localization.Away s)⁺`
and instantiate the rational-open comap pullback law for the `algebraMap A
→ Localization.Away s` map.

This file lands the **smallest usable plus-subring construction**:
`Subring.map (algebraMap A _) A⁺` (the IMAGE of `A⁺` under `algebraMap`).
This is the minimal subring of `Localization.Away s` ensuring the
plus-subring containment hypothesis `(A⁺ : Set A) ≤ ((Localization.Away
s)⁺ : Set _).comap (algebraMap A _)` holds trivially. It does NOT
replicate Wedhorn's full Definition 7.14 conditions (open + integrally
closed) — those refinements are documented as a future strengthening
target and not needed for the rational-open transfer alone.

## API audit (this file)

### `PlusSubring` definition recap (`Adic spaces/AdicSpectrum.lean:96`)

```
class PlusSubring (A : Type*) [CommRing A] where
  toSubring : Subring A
```

The plus-subring is just a designated `Subring`; the typeclass holds no
additional structure beyond the subring choice. Therefore, providing a
`PlusSubring (Localization.Away s)` reduces to providing a `Subring
(Localization.Away s)`.

### `Spa` membership constraint (`Adic spaces/AdicSpectrum.lean:110`)

```
def Spa (A : Type*) [CommRing A] [TopologicalSpace A] (Aplus : Subring A)
    : Set (Spv A) :=
  { v ∈ Cont A | ∀ f ∈ Aplus, v.vle f 1 }
```

`Spa(B, B⁺)` requires `v.vle f 1` for every `f ∈ B⁺`. To make the
comap `comap (algebraMap A _) v ∈ Spa(A, A⁺)` (when `v ∈ Spa(B, B⁺)`),
we need `B⁺ ⊇ algebraMap '' A⁺` (so that `v` already enforces
`v.vle (algebraMap f) 1` for all `f ∈ A⁺`).

The minimal such `B⁺` is `Subring.map (algebraMap A _) A⁺` — the IMAGE
of `A⁺` as a subring of `Localization.Away s`.

## What this file provides

1. `localizationAwayPlusSubring` — the canonical `PlusSubring (Localization.Away s)`
   instance choice as a `noncomputable def`, using `Subring.map (algebraMap A
   (Localization.Away s)) A⁺`. Provided as `def` rather than `instance` to
   avoid global instance-resolution interference; consumers `letI` it at
   the callsite.

2. `localizationAwayPlusSubring_aplus_le_comap` — the plus-subring
   containment hypothesis required by `comap_mem_rationalOpen_iff`:
   `(A⁺ : Set A) ≤ ((Localization.Away s)⁺ : Set _).comap (algebraMap A _)`.
   Proof: trivial — `algebraMap f` is in the image, by `Subring.mem_map`.

3. Documented continuity gap
   (`locTopology_algebraMap_continuous` — UNFORMALISED), with a precise
   proof sketch. This is the LAST upstream API gap before the full
   `rationalOpen_transfer_via_localization` chain can compile.

## What this file does NOT provide

* The continuity proof for `algebraMap A → Localization.Away s` under
  `locTopology`. Documented as a target signature with proof sketch in
  the trailing docblock; the proof requires reaching into the
  `RingSubgroupsBasis` machinery of `LocalizationTopology` and is the
  next concrete formalisation target.
* Wedhorn's Definition 7.14 refinements: openness and integral closedness
  of `(Localization.Away s)⁺`. The minimal IMAGE choice here does not
  satisfy these — it is just the minimum required for the rational-open
  transfer law. A future ticket can refine to the integral-closure form.

No Lane B / Cor 8.32 / Jacobson / faithful-flatness / T001 content. -/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-- **The canonical plus-subring on `Localization.Away s`** (image-form).

The smallest usable choice: the image of `A⁺` under
`algebraMap A (Localization.Away s)`, as a `Subring (Localization.Away s)`.
Provided as a `noncomputable def` (not `instance`) to avoid global
instance-resolution interference; consumers introduce it locally via
`letI := localizationAwayPlusSubring s` at the callsite.

**Properties**:
* Trivial plus-subring containment
  (`localizationAwayPlusSubring_aplus_le_comap` below).
* Does NOT satisfy Wedhorn's Definition 7.14 refinements (openness +
  integral closedness). Adequate for the rational-open transfer law
  (`comap_mem_rationalOpen_iff`); refinement to a Wedhorn-class plus
  subring is future work. -/
@[reducible]
noncomputable def localizationAwayPlusSubring (s : A) :
    PlusSubring (Localization.Away s) where
  toSubring := Subring.map (algebraMap A (Localization.Away s)) A⁺

omit [TopologicalSpace A] in
/-- **Plus-subring containment**: under the canonical `localizationAwayPlusSubring`
choice on `Localization.Away s`, the hypothesis
`(A⁺ : Set A) ≤ ((Localization.Away s)⁺ : Set _).comap (algebraMap A _)`
holds trivially.

**Use case**: this is the `hAB` argument of
`comap_mem_rationalOpen_iff`. Combined with the (still missing)
continuity of `algebraMap` under `locTopology`, it discharges the
prerequisite hypotheses of the rational-open comap pullback for the
specific `algebraMap A → Localization.Away C.base.s` map of the Wedhorn
8.34(ii) Route B pre-localisation step. -/
theorem localizationAwayPlusSubring_aplus_le_comap (s : A) :
    letI : PlusSubring (Localization.Away s) := localizationAwayPlusSubring s
    (A⁺ : Subring A) ≤
      (PlusSubring.toSubring (A := Localization.Away s)).comap
        (algebraMap A (Localization.Away s)) := by
  intro f hf
  exact Subring.mem_map.mpr ⟨f, hf, rfl⟩

/-! ## Caller composition: rational-open transfer once continuity lands

With `localizationAwayPlusSubring` and `localizationAwayPlusSubring_aplus_le_comap`
in hand, the rational-open transfer through `algebraMap A
(Localization.Away s)` reduces to a single missing input: the continuity
of `algebraMap` under the chosen `locTopology`.

### Smallest upstream gap (concrete target signature)

```
theorem locTopology_algebraMap_continuous
    [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    @Continuous A (Localization.Away s) _
      (locTopology P T s hopen)
      (algebraMap A (Localization.Away s))
```

### Proof sketch (NOT implemented here)

The `locTopology` is generated by the `RingSubgroupsBasis` of
neighborhoods `locNhd P T s n = image of (locIdeal)^n` in
`Localization.Away s`. To verify continuity of `algebraMap` at `0`:

1. By `locNhd_preimage_eq_locIdeal_pow`, the preimage of `locNhd n`
   under the `locSubring → Localization.Away s` inclusion is exactly
   `(locIdeal)^n` (an ideal of `locSubring`).
2. The composite `algebraMap : A → locSubring → Localization.Away s`
   factors through `algebraMapD : A → locSubring`, so the preimage
   `algebraMap⁻¹(locNhd n) = algebraMapD⁻¹((locIdeal)^n)`.
3. `(locIdeal)^n = Ideal.map algebraMapD (P.I^n)` (by definition of
   `locIdeal`), so `algebraMapD⁻¹(image) ⊇ P.I^n` (subring of A
   underlying `algebraMapD`).
4. `P.I^n` is a neighborhood of `0` in `A` (by `P.hasBasis_nhds_zero`).
5. Therefore `algebraMap⁻¹(locNhd n)` contains a neighborhood of `0`
   in `A`. Continuity at `0` follows; full continuity follows since
   `algebraMap` is an additive group homomorphism.

### Remaining obligations after `locTopology_algebraMap_continuous` lands

Once the continuity above is formalised, the full transfer chain
```
v ∈ Spa(Localization.Away s, (Localization.Away s)⁺)
  → comap (algebraMap A _) v ∈ rationalOpen T s ↔ ...
```
follows by composing:

* `localizationAwayPlusSubring` (this file) — supplies
  `[PlusSubring (Localization.Away s)]`.
* `locTopology_algebraMap_continuous` (the gap above) — supplies
  `Continuous (algebraMap A (Localization.Away s))`.
* `localizationAwayPlusSubring_aplus_le_comap` (this file) — supplies
  the plus-subring containment.
* `comap_mem_rationalOpen_iff` (`WedhornPrelocalizationTransfer.lean`)
  — applies the rational-open pullback.

### Status

This file completes 3 of the 4 upstream APIs. The single remaining
gap is the named `locTopology_algebraMap_continuous` lemma above,
whose proof sketch is provided. Implementing it requires manipulation
of `RingSubgroupsBasis.openAddGroupTopology` plus `locNhd_preimage_eq_locIdeal_pow`
and `P.hasBasis_nhds_zero` — all available in `LocalizationTopology.lean`.

### Future strengthening

The minimal `Subring.map`-based plus subring lacks Wedhorn's Definition
7.14 properties (open + integrally closed). For applications requiring
the full Wedhorn-class plus subring on the localisation, replace
`localizationAwayPlusSubring` with the integral-closure construction:
```
toSubring := IntegralClosure.subring _
  (Subring.closure (image of A⁺ ∪ {1/s}))  -- integrally closed in A_loc
```
The minimal image-based form here remains adequate for the rational-open
transfer alone.

No Lane B / Cor 8.32 / Jacobson / faithful-flatness / T001 content. -/

end ValuationSpectrum
