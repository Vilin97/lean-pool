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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Uniform

/-!
# Nonarchimedean Scottish Book — Problem 7

**Proposer:** Kiran S. Kedlaya | **Date:** 18 December 2015

## Statement

> Let `(A, A⁺)` be a sheafy uniform Huber pair. Is `(A, A⁺)` necessarily stably uniform?

## Notes

Remains open even for strongly noetherian `A` (Alex Mathers, 26 Apr 2022).

## Mathematical Background

A Huber pair `(A, A⁺)` is **uniform** if the subring `A°` of power-bounded elements is
bounded (Definition 7.36 of Wedhorn). It is **stably uniform** if for every rational
localization `(A, A⁺) → (B, B⁺)`, the pair `(B, B⁺)` is again uniform.

The importance of this problem: stably uniform implies sheafy (Buzzard–Verberkmoes), so
this asks whether the converse holds among uniform Huber pairs.

## Definitions to formalize

1. `IsUniform A` — the set `A°` of power-bounded elements is bounded
2. `IsStablyUniform A` — every rational localization is uniform
3. The problem statement: `IsSheafy A → IsUniform A → IsStablyUniform A`

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 7
* Wedhorn, *Adic Spaces*, §7 (Definitions 7.36, 7.37)
* Buzzard–Verberkmoes, *Stably uniform affinoids are sheafy*
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### Re-export uniform definitions

The classes `IsUniform` and `IsStablyUniform` are defined in
`TopologicalRing` namespace in `Adic spaces/Uniform.lean`
(Definitions 7.36, 7.37 of Wedhorn). We re-export them here
for use in the ScottishBook namespace. -/

/-- Alias for `TopologicalRing.IsUniform` in the ScottishBook namespace. -/
abbrev IsUniform := TopologicalRing.IsUniform A

/-- Alias for `TopologicalRing.IsStablyUniform` in the ScottishBook namespace. -/
abbrev IsStablyUniform [PlusSubring A] [IsHuberRing A] :=
  TopologicalRing.IsStablyUniform A

/-! ### The open problem -/

/-- **Scottish Book Problem 7** (Kedlaya, 18 Dec 2015):
*Every sheafy uniform Huber pair is stably uniform.*

This is an **open problem** — the `sorry` is intentional and represents the open question.
Formalized here as an axiom-free statement to serve as a target for partial results. -/
theorem problem7 [PlusSubring A] [IsHuberRing A]
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] [IsSheafy A]
    [TopologicalRing.IsUniform A] :
    TopologicalRing.IsStablyUniform A := by
  sorry

/-! ### Partial results and related facts -/

/-- Stably uniform implies uniform for discrete rings.

In the discrete case, this is immediate because `IsUniform.discrete` gives uniform
for any discrete ring. The general (non-discrete) case requires identifying `A` with
its own trivial localization and transferring boundedness through the completion map;
see `IsStablyUniform.isUniform_general` for the statement. -/
theorem IsStablyUniform.isUniform_discrete [PlusSubring A] [IsHuberRing A]
    [DiscreteTopology A] [TopologicalRing.IsStablyUniform A] :
    TopologicalRing.IsUniform A :=
  TopologicalRing.IsUniform.discrete

/-- Stably uniform implies uniform (general case).

Mathematically, `A` is (up to completion) its own trivial localization at `s = 1`:
`presheafValue (globalLocData P) ≅ Â`. Since `IsStablyUniform` says this completion
is uniform, and the canonical map `A → Â` sends power-bounded elements to power-bounded
elements, one can pull back boundedness to `A` (when `A` is complete, `A ≅ Â`).

The full formal proof requires:
1. An `[IsHuberRing A]` assumption (to obtain a `PairOfDefinition P`)
2. Showing the canonical map `A → presheafValue (globalLocData P)` preserves
   and reflects power-boundedness
3. Transferring the `IsBounded` condition through this map

This infrastructure connects `Bounded.lean`, `Presheaf.lean`, and `LocalizationTopology.lean`
in a way that is not yet formalized. -/
theorem IsStablyUniform.isUniform [PlusSubring A] [IsHuberRing A]
    [TopologicalRing.IsStablyUniform A] : TopologicalRing.IsUniform A := by
  sorry -- needs: identify A with presheafValue (globalLocData P) via Remark 8.3

/-- Stably uniform implies sheafy (Buzzard--Verberkmoes).
This is the known implication; Problem 7 asks about the converse for uniform pairs.

The proof, due to Buzzard and Verberkmoes, shows that if all rational localizations
are uniform (have bounded power-bounded subring), then the product restriction maps
for rational coverings are injective (separation axiom for the presheaf).

The argument proceeds by:
1. For a uniform localization, the completion map is injective on power-bounded elements
2. The restriction maps between uniform localizations are determined on dense subrings
3. Injectivity of the product restriction follows from a patching argument

This is a full research paper result and is beyond the scope of the current formalization. -/
theorem IsStablyUniform.isSheafy [PlusSubring A] [IsHuberRing A]
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] [TopologicalRing.IsStablyUniform A] : IsSheafy A := by
  sorry -- needs: Buzzard--Verberkmoes argument (research paper level)

end ScottishBook
