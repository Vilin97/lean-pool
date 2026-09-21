/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidRing

/-!
# Nonarchimedean Scottish Book — Problem 6

**Proposer:** David Hansen
**Date:** 18 December 2015

## Problem Statement

Define a Tate ring A to be *sousperfectoid* if there exists a perfectoid Tate ring B and a
continuous map A → B admitting a continuous A-Banach module splitting. Is there an example
of a stably uniform Tate ring which is not sousperfectoid?

## Notes

None.

## Status

Open.

## Formalization

We define `IsSousperfectoid` locally by requiring a perfectoid ring `B`, a continuous ring
homomorphism `A →+* B`, and a continuous left inverse of its underlying function. The problem asks
whether all stably uniform rings are sousperfectoid.
-/

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- A ring `A` is **sousperfectoid** here if there exists a perfectoid ring `B` and a continuous
ring homomorphism `f : A →+* B` whose underlying function admits a continuous left inverse
`g : B → A`.

This notion was introduced by Hansen in the context of Problem 6 of the Nonarchimedean
Scottish Book. -/
def IsSousperfectoid (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] : Prop :=
  ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsTopologicalRing B)
    (_ : UniformSpace B) (_ : IsLinearTopology B B) (_ : IsPerfectoidRing p B)
    (f : A →+* B),
    Continuous f ∧
    ∃ (g : B → A), Continuous g ∧ ∀ a : A, g (f a) = a

/-- **Scottish Book Problem 6** (Hansen, 18 Dec 2015):
*There exists a stably uniform Tate ring that is not sousperfectoid.*

This is an **open problem** — the `sorry` is intentional and represents the open question.
The problem asks for a counterexample to the claim that all stably uniform rings
are sousperfectoid. -/
theorem problem6 (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : UniformSpace A) (_ : IsLinearTopology A A) (_ : PlusSubring A)
      (_ : IsHuberRing A) (_ : IsStablyUniform A),
    ¬ IsSousperfectoid p A := by
  sorry

end ScottishBook
