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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidRing
public import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Nonarchimedean Scottish Book — Problem 3

**Proposer:** David Hansen
**Date:** 17 December 2015

## Problem Statement

Let A be a perfectoid Tate ring with a finite group action. Is the fixed subring A^G
perfectoid?

## Notes

None.

## Status

RESOLVED: Yes.

## Formalization

We state that the fixed-point subring `MulAction.fixedPoints G A` of a perfectoid ring
under a finite group action is again perfectoid (with appropriate topological structure).
The resolution is affirmative.
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 3** (Hansen, 17 Dec 2015):
*The fixed subring `A^G` of a perfectoid ring under a finite group action is perfectoid.*

This is **resolved** (affirmatively). The `sorry` represents the proof, which goes through
almost mathematics and the almost purity theorem.

The statement says: for a perfectoid ring `A` with a finite group `G` acting by ring
automorphisms, the fixed-point set `A^G = {a ∈ A | ∀ g, g • a = a}` admits a perfectoid
ring structure. -/
theorem problem3
    (p : ℕ) [Fact (Nat.Prime p)]
    (G : Type*) [Group G] [Finite G]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    [MulSemiringAction G A] :
    ∃ (_ : CommRing (MulAction.fixedPoints G A))
      (_ : TopologicalSpace (MulAction.fixedPoints G A))
      (_ : IsTopologicalRing (MulAction.fixedPoints G A))
      (_ : UniformSpace (MulAction.fixedPoints G A))
      (_ : IsLinearTopology (MulAction.fixedPoints G A) (MulAction.fixedPoints G A)),
    IsPerfectoidRing p (MulAction.fixedPoints G A) := by
  sorry

end ScottishBook
