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
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SeminormalRing

/-!
# Nonarchimedean Scottish Book — Problem 20

**Proposer:** Kiran Kedlaya
**Date:** 27 April 2016

## Problem Statement

Let A be a perfectoid ring. Let B be the seminormalization of a finite A-algebra. Is the
(uniform) completion of B perfectoid?

## Notes

None.

## Status

Open.

## Formalization

We state: given a perfectoid ring `A`, a finite `A`-algebra `B` that is seminormal, and the
completion `B̂` of `B`, is `B̂` perfectoid? The completion and topology on `B` are left
existential since the seminormalization construction requires additional infrastructure.
-/

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 20** (Kedlaya, 27 Apr 2016):
*The uniform completion of the seminormalization of a finite perfectoid algebra is perfectoid.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

The statement says: given a perfectoid ring `A` and a finite `A`-algebra `B` that is
seminormal (i.e., `b³ = c²` implies existence of `a` with `a² = b`, `a³ = c`), the
completion of `B` admits a perfectoid ring structure. -/
theorem problem20
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsSeminormalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [UniformSpace B] [IsLinearTopology B B] [CompleteSpace B] [T0Space B] :
    ∃ (_ : IsPerfectoidRing p B), True := by
  sorry

end ScottishBook
