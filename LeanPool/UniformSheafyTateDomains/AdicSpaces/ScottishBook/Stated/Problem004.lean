/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidSpace
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidRing

/-!
# Nonarchimedean Scottish Book — Problem 4

**Proposer:** David Hansen
**Date:** 18 December 2015

## Problem Statement

Let A be a sheafy Tate ring, and suppose some Zariski-open dense subset of Spa(A, A+)
is perfectoid. Is A perfectoid?

## Notes

- This is a stronger version of Problem 2.

## Status

Open.

## Formalization

We state: given a sheafy Tate ring `A` and an open dense subset `U` of `Spa(A, A⁺)` that
carries a perfectoid space structure, is `A` a perfectoid ring?

The Zariski-dense condition is captured by requiring `Dense U` in the topology of
`Spa(A, A⁺)`. The perfectoid condition on `U` is stated via the existence of an
`AffinoidPerfectoidSpace` covering the open subset.
-/

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 4** (Hansen, 18 Dec 2015):
*If a Zariski-open dense subset of `Spa(A, A⁺)` is perfectoid, then `A` is perfectoid.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

This is a stronger version of Problem 2. -/
theorem problem4
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A]
    [PlusSubring A] [IsHuberRing A]
    [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] [IsSheafy A]
    -- There exists an open dense subset that is perfectoid
    (U : TopologicalSpace.Opens (SpaTop A))
    (hU_dense : Dense (U : Set (SpaTop A)))
    (hU_perf : ∃ (S : AffinoidPerfectoidSpace.{u} p),
      Nonempty (↥U ≃ₜ S.toTopCat)) :
    IsPerfectoidRing p A := by
  sorry

end ScottishBook
