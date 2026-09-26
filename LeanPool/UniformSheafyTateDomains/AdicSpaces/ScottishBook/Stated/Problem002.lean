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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidSpace

/-!
# Nonarchimedean Scottish Book — Problem 2

**Proposer:** Kiran Kedlaya
**Date:** 17 December 2015

## Problem Statement

Let (A, A+) be a Huber pair which is Tate. Suppose that Spa(A, A+) is a perfectoid space.
Is A necessarily a perfectoid algebra?

## Notes

- A counterexample is known in general.
- The question remains open for stably uniform cases.

## Status

Partially resolved (counterexample known; open for stably uniform).

## Formalization

We state the problem as: if `Spa(A, A⁺)` (viewed as an adic space) is a perfectoid space,
does `A` admit a perfectoid ring structure? The counterexample shows this is false in general,
so we also state the stably uniform variant which remains open.
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- **Scottish Book Problem 2** (Kedlaya, 17 Dec 2015):
*If `Spa(A, A⁺)` is a perfectoid space, is `A` a perfectoid ring?*

This is **partially resolved** — a counterexample exists in general. The `sorry` represents
the (false) general statement; see `problem2_counterexample` for the negation and
`problem2_stablyUniform` for the open stably uniform case. -/
theorem problem2
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [PlusSubring A]
    [IsTateRing A]
    (X : AdicSpacePresentation.{u}) (hX : IsPerfectoidSpacePresentation p X) :
    IsPerfectoidRing p A := by
  sorry

/-- The **counterexample** to Problem 2: there exists a Tate Huber pair whose adic spectrum
is a perfectoid space but whose ring is not perfectoid. -/
theorem problem2_counterexample :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : UniformSpace A) (_ : IsLinearTopology A A) (_ : PlusSubring A)
      (_ : IsTateRing A),
      (∃ (X : AdicSpacePresentation.{u}), IsPerfectoidSpacePresentation p X) ∧
      ¬ ∃ (_ : IsHuberRing A), IsPerfectoidRing p A := by
  sorry

/-- **Scottish Book Problem 2 (stably uniform case)** (open):
*If `(A, A⁺)` is a stably uniform Tate pair and `Spa(A, A⁺)` is perfectoid, is `A` perfectoid?* -/
theorem problem2_stablyUniform
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [PlusSubring A]
    [IsTateRing A] [IsStablyUniform A]
    (X : AdicSpacePresentation.{u}) (hX : IsPerfectoidSpacePresentation p X) :
    IsPerfectoidRing p A := by
  sorry

end ScottishBook
