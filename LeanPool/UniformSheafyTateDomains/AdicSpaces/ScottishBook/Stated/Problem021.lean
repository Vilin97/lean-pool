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
import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletedResidueField

/-!
# Nonarchimedean Scottish Book — Problem 21

**Proposer:** Kiran Kedlaya
**Date:** 28 April 2016

## Problem Statement

Let (A, A+) be a Huber pair such that Spa(A, A+) has the property that every point has a
perfectoid residue field. When can we conclude that A is perfectoid?

## Notes

None.

## Status

Open.

## Formalization

We state: if every point `v` of `Spa(A, A⁺)` has a completed residue field that admits a
perfectoid ring structure, then `A` is perfectoid.

The `completedResidueField` is defined (as a placeholder) in `CompletedResidueField.lean`.
-/

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 21** (Kedlaya, 28 Apr 2016):
*If every completed residue field of `Spa(A, A⁺)` is perfectoid, then `A` is perfectoid.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

The statement says: given a Huber pair `(A, A⁺)` such that for every `v ∈ Spa(A, A⁺)`,
the completed residue field `κ(v)` admits a perfectoid ring structure, then `A` itself
is perfectoid. -/
theorem problem21
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A]
    [PlusSubring A] [IsTateRing A]
    (hresfields : ∀ (x : ↥(Spa A A⁺)),
      ∃ (τ : TopologicalSpace (completedResidueField A x))
        (h₁ : @IsTopologicalRing (completedResidueField A x) τ _)
        (u : UniformSpace (completedResidueField A x))
        (_ : @IsLinearTopology (completedResidueField A x) (completedResidueField A x)
          _ _ _ τ),
      @IsPerfectoidRing p _ (completedResidueField A x) _ τ h₁ u _) :
    IsPerfectoidRing p A := by
  sorry

end ScottishBook
