/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

import LeanPool.UniformSheafyTateDomains.AdicSpaces.ScottishBook.Stated.Problem007
import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletedResidueField

/-!
# Nonarchimedean Scottish Book — Problem 35

**Proposer:** Kiran Kedlaya
**Date:** 29 October 2020

## Problem Statement

Let (A, A+) be a Tate Huber pair. Does there exist a stably uniform (B, B+) inducing a
homeomorphism on adic spectra and complete residue field isomorphisms?

## Notes

None.

## Status

Open.

## Definitions needed

- **Stably uniform approximation**: A stably uniform Huber pair (B, B+) with a morphism
  from (A, A+) such that Spa(B, B+) → Spa(A, A+) is a homeomorphism.
- **Residue field isomorphism**: For each point x ∈ Spa(A, A+), the induced map on
  completed residue fields is an isomorphism.
  See `ValuationSpectrum.completedResidueField` in `CompletedResidueField.lean`.
-/

open ValuationSpectrum ScottishBook

universe u

namespace ScottishBook

/-- **Scottish Book Problem 35** (Kedlaya, 29 Oct 2020):
*Every Tate Huber pair admits a stably uniform approximation.*

Given a Tate Huber pair `(A, A⁺)`, there exists a stably uniform Huber pair `(B, B⁺)`
together with a homeomorphism `φ : Spa(B, B⁺) ≃ₜ Spa(A, A⁺)` that induces ring
isomorphisms on completed residue fields at every point.

The existentially bound instances on `B` equip it with the structure of a commutative
topological ring with `PlusSubring`, `IsHuberRing`, and `IsStablyUniform`.

This is an **open problem** — the `sorry` is intentional and represents the open question. -/
theorem problem35 (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsTateRing A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsTopologicalRing B)
      (_ : PlusSubring B) (_ : IsHuberRing B) (_ : IsStablyUniform B)
      (φ : ↥(Spa B PlusSubring.toSubring) ≃ₜ ↥(Spa A A⁺)),
      ∀ (x : ↥(Spa A A⁺)),
        Nonempty (completedResidueField A x ≃+*
          completedResidueField B (φ.symm x)) := by
  sorry

end ScottishBook
