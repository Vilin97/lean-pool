/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.ExcellentRing

/-!
# Nonarchimedean Scottish Book — Problem 37

**Proposer:** Kiran Kedlaya
**Date:** 24 February 2021

## Problem Statement

Let A be a complete Tate strongly noetherian Huber ring. Does A being excellent imply that
A⟨T⟩ is excellent?

## Notes

Likely negative answer. Gabber suggests failure possible even with noetherian ring of
definition.

## Status

Open.
-/

@[expose] public section

universe u

namespace ScottishBook

/-! ### The problem statement -/

/-- **Scottish Book Problem 37** (Kedlaya, open):
Does excellence pass to restricted power series for strongly noetherian Tate rings?

Here `restrictedMvPowerSeriesSubring 1 A` is `A⟨T⟩`, the ring of one-variable power series
over `A` with coefficients tending to `0`. -/
theorem problem37 (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsTateRing A] [IsStronglyNoetherian A] [IsExcellentRing A] :
    IsExcellentRing (restrictedMvPowerSeriesSubring 1 A) := by
  sorry

end ScottishBook
