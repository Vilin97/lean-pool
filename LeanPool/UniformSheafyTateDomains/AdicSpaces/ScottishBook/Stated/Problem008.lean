/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ScottishBook.Stated.Problem007

/-!
# Nonarchimedean Scottish Book — Problem 8

**Proposer:** Kiran Kedlaya
**Date:** 18 December 2015

## Problem Statement

Let (A, A+) be a Huber pair. Is sheafiness or stable uniformity independent of the choice
of A+?

## Notes

None.

## Status

RESOLVED: Yes, both sheafiness and stable uniformity are independent of A+.
- Hansen proved independence of stable uniformity.
- Gabber proved independence of sheafiness.

## Definitions needed

- **Independence of A+**: The property that sheafiness/stable uniformity of (A, A+) does
  not depend on the choice of the ring of integral elements A+ (already formalized as
  `PlusSubring` in this project).
-/

open ValuationSpectrum ScottishBook

namespace ScottishBook

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### Independence of A⁺

The key challenge is that `IsSheafy` and `IsStablyUniform` depend on a `PlusSubring A`
instance (which determines `A⁺`) and an `IsHuberRing A` instance. To state
"independent of A⁺", we parameterize by two different `PlusSubring` instances.
Since `IsHuberRing` does not depend on `PlusSubring`, a single instance suffices.
-/

/-- **Scottish Book Problem 8a** (Kedlaya, resolved by Gabber):
*Sheafiness is independent of the choice of A⁺.*

Given two choices of rings of integral elements `A⁺₁` and `A⁺₂` for the same
topological ring `A`, if `(A, A⁺₁)` is sheafy then so is `(A, A⁺₂)`. -/
theorem problem8_sheafy [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (inst₁ : PlusSubring A) (inst₂ : PlusSubring A)
    (hIR₁ : IsRingOfIntegralElements (inst₁.toSubring))
    (hIR₂ : IsRingOfIntegralElements (inst₂.toSubring))
    (h : @IsSheafy A _ _ _ inst₁ _ _ _ _ hIR₁) :
    @IsSheafy A _ _ _ inst₂ _ _ _ _ hIR₂ := by
  sorry

/-- **Scottish Book Problem 8b** (Kedlaya, resolved by Hansen):
*Stable uniformity is independent of the choice of A⁺.*

Given two choices of rings of integral elements `A⁺₁` and `A⁺₂` for the same
topological ring `A`, if `(A, A⁺₁)` is stably uniform then so is `(A, A⁺₂)`. -/
theorem problem8_stablyUniform [IsHuberRing A]
    (inst₁ : PlusSubring A) (inst₂ : PlusSubring A)
    (h : @IsStablyUniform A _ _ _ inst₁ _) :
    @IsStablyUniform A _ _ _ inst₂ _ := by
  sorry

end ScottishBook
