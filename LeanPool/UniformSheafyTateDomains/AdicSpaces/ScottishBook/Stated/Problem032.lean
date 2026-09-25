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

/-!
# Nonarchimedean Scottish Book — Problem 32

**Proposer:** Kiran Kedlaya
**Date:** 7 July 2020

## Problem Statement

Let A be a perfectoid ring over a perfectoid field K. Let B be an affinoid algebra over K.
Is the completed tensor product of A with B over K sheafy?

## Notes

None.

## Status

Open.

## Formalization

We state: given a perfectoid field `K`, a perfectoid `K`-algebra `A`, and a Tate `K`-algebra
`B`, the completed tensor product `A ⊗̂_K B` is sheafy.

Since the completed tensor product is not yet formalized, we state the existence of a ring
`C` representing `A ⊗̂_K B` with the required sheafy property.
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 32** (Kedlaya, 7 Jul 2020):
*The completed tensor product of a perfectoid ring with an affinoid algebra is sheafy.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

The statement says: given a perfectoid field `K`, a perfectoid `K`-algebra `A`, and a
Tate `K`-algebra `B` (affinoid), there exists a ring `C` (representing the completed
tensor product `A ⊗̂_K B`) that is sheafy. -/
theorem problem32
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [UniformSpace K] [IsLinearTopology K K] [IsPerfectoidField p K]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    [Algebra K A]
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [UniformSpace B] [IsLinearTopology B B] [IsTateRing B]
    [Algebra K B] :
    -- The completed tensor product A ⊗̂_K B is sheafy
    ∃ (C : Type u) (_ : CommRing C) (τ : TopologicalSpace C) (ps : @PlusSubring C _)
      (h₁ : @IsTopologicalRing C τ _) (h₂ : @IsHuberRing C _ τ)
      (hT2 : @T2Space C τ) (hNA : @NonarchimedeanRing C _ τ)
      (hCS : @CompleteSpace C
        (@IsTopologicalAddGroup.rightUniformSpace C _ τ (letI := h₁; inferInstance)))
      (hIR : @IsRingOfIntegralElements C _ τ (@PlusSubring.toSubring C _ ps)),
    @IsSheafy C _ τ h₁ ps h₂ hT2 hNA hCS hIR := by
  sorry

end ScottishBook
