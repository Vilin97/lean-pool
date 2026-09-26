/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings

/-!
# Nonarchimedean Scottish Book — Problem 28

**Proposer:** Kiran Kedlaya
**Date:** 11 October 2017

## Problem Statement

Do there exist (A, A+) with A Tate/perfectoid and an element f where multiplication by f
is a strict inclusion on A but f restricts to zero on some rational subspace?

## Notes

None.

## Status

Open.

## Definitions needed

- **Strict morphism**: A continuous linear map between topological modules such that the
  induced map from the quotient by the kernel (with quotient topology) to the image (with
  subspace topology) is a homeomorphism.
- **Rational subspace restriction**: The image of f under the canonical map A → B for a
  rational localization (B, B+) of (A, A+).

## Mathematical Background

Given a Tate Huber pair `(A, A⁺)` and an element `f : A`, "multiplication by `f` is a
strict inclusion" means:
1. The map `a ↦ f * a` is injective (i.e., `f` is a non-zero-divisor).
2. The map `a ↦ f * a`, viewed as a map onto its image `fA ⊆ A`, is open (equivalently,
   the quotient topology on `A / ker(f·) ≅ A` coincides with the subspace topology on `fA`).

"f restricts to zero on some rational subspace" means there exists a rational localization
datum `D` such that the image of `f` under `algebraMap A (Localization.Away D.s)` is zero,
i.e., `f` is annihilated by a power of `D.s` in `A`.

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 28
* Wedhorn, *Adic Spaces*, §6 (Huber/Tate rings), §8.1 (rational localizations)
-/

@[expose] public section

open ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 28** (Kedlaya, 11 Oct 2017):

*Does there exist a Tate Huber pair `(A, A⁺)` with an element `f : A` such that
multiplication by `f` is injective and open onto its image (i.e., a strict inclusion),
yet `f` maps to zero in the localization `Localization.Away D.s` for some rational
localization datum `D`?*

The three conjuncts encode:
1. `Function.Injective (f * ·)` — `f` is a non-zero-divisor.
2. `IsOpenMap (Set.rangeFactorization (f * ·))` — multiplication by `f` is open onto
   its image `fA` (the "strictness" condition).
3. `algebraMap A (Localization.Away D.s) f = 0` — `f` restricts to zero on the rational
   subspace `R(D.T / D.s)`.

The `sorry` represents this open problem. -/
theorem problem28 :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : PlusSubring A) (_ : IsTateRing A) (f : A)
      (D : RationalLocData A),
      Function.Injective (f * ·) ∧
      IsOpenMap (Set.rangeFactorization (f * ·)) ∧
      algebraMap A (Localization.Away D.s) f = 0 := by
  sorry

end ScottishBook
