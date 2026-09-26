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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.IntegralStructureSheaf

/-!
# Nonarchimedean Scottish Book — Problem 27

**Proposer:** Kiran Kedlaya
**Date:** 11 June 2017

## Problem Statement

Let (A, A+) be a Tate Huber pair. Is H^1(Spa(A, A+), O+) always annihilated by some
topologically nilpotent unit?

## Notes

None.

## Status

Open.

## Definitions needed

- **O+ sheaf**: The integral structure sheaf on Spa(A, A+), whose sections on a rational
  subset R(T/s) are the power-bounded elements of the completed localization
  (see `integralPresheafValue` in `IntegralStructureSheaf.lean`).
- **Sheaf cohomology H^1**: The first derived functor cohomology of the sheaf O+ on the
  topological space Spa(A, A+) (see `integralCohomology` in `IntegralStructureSheaf.lean`).
- **AnnihilatedByTopNilpotentUnit**: The predicate that a module is killed by a
  topologically nilpotent unit (see `IntegralStructureSheaf.lean`).

## Mathematical Background

The integral structure sheaf `O⁺` on `X = Spa(A, A⁺)` assigns to each rational subset
`R(T/s)` the subring `O⁺(R(T/s)) = A°(R(T/s))` of power-bounded elements in the
presheaf value `O_X(R(T/s))`.

Problem 27 asks whether `H¹(X, O⁺)` is always "almost zero" in the sense that it is
annihilated by a topologically nilpotent unit of `A`. This would mean that `O⁺` is
"almost acyclic" in degree 1, a key property for the theory of adic spaces.

A positive answer is known for:
- Perfectoid algebras (Scholze, 2012).
- Strongly noetherian Tate rings (Huber).

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 27
* Wedhorn, *Adic Spaces*, §8.1 (integral structure sheaf)
* Scholze, *Perfectoid Spaces*, Theorem 6.3
-/

@[expose] public section

open ValuationSpectrum

universe u

namespace ScottishBook

/-- **Nonarchimedean Scottish Book, Problem 27** (Kedlaya, 11 Jun 2017).

*Let `(A, A⁺)` be a Tate Huber pair. Is `H¹(Spa(A, A⁺), O⁺)` always annihilated by
some topologically nilpotent unit of `A`?*

The integral structure sheaf `O⁺` assigns to each rational subset `R(T/s)` the
power-bounded elements of `O_X(R(T/s))` (see `integralPresheafValue`). The question
asks whether the first cohomology of this sheaf is always killed by a topologically
nilpotent unit, which would imply that `O⁺` is "almost acyclic" in degree 1.

This is an **open problem** -- the `sorry` is intentional. -/
theorem problem27 (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsTateRing A] :
    AnnihilatedByTopNilpotentUnit A (integralCohomology A 1) := by
  sorry

end ScottishBook
