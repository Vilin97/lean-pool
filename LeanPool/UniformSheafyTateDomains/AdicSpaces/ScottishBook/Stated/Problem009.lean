/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


public import LeanPool.UniformSheafyTateDomains.AdicSpaces.ScottishBook.Stated.Problem007
public import Mathlib.RingTheory.Etale.Basic

/-!
# Nonarchimedean Scottish Book — Problem 9

**Proposer:** Kiran Kedlaya
**Date:** 18 December 2015

## Problem Statement

Let (A, A+) → (B, B+) be finite étale. If (A, A+) is stably uniform, is (B, B+) stably
uniform?

## Notes

- True if A is sousperfectoid.

## Status

Open.

## Mathematical Background

A morphism of Huber pairs `(A, A⁺) → (B, B⁺)` is **finite étale** if `B` is a finite
étale `A`-algebra, i.e., `B` is étale over `A` (formally étale + finite presentation) and
finite as an `A`-module.

We formalize "finite étale" using the conjunction of Mathlib's `Algebra.Etale A B`
(= `Algebra.FormallyEtale A B` + `Algebra.FinitePresentation A B`) and `Module.Finite A B`.

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 9
* Wedhorn, *Adic Spaces*, §7 (Definition 7.37)
-/

@[expose] public section

open ValuationSpectrum ScottishBook

namespace ScottishBook

universe u v

/-- **Scottish Book Problem 9** (Kedlaya, 18 Dec 2015, open):
*Finite étale extensions preserve stable uniformity.*

Let `(A, A⁺) → (B, B⁺)` be a morphism of Huber pairs such that `B` is a finite étale
`A`-algebra. If `(A, A⁺)` is stably uniform, is `(B, B⁺)` stably uniform?

The hypothesis `Algebra.Etale A B` encodes that `B` is formally étale and of finite
presentation over `A`; `Module.Finite A B` further requires that `B` is finite as an
`A`-module. The `sorry` is intentional — this is an open problem. -/
theorem problem9
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsHuberRing A] [IsStablyUniform A]
    (B : Type v) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [PlusSubring B] [IsHuberRing B]
    [Algebra A B] [Algebra.Etale A B] [Module.Finite A B] :
    IsStablyUniform B := by
  sorry

end ScottishBook
