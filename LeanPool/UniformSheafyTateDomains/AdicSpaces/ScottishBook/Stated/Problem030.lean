/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Nonarchimedean Scottish Book — Problem 30

**Proposer:** Alexander Zavyalov
**Date:** 6 June 2019

## Problem Statement

Let X = Spa(A, A+) be the adic spectrum of a complete strongly noetherian Tate-Huber pair.
For x ∈ X, is the stalk O_{X,x} noetherian?

## Notes

Known for topologically finitely generated over rank-1 valuation field (Temkin).

## Status

Open.

## Definitions needed

- **Strongly noetherian**: A Tate ring A such that A⟨T_1, ..., T_n⟩ is noetherian for
  all n.
- **Stalk of structure sheaf**: The colimit O_{X,x} = colim_{x ∈ U} O_X(U) over open
  neighborhoods of x in Spa(A, A+).
-/

open ValuationSpectrum Filter

universe u

namespace ScottishBook

/-! ### The problem statement -/

/-- **Nonarchimedean Scottish Book, Problem 30** (Zavyalov, open).

Let `X = Spa(A, A⁺)` be the adic spectrum of a complete, strongly noetherian Tate-Huber pair.
For `x ∈ X`, is the stalk `𝒪_{X,x}` noetherian?

Here `𝒪_{X,x}` is modeled by the algebraic stalk `Localization.AtPrime x.val.supp`,
i.e., the localization of `A` at the prime ideal `supp(x)`. -/
theorem problem30 (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [CompleteSpace A]
    [PlusSubring A] [IsTateRing A] [IsStronglyNoetherian A]
    (x : Spa A A⁺) : IsNoetherianRing (Localization.AtPrime x.val.supp) := by
  sorry

end ScottishBook
