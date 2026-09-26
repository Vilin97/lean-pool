/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Nonarchimedean Scottish Book — Problem 31

**Proposer:** Kiran Kedlaya
**Date:** 29 November 2019

## Problem Statement

Let (A, A+) be an adic ring with finitely generated ideal I. If the complement of the zero
locus of I in Spec A⟨T_1, ..., T_n⟩ is noetherian for all n, is A sheafy?

## Notes

None.

## Status

Open.

## Definitions needed

- **Zero locus complement**: The open subset Spec(A⟨T_1, ..., T_n⟩) \ V(I) where V(I) is
  the vanishing locus of the ideal I.
- **Restricted power series ring**: A⟨T_1, ..., T_n⟩ = `restrictedMvPowerSeriesSubring n A`,
  the subring of `MvPowerSeries (Fin n) A` with coefficients tending to 0.
-/

@[expose] public section

open ValuationSpectrum TopologicalSpace

universe u

/-- **Nonarchimedean Scottish Book, Problem 31** (Kedlaya, open).

Let `(A, A⁺)` be an adic ring with finitely generated ideal of definition `I`.
If the complement of the zero locus `V(I)` in `Spec A⟨T₁,...,Tₙ⟩` is a Noetherian
topological space for all `n`, is `A` sheafy?

Here `A⟨T₁,...,Tₙ⟩` is `restrictedMvPowerSeriesSubring n A`, the canonical concrete
definition of the restricted power series ring. -/
theorem problem31 (A : Type u) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [PlusSubring A] [IsHuberRing A] [T2Space A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (I : Ideal A) (hI : I.FG)
    (h : ∀ n : ℕ, NoetherianSpace
      ↥(PrimeSpectrum.zeroLocus
        (SetLike.coe (I.map (algebraMap A (restrictedMvPowerSeriesSubring n A)))))ᶜ) :
    IsSheafy A := by
  sorry
