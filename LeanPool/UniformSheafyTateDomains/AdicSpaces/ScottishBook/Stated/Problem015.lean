/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.Field.IsField
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CoherentRing

/-!
# Nonarchimedean Scottish Book -- Problem 15

**Proposer:** Kiran Kedlaya
**Date:** 29 December 2015

## Problem Statement

Let R be a perfect valuation ring of characteristic p (not a field). Is W(R) coherent?

## Notes

- The answer is likely negative.

## Status

Open.

## Definitions needed

- **Perfect valuation ring**: A valuation ring R of characteristic p such that the Frobenius
  endomorphism is surjective (equivalently, bijective).
- **Witt vectors W(R)**: The ring of p-typical Witt vectors of R.
- **Coherent ring**: A ring in which every finitely generated ideal is finitely presented
  as a module over itself. See `IsCoherentRing` in `CoherentRing.lean`.
-/

@[expose] public section

/-- **Problem 15** (Kedlaya, 2015): Let `R` be a perfect valuation ring of characteristic `p`
(not a field). Is `𝕎 R` (the ring of `p`-typical Witt vectors over `R`) coherent?

Here `𝕎 R = WittVector p R` denotes the ring of `p`-typical Witt vectors. By a theorem of
Kedlaya, `𝕎 R` is a (non-Noetherian) integral domain when `R` is a perfect valuation ring
of characteristic `p`. The question is whether it is at least coherent.

The expected answer is *negative*. -/
theorem problem15 (p : ℕ) [hp : Fact (Nat.Prime p)]
    (R : Type*) [CommRing R] [IsDomain R] [CharP R p] [PerfectRing R p] [ValuationRing R]
    (hR : ¬ IsField R) :
    IsCoherentRing (WittVector p R) := by
  sorry
