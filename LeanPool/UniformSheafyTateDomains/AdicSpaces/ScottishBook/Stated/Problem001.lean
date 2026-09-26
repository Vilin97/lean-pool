/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Algebra.Field.IsField
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.UniformBanach

/-!
# Nonarchimedean Scottish Book — Problem 1

**Proposer:** Kiran Kedlaya
**Date:** 17 December 2015

## Problem Statement

Let K be a nonarchimedean commutative Banach ring whose underlying ring is a field.
Suppose in addition that K is uniform. Is K necessarily a nonarchimedean field?

## Notes

- The answer is negative if the uniformity hypothesis is omitted.
- The answer is positive for perfectoid rings when the base field is non-discretely valued.

## Status

Open.

## Definitions

- **Banach ring**: A complete normed commutative ring (`NormedCommRing K`, `CompleteSpace K`).
- **Nonarchimedean**: The norm satisfies the ultrametric inequality (`IsUltrametricDist K`).
- **Uniform**: The set of power-bounded elements `{a | sup_n ‖aⁿ‖ < ∞}` is bounded.
  See `IsUniformBanach` in `UniformBanach.lean`.
- **Nonarchimedean field**: The norm is multiplicative: `‖a * b‖ = ‖a‖ * ‖b‖`.

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 1
-/

@[expose] public section

namespace ScottishBook

/-! ### The open problem -/

/-- **Scottish Book Problem 1** (Kedlaya, 17 Dec 2015):
*A uniform nonarchimedean commutative Banach ring whose underlying ring is a field
has a multiplicative norm.*

More precisely: if `K` is a nonarchimedean (`IsUltrametricDist`) commutative Banach ring
(`NormedCommRing K`, `CompleteSpace K`) whose underlying ring is a field (`IsField K`),
and `K` is uniform (`IsUniformBanach K`), then the norm is multiplicative:
`‖a * b‖ = ‖a‖ * ‖b‖` for all `a b : K`.

This is an **open problem** — the `sorry` is intentional and represents the open question.
-/
theorem problem1 (K : Type*) [NormedCommRing K] [CompleteSpace K]
    [IsUltrametricDist K] [IsUniformBanach K] (hfield : IsField K) :
    ∀ (a b : K), ‖a * b‖ = ‖a‖ * ‖b‖ := by
  sorry

end ScottishBook
