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
# Nonarchimedean Scottish Book — Problem 14

**Proposer:** Kiran Kedlaya
**Date:** 26 December 2015

## Problem Statement

Let K be an infinite algebraic extension of Q_p. If K is arithmetically profinite, is the
completion of K a perfectoid field? Does the converse hold?

## Notes

None.

## Status

Open.

## Formalization

We define `IsArithmeticallyProfinite` locally: an algebraic extension `K/ℚ_p` is
arithmetically profinite if the higher ramification groups have finite index at each level.
The problem asks whether such extensions complete to perfectoid fields.

Since the formalization of ramification theory is beyond the current library, we define
`IsArithmeticallyProfinite` as an abstract predicate on valued fields.
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- An infinite algebraic extension of `ℚ_p` is **arithmetically profinite** if the higher
ramification filtration has finite quotients at each level.

This is an abstract predicate since the full ramification theory is not yet formalized.
The key examples are the `p`-cyclotomic extension `ℚ_p(ζ_{p^∞})` and more generally
Lubin--Tate extensions. -/
def IsArithmeticallyProfinite
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] : Prop :=
  sorry -- Full definition requires ramification theory

/-- **Scottish Book Problem 14** (Kedlaya, 26 Dec 2015):
*An arithmetically profinite extension of `ℚ_p` completes to a perfectoid field.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

The forward direction: if `K` is arithmetically profinite, then its completion `K̂` admits
a perfectoid field structure. The converse is also open: does every perfectoid field arise
this way? -/
theorem problem14_forward
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [UniformSpace K] [IsLinearTopology K K]
    [CompleteSpace K] [T0Space K]
    (harith : IsArithmeticallyProfinite K) :
    IsPerfectoidField p K := by
  sorry

/-- The converse of Problem 14: every perfectoid field over `ℚ_p` is the completion
of an arithmetically profinite extension. -/
theorem problem14_converse
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [UniformSpace K] [IsLinearTopology K K]
    [IsPerfectoidField p K] :
    IsArithmeticallyProfinite K := by
  sorry

end ScottishBook
