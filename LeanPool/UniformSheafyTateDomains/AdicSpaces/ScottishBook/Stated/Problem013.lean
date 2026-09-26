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
# Nonarchimedean Scottish Book — Problem 13

**Proposer:** David Hansen
**Date:** 20 December 2015

## Problem Statement

Let A be a perfectoid Tate ring over Q_p. Does A contain a perfectoid field?

## Notes

None.

## Status

RESOLVED: No (Gabber counterexample).

## Formalization

We state the negation: there exists a perfectoid ring (of mixed characteristic) that does not
contain any perfectoid subfield. The resolution is via a counterexample due to Gabber.
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 13** (Hansen, 20 Dec 2015):
*Not every perfectoid ring contains a perfectoid field.*

This is **resolved** (negatively, by Gabber). The `sorry` represents the construction of the
counterexample: a perfectoid ring `A` such that no subring of `A` that is a field admits a
perfectoid field structure.

The statement is: there exists a perfectoid ring `A` (for some prime `p`) such that there is
no subfield `K ⊆ A` that is perfectoid. -/
theorem problem13 :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p))
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : UniformSpace A) (_ : IsLinearTopology A A) (_ : IsPerfectoidRing p A),
    ¬ ∃ (K : Type u) (_ : Field K) (_ : TopologicalSpace K) (_ : IsTopologicalRing K)
        (_ : UniformSpace K) (_ : IsLinearTopology K K) (_ : IsPerfectoidField p K)
        (_ : K →+* A),
      True := by
  sorry

end ScottishBook
