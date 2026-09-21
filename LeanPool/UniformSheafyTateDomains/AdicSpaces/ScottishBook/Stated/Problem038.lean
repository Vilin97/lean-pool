/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Tilting

/-!
# Nonarchimedean Scottish Book — Problem 38

**Proposer:** Shahoseini
**Date:** 24 February 2021

## Problem Statement

Let K be a perfectoid field of characteristic 0. Let E be a perfectoid subfield of the
tilt K^b. Is E necessarily the tilt of a perfectoid subfield of K?

## Notes

None.

## Status

RESOLVED: No.

## Formalization

We state the negation: there exists a perfectoid field `K` of characteristic 0 whose tilt
`K♭` contains a perfectoid subfield `E` that is not the tilt of any perfectoid subfield
of `K`.
-/

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 38** (Shahoseini, 24 Feb 2021):
*Not every perfectoid subfield of the tilt `K♭` is the tilt of a perfectoid subfield of `K`.*

This is **resolved** (negatively). The `sorry` represents the construction of the
counterexample.

The statement says: there exists a perfectoid field `K` and a subfield of its tilt `K♭` that
is perfectoid but does not arise as the tilt of any perfectoid subfield of `K`. -/
theorem problem38 :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p))
      (K : Type u) (_ : Field K) (τ : TopologicalSpace K) (_ : IsTopologicalRing K)
      (u : UniformSpace K) (_ : IsLinearTopology K K) (_ : IsPerfectoidField p K),
    -- There exists a perfectoid subfield of K♭ that is not the tilt of any
    -- perfectoid subfield of K
    ∃ (E : Type u) (_ : Field E) (_ : TopologicalSpace E) (_ : IsTopologicalRing E)
        (_ : UniformSpace E) (_ : IsLinearTopology E E) (_ : IsPerfectoidField p E)
        (_ : E →+* PerfectoidRing.tilt p K),
      ¬ ∃ (L : Type u) (_ : Field L) (_ : TopologicalSpace L) (_ : IsTopologicalRing L)
          (_ : UniformSpace L) (_ : IsLinearTopology L L) (_ : IsPerfectoidField p L)
          (_ : L →+* K),
        Nonempty (E ≃+* PerfectoidRing.tilt p L) := by
  sorry

end ScottishBook
