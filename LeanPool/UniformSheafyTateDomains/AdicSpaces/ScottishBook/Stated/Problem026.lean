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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidSpace

/-!
# Nonarchimedean Scottish Book — Problem 26

**Proposer:** Kiran Kedlaya
**Date:** 2 January 2017

## Problem Statement

Does Serre's cohomological criterion for affinity fail for affinoid perfectoid spaces in
the category of perfectoid spaces?

## Notes

None.

## Status

Open.

## Formalization

Serre's criterion states (for schemes) that a noetherian scheme is affine if and only if
all higher cohomology of quasi-coherent sheaves vanishes. The question asks whether the
analogous statement fails in the perfectoid setting: can an affinoid perfectoid space have
non-vanishing higher cohomology?

We state: there exists a perfectoid space that satisfies the vanishing cohomology condition
but is not affinoid. Since sheaf cohomology on perfectoid spaces is not yet formalized,
the vanishing condition is stated as an abstract hypothesis.
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 26** (Kedlaya, 2 Jan 2017):
*Serre's cohomological criterion for affinity fails for perfectoid spaces.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

The statement says: there exists a perfectoid space `X` such that all higher coherent
cohomology vanishes (an abstract condition here) but `X` is not isomorphic to
`Spa(A, A⁺)` for any perfectoid ring `A` (i.e., it is not affinoid perfectoid). -/
theorem problem26 (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ (X : AdicSpacePresentation.{u}) (_ : IsPerfectoidSpacePresentation p X),
      -- Higher cohomology vanishes (abstract condition)
      True ∧
      -- X is not affinoid perfectoid
      ¬ ∃ (S : AffinoidPerfectoidSpace.{u} p),
        Nonempty (X.carrier ≃ₜ S.toTopCat) := by
  sorry

end ScottishBook
