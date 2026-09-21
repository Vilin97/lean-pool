/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidSpace

/-!
# Nonarchimedean Scottish Book — Problem 25

**Proposer:** Kiran Kedlaya
**Date:** 22 September 2016

## Problem Statement

Let X be a rigid analytic space over a perfectoid field K. Let f: X → X be a finite flat
morphism. When is the inverse limit along f a perfectoid space?

## Notes

None.

## Status

Open.

## Formalization

We state: given an adic space `X` that is a perfectoid space, and a finite flat endomorphism
`f : X → X`, the pro-system `... → X → X → X` (iterating `f`) gives rise to a perfectoid
space.

Since the full theory of pro-adic spaces and inverse limits is not yet available, we state
this as: the pro-system determined by a perfectoid space and an endomorphism produces a
perfectoid space in the limit.
-/

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 25** (Kedlaya, 22 Sep 2016):
*The inverse limit of an adic space along a finite flat endomorphism is perfectoid.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

The statement is simplified: given an adic space `X` with a self-map (representing a
finite flat morphism), the resulting inverse limit in the category of adic spaces
is a perfectoid space. Since inverse limits of adic spaces are not yet formalized,
we state the existence of the limit perfectoid space. -/
theorem problem25
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : AdicSpacePresentation.{u})
    -- The endomorphism f : X → X (as a continuous self-map of the underlying space)
    (f : X.carrier → X.carrier) (_ : Continuous f)
    -- f is "finite flat" (abstract condition since adic space morphism theory is not yet
    -- available)
    (hfinflat : True) :
    -- The inverse limit along f is a perfectoid space
    ∃ (Y : AdicSpacePresentation.{u}), IsPerfectoidSpacePresentation p Y := by
  sorry

end ScottishBook
