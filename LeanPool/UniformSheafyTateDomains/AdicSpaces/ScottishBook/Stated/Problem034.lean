/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidRing
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Uniform

/-!
# Nonarchimedean Scottish Book — Problem 34

**Proposer:** Kiran Kedlaya
**Date:** 10 September 2020

## Problem Statement

Let Y → X be a morphism where X is perfectoid, Y is uniform, and each fiber is perfectoid.
Is Y perfectoid?

## Notes

None.

## Status

Open.

## Formalization

We state the algebraic version at the level of Huber rings: given a continuous ring
homomorphism `f : A → B` where `A` is perfectoid and `B` is uniform, if every fiber
is perfectoid, then `B` is perfectoid.

The fiber condition is abstracted as a `Prop` parameter since fully formalizing "every fiber
of a morphism of adic spaces is perfectoid" requires adic space morphisms and fiber
functors that are not yet available in this library.
-/

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 34** (Kedlaya, 10 Sep 2020):
*If `Y → X` is a morphism with `X` perfectoid, `Y` uniform, and all fibers perfectoid,
then `Y` is perfectoid.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

The algebraic formulation: given a continuous ring homomorphism `A → B` where `A` is
perfectoid and `B` is uniform, if every "fiber" is perfectoid, then `B` is perfectoid.

The fiber perfectoid condition is encoded as an abstract hypothesis since full adic space
fiber functors are not yet available. -/
theorem problem34
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [UniformSpace B] [IsLinearTopology B B] [IsUniform B]
    (f : A →+* B) (_ : Continuous f)
    -- Abstract fiber perfectoid condition:
    -- for each prime ideal of A, the "fiber" admits a perfectoid structure
    (hfibers : ∀ (𝔭 : Ideal A), 𝔭.IsPrime →
      ∃ (C : Type u) (_ : CommRing C) (τ : TopologicalSpace C) (_ : IsTopologicalRing C)
        (u : UniformSpace C) (_ : IsLinearTopology C C),
      IsPerfectoidRing p C) :
    IsPerfectoidRing p B := by
  sorry

end ScottishBook
