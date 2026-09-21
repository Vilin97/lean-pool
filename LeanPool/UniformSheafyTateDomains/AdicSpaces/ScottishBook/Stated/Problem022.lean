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
# Nonarchimedean Scottish Book — Problem 22

**Proposer:** Kiran Kedlaya
**Date:** 28 April 2016

## Problem Statement

Let f: A → B be a morphism of perfectoid rings corresponding to g: R → S of perfect rings
(under the tilting correspondence). Is f finite if and only if g is finite?

## Notes

None.

## Status

Open.

## Formalization

We state: given perfectoid rings `A` and `B` with a continuous ring homomorphism `A → B`,
the homomorphism makes `B` a finite `A`-module if and only if the tilted map
`A♭ → B♭` makes `B♭` a finite `A♭`-module.

The tilting operation `PerfectoidRing.tilt` from `Tilting.lean` gives the tilt of each ring.
The "tilted morphism" is stated existentially since constructing the functorial tilt of a
morphism requires establishing that the tilt operation is functorial on the ring of
power-bounded elements.
-/

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 22** (Kedlaya, 28 Apr 2016):
*A morphism `f : A → B` of perfectoid rings is finite if and only if the corresponding
tilted morphism `f♭ : A♭ → B♭` is finite.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

The statement says: given a morphism of perfectoid rings making `B` a finite `A`-algebra,
the induced morphism on tilts makes `B♭` a finite `A♭`-algebra, and conversely. -/
theorem problem22
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A]
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [UniformSpace B] [IsLinearTopology B B] [IsPerfectoidRing p B] [Nontrivial B]
    (f : A →+* B) (_ : Continuous f) [Algebra A B] :
    -- Forward: f finite implies tilt finite
    (Module.Finite A B →
      ∃ (alg : Algebra (PerfectoidRing.tilt p A) (PerfectoidRing.tilt p B)),
        @Module.Finite (PerfectoidRing.tilt p A) (PerfectoidRing.tilt p B) _ _
          alg.toModule) ∧
    -- Backward: tilt finite implies f finite
    (∀ (alg : Algebra (PerfectoidRing.tilt p A) (PerfectoidRing.tilt p B)),
      @Module.Finite (PerfectoidRing.tilt p A) (PerfectoidRing.tilt p B) _ _
        alg.toModule →
        Module.Finite A B) := by
  sorry

end ScottishBook
