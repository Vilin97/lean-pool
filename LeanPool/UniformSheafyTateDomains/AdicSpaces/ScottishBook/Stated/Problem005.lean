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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Tilting
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Uniform

/-!
# Nonarchimedean Scottish Book — Problem 5

**Proposer:** David Hansen
**Date:** 18 December 2015

## Problem Statement

Let A be a stably uniform Tate ring over Q_p, and let R+ ⊂ R be a perfectoid Tate ring
in characteristic p. Is (W(R+) ⊗ A°)[1/p] stably uniform?

## Notes

- The answer is yes for finite etale A over Q_p<X_1, ..., X_n>.

## Status

Open.

## Formalization

We state: given a stably uniform Tate ring `A` and a perfectoid ring `R` in characteristic `p`,
the localization `(W(R⁺) ⊗ A°)[1/p]` (formed as a tensor product of Witt vectors with the
ring of power-bounded elements, then inverting `p`) is stably uniform.

The completed tensor product and `[1/p]` localization require infrastructure beyond what is
currently available, so the statement is formulated existentially: there exists a ring `C`
representing `(W(R⁺) ⊗̂ A°)[1/p]` with the required properties.
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

/-- **Scottish Book Problem 5** (Hansen, 18 Dec 2015):
*For `A` stably uniform over `ℚ_p` and `R` perfectoid of char `p`,
the ring `(W(R⁺) ⊗̂ A°)[1/p]` is stably uniform.*

This is an **open problem** — the `sorry` is intentional and represents the open question.

The statement is simplified: we assume `A` is a stably uniform Tate ring and `R` is a
perfectoid ring of characteristic `p`, and assert the existence of a stably uniform ring `C`
representing the completed tensor product construction. The `Ainf` construction from
`Tilting.lean` provides `W(R♭)` which is related to `W(R⁺)` in the characteristic `p` case.
-/
theorem problem5
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [PlusSubring A]
    [IsTateRing A] [IsStablyUniform A]
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [UniformSpace R] [IsLinearTopology R R]
    [CharP R p] [IsPerfectoidRing p R] :
    -- There exists a ring C = (W(R+) ⊗̂ A°)[1/p] with stably uniform structure
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : PlusSubring C) (_ : IsHuberRing C),
    IsStablyUniform C := by
  sorry

end ScottishBook
