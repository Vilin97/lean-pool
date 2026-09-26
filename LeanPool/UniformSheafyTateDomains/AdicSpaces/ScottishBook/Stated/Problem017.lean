/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf

/-!
# Nonarchimedean Scottish Book — Problem 17

**Proposer:** Kiran Kedlaya
**Date:** 11 January 2016

## Problem Statement

Let (A, A+) → (B, B+) be a rational localization of adic Banach rings. Does contraction of
a maximal ideal of B to A give a maximal ideal?

## Notes

- A counterexample exists for the strongly noetherian case (due to Gabber).

## Status

Open in general (counterexample in strongly noetherian case).

## Definitions needed

- **Adic Banach ring**: A Banach ring with an adic topology (defined by powers of an ideal).
- **Maximal ideal contraction**: Given a ring homomorphism f: A → B and a maximal ideal
  m ⊂ B, the contraction f⁻¹(m) ⊂ A.
-/

@[expose] public section

open ValuationSpectrum

namespace ScottishBook

/-- **Scottish Book Problem 17** (Kedlaya, counterexample by Gabber):

There exists a Huber pair `(A, A⁺)` with restriction maps and a rational localization
datum `D`, together with a maximal ideal `m` of the presheaf value `𝒪_X(R(T/s))`,
such that the contraction `D.canonicalMap⁻¹(m)` is **not** maximal in `A`.

This witnesses the negative answer to Problem 17 in the strongly noetherian case. -/
theorem problem17_counterexample :
    ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : PlusSubring A) (_ : IsHuberRing A) (D : RationalLocData A)
      (m : Ideal (presheafValue D)),
      m.IsMaximal ∧ ¬(Ideal.comap D.canonicalMap m).IsMaximal := by
  sorry

end ScottishBook
