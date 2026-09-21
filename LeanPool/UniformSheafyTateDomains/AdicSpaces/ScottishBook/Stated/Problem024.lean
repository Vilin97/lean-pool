/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
import Mathlib.RingTheory.Flat.Basic

/-!
# Nonarchimedean Scottish Book — Problem 24

**Proposer:** Kiran Kedlaya
**Date:** 16 September 2016

## Problem Statement

Let (A, A+) → (B, B+) be a rational localization of Huber-Tate pairs. Is the morphism
A → B necessarily flat?

## Notes

- True in the strongly noetherian case (due to Huber).
- For stably uniform pairs, "pseudoflatness" is shown in [KL2].

## Status

Open in general.

## Definitions needed

- **Rational localization flatness**: Whether the canonical map A → B arising from a
  rational localization (A, A+) → (B, B+) is a flat ring homomorphism.

## Mathematical Background

Given a Huber-Tate pair `(A, A⁺)` and a rational localization datum `D = (T, s)`,
the localization `Localization.Away D.s` is an `A`-algebra via `algebraMap`. The
completed localization `presheafValue D` (the presheaf value `A⟨T/s⟩`) also carries
an `A`-module structure via the canonical map `D.canonicalMap : A →+* presheafValue D`.

Problem 24 asks whether these are flat `A`-modules.

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 24
* Wedhorn, *Adic Spaces*, §8.1 (rational localizations)
* Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*
-/

open ValuationSpectrum

namespace ScottishBook

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### Problem 24: Flatness of rational localizations -/

/-- **Scottish Book Problem 24** (Kedlaya, 16 Sep 2016), algebraic version:
*For a Tate ring `A` and a rational localization datum `D`, the localization
`Localization.Away D.s` is flat as an `A`-module.*

This is the algebraic formulation: flatness of `A → Aₛ` before completion.
The `sorry` represents the open problem. -/
theorem problem24 [PlusSubring A] [IsTateRing A] (D : RationalLocData A) :
    Module.Flat A (Localization.Away D.s) := by
  sorry

/-- **Scottish Book Problem 24** (Kedlaya, 16 Sep 2016), completed version:
*For a Tate ring `A` with restriction maps and a rational localization datum `D`,
the completed localization `A⟨T/s⟩ = presheafValue D` is flat as an `A`-module.*

This is the analytic formulation: flatness of the completed localization `A → A⟨T/s⟩`.
The `sorry` represents the open problem. -/
theorem problem24' [PlusSubring A] [IsTateRing A]
    (D : RationalLocData A) :
    @Module.Flat A (presheafValue D)
      _ _ (RingHom.toModule D.canonicalMap) := by
  sorry

end ScottishBook
