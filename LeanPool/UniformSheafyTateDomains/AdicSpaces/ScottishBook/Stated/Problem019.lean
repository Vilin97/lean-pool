/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Nonarchimedean Scottish Book — Problem 19

**Proposer:** Kiran Kedlaya
**Date:** 3 February 2016

## Problem Statement

Let (A, A⁺) be a sheafy Huber pair (not necessarily Tate). Is the structure sheaf
acyclic? Does glueing hold for finite projective modules?

## Notes

None.

## Status

Likely RESOLVED (due to Gabber).

## Mathematical Background

A Huber pair `(A, A⁺)` is **sheafy** if the structure presheaf on `Spa(A, A⁺)` is
a sheaf (Definition 8.26 of Wedhorn).  Problem 19 asks two questions about such pairs:

1. **Acyclicity**: Does `H^i(Spa(A, A⁺), O_X) = 0` for all `i > 0`?  This is the
   higher cohomology vanishing for the structure sheaf, generalizing the classical
   result for affine schemes (Serre's vanishing theorem).

2. **Descent for finite projective modules**: Does every vector bundle (finite locally
   free sheaf) on `Spa(A, A⁺)` come from a finite projective `A`-module?  This is
   the analogue of Serre's theorem that vector bundles on `Spec(A)` correspond to
   finite projective `A`-modules.

Gabber has announced positive answers to both questions.

## Definitions formalized

1. `IsAcyclicStructureSheaf A` — the structure sheaf has vanishing higher cohomology
2. `HasFiniteProjectiveDescent A` — finite projective modules satisfy descent
3. `problem19a` / `problem19b` — the two parts of Problem 19

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 19
* Wedhorn, *Adic Spaces*, §8 (Definition 8.26)
-/

open ValuationSpectrum CategoryTheory

namespace ScottishBook

universe u

/-! ### Acyclicity of the structure sheaf -/

/-- The structure sheaf on `Spa(A, A⁺)` is **acyclic** if the higher
Cech cohomology groups vanish for every rational covering.

Since derived functor cohomology `H^i(X, F)` for topological sheaves
is not yet fully developed in Mathlib, we encode acyclicity as:
(1) `IsSheafy` (H^0 exactness / separation), and
(2) a placeholder for higher vanishing.

The placeholder `True` for higher vanishing will be refined once
Mathlib has sheaf cohomology for topological spaces. -/
class IsAcyclicStructureSheaf (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] : Prop where
  /-- The structure presheaf is a sheaf (H^0 exactness). -/
  isSheafy : IsSheafy A
  /-- Higher Cech cohomology vanishes for every rational covering.
  Placeholder pending Mathlib sheaf cohomology infrastructure. -/
  higher_vanishes : True

/-! ### Descent for finite projective modules -/

/-- **Descent for finite projective modules** on `Spa(A, A⁺)`:
every compatible family of finite projective modules over rational
localization rings glues to a finite projective `A`-module.

The precise formulation requires the category of vector bundles on
`Spa(A, A⁺)` and descent data, which are not yet available in
Mathlib.  We record the property as a `Prop`-valued class.

The field `isSheafy` ensures the class is meaningful only for sheafy
pairs; `descent` is a placeholder for the full descent statement. -/
class HasFiniteProjectiveDescent (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] : Prop where
  /-- The underlying sheaf condition. -/
  isSheafy : IsSheafy A
  /-- Compatible families of finite projective modules glue.
  Placeholder pending Mathlib vector bundle infrastructure. -/
  descent : True

/-! ### The open problem -/

variable (A : Type u) [CommRing A] [TopologicalSpace A]
  [PlusSubring A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
  [IsRingOfIntegralElements (A⁺)]

/-- **Scottish Book Problem 19a** (Kedlaya, 3 Feb 2016, likely
resolved by Gabber):
*For a sheafy Huber pair `(A, A⁺)` (not necessarily Tate), the
structure sheaf `O_X` on `Spa(A, A⁺)` is acyclic:
`H^i(Spa(A, A⁺), O_X) = 0` for all `i > 0`.*

The `sorry` represents Gabber's acyclicity theorem for structure
sheaves of adic spaces. -/
theorem problem19a [IsSheafy A] :
    IsAcyclicStructureSheaf A := by
  sorry

/-- **Scottish Book Problem 19b** (Kedlaya, 3 Feb 2016, likely
resolved by Gabber):
*Finite projective modules satisfy descent on `Spa(A, A⁺)` for
sheafy Huber pairs: every vector bundle on `Spa(A, A⁺)` arises
from a finite projective `A`-module.*

The `sorry` represents Gabber's descent theorem for vector bundles
on adic spaces. -/
theorem problem19b [IsSheafy A] :
    HasFiniteProjectiveDescent A := by
  sorry

end ScottishBook
