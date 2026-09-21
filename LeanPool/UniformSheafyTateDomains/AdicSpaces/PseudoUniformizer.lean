/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings

/-!
# Pseudo-uniformizers

A **pseudo-uniformizer** of a topological ring `A` is a topologically nilpotent unit
(Definition 6.10 of Wedhorn). Every Tate ring has a pseudo-uniformizer.

## Main definitions

* `IsPseudoUniformizer w` : A unit `w : Aˣ` is topologically nilpotent.
* `PseudoUniformizer A` : The type of pseudo-uniformizers of `A`.
* `IsTateRing.pseudoUniformizer` : Extract a pseudo-uniformizer from a Tate ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 6.10
-/

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A unit `w : Aˣ` is a **pseudo-uniformizer** if it is topologically nilpotent
(Definition 6.10 of Wedhorn). -/
def IsPseudoUniformizer (w : Aˣ) : Prop :=
  IsTopologicallyNilpotent (w : A)

/-- The type of pseudo-uniformizers of a topological ring `A`. -/
def PseudoUniformizer (A : Type*) [CommRing A] [TopologicalSpace A] :=
  {w : Aˣ // IsPseudoUniformizer w}

instance : CoeOut (PseudoUniformizer A) Aˣ := ⟨Subtype.val⟩

/-- Every Tate ring has a pseudo-uniformizer. -/
noncomputable def IsTateRing.pseudoUniformizer [IsTateRing A] :
    PseudoUniformizer A :=
  ⟨IsTateRing.exists_topologicallyNilpotent_unit.choose,
   IsTateRing.exists_topologicallyNilpotent_unit.choose_spec⟩

/-- A pseudo-uniformizer is topologically nilpotent. -/
theorem PseudoUniformizer.isTopologicallyNilpotent (w : PseudoUniformizer A) :
    IsTopologicallyNilpotent (w.val : A) :=
  w.property
