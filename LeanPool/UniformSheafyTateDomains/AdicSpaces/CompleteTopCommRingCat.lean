/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Category.TopCommRingCat
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformRing

/-!
# Category of Complete Topological Commutative Rings

The category `CompleteTopCommRingCat` of complete separated topological commutative rings,
the target category for presheaf values on adic spectra (§8.1 of Wedhorn).

## Main definitions

* `CompleteTopCommRingCat` : Bundled complete separated topological commutative ring.
* `forgetToTopCommRingCat` : Forgetful functor to `TopCommRingCat`.
* `forgetToCommRingCat` : Forgetful functor to `CommRingCat`.
* `forgetToTopCat` : Forgetful functor to `TopCat`.

## Coherence

An object stores a `UniformSpace` (with completeness and separation about *it*); its
topology is **derived** — `instUniformSpace.toTopologicalSpace` — never stored
separately. Earlier revisions carried independent `TopologicalSpace` and
`UniformSpace` fields, so an object could be built whose `Hom`-continuity referred to
one topology while `CompleteSpace` referred to an unrelated uniformity; that
incoherence is structurally impossible now (audit 2026-07-20, WO1 task 2).
`IsTopologicalRing` is stated about the derived topology, and `IsUniformAddGroup`
ties the additive structure to the uniformity itself.
-/

universe u

open CategoryTheory

/-- A bundled complete separated topological commutative ring (§8.1 of Wedhorn). The
topology of the carrier is the topology of the stored uniformity (see the module
docstring: no independent, possibly incoherent `TopologicalSpace` field exists). -/
structure CompleteTopCommRingCat where
  of ::
  /-- The carrier type. -/
  α : Type u
  [instCommRing : CommRing α]
  [instUniformSpace : UniformSpace α]
  [instIsUniformAddGroup : IsUniformAddGroup α]
  [instIsTopologicalRing : IsTopologicalRing α]
  [instCompleteSpace : CompleteSpace α]
  [instT0Space : T0Space α]

namespace CompleteTopCommRingCat

/-- Coerce a `CompleteTopCommRingCat` to its carrier type. -/
instance : CoeSort CompleteTopCommRingCat.{u} (Type u) :=
  ⟨CompleteTopCommRingCat.α⟩

attribute [instance] instCommRing instUniformSpace instIsUniformAddGroup
  instIsTopologicalRing instCompleteSpace instT0Space

/-- Category structure on `CompleteTopCommRingCat`. -/
instance : Category CompleteTopCommRingCat.{u} where
  Hom R S := { f : R →+* S // Continuous f }
  id R := ⟨RingHom.id R, continuous_id⟩
  comp f g := ⟨g.val.comp f.val, g.2.comp f.2⟩

/-- `FunLike` instance for morphisms in `CompleteTopCommRingCat`. -/
instance (R S : CompleteTopCommRingCat.{u}) :
    FunLike { f : R →+* S // Continuous f } R S where
  coe f := f.val
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

/-- `CompleteTopCommRingCat` is a concrete category. -/
instance : ConcreteCategory CompleteTopCommRingCat.{u}
    (fun R S ↦ { f : R →+* S // Continuous f }) where
  hom f := f
  ofHom f := f

/-- Forgetful functor to `TopCommRingCat`. -/
def forgetToTopCommRingCat : CompleteTopCommRingCat.{u} ⥤ TopCommRingCat.{u} where
  obj R := TopCommRingCat.of R
  map f := ⟨f.val, f.2⟩

/-- Forgetful functor to `CommRingCat`. -/
def forgetToCommRingCat : CompleteTopCommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of R
  map f := CommRingCat.ofHom f.val

/-- Forgetful functor to `TopCat`. -/
def forgetToTopCat : CompleteTopCommRingCat.{u} ⥤ TopCat.{u} where
  obj R := TopCat.of R
  map f := TopCat.ofHom ⟨⇑f.1, f.2⟩

end CompleteTopCommRingCat
