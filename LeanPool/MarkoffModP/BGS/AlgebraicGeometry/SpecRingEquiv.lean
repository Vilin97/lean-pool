/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Concrete `Spec` isomorphisms from ring equivalences

The concrete constructor `AlgebraicGeometry.Spec` and the functor `Scheme.Spec` have propositionally
equivalent objects, but mixing them introduces equality transports in later compositions.  This
module keeps affine scheme isomorphisms in the concrete `Spec` presentation used by the project.
-/

namespace BGS

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A ring equivalence induces the contravariant isomorphism of its concrete affine spectra. -/
def specIsoOfRingEquiv (e : R ≃+* S) :
    Spec (CommRingCat.of S) ≅ Spec (CommRingCat.of R) where
  hom := Spec.map (CommRingCat.ofHom e.toRingHom)
  inv := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp

/-- Transport an equality between a two-step and a three-step ring map to the corresponding
contravariant equality of concrete affine-spectrum morphisms. -/
theorem specMap_two_eq_three_of_comp_eq
    {A B C B' C' : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing B'] [CommRing C']
    (f : A →+* B) (g : B →+* C)
    (f' : A →+* B') (g' : B' →+* C') (h' : C' →+* C)
    (h : g.comp f = h'.comp (g'.comp f')) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h') ≫ Spec.map (CommRingCat.ofHom g') ≫
        Spec.map (CommRingCat.ofHom f') := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  rw [h]

/-- Contravariant `Spec` transports an equality between two two-step ring maps. -/
theorem specMap_two_eq_two_of_comp_eq
    {A B C B' : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing B']
    (f : A →+* B) (g : B →+* C) (f' : A →+* B') (g' : B' →+* C)
    (h : g.comp f = g'.comp f') :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom f') := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rw [h]

end

end BGS
