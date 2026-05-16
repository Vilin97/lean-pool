/-
Copyright (c) 2026 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Retract

/-!
# Epimorphism preservation under retracts of functors

Auxiliary lemmas on retract data: an epimorphism is stable under taking the
right leg of a retract in the arrow category, and the
`PreservesEpimorphisms` property transfers along natural transformations
and retracts of functors.
-/

open CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D] {F G : C ⥤ D}

lemma epi_of_Retract {f g : Arrow C} (π : f ⟶ g) [Epi f.hom] [Epi π.right] : Epi g.hom :=
  have : Epi (π.left ≫ g.hom) := π.w ▸ epi_comp f.hom π.right
  epi_of_epi (π.left) _

lemma preservesEpi_of_Epi (f : F ⟶ G) (hf : ∀ X, Epi (f.app X)) [F.PreservesEpimorphisms] :
    G.PreservesEpimorphisms where
  preserves {X Y} π hπ :=
    have : Epi (f.app X ≫ G.map π) := by
      rw [← f.naturality π]
      exact epi_comp (F.map π) (f.app Y)
    epi_of_epi (f.app X) (G.map π)

lemma preservesEpi_ofRetract (r : Retract G F) [F.PreservesEpimorphisms] :
    G.PreservesEpimorphisms where
  preserves := (preservesEpi_of_Epi _
    (fun _ ↦ (SplitEpi.mk (r.i.app _)
    (by rw [← NatTrans.comp_app, r.retract, NatTrans.id_app])).epi)).preserves
