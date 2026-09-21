/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModBiprod
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModIso

/-!
# Functoriality of the biproduct of super modules

A pair of morphisms of super modules induces one on the
biproducts, componentwise; a pair of isomorphisms induces an
isomorphism.
-/

namespace RS

open CategoryTheory

universe u u'

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u'}}

/-- **The biproduct of two morphisms of super modules.** -/
def biprodMap {M M' N N' : S.Mod} (f : M ⟶ M') (g : N ⟶ N') :
    M.biprod N ⟶ M'.biprod N' where
  evenMap := LinearMap.prodMap f.evenMap g.evenMap
  oddMap := LinearMap.prodMap f.oddMap g.oddMap
  map_actEE _ _ := Prod.ext (f.map_actEE _ _) (g.map_actEE _ _)
  map_actEO _ _ := Prod.ext (f.map_actEO _ _) (g.map_actEO _ _)
  map_actOE _ _ := Prod.ext (f.map_actOE _ _) (g.map_actOE _ _)
  map_actOO _ _ := Prod.ext (f.map_actOO _ _) (g.map_actOO _ _)

/-- The even component of an isomorphism is bijective. -/
theorem bijective_evenMap {M N : S.Mod} (e : M ≅ N) :
    Function.Bijective e.hom.evenMap := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨e.inv.evenMap, ?_, ?_⟩
  · intro m
    show (e.hom ≫ e.inv).evenMap m = m
    rw [e.hom_inv_id]
    rfl
  · intro n
    show (e.inv ≫ e.hom).evenMap n = n
    rw [e.inv_hom_id]
    rfl

/-- The odd component of an isomorphism is bijective. -/
theorem bijective_oddMap {M N : S.Mod} (e : M ≅ N) :
    Function.Bijective e.hom.oddMap := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨e.inv.oddMap, ?_, ?_⟩
  · intro m
    show (e.hom ≫ e.inv).oddMap m = m
    rw [e.hom_inv_id]
    rfl
  · intro n
    show (e.inv ≫ e.hom).oddMap n = n
    rw [e.inv_hom_id]
    rfl

end SuperCommAlgebra.Mod

end RS
