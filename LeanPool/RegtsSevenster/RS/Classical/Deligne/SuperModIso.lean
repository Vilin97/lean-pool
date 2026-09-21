/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModHom

/-!
# Recognising isomorphisms of super modules

A morphism of super modules whose two components are bijective is
an isomorphism: the componentwise inverses are again ℂ-linear and
again commute with the four actions, because the actions on the
source are determined by those on the target.
-/

namespace RS

open CategoryTheory

universe u u'

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u'}}

/-- **A degreewise bijective morphism of super modules is an
isomorphism.** -/
noncomputable def isoOfComponents {M N : S.Mod} (f : M ⟶ N)
    (he : Function.Bijective f.evenMap)
    (ho : Function.Bijective f.oddMap) : M ≅ N where
  hom := f
  inv :=
    { evenMap := (LinearEquiv.ofBijective f.evenMap he).symm
      oddMap := (LinearEquiv.ofBijective f.oddMap ho).symm
      map_actEE := fun x n => by
        refine he.1 ?_
        rw [f.map_actEE]
        simp
      map_actEO := fun x n => by
        refine ho.1 ?_
        rw [f.map_actEO]
        simp
      map_actOE := fun u n => by
        refine ho.1 ?_
        rw [f.map_actOE]
        simp
      map_actOO := fun u n => by
        refine he.1 ?_
        rw [f.map_actOO]
        simp }
  hom_inv_id := by
    refine Hom.ext (LinearMap.ext fun m => ?_)
      (LinearMap.ext fun m => ?_)
    · exact (LinearEquiv.ofBijective f.evenMap he).symm_apply_apply m
    · exact (LinearEquiv.ofBijective f.oddMap ho).symm_apply_apply m
  inv_hom_id := by
    refine Hom.ext (LinearMap.ext fun n => ?_)
      (LinearMap.ext fun n => ?_)
    · exact (LinearEquiv.ofBijective f.evenMap he).apply_symm_apply n
    · exact (LinearEquiv.ofBijective f.oddMap ho).apply_symm_apply n

/-- **A degreewise bijective morphism of super modules is an
isomorphism**, as an instance-friendly statement. -/
theorem isIso_of_components {M N : S.Mod} (f : M ⟶ N)
    (he : Function.Bijective f.evenMap)
    (ho : Function.Bijective f.oddMap) : IsIso f :=
  ⟨(isoOfComponents f he ho).inv,
    (isoOfComponents f he ho).hom_inv_id,
    (isoOfComponents f he ho).inv_hom_id⟩

end SuperCommAlgebra.Mod

end RS
