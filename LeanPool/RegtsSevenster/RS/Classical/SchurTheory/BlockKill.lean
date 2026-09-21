/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.KillSimples

/-!
# Kill criteria for the block development

Vanishing of the `ofModule` action is elementwise annihilation;
intertwiners commute with the whole algebra action, so
annihilation transports along equivalences of representations.
-/

namespace RS

open Finset LinearMap

variable {G : Type*}

/-- An intertwiner commutes with the algebra action. -/
theorem intertwiner_comp_asAlgebraHom [Group G]
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : V →ₗ[ℂ] W) (hf : ∀ g : G, f ∘ₗ (ρ g : V →ₗ[ℂ] V) =
      (σ g : W →ₗ[ℂ] W) ∘ₗ f) (y : MonoidAlgebra ℂ G) :
    f ∘ₗ ρ.asAlgebraHom y = σ.asAlgebraHom y ∘ₗ f := by
  induction y using MonoidAlgebra.induction_on with
  | of g =>
    rw [show MonoidAlgebra.of ℂ G g =
      MonoidAlgebra.single g (1 : ℂ) from rfl]
    rw [show (ρ.asAlgebraHom (MonoidAlgebra.single g 1) :
        V →ₗ[ℂ] V) = (ρ g : V →ₗ[ℂ] V) from by
      rw [Representation.asAlgebraHom_single, one_smul]]
    rw [show (σ.asAlgebraHom (MonoidAlgebra.single g 1) :
        W →ₗ[ℂ] W) = (σ g : W →ₗ[ℂ] W) from by
      rw [Representation.asAlgebraHom_single, one_smul]]
    exact hf g
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp,
      ha, hb]
  | smul r a ha =>
    rw [map_smul, map_smul, LinearMap.comp_smul,
      LinearMap.smul_comp, ha]

end RS
