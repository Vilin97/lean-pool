/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SchurAction

/-!
# Identifying the Schur scalar by its trace

The scalar through which a class-function element acts on an
irreducible representation is determined by the character pairing:
`z · dim V = ∑ g, c g · χ_ρ(g)`.
-/

namespace RS

open Finset LinearMap

variable {G V : Type*}

/-- The trace of the action of a class element is the character
pairing. -/
theorem trace_asAlgebraHom_classElem
    [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (c : G → ℂ) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classElem c)) =
      ∑ g : G, c g * ρ.character g := by
  rw [classElem, map_sum]
  rw [show (LinearMap.trace ℂ V)
      (∑ g : G, ρ.asAlgebraHom (c g • MonoidAlgebra.single g 1)) =
    ∑ g : G, LinearMap.trace ℂ V
      (ρ.asAlgebraHom (c g • MonoidAlgebra.single g 1)) from
    map_sum _ _ _]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, map_smul, smul_eq_mul]
  congr 1
  rw [show (ρ.asAlgebraHom (MonoidAlgebra.single g 1) :
      V →ₗ[ℂ] V) = (ρ g : V →ₗ[ℂ] V) from by
    rw [Representation.asAlgebraHom_single, one_smul]]
  rfl

/-- **The identified scalar action**: a class-function element
acts on an irreducible representation as the character-pairing
scalar divided by the dimension. -/
theorem classElem_scalar_eq
    [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V}
    (hirr : IsIrredRep ρ) (c : G → ℂ)
    (hc : ∀ g h : G, c (h * g * h⁻¹) = c g) :
    ρ.asAlgebraHom (classElem c) =
      ((∑ g : G, c g * ρ.character g) /
        (Module.finrank ℂ V : ℂ)) • LinearMap.id := by
  classical
  obtain ⟨z, hz⟩ := asAlgebraHom_classElem_scalar hirr c hc
  have htr := trace_asAlgebraHom_classElem ρ c
  rw [hz] at htr ⊢
  rw [map_smul, trace_id, smul_eq_mul] at htr
  have : Nontrivial V := hirr.1
  have hdim : (Module.finrank ℂ V : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  congr 1
  rw [eq_div_iff hdim]
  linear_combination htr

end RS
