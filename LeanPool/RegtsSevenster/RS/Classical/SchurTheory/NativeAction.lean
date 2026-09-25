/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.BlockKill
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.EndSum

/-!
# The native simple-submodule representation

The representation of a simple submodule of the regular module,
carried on the canonically-instanced restricted-scalars subtype
via `Representation.ofModule'`: the algebra action is
definitionally scalar multiplication, so no transparency options
and no equivalence transport are needed.
-/

namespace RS

open Finset LinearMap

variable {G : Type*}

/-- The canonically-instanced carrier. -/
abbrev subCarrier
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    Type _ :=
  ↥(S.restrictScalars ℂ)

/-- The submodule carries the group-algebra action, definitionally
by scalar multiplication. -/
noncomputable instance
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    Module (MonoidAlgebra ℂ G)
    (subCarrier S) :=
  inferInstanceAs (Module (MonoidAlgebra ℂ G) ↥S)

/-- The complex and group-algebra actions agree on scalars. -/
instance [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    IsScalarTower ℂ (MonoidAlgebra ℂ G) (subCarrier S) where
  smul_assoc z y m := by
    apply Subtype.ext
    change ((z • y) • (m : MonoidAlgebra ℂ G)) =
      z • (y • (m : MonoidAlgebra ℂ G))
    rw [smul_assoc]

/-- The native representation of a submodule of the regular
module. -/
noncomputable def rhoS
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    Representation ℂ G (subCarrier S) :=
  Representation.ofModule' (k := ℂ) (G := G) (subCarrier S)

/-- The algebra action of the native representation is scalar
multiplication. -/
theorem rhoS_asAlgebraHom_apply
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (y : MonoidAlgebra ℂ G)
    (m : subCarrier S) :
    (rhoS S).asAlgebraHom y m = y • m := by
  rw [rhoS, Representation.asAlgebraHom_def,
    Representation.ofModule']
  rw [Equiv.apply_symm_apply]
  rfl

/-- Its group action is scalar multiplication by the group
element. -/
theorem rhoS_apply
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (g : G) (m : subCarrier S) :
    rhoS S g m = (MonoidAlgebra.single g (1 : ℂ)) • m := by
  have h := rhoS_asAlgebraHom_apply S
    (MonoidAlgebra.single g 1) m
  rw [show ((rhoS S).asAlgebraHom (MonoidAlgebra.single g 1)) m =
    rhoS S g m from by
    rw [Representation.asAlgebraHom_single, one_smul]] at h
  exact h

/-- The native representation of a simple submodule satisfies the
invariant-submodule irreducibility. -/
theorem isIrredRep_rhoS
    [Group G] (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S) :
    IsIrredRep (rhoS S) := by
  constructor
  · -- Nontrivial
    have := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) S
    exact inferInstanceAs (Nontrivial ↥S)
  · intro p hp
    -- The invariant ℂ-subspace is a `ℂ[G]`-submodule.
    have hclosed : ∀ (y : MonoidAlgebra ℂ G) (m : subCarrier S),
        m ∈ p → y • m ∈ p := by
      intro y
      induction y using MonoidAlgebra.induction_on with
      | of g =>
        intro m hm
        have := hp g m hm
        rw [rhoS_apply] at this
        rw [show MonoidAlgebra.of ℂ G g =
          MonoidAlgebra.single g (1 : ℂ) from rfl]
        exact this
      | add a b ha hb =>
        intro m hm
        rw [add_smul]
        exact p.add_mem (ha m hm) (hb m hm)
      | smul r a ha =>
        intro m hm
        rw [smul_assoc]
        exact p.smul_mem r (ha m hm)
    -- Transfer to the simple lattice.
    set q : Submodule (MonoidAlgebra ℂ G) ↥S :=
      { carrier := (p : Set (subCarrier S))
        add_mem' := fun ha hb => p.add_mem ha hb
        zero_mem' := p.zero_mem
        smul_mem' := fun y {m} hm => hclosed y m hm } with hq
    rcases hS.eq_bot_or_eq_top q with hb | ht
    · left
      apply (Submodule.eq_bot_iff _).mpr
      intro m hm
      have : m ∈ q := hm
      rw [hb] at this
      exact this
    · right
      apply Submodule.eq_top_iff'.mpr
      intro m
      have : m ∈ q := by rw [ht]; trivial
      exact this

end RS
