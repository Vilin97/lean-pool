/-
Copyright (c) 2026 Tanner Duve, Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import LeanPool.Computability.TuringDegree
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Hom.Basic

/-!
# Automorphism Group of the Turing Degrees

This file sets up the automorphism group of the Turing degrees as the group of order
isomorphisms of `TuringDegree`.
-/

namespace Computability

/-- The order automorphisms of a type `α`, namely the order isomorphisms `α ≃o α`. -/
abbrev OrderAut (α : Type*) [LE α] := OrderIso α α

/-- The group structure on the order automorphisms of `α`. -/
instance OrderAutGroup (α : Type) [LE α] : Group (OrderAut α) where
  mul := OrderIso.trans
  one := OrderIso.refl α
  inv := OrderIso.symm
  mul_assoc := fun a b c => OrderIso.ext rfl
  one_mul := fun a => OrderIso.ext rfl
  mul_one := fun a => OrderIso.ext rfl
  inv_mul_cancel := OrderIso.symm_trans_self

namespace TuringDegree

/-- The automorphism group of the Turing degrees. -/
def automorphismGroup : Type := OrderAut TuringDegree

instance automorphismGroup.isGroup : Group automorphismGroup :=
  OrderAutGroup TuringDegree

instance automorphismGroup.existsAut : Inhabited automorphismGroup :=
  ⟨OrderIso.refl TuringDegree⟩

end TuringDegree

end Computability
