/-
Copyright (c) 2026 Tanner Duve, Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import LeanPool.Computability.TuringDegree
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Hom.Basic

/-
Define the automorphism group of the Turing degrees.
-/

abbrev OrderAut (α : Type*) [LE α] := OrderIso α α

instance OrderAutGroup (α : Type) [LE α] : Group (OrderAut α) where
  mul := OrderIso.trans
  one := OrderIso.refl α
  inv := OrderIso.symm
  mul_assoc := fun a b c => OrderIso.ext rfl
  one_mul := fun a => OrderIso.ext rfl
  mul_one := fun a => OrderIso.ext rfl
  inv_mul_cancel := OrderIso.symm_trans_self

def TuringDegree.automorphismGroup : Type := OrderAut TuringDegree

instance TuringDegree.automorphismGroup.isGroup : Group (TuringDegree.automorphismGroup) :=
  OrderAutGroup TuringDegree

instance TuringDegree.automorphismGroup.existsAut : Inhabited (TuringDegree.automorphismGroup) :=
  ⟨OrderIso.refl TuringDegree⟩
