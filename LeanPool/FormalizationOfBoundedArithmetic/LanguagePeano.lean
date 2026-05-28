/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import Mathlib.ModelTheory.Order

import LeanPool.FormalizationOfBoundedArithmetic.Register

universe u v

namespace FirstOrder
namespace Language

-- this style of definition is inspired by https://github.com/leanprover-community/mathlib4/blob/2cb771d3006e8b7579f66990fed1b433bf2e7fed/Mathlib/ModelTheory/Arithmetic/Presburger/Basic.lean
-- Definition 2.3, page 12 of draft (23 of pdf);
--   + remark in section 3.1, top of page 34 of draft (45 of pdf)
-- note: the equality relation is present by default in Mathlib.ModelTheory
-- it is explicit in Cook and Nguyen, but it doesn't seem to lead to any inconsistencies
-- note: checking if 'x = y is not always trivial; if x and y are long bit-strings,
-- encoded as lists (e.g. 3 encoded as S(S(S(Z)))), checking for their equality
-- is linear-time, thus not trivial at all. But here we only use equality in proofs
-- and the only way to assert equality is to prove it from axioms. So it seems like we'll
-- never run into the problem of having to brute-force checking for equality
/-- Function symbols for the Peano arithmetic language. -/
inductive PeanoFunc : Nat -> Type*
  | zero : PeanoFunc 0
  | one : PeanoFunc 0
  | add : PeanoFunc 2
  | mul : PeanoFunc 2
  deriving DecidableEq

/-- Relation symbols for the Peano arithmetic language. -/
inductive PeanoRel : Nat -> Type*
  | leq : PeanoRel 2
  deriving DecidableEq

/-- The first-order language of Peano arithmetic used by the formalization. -/
def peano : Language :=
{ Functions := PeanoFunc,
  Relations := PeanoRel
}

namespace peano
variable {a : Type u}

@[delta0_simps]
instance : Language.IsOrdered peano where
  leSymb := PeanoRel.leq

@[delta0_simps] instance : Zero (peano.Term a) where
  zero := Constants.term .zero

@[delta0_simps] instance : One (peano.Term a) where
  one := Constants.term .one

@[delta0_simps] instance : Add (peano.Term a) where
  add := Functions.apply₂ .add

@[delta0_simps] instance : Mul (peano.Term a) where
  mul := Functions.apply₂ .mul

-- inspired by https://github.com/leanprover-community/mathlib4/blob/cff2a6ea669abe2e384ea4c359f20ee90a5dc855/Mathlib/ModelTheory/Syntax.lean#L732
-- standard precedence of ≤, ≠, <: 50
-- standard precedence of +: 65; of *: 70
-- precedence of ⟹ in ModelTheory: 62, of =': 88
-- the higher precedence the tighter bounding
@[inherit_doc] scoped[FirstOrder.Language] infixl:89 " <=' " => Term.le
@[inherit_doc] scoped[FirstOrder.Language] infixl:89 " <' " => Term.lt

/-- The not-equal relation of two terms as a bounded formula -/
@[delta0_simps]
def _root_.FirstOrder.Term.neq
    {a : Type u} {n} {L : Language} (t1 t2 : L.Term (a ⊕ Fin n)) :
    L.BoundedFormula a n :=
  ∼(t1 =' t2)
@[inherit_doc] scoped[FirstOrder.Language] infixl:88 " ≠' " => Term.neq


instance {M} [h : Language.peano.Structure M] : Zero M :=
  ⟨h.funMap PeanoFunc.zero ![]⟩

instance {M} [h : Language.peano.Structure M] : One M :=
  ⟨h.funMap PeanoFunc.one ![]⟩

instance {M} [h : Language.peano.Structure M] : Add M :=
  ⟨fun x y => h.funMap PeanoFunc.add ![x, y]⟩

instance {M} [h : Language.peano.Structure M] : Mul M :=
  ⟨fun x y => h.funMap PeanoFunc.mul ![x, y]⟩

instance {M} [h : Language.peano.Structure M] : LE M :=
  ⟨fun x y => h.RelMap PeanoRel.leq ![x, y]⟩

@[simp]
instance {M} [h : Language.peano.Structure M] : LT M :=
  ⟨fun x y => x <= y ∧ ¬ y <= x⟩

/-- Interpret natural-number literals in a structure for the Peano language. -/
def natToM {M} [h : Language.peano.Structure M] : Nat -> M
| 0 => 0
| 1 => 1
| n + 1 => natToM n + 1

instance {M} [h : Language.peano.Structure M] (n) : OfNat M n where
  ofNat := natToM n

end FirstOrder.Language.peano
