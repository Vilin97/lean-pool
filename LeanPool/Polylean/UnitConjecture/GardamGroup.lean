/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Tactic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import LeanPool.Polylean.UnitConjecture.MetabelianGroup
import LeanPool.Polylean.UnitConjecture.AddFreeGroup

namespace LeanPool.Polylean

/-!
## The construction of the group `P`

We construct the group `P` (the *Promislow* or *Hantzsche–Wendt* group) as a Metabelian group.

This is done via the cocycle construction, using the explicit action and cocycle described in
Section 3.1 of Giles Gardam's paper (https: //arxiv.org/abs/2102.11818).
-/

/-!
### The components of the group `P`
The group `P` is constructed as a Metabelian group with kernel `K := ℤ³` and
quotient `Q := ℤ/2 × ℤ/2`.
-/

/-! The *kernel* group -/

/-- The *kernel* group - `ℤ³`, the free Abelian group on three generators. -/
@[aesop safe (rule_sets := [P])]
abbrev K := ℤ × ℤ × ℤ

instance KGrp : AddCommGroup K := inferInstance

/-- Equality of endomorphisms of `K` is decidable, as `K` is a free group with
basis `Unit ⊕ Unit ⊕ Unit`. -/
instance : DecidableEq (K →+ K) := decideHomsEqual (X := Unit ⊕ Unit ⊕ Unit)


/-! The *quotient* group -/

/-- The *quotient* group - `ℤ/2 × ℤ/2`, the Klein Four group. -/
abbrev Q := Fin 2 × Fin 2

instance QGrp : AddCommGroup Q := inferInstance

/-!
### The group elements
-/

namespace K

/-! The generators of the free Abelian group `K`. -/

/-- The first generator of `K`. -/
@[aesop norm unfold (rule_sets := [P])]
abbrev x : K := (1, 0, 0)
/-- The second generator of `K`. -/
@[aesop norm unfold (rule_sets := [P])]
abbrev y : K := (0, 1, 0)
/-- The third generator of `K`. -/
@[aesop norm unfold (rule_sets := [P])]
abbrev z : K := (0, 0, 1)

end K


namespace Q

/-! The elements of the Klein Four group `Q`. -/

/-- The identity element of `Q`. -/
@[match_pattern]
def e : Q := (⟨0, by decide⟩, ⟨0, by decide⟩)
/-- The first generator of `Q`. -/
@[match_pattern]
def a : Q := (⟨1, by decide⟩, ⟨0, by decide⟩)
/-- The second generator of `Q`. -/
@[match_pattern]
def b : Q := (⟨0, by decide⟩, ⟨1, by decide⟩)
/-- The product of the first two generators of `Q`. -/
@[match_pattern]
def c : Q := (⟨1, by decide⟩, ⟨1, by decide⟩)

end Q


/-!
### The action of `Q` on `K` by automorphisms
The action of the group `Q` on the kernel `K` by automorphisms required for constructing `P`.
-/

/-- An abbreviation for the negation homomorphism on commutative groups. -/
@[aesop norm unfold (rule_sets := [P])]
abbrev neg (α : Type _) [SubtractionCommMonoid α] := negAddMonoidHom (α := α)

attribute [aesop norm unfold (rule_sets := [P])] negAddMonoidHom

/-- A temporary notation for easily describing products of additive monoid homomorphisms. -/
local infixr: 100 " × " => AddMonoidHom.prodMap

/-- The action of `Q` on `K` by automorphisms.
The action can be given a component-wise description in terms of `id` and `neg`, the
identity and negation homomorphisms. -/
@[aesop norm unfold (rule_sets := [P]), reducible]
def action : Q → (K →+ K)
  | .e => .id ℤ × .id ℤ × .id ℤ
  | .a => .id ℤ × neg ℤ × neg ℤ
  | .b => neg ℤ × .id ℤ × neg ℤ
  | .c => neg ℤ × neg ℤ × .id ℤ

/-- A verification that the above action is indeed an action by automorphisms.
  This is done automatically with the machinery of decidable equality of homomorphisms
  on free groups. -/
instance : AutAction action :=
  { id_action := rfl
    compatibility := by decide }

/-! ### The cocycle -/

open K Q in
/-- The cocycle in the construction of `P`. -/
@[aesop norm unfold (rule_sets := [P]), reducible]
def cocycle : Q → Q → K
  | a , a => x
  | a , c => x
  | b , b => y
  | c , b => -y
  | c , c => z
  | b , c => -x + -z
  | c , a => -y + z
  | b , a => -x + y + -z
  | _ , _ => 0

/-- A verification that the `cocycle` function indeed satisfies the cocycle condition.
  This check is performed fully automatically using previously defined decision procedures. -/
instance P_cocycle : Cocycle cocycle :=
  { α := action
    autAct := inferInstance
    cocycle_zero := rfl
    cocycle_condition := by decide }

/-!
### The construction of `P`
The construction of the group `P` as a Metabelian group from the given action and cocycle.
-/

/-- the group `P` constructed via the cocycle construction -/
@[aesop norm unfold (rule_sets := [P])]
def P := K × Q

namespace P

instance (priority := high) PGrp : Group P := MetabelianGroup.metabelianGroup cocycle

/-- Multiplication for `P` coming from its metabelian group structure. -/
scoped instance (priority := high) : HMul (K × Q) (K × Q) (K × Q) := ⟨PGrp.mul⟩
/-- Multiplication for `P` coming from its metabelian group structure. -/
scoped instance (priority := high) : Mul (K × Q) := ⟨PGrp.mul⟩
@[reducible]
instance instPow : Pow (K × Q) ℕ :=
  ⟨fun p n => PGrp.toMonoid.npow n p⟩


instance : DecidableEq P := inferInstanceAs <| DecidableEq (K × Q)

/-- A confirmation that multiplication in `P` is as expected from the Metabelian
group structure. -/
@[aesop norm (rule_sets := [P]), simp]
theorem mul (k k' : K) (q q' : Q) :
    (k, q) * (k', q') = (k + action q k' + cocycle q q', q + q') := rfl

@[aesop norm (rule_sets := [P])]
theorem one : (1 : P) = ((0, 0, 0), Q.e) := rfl

/-- Powers of kernel elements remain in the kernel. -/
theorem kernel_pow (k : K) (n : ℕ) : ((k, Q.e) : P) ^ n = (n • k, Q.e) := by
  induction n with
  | zero =>
      unfold HPow.hPow instHPow Pow.pow instPow
      simp
      rfl
  | succ n ih =>
      unfold HPow.hPow instHPow Pow.pow instPow
      change PGrp.toMonoid.npow (n + 1) ((k, Q.e) : P) = ((n + 1) • k, Q.e)
      rw [PGrp.toMonoid.npow_succ]
      change ((k, Q.e) : P) ^ n * (k, Q.e) = ((n + 1) • k, Q.e)
      rw [ih]
      rw [P.mul]
      simp only [nsmul_eq_mul, AddMonoidHom.coe_prodMap, AddMonoidHom.coe_id,
        Prod.map_id, id_eq, add_zero, Nat.cast_add, Nat.cast_one, Prod.mk.injEq,
        add_eq_left]
      constructor
      · ext <;> ring_nf
      · rfl

end P

end LeanPool.Polylean
