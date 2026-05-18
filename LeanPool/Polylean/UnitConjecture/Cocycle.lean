/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Algebra.Group.Action.Basic
import LeanPool.Polylean.UnitConjecture.Tactics.AesopRuleSets

namespace LeanPool.Polylean

/-!
## Cocycles and Group actions by automorphisms
The definitions of cocycles and group actions by automorphisms, which are required for the Metabelian construction.

## Overview
- `AutAction` - the definition of an action of one group on another by automorphisms.
  This is done as a typeclass representing the property of being an action by automorphisms.
- `Cocycle` - the definition of a *cocycle* associated with a certain action by automorphisms.
  This is also done as a typeclass with the function as an explicit argument and the action as a field of the structure.
-/

/-!
### Actions by automorphisms
-/

/-- An action of an additive group on another additive group by automorphisms.
    There is a closely related typeclass `DistribMulAction` in `Mathlib` that uses multiplicative notation. -/
class AutAction {A B : Type _} [AddGroup A] [AddGroup B] (α : A → (B →+ B)) where
  /-- The automorphism corresponding to the zero element is the identity. -/
  id_action : α 0 = .id _
  /-- The compatibility of group addition with the action by automorphisms. -/
  compatibility : ∀ a a' : A, α (a + a') = (α a).comp (α a')


namespace AutAction

attribute [aesop norm (rule_sets := [AutAction])] id_action compatibility

variable {A B : Type _} [AddGroup A] [AddGroup B] (α : A → (B →+ B)) [AutAction α]

/-!
Some easy consequences of the definition of an action by automorphisms.
-/

@[aesop norm (rule_sets := [AutAction])]
lemma action_zero : ∀ {a : A}, α a (0 : B) = (0 : B) := by
  intro a
  exact (α a).map_zero

@[aesop norm (rule_sets := [AutAction])]
lemma action_dist : ∀ {a : A} {b b' : B}, α a (b + b') = α a b + α a b' := by
  intro a b b'
  exact (α a).map_add b b'

@[aesop norm (rule_sets := [AutAction])]
lemma compatibility' : ∀ {a a' : A} {b : B}, α a (α a' b) = α (a + a') b := by aesop (rule_sets := [AutAction])

@[aesop norm (rule_sets := [AutAction])]
lemma act_neg_act {a : A} {b : B} : α a (α (-a) b) = b := by
  rw [compatibility']
  aesop (erase compatibility) (rule_sets := [AutAction])

@[aesop norm (rule_sets := [AutAction])]
lemma action_neg : ∀ {a : A} {b : B}, α a (-b) = -α a b := by
  intro a b
  exact (α a).map_neg b

end AutAction


/-!
### Cocycles
-/

/--
A cocycle associated with a certain action of `Q` on `K` via automorphisms is a
function from `Q × Q` to `K` satisfying a certain requirement known as the "cocycle condition". -/
class Cocycle {Q K : Type _} [AddGroup Q] [AddGroup K] (c : Q → Q → K) where
  /-- An action of the quotient on the kernel by automorphisms. -/
  α : Q → (K →+ K)
  /-- A typeclass instance for the action by automorphisms. -/
  autAct : AutAction α
  /-- The value of the cocycle is zero when its inputs are zero, as a convention. -/
  cocycle_zero : c 0 0 = (0 : K)
  /-- The *cocycle condition*. -/
  cocycle_condition :
    ∀ q q' q'' : Q, c q q' + c (q + q') q'' = α q (c q' q'') + c q (q' + q'')


namespace Cocycle

/-!
A few deductions from the cocycle condition.
-/

variable {Q K : Type _} [AddGroup Q] [AddGroup K]
variable (c : Q → Q → K) [ccl : Cocycle c]

attribute [aesop norm (rule_sets := [Cocycle])] Cocycle.cocycle_zero
attribute [aesop norm (rule_sets := [Cocycle])] Cocycle.cocycle_condition

@[aesop norm (rule_sets := [Cocycle])]
lemma left_id {q : Q} : c 0 q = (0 : K) := by
  letI : AutAction ccl.α := ccl.autAct
  have := ccl.cocycle_condition 0 0 q
  rw [add_zero, zero_add, ccl.cocycle_zero, zero_add] at this
  simp [AutAction.id_action] at this
  exact this


@[aesop norm (rule_sets := [Cocycle])]
lemma right_id {q : Q} : c q 0 = (0 : K) := by
  letI : AutAction ccl.α := ccl.autAct
  have := ccl.cocycle_condition q 0 0
  rw [add_zero, zero_add, ccl.cocycle_zero] at this
  simp at this
  simpa using this

@[aesop norm (rule_sets := [Cocycle])]
lemma inv_rel (q : Q) : c q (-q) = ccl.α q (c (-q) q) := by
  letI : AutAction ccl.α := ccl.autAct
  have := ccl.cocycle_condition q (-q) q
  simp_all [left_id, add_zero, neg_add_cancel, right_id]

@[aesop norm (rule_sets := [Cocycle])]
lemma inv_rel' (q : Q) : c (-q) q = ccl.α (-q) (c q (-q)) := by
  have := inv_rel c (-q)
  simp_all only [neg_neg]

end Cocycle

end LeanPool.Polylean
