/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Tactic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Hom.Defs
import LeanPool.Polylean.UnitConjecture.Tactics.AesopRuleSets

namespace LeanPool.Polylean

/-!
## Cocycles and Group actions by automorphisms
The definitions of cocycles and group actions by automorphisms, which are required for the
Metabelian construction.

## Overview
- `AutAction` - the definition of an action of one group on another by automorphisms.
  This is done as a typeclass representing the property of being an action by automorphisms.
- `Cocycle` - the definition of a *cocycle* associated with a certain action by
  automorphisms. This is also done as a typeclass with the function as an explicit
  argument and the action as a field of the structure.
-/

/-!
### Actions by automorphisms
-/

/-- An action of an additive group on another additive group by automorphisms.
    There is a closely related typeclass `DistribMulAction` in `Mathlib` that uses
    multiplicative notation. -/
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

omit [AddGroup A] [AutAction α] in
@[aesop norm (rule_sets := [AutAction])]
lemma apply_zero : ∀ {a : A}, α a (0 : B) = (0 : B) := by
  intro a
  exact map_zero (α a)

@[aesop norm (rule_sets := [AutAction])]
lemma zero_apply : ∀ {b : B}, α (0 : A) b = b := by
  intro b
  have h := congrArg (fun f : B →+ B => f b) (AutAction.id_action (α := α))
  simpa using h

omit [AddGroup A] [AutAction α] in
@[aesop norm (rule_sets := [AutAction])]
lemma apply_add : ∀ {a : A} {b b' : B}, α a (b + b') = α a b + α a b' := by
  intro a b b'
  exact map_add (α a) b b'

@[aesop safe (rule_sets := [AutAction])]
lemma compatibility' : ∀ {a a' : A} {b : B}, α a (α a' b) = α (a + a') b := by
  intro a a' b
  have h := congrArg (fun f : B →+ B => f b) (AutAction.compatibility (α := α) a a')
  simpa [AddMonoidHom.comp_apply] using h.symm

@[aesop norm (rule_sets := [AutAction])]
lemma act_neg_act {a : A} {b : B} : α a (α (-a) b) = b := by
  rw [compatibility']
  aesop (erase compatibility) (rule_sets := [AutAction])

omit [AddGroup A] [AutAction α] in
@[aesop safe (rule_sets := [AutAction])]
lemma apply_neg : ∀ {a : A} {b : B}, α a (-b) = -α a b := by
  intro a b
  exact map_neg (α a) b

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

instance : AutAction ccl.α := ccl.autAct

@[aesop norm (rule_sets := [Cocycle])]
lemma left_id {q : Q} : c 0 q = (0 : K) := by
  have := ccl.cocycle_condition 0 0 q
  simp only [ccl.cocycle_zero, AutAction.id_action, zero_add, add_zero,
    AddMonoidHom.id_apply] at this
  exact (add_left_cancel (a := c 0 q)
    (show c 0 q + 0 = c 0 q + c 0 q by simpa only [add_zero] using this)).symm


@[aesop norm (rule_sets := [Cocycle])]
lemma right_id {q : Q} : c q 0 = (0 : K) := by
  have := ccl.cocycle_condition q 0 0
  simp only [ccl.cocycle_zero, AutAction.apply_zero, zero_add, add_zero] at this
  exact add_left_cancel (a := c q 0)
    (show c q 0 + c q 0 = c q 0 + 0 by simpa only [add_zero] using this)

@[aesop safe (rule_sets := [Cocycle])]
lemma inv_rel (q : Q) : c q (-q) = ccl.α q (c (-q) q) := by
  have := ccl.cocycle_condition q (-q) q
  simpa [left_id, right_id] using this

@[aesop safe (rule_sets := [Cocycle])]
lemma inv_rel' (q : Q) : c (-q) q = ccl.α (-q) (c q (-q)) := by
  have := inv_rel c (-q)
  simp_all only [neg_neg]

end Cocycle

end LeanPool.Polylean
