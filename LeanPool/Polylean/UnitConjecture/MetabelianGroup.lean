/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.GroupTheory.Congruence.Basic
import LeanPool.Polylean.UnitConjecture.Cocycle
import LeanPool.Polylean.UnitConjecture.Tactics.AesopRuleSets

namespace LeanPool.Polylean

/-!

## Metabelian groups

Metabelian groups are group extensions `1 → K → G → Q → 1` with both the kernel and the quotient Abelian.
Such an extension is determined by data:

* a group action of `Q` on `K` by automorphisms
* a cocyle `c: Q → Q → K`

We define the cocycle condition and construct a group structure on a structure extending `K × Q`.
The main step is to show that the cocyle condition implies associativity.
-/

namespace MetabelianGroup

variable {Q K : Type _} [AddGroup Q] [AddCommGroup K]
variable (c : Q → Q → K) [ccl : Cocycle c]

/-- The multiplication operation defined using the cocycle.
The cocycle condition is crucially used in showing associativity and other properties. -/
@[reducible, aesop norm unfold (rule_sets := [Metabelian])]
def mul : (K × Q) → (K × Q) → (K × Q)
  | (k, q), (k', q') => (k + ccl.α q k' + c q q', q + q')

/-- The identity element of the Metabelian group,
  which is the ordered pair of the identities of the individual groups. -/
@[reducible, aesop norm unfold (rule_sets := [Metabelian])]
def e : K × Q := (0, 0)

/-- The inverse operation of the Metabelian group. -/
@[reducible, aesop norm unfold (rule_sets := [Metabelian])]
def inv : K × Q → K × Q
  | (k, q) => (- (ccl.α (-q) (k  + c q (-q))), -q)

/-!
Some of the standard lemmas to show that `K × Q` has the structure of a group with the above operations.
-/

@[aesop norm (rule_sets := [Metabelian])]
lemma left_id : ∀ (g : K × Q), mul c e g = g
  | (k, q) => by
    letI : AutAction ccl.α := ccl.autAct
    simp [mul, AutAction.id_action, Cocycle.left_id]

@[aesop norm (rule_sets := [Metabelian])]
lemma right_id : ∀ (g : K × Q), mul c g e = g
  | (k, q) => by
    letI : AutAction ccl.α := ccl.autAct
    simp [mul, Cocycle.right_id]

@[aesop norm (rule_sets := [Metabelian])]
lemma left_inv : ∀ (g : K × Q), mul c (inv c g) g = e
  | (k , q) => by
    letI : AutAction ccl.α := ccl.autAct
    simp [mul, e, Cocycle.inv_rel', AutAction.action_dist]

@[aesop norm (rule_sets := [Metabelian])]
lemma right_inv : ∀ (g : K × Q), mul c g (inv c g) = e
  | (k, q) => by
    letI : AutAction ccl.α := ccl.autAct
    simp [mul, e, Cocycle.inv_rel, AutAction.action_dist, AutAction.act_neg_act]

@[aesop norm (rule_sets := [Metabelian])]
theorem mul_assoc : ∀ (g g' g'' : K × Q), mul c (mul c g g') g'' =  mul c g (mul c g' g'')
  | (k, q), (k', q'), (k'', q'') => by
    letI : AutAction ccl.α := ccl.autAct
    simp [mul, AutAction.action_dist, AutAction.compatibility', add_assoc]
    rw [show c q q' + (ccl.α (q + q') k'' + c (q + q') q'') =
        ccl.α (q + q') k'' + (c q q' + c (q + q') q'') by ac_rfl]
    rw [ccl.cocycle_condition q q' q'']
/-- A group structure on `K × Q` using the above multiplication operation. -/
def metabelianGroup : Group (K × Q) :=
  {
    mul := mul c,
    one := e,
    inv := inv c,

    mul_one := right_id c,
    one_mul := left_id c,
    mul_assoc := mul_assoc c,

    inv_mul_cancel := left_inv c,
    div_eq_mul_inv := by intros; rfl
  }

@[aesop norm simp (rule_sets := [Metabelian])]
theorem mul_def {k k' : K} {q q' : Q} :
    mul c (k, q) (k', q') = (k + ccl.α q k' + c q q', q + q') := rfl

end MetabelianGroup

end LeanPool.Polylean
