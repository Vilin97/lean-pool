/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import LeanPool.Polylean.UnitConjecture.Cocycle
import LeanPool.Polylean.UnitConjecture.Tactics.AesopRuleSets

/-!

## Metabelian groups

Metabelian groups are group extensions `1 → K → G → Q → 1` with both the kernel
and the quotient Abelian.
Such an extension is determined by data:

* a group action of `Q` on `K` by automorphisms
* a cocyle `c: Q → Q → K`

We define the cocycle condition and construct a group structure on a structure extending `K × Q`.
The main step is to show that the cocyle condition implies associativity.
-/

namespace LeanPool.Polylean


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
  | (k, q) => (- (ccl.α (-q) (k + c q (-q))), -q)

/-!
Some of the standard lemmas to show that `K × Q` has the structure of a group with the
above operations.
-/

@[aesop norm (rule_sets := [Metabelian])]
lemma left_id : ∀ (g : K × Q), mul c e g = g
  | (k, q) => by
    haveI : AutAction ccl.α := ccl.autAct
    simp [mul, Cocycle.left_id (c := c), AutAction.zero_apply]

@[aesop norm (rule_sets := [Metabelian])]
lemma right_id : ∀ (g : K × Q), mul c g e = g
  | (k, q) => by
    haveI : AutAction ccl.α := ccl.autAct
    simp [mul, Cocycle.right_id (c := c), AutAction.apply_zero]

@[aesop norm (rule_sets := [Metabelian])]
lemma left_inv : ∀ (g : K × Q), mul c (inv c g) g = e
  | (k , q) => by
    have := Cocycle.inv_rel' c q
    aesop (rule_sets := [Metabelian, Cocycle, AutAction])

@[aesop norm (rule_sets := [Metabelian])]
lemma right_inv : ∀ (g : K × Q), mul c g (inv c g) = e
  | (k, q) => by aesop (rule_sets := [Metabelian, Cocycle, AutAction])

@[aesop safe (rule_sets := [Metabelian])]
theorem mul_assoc : ∀ (g g' g'' : K × Q), mul c (mul c g g') g'' = mul c g (mul c g' g'')
  | (k, q), (k', q'), (k'', q'') => by
    simp only [mul, Prod.mk.injEq, map_add, AutAction.compatibility']
    constructor
    · simp only [add_assoc, add_left_cancel_iff]
      rw [add_left_comm, add_left_cancel_iff]
      exact ccl.cocycle_condition q q' q''
    · apply add_assoc

/-- A group structure on `K × Q` using the above multiplication operation. -/
@[reducible]
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

end MetabelianGroup

end LeanPool.Polylean
