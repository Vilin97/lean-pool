/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.General

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Player

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame

/-- a player in a Gale-Stewart game -/
inductive Player
  | zero
  | one

section «Section1»
open Lean Meta Elab Tactic Term Qq
/-- Tactic support used by the Borel determinacy formalization. -/
elab "casesPlayer" : tactic => withMainContext do
  for hyp in ← getLCtx do
    if ← isDefEq (← instantiateMVars hyp.type) q(Player) then
      let syn ← exprToSyntax hyp.toExpr
      evalTactic (← `(tactic | cases $syn:term))
      return
  throwError "no variable of type player"
/-- Tactic support used by the Borel determinacy formalization. -/
macro "casesPlayers" : tactic => `(tactic | focus repeat all_goals casesPlayer)
attribute [simp_isPosition]
  iff_true iff_false true_iff false_iff
  and_true true_and and_false false_and
  or_true true_or or_false false_or
  ite_eq_iff eq_ite_iff ite_prop_iff_or
  --apply_ite
  --maybe reduce priority to stop (apply_ite (Eq _))
attribute [simp_isPosition] reduceCtorEq
/-- Tactic support used by the Borel determinacy formalization. -/
macro "synthIsPosition" : tactic =>
  `(tactic | first | done |
  (casesPlayers <;> (try apply_fun List.length at *) <;>
    simpAtStar (config := {failIfUnchanged := false}) only [simp_isPosition, simp_lengths] <;>
    /-(try split_ifs at * <;>
      --split_ifs at * fails in win_asap due to order issue
      --(manually reordering goals fixes the issue)
      simpAtStar (config := {failIfUnchanged := false}) only [simp_isPosition]) <;>-/
    omega))
end «Section1»

variable {A : Type*} (x : List A) (p q : Player)
namespace Player
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def toNat : Player → ℕ
  | zero => 0
  | one => 1
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp_isPosition] lemma apply_ite_toNat (P : Prop) [Decidable P] (a b : Player) :
    toNat (if P then a else b) = if P then toNat a else toNat b := by
  simpa using (apply_ite toNat P a b)
@[simp, simp_isPosition] lemma zero_toNat : zero.toNat = 0 := rfl
@[simp, simp_isPosition] lemma one_toNat : one.toNat = 1 := rfl
@[ext] lemma ext (h : p.toNat = q.toNat) : p = q := by synthIsPosition

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def swap : Player → Player
  | zero => one
  | one => zero
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp_isPosition] lemma apply_ite_swap (P : Prop) [Decidable P] (a b : Player) :
    swap (if P then a else b) = if P then swap a else swap b := by
  simpa using (apply_ite swap P a b)
@[simp, simp_isPosition] lemma swap_zero : zero.swap = one := rfl
@[simp, simp_isPosition] lemma swap_one : one.swap = zero := rfl

/-- if `p` moves in position `[]`, then `p.residual x` moves in position `x` -/
@[simp_isPosition] def residual := if x.length % 2 = 0 then p else p.swap
end Player

/-- is player `p` to move in position `x`? -/
@[simp_isPosition] def IsPosition (x : List A) (p : Player) : Prop := x.length % 2 = p.toNat



namespace Player
@[simp] lemma residual_swap :
  (p.residual x).swap = p.swap.residual x := by synthIsPosition
@[simp] lemma residual_residual {x y : List A} :
  (p.residual x).residual y = p.residual (x ++ y) := by synthIsPosition
@[simp] lemma residual_even (h : x.length % 2 = 0) :
  p.residual x = p := by synthIsPosition
@[simp] lemma residual_odd (h : x.length % 2 = 1) :
  p.residual x = p.swap := by synthIsPosition
@[simp] lemma residual_append_both {y} : (p.residual (x ++ (y ++ x))) = p.residual y := by
  synthIsPosition
@[simp] lemma residual_cons {a} : (p.residual (a :: x)) = (p.residual x).swap := by
  synthIsPosition
@[simp] lemma residual_append_cons {a} {y} :
  (p.residual (x ++ a :: y)) = (p.residual (x ++ y)).swap := by synthIsPosition
lemma residual_concat {a} : (p.residual (x ++ [a])) = (p.residual x).swap := by
  synthIsPosition
lemma residual_concat2 {a b} : (p.residual (x ++ [a, b])) = p.residual x := by
  synthIsPosition
end Player
/-this should probably be removed
namespace Player
@[simp] lemma zero_toNat_iff : p.toNat = 0 ↔ p = zero := by synthIsPosition
@[simp] lemma zero_toNat_iff' : 0 = p.toNat ↔ p = zero := by synthIsPosition
@[simp] lemma one_toNat_iff : p.toNat = 1 ↔ p = one := by synthIsPosition
@[simp] lemma one_toNat_iff' : 1 = p.toNat ↔ p = one := by synthIsPosition

@[simp] lemma equal_swap_ne : p ≠ q ↔ p = q.swap := by
  cases p <;> cases q <;> tauto
@[simp] lemma swap_rhs : p.swap = q ↔ p = q.swap := by
  cases p <;> cases q <;> tauto
@[simp] lemma swap_swap : p.swap.swap = p := by cases p <;> rfl
@[simp] lemma swap_toNat : p.swap.toNat = 1 - p.toNat := by synthIsPosition

@[simp] lemma residual_even (h : x.length % 2 = 0) :
  p.residual x = p := by synthIsPosition
@[simp] lemma residual_odd (h : x.length % 2 = 1) :
  p.residual x = p.swap := by synthIsPosition
@[simp] lemma residual_residual {x y : List A} :
  (p.residual x).residual y = p.residual (x ++ y) := by synthIsPosition
@[simp] lemma residual_toNat : (p.residual x).toNat = (p.toNat + x.length) % 2 := by
  synthIsPosition
@[simp] lemma residual_swap :
  (p.residual x).swap = p.swap.residual x := by synthIsPosition
@[simp] lemma residual_cons {a} : (p.residual (a :: x)) = (p.residual x).swap := by
  synthIsPosition
@[simp] lemma residual_concat {a} : (p.residual (x ++ [a])) = (p.residual x).swap := by
  synthIsPosition
@[simp] lemma residual_concat2 {a b} : (p.residual (x ++ [a, b])) = p.residual x := by
  synthIsPosition
@[simp] lemma residual_append_both {y} : (p.residual (x ++ (y ++ x))) = p.residual y := by
  synthIsPosition
end Player
namespace IsPosition
lemma append_left {x y : List A} :
  IsPosition (x ++ y) p ↔ (x.length % 2 = 0 ↔ IsPosition y p) := by synthIsPosition
lemma append_right {x y : List A} :
  IsPosition (x ++ y) p ↔ (y.length % 2 = 0 ↔ IsPosition x p) := by synthIsPosition
@[simp] lemma append_both {x y : List A} :
  IsPosition (x ++ (y ++ x)) p ↔ IsPosition y p := by synthIsPosition
@[simp] lemma even {p : Player} {x : List A} (h : x.length % 2 = 0) :
  IsPosition x p ↔ p = Player.zero := by synthIsPosition
@[simp] lemma odd {p : Player} {x : List A} (h : x.length % 2 = 1) :
  IsPosition x p ↔ p = Player.one := by synthIsPosition
@[simp] lemma not {x : List A} {p : Player} :
  ¬ IsPosition x p ↔ IsPosition x p.swap := by synthIsPosition
@[simp] lemma change {x : List A} {a : A} {p : Player} :
  IsPosition (x ++ [a]) p ↔ IsPosition x p.swap := by synthIsPosition
@[simp] lemma change2 {x : List A} {a b : A} {p : Player} :
  IsPosition (x ++ [a, b]) p ↔ IsPosition x p := by synthIsPosition
@[simp] lemma cons {x : List A} {a : A} {p : Player} :
  IsPosition (a :: x) p ↔ IsPosition x p.swap := by synthIsPosition
@[simp] lemma residual {x y : List A}  {p : Player} :
  IsPosition y (p.residual x) ↔ IsPosition (x ++ y) p := by synthIsPosition
end IsPosition-/

end GaleStewartGame
