/-
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic.DeriveFintype
public import Mathlib.Algebra.Group.Defs

/-!
Misere combinatorial games.
-/

namespace MisereGames

public section

/-- Either the Left or Right player. -/
@[aesop safe cases]
inductive Player where
  /-- The Left player. -/
  | left  : Player
  /-- The Right player. -/
  | right : Player
deriving DecidableEq, Fintype, Inhabited

namespace Player

/-- Specify a function `Player → α` from its two outputs. -/
@[simp]
abbrev cases {α : Sort*} (l r : α) : Player → α
  | .left => l
  | .right => r

lemma apply_cases {α β : Sort*} (f : α → β) (l r : α) (p : Player) :
    f (cases l r p) = cases (f l) (f r) p := by
  cases p <;> rfl

@[simp]
theorem cases_inj {α : Sort*} {l₁ r₁ l₂ r₂ : α} :
    cases l₁ r₁ = cases l₂ r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ :=
  ⟨fun h ↦ ⟨congr($h left), congr($h right)⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩

theorem const_of_left_eq_right {α : Sort*} {f : Player → α} (hf : f left = f right) :
    ∀ p q, f p = f q
  | left, left | right, right => rfl
  | left, right => hf
  | right, left => hf.symm

theorem const_of_left_eq_right' {f : Player → Prop} (hf : f left ↔ f right) (p q) : f p ↔ f q :=
  (const_of_left_eq_right hf.eq ..).to_iff

@[simp low]
protected lemma «forall» {p : Player → Prop} :
    (∀ x, p x) ↔ p left ∧ p right :=
  ⟨fun h ↦ ⟨h left, h right⟩, fun ⟨hl, hr⟩ ↦ fun | left => hl | right => hr⟩

@[simp low]
protected lemma «exists» {p : Player → Prop} :
    (∃ x, p x) ↔ p left ∨ p right :=
  ⟨fun | ⟨left, h⟩ => .inl h | ⟨right, h⟩ => .inr h, fun | .inl h | .inr h => ⟨_, h⟩⟩

instance : Neg Player where
  neg := cases right left

@[simp] lemma neg_left : -left = right := rfl
@[simp] lemma neg_right : -right = left := rfl

instance : InvolutiveNeg Player where
  neg_neg := by decide

@[simp]
theorem ne_iff_eq_neg {a b : Player} : (a ≠ b ↔ a = -b) := by
  cases a <;> cases b <;> simp

protected theorem absurd {p q : Player} (h1 : p = q) (h2 : p = -q) : False := by
  subst h1
  cases p <;> simp at h2

instance : LE Player where
  le lhs rhs := (lhs = .right) ∨ (lhs = .left ∧ rhs = .left)

instance : DecidableLE Player := by
  simp only [DecidableLE, DecidableRel, LE.le]
  infer_instance

theorem le_right_eq (p : Player) (h1 : p ≤ .right) : p = .right := by
  simp only [LE.le, reduceCtorEq, and_false, or_false] at h1
  exact h1

@[simp]
theorem le_right_iff (p : Player) : p ≤ .right ↔ p = .right :=
  ⟨le_right_eq p, by
    intro h
    subst p
    exact Or.inl rfl⟩

theorem le_left_eq (p : Player) (h1 : .left ≤ p) : p = .left := by
  simp only [LE.le, reduceCtorEq, true_and, false_or] at h1
  exact h1

@[simp]
theorem left_le_iff (p : Player) : .left ≤ p ↔ p = .left :=
  ⟨le_left_eq p, by
    intro h
    subst p
    exact Or.inr ⟨rfl, rfl⟩⟩

@[simp]
theorem right_le (p : Player) : .right ≤ p := by
  simp only [LE.le, reduceCtorEq, or_false, false_and]

@[simp]
theorem le_left (p : Player) : p ≤ .left := by
  cases p <;> simp only [LE.le, reduceCtorEq, and_self, or_false, or_true, and_true]

theorem left_le_right (h1 : Player.left ≤ Player.right) : False := by
  simp only [LE.le, reduceCtorEq, and_false, or_self] at h1

theorem not_left_le_right : ¬ Player.left ≤ Player.right :=
  left_le_right

end Player

end

end MisereGames
