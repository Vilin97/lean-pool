/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

import LeanPool.Circuitlib.Circuit.Belnap.Level
import LeanPool.Circuitlib.Circuit.Wires

/-! # Belnap circuits

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

namespace Belnap

/-- The AND wire-function on a pair of Belnap-valued wires. -/
@[inline]
def and (w : Wires BelnapLevel 2) : Wires BelnapLevel 1 := #v[(w.get 0).and (w.get 1)]

@[simp]
lemma and_leq
    {a₁ a₂ b₁ b₂ : BelnapLevel}
    (h0 : a₁ ≤ b₁)
    (h1 : a₂ ≤ b₂) :
    a₁.and a₂ ≤ b₁.and b₂ := by
  cases a₁ <;> try (rename_i x; cases x <;> try (rename_i x; cases x))
  all_goals (cases a₂ <;> try (rename_i x; cases x <;> try (rename_i x; cases x)))
  all_goals (cases b₁ <;> try (rename_i x; cases x <;> try (rename_i x; cases x)))
  all_goals (cases b₂ <;> try (rename_i x; cases x <;> try (rename_i x; cases x)))
  all_goals (first | exact h0 | exact h1 | rfl)

@[simp]
lemma and_monotonic : Monotone and := by
  intro a b hab i
  have hi : i = 0 := by ext; omega
  subst hi
  exact and_leq (hab 0) (hab 1)

/-- The OR wire-function on a pair of Belnap-valued wires. -/
@[inline]
def or (w : Wires BelnapLevel 2) : Wires BelnapLevel 1 := #v[(w.get 0).or (w.get 1)]

@[simp]
lemma or_leq
    {a₁ a₂ b₁ b₂ : BelnapLevel}
    (h0 : a₁ ≤ b₁)
    (h1 : a₂ ≤ b₂) :
    a₁.or a₂ ≤ b₁.or b₂ := by
  cases a₁ <;> try (rename_i x; cases x <;> try (rename_i x; cases x))
  all_goals (cases a₂ <;> try (rename_i x; cases x <;> try (rename_i x; cases x)))
  all_goals (cases b₁ <;> try (rename_i x; cases x <;> try (rename_i x; cases x)))
  all_goals (cases b₂ <;> try (rename_i x; cases x <;> try (rename_i x; cases x)))
  all_goals (first | exact h0 | exact h1 | rfl)

@[simp]
lemma or_monotonic : Monotone or := by
  intro a b hab i
  have hi : i = 0 := by ext; omega
  subst hi
  exact or_leq (hab 0) (hab 1)

/-- The NOT wire-function on a single Belnap-valued wire. -/
@[inline]
def not (w : Wires BelnapLevel 1) : Wires BelnapLevel 1 := #v[ (w.get 0).not ]

@[simp]
lemma not_leq {x y : BelnapLevel} (h : x ≤ y) : x.not ≤ y.not := by
  cases x with
  | none => exact h
  | some x => cases x with
    | top =>
      cases y with | none => exact h | some y => cases y <;> exact h
    | coe xv =>
      cases y with
      | none => exact h
      | some y => cases y with
        | top => exact h
        | coe yv => cases xv <;> cases yv <;> exact h

@[simp]
lemma not_monotonic : Monotone not := by
  intro a b hab i
  have hi : i = 0 := by ext; omega
  subst hi
  exact not_leq (hab 0)

end Belnap

end Circuit
