/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

import Mathlib.Order.WithBotTop

/-! # Belnap levels

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- The Belnap four-valued logic lattice on `Bool`, with a bottom (no information) and a
top (conflicting information) adjoined. -/
def BelnapLevel := WithBotTop Bool

namespace BelnapLevel

instance : Coe (WithBotTop Bool) (BelnapLevel) where
  coe l := l

instance : Bot BelnapLevel where
  bot := .none

instance : Top BelnapLevel where
  top := .some .none

/-- The information ordering on Belnap levels: `⊥` is below everything, everything is below `⊤`,
and the two classical values are only related to themselves. -/
@[inline]
def le : BelnapLevel → BelnapLevel → Prop
  | ⊥, _ => true
  | _, ⊤ => true
  | .some (.some x), .some (.some y) => x == y
  | _, _ => false

lemma le_refl : ∀ (a : BelnapLevel), a.le a := by
  rintro (_ | (_ | (_ | _))) <;> trivial

lemma le_trans : ∀ (a b c : BelnapLevel), a.le b → b.le c → a.le c := by
  rintro (_ | (_ | a)) (_ | (_ | b)) (_ | (_ | c)) hab hbc <;> simp_all [le]

instance : Preorder BelnapLevel where
  le
  le_refl
  le_trans

lemma le_antisymm : ∀ (a b : BelnapLevel), a ≤ b → b ≤ a → a = b := by
  rintro (_ | (_ | a)) (_ | (_ | b)) hab hba <;> simp_all [LE.le, le]

/-- The join (least upper bound) on Belnap levels in the information order. -/
def sup : BelnapLevel → BelnapLevel → BelnapLevel
  | .none, x => x
  | x, .none => x
  | .some .none, _ => .some .none
  | _, .some .none => .some .none
  | .some (.some x), .some (.some y) => if x == y then .some (.some x) else .some .none

lemma le_sup_left : ∀ (a b : BelnapLevel), a ≤ a.sup b:= by
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) <;> simp_all [LE.le, le, sup]

lemma le_sup_right : ∀ (a b : BelnapLevel), b ≤ a.sup b := by
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) <;> simp_all [LE.le, le, sup]

lemma sup_le : ∀ (a b c : BelnapLevel), a ≤ c → b ≤ c → a.sup b ≤ c  := by
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) hac hbc <;>
    simp_all [LE.le, le, sup]

instance : SemilatticeSup BelnapLevel where
  le_antisymm
  sup
  le_sup_left
  le_sup_right
  sup_le

/-- Logical AND. -/
@[inline]
def and (a b : BelnapLevel) : BelnapLevel := match a, b with
  | .some (.some false), _ => false
  | _, .some (.some false) => false
  | .some (.some true), x => x
  | x, .some (.some true) => x
  | ⊥, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | _, _ => false

/-- Logical OR. -/
@[inline]
def or (a b : BelnapLevel) : BelnapLevel := match a, b with
  | .some (.some true), _ => true
  | _, .some (.some true) => true
  | .some (.some false), x => x
  | x, .some (.some false) => x
  | ⊥, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | _, _ => true

/-- Logical NOT. -/
@[inline]
def not : BelnapLevel → BelnapLevel
  | .some (.some b) => !b
  | x => x

end BelnapLevel

end Circuit
