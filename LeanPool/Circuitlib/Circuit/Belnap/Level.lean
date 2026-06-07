/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Mathlib.Order.WithBotTop

@[expose] public section

/-! # Belnap levels

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

def BelnapLevel := WithBotTop Bool

namespace BelnapLevel

instance : Coe (WithBotTop Bool) (BelnapLevel) where
  coe l := l

instance : Bot BelnapLevel where
  bot := .none

instance : Top BelnapLevel where
  top := .some .none

@[inline, simp]
def le : BelnapLevel → BelnapLevel → Prop
  | ⊥, _ => true
  | _, ⊤ => true
  | .some (.some x), .some (.some y) => x == y
  | _, _ => false

@[simp]
lemma le_refl : ∀ (a : BelnapLevel), a.le a := by
  intro a
  cases a with
  | none => trivial
  | some a =>
    cases a with
    | top => trivial
    | coe b => cases b <;> trivial

@[simp]
lemma le_trans : ∀ (a b c : BelnapLevel), a.le b → b.le c → a.le c := by
  intro a b c hab hbc
  cases a with
  | none => trivial
  | some a => cases a with
    | top =>
      cases b with
      | none => simp_all
      | some b => cases b with
        | top => exact hbc
        | coe bv => cases bv <;> simp_all
    | coe av => cases c with
      | none =>
        cases b with
        | none => cases av <;> simp_all
        | some b => cases b with
          | top => simp_all
          | coe bv => cases bv <;> simp_all
      | some c => cases c with
        | top => trivial
        | coe cv =>
          cases b with
          | none => cases av <;> simp_all
          | some b => cases b with
            | top => cases cv <;> simp_all
            | coe bv => cases av <;> cases bv <;> cases cv <;> simp_all

instance : Preorder BelnapLevel where
  le
  le_refl
  le_trans

@[simp]
lemma le_antisymm : ∀ (a b : BelnapLevel), a ≤ b → b ≤ a → a = b := by
  intro a b hab hba
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some _ => cases hba
  | some a => cases a with
    | top =>
      cases b with
      | none => cases hab
      | some b => cases b with
        | top => rfl
        | coe _ => cases hab
    | coe av =>
      cases b with
      | none => cases hab
      | some b => cases b with
        | top => cases hba
        | coe bv => cases av <;> cases bv <;> first | rfl | cases hab

@[simp]
def sup : BelnapLevel → BelnapLevel → BelnapLevel
  | .none, x => x
  | x, .none => x
  | .some .none, _ => .some .none
  | _, .some .none => .some .none
  | .some (.some x), .some (.some y) => if x == y then .some (.some x) else .some .none

@[simp]
def le_sup_left : ∀ (a b : BelnapLevel), a ≤ a.sup b:= by
  intro a b
  cases a with
  | none => trivial
  | some a => cases a with
    | top =>
      cases b with
      | none => trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases bv <;> trivial
    | coe av =>
      cases b with
      | none => cases av <;> trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases av <;> cases bv <;> trivial

@[simp]
lemma le_sup_right : ∀ (a b : BelnapLevel), b ≤ a.sup b := by
  intro a b
  cases a with
  | none => trivial
  | some a => cases a with
    | top =>
      cases b with
      | none => trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases bv <;> trivial
    | coe av =>
      cases b with
      | none => cases av <;> trivial
      | some b => cases b with
        | top => trivial
        | coe bv => cases av <;> cases bv <;> trivial

@[simp]
lemma sup_le : ∀ (a b c : BelnapLevel), a ≤ c → b ≤ c → a.sup b ≤ c  := by
  intro a b c hac hbc
  cases a with
  | none => exact hbc
  | some a => cases a with
    | top => cases b <;> exact hac
    | coe av =>
      cases b with
      | none => exact hac
      | some b => cases b with
        | top => exact hbc
        | coe bv =>
          cases av <;> cases bv <;>
            first
            | exact hac
            | cases c with
                | none => cases hac
                | some c => cases c with
                  | top => trivial
                  | coe cv => cases cv <;> first | cases hbc; done | cases hac

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
