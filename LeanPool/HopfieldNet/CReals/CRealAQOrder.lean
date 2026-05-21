/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealAQ

namespace Computable

namespace CRealAQ

variable {AQ : Type} [ApproxRationals AQ]

/-!
### Order transport

We define `≤` and `<` on `CRealAQ AQ` by pulling back the order on the
specification quotient `CReal` along the denotation map `toCReal`.

-/

instance : LE (CRealAQ AQ) :=
  ⟨fun a b => toCReal (AQ := AQ) a ≤ toCReal (AQ := AQ) b⟩

instance : LT (CRealAQ AQ) :=
  ⟨fun a b => toCReal (AQ := AQ) a < toCReal (AQ := AQ) b⟩

@[simp] theorem le_def (a b : CRealAQ AQ) :
    (a ≤ b) ↔ toCReal (AQ := AQ) a ≤ toCReal (AQ := AQ) b := Iff.rfl

@[simp] theorem lt_def (a b : CRealAQ AQ) :
    (a < b) ↔ toCReal (AQ := AQ) a < toCReal (AQ := AQ) b := Iff.rfl

/-- Reflexivity of the transported order. -/
@[simp] theorem le_refl (a : CRealAQ AQ) : a ≤ a := by
  -- unfold `≤` and use reflexivity on `CReal`
  change toCReal (AQ := AQ) a ≤ toCReal (AQ := AQ) a
  exact (_root_.le_rfl : toCReal (AQ := AQ) a ≤ toCReal (AQ := AQ) a)

/-- Transitivity of the transported order. -/
@[simp] theorem le_trans {a b c : CRealAQ AQ} : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  -- force the transitivity lemma on `CReal`
  change toCReal (AQ := AQ) a ≤ toCReal (AQ := AQ) c
  exact (_root_.le_trans (α := CReal) hab hbc)

/-- Antisymmetry of the transported order, using injectivity of `toCReal`. -/
@[simp] theorem le_antisymm {a b : CRealAQ AQ} : a ≤ b → b ≤ a → a = b := by
  intro hab hba
  apply toCReal_injective (AQ := AQ)
  exact _root_.le_antisymm hab hba

instance : Preorder (CRealAQ AQ) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by intro a; exact CRealAQ.le_refl (AQ := AQ) a
  le_trans := by
    intro a b c hab hbc
    exact CRealAQ.le_trans (AQ := AQ) hab hbc

instance : PartialOrder (CRealAQ AQ) where
  le := (· ≤ ·)
  le_refl := by intro a; exact CRealAQ.le_refl (AQ := AQ) a
  le_trans := by
    intro a b c hab hbc
    exact CRealAQ.le_trans (AQ := AQ) hab hbc
  le_antisymm := by intro a b; exact le_antisymm (AQ := AQ)

/-!
### Ordered ring structure

These instances are transported from the ordered ring structure on `CReal`.
-/

theorem add_le_add_left' (a b : CRealAQ AQ) (h : a ≤ b) (c : CRealAQ AQ) : c + a ≤ c + b := by
  -- reduce to the corresponding lemma on `CReal`
  change toCReal (AQ := AQ) (c + a) ≤ toCReal (AQ := AQ) (c + b)
  -- expand both sides without triggering simp-cancellation lemmas
  rw [CRealAQ.toCReal_add]
  rw [CRealAQ.toCReal_add]
  have h' : toCReal (AQ := AQ) a ≤ toCReal (AQ := AQ) b := by simpa using h
  exact Computable.CReal.add_le_add_left (toCReal (AQ := AQ) a) (toCReal (AQ := AQ) b) h'
    (toCReal (AQ := AQ) c)

theorem mul_le_mul_of_nonneg_left' (a b : CRealAQ AQ) (h : a ≤ b) (c : CRealAQ AQ) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  change toCReal (AQ := AQ) (c * a) ≤ toCReal (AQ := AQ) (c * b)
  rw [CRealAQ.toCReal_mul]
  rw [CRealAQ.toCReal_mul]
  have h' : toCReal (AQ := AQ) a ≤ toCReal (AQ := AQ) b := by simpa using h
  have hc' : (0 : CReal) ≤ toCReal (AQ := AQ) c := by simpa using hc
  exact Computable.CReal.mul_le_mul_of_nonneg_left'
    (a := toCReal (AQ := AQ) a) (b := toCReal (AQ := AQ) b) (c := toCReal (AQ := AQ) c) h' hc'

theorem mul_le_mul_of_nonneg_right' (a b : CRealAQ AQ) (h : a ≤ b) (c : CRealAQ AQ) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  change toCReal (AQ := AQ) (a * c) ≤ toCReal (AQ := AQ) (b * c)
  rw [CRealAQ.toCReal_mul]
  rw [CRealAQ.toCReal_mul]
  have h' : toCReal (AQ := AQ) a ≤ toCReal (AQ := AQ) b := by simpa using h
  have hc' : (0 : CReal) ≤ toCReal (AQ := AQ) c := by simpa using hc
  exact Computable.CReal.mul_le_mul_of_nonneg_right'
    (a := toCReal (AQ := AQ) a) (b := toCReal (AQ := AQ) b) (c := toCReal (AQ := AQ) c) h' hc'

theorem zero_le_one : (0 : CRealAQ AQ) ≤ (1 : CRealAQ AQ) := by
  -- pulled back from `CReal`.
  simp

instance : IsOrderedRing (CRealAQ AQ) where
  add_le_add_left := by
    intro a b hab c
    simp_all only [le_def, toCReal_add, add_le_add_iff_right]
  zero_le_one := zero_le_one (AQ := AQ)
  mul_le_mul_of_nonneg_left := by
    intro c hc a b hab
    -- expected order: nonneg multiplier first
    exact mul_le_mul_of_nonneg_left' (AQ := AQ) a b hab c hc
  mul_le_mul_of_nonneg_right := by
    intro c hc a b hab
    exact mul_le_mul_of_nonneg_right' (AQ := AQ) a b hab c hc

end CRealAQ

end Computable
