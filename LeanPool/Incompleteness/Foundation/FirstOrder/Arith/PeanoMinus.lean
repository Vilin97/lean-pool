/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.CobhamR0
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Nat.Cast.Order.Basic

/-! # PeanoMinus -/


noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {M : Type*} [ORingStruc M]

open Language

/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instLEofPeanoMinus : LE M := ⟨fun x y => x = y ∨ x < y⟩

lemma le_def {x y : M} : x ≤ y ↔ x = y ∨ x < y := iff_of_eq rfl

variable [M ⊧ₘ* 𝐏𝐀⁻]

protected lemma add_zero (x : M) : x + 0 = x := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.addZero (fun _ ↦ x)

protected lemma add_assoc (x y z : M) : (x + y) + z = x + (y + z) := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.addAssoc (x :>ₙ y :>ₙ fun _ ↦ z)

protected lemma add_comm (x y : M) : x + y = y + x := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.addComm (x :>ₙ fun _ ↦ y)

lemma add_eq_of_lt (x y : M) : x < y → ∃ z, x + z = y := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.addEqOfLt (x :>ₙ fun _ ↦ y)

@[simp] lemma zero_le (x : M) : 0 ≤ x := by
  rw [le_def]
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M
    Theory.PeanoMinus.zeroLe (fun _ ↦ x)

lemma zero_lt_one : (0 : M) < 1 := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.zeroLtOne

lemma one_le_of_zero_lt (x : M) : 0 < x → 1 ≤ x := by
  rw [le_def]
  simpa[models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M
    Theory.PeanoMinus.oneLeOfZeroLt (fun _ ↦ x)

lemma add_lt_add (x y z : M) : x < y → x + z < y + z := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.addLtAdd (x :>ₙ y :>ₙ fun _ ↦ z)

protected lemma mul_zero (x : M) : x * 0 = 0 := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.mulZero (fun _ ↦ x)

protected lemma mul_one (x : M) : x * 1 = x := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.mulOne (fun _ ↦ x)

protected lemma mul_assoc (x y z : M) : (x * y) * z = x * (y * z) := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.mulAssoc (x :>ₙ y :>ₙ fun _ ↦ z)

protected lemma mul_comm (x y : M) : x * y = y * x := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.mulComm (x :>ₙ fun _ ↦ y)

lemma mul_lt_mul (x y z : M) : x < y → 0 < z → x * z < y * z := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.mulLtMul (x :>ₙ y :>ₙ fun _ ↦ z)

lemma distr (x y z : M) : x * (y + z) = x * y + x * z := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.distr (x :>ₙ y :>ₙ fun _ ↦ z)

lemma lt_irrefl (x : M) : ¬x < x := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.ltIrrefl (fun _ ↦ x)

protected lemma lt_trans (x y z : M) : x < y → y < z → x < z := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.ltTrans (x :>ₙ y :>ₙ fun _ ↦ z)

lemma lt_tri (x y : M) : x < y ∨ x = y ∨ y < x := by
  simpa[models_iff] using ModelsTheory.models M Theory.PeanoMinus.ltTri (x :>ₙ fun _ ↦ y)

/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instAddCommMonoidOfPeanoMinus : AddCommMonoid M where
  add_assoc := Arith.add_assoc
  zero_add  := fun x => Arith.add_comm x 0 ▸ Arith.add_zero x
  add_zero  := Arith.add_zero
  add_comm  := Arith.add_comm
  nsmul := nsmulRec

/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instCommMonoidOfPeanoMinus : CommMonoid M where
  mul_assoc := Arith.mul_assoc
  one_mul   := fun x => Arith.mul_comm x 1 ▸ Arith.mul_one x
  mul_one   := Arith.mul_one
  mul_comm  := Arith.mul_comm

/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instLinearOrderOfPeanoMinus : LinearOrder M where
  le_refl := fun x => Or.inl (by simp)
  le_trans := by
    rintro x y z (rfl | hx) (rfl | hy)
    · exact Or.inl rfl
    · exact Or.inr hy
    · exact Or.inr hx
    · exact Or.inr (Arith.lt_trans _ _ _ hx hy)
  le_antisymm := by
    rintro x y (rfl | hx) hyx
    · rfl
    · rcases hyx with (rfl | hy)
      · rfl
      · exact False.elim <| Arith.lt_irrefl _ (Arith.lt_trans _ _ _ hx hy)
  le_total := by
    intro x y
    rcases Arith.lt_tri x y with (h | rfl | h) <;> simp[*, le_def]
  lt_iff_le_not_ge := fun x y =>
    ⟨fun h => ⟨Or.inr h, by
      simp only [le_def]
      rintro (rfl | h')
      · exact lt_irrefl y h
      · exact lt_irrefl _ (Arith.lt_trans _ _ _ h h')⟩,
     by
      rintro ⟨(rfl | h), hyx⟩
      · exact False.elim (hyx (Or.inl rfl))
      · exact h ⟩
  toDecidableLE := fun _ _ => Classical.dec _

protected lemma zero_mul : ∀ x : M, 0 * x = 0 := fun x => by simpa[mul_comm] using Arith.mul_zero x

/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instCommSemiringOfPeanoMinus : CommSemiring M where
  add_assoc := Arith.add_assoc
  zero_add  := fun x => Arith.add_comm x 0 ▸ Arith.add_zero x
  add_zero  := Arith.add_zero
  add_comm  := Arith.add_comm
  nsmul := nsmulRec
  left_distrib := distr
  right_distrib := fun x y z => by
    rw [mul_comm (x + y) z, mul_comm x z, mul_comm y z]
    exact distr z x y
  zero_mul := Arith.zero_mul
  mul_zero := Arith.mul_zero
  mul_assoc := Arith.mul_assoc
  mul_comm := mul_comm
  one_mul   := fun x => Arith.mul_comm x 1 ▸ Arith.mul_one x
  mul_one   := Arith.mul_one

scoped instance : IsOrderedCancelAddMonoid M where
  add_le_add_left := by
    rintro x y (rfl | h) z
    · exact Or.inl rfl
    · exact Or.inr (by simpa [add_comm z] using add_lt_add x y z h)
  le_of_add_le_add_left := by
    rintro x y z h
    have : y ≤ z ∨ z < y := le_or_gt y z
    rcases this with (hyz | hyz)
    · exact hyz
    · have : x + z < x + y := by simpa[add_comm] using add_lt_add z y x hyz
      exact False.elim (lt_iff_not_ge.mp this h)

scoped instance : ZeroLEOneClass M where
  zero_le_one := Or.inr zero_lt_one

scoped instance : Nontrivial M where
  exists_pair_ne := ⟨0, 1, ne_of_lt zero_lt_one⟩

scoped instance : PosMulStrictMono M where
  mul_lt_mul_of_pos_left := by
    intro z hz x y h
    simpa[mul_comm z] using mul_lt_mul x y z h hz

scoped instance : MulPosStrictMono M where
  mul_lt_mul_of_pos_right := by
    intro z hz x y h
    exact mul_lt_mul x y z h hz

scoped instance : IsStrictOrderedRing M where

scoped instance : CanonicallyOrderedAdd M where
  exists_add_of_le := by
    rintro x y (rfl | h)
    · exact ⟨0, by simp⟩
    · simpa[eq_comm] using add_eq_of_lt x y h
  le_add_self := by
    intro x y
    rw [add_comm]
    exact show x ≤ x + y by
      rcases zero_le y with (rfl | hy)
      · exact Or.inl (by simp)
      · exact Or.inr (by simpa using add_lt_add 0 y x hy)
  le_self_add := by
    intro x y
    rcases zero_le y with (rfl | hy)
    · exact Or.inl (by simp)
    · exact Or.inr (by simpa using add_lt_add 0 y x hy)

lemma numeral_eq_natCast : (n : ℕ) → (ORingStruc.numeral n : M) = n
  | 0     => rfl
  | 1     => by simp
  | n + 2 => by simp[ORingStruc.numeral, numeral_eq_natCast (n + 1), add_assoc, one_add_one_eq_two]

lemma not_neg (x : M) : ¬x < 0 := by simp

lemma eq_succ_of_pos {x : M} (h : 0 < x) : ∃ y, x = y + 1 := by
  rcases le_iff_exists_add.mp (one_le_of_zero_lt x h) with ⟨y, rfl⟩
  exact ⟨y, add_comm 1 y⟩

lemma le_iff_lt_succ {x y : M} : x ≤ y ↔ x < y + 1 :=
  ⟨by intro h; exact lt_of_le_of_lt h (lt_add_one y),
   fun h => by
    rcases lt_iff_exists_add.mp h with ⟨z, hz, h⟩
    rcases eq_succ_of_pos hz with ⟨z', rfl⟩
    have : y = x + z' := by simpa[←add_assoc] using h
    simp[this]⟩

lemma eq_nat_of_lt_nat : ∀ {n : ℕ} {x : M}, x < n → ∃ m : ℕ, x = m
  | 0,     x, hx => by simp[] at hx
  | n + 1, x, hx => by
    have : x ≤ n := by simpa[le_iff_lt_succ] using hx
    rcases this with (rfl | hx)
    · exact ⟨n, rfl⟩
    · exact eq_nat_of_lt_nat hx

instance qq : M ⊧ₘ* 𝐑₀ := modelsTheory_iff.mpr <| by
  intro φ h
  rcases h
  case equal h =>
    have : M ⊧ₘ* (𝐄𝐐 : Theory ℒₒᵣ) := inferInstance
    exact modelsTheory_iff.mp this h
  case Ω₁ n m =>
    simp [models_iff, numeral_eq_natCast]
  case Ω₂ n m =>
    simp [models_iff, numeral_eq_natCast]
  case Ω₃ n m h =>
    simp [models_iff, numeral_eq_natCast, h]
  case Ω₄ n =>
      simp only [Nat.reduceAdd, Fin.isValue, models_iff, Semiformula.eval_all,
        Nat.succ_eq_add_one, LogicalConnective.HomClass.map_iff, Semiformula.eval_operator₂,
        Semiterm.val_bvar, Matrix.vecCons_zero, Semiterm.val_const,
        Structure.numeral_eq_numeral, numeral_eq_natCast, Structure.LT.lt, hom_disj_prop,
        Structure.Eq.eq, LogicalConnective.Prop.iff_eq, forall_const]
      intro x
      constructor
      · intro hx; rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩; exact ⟨x, by simpa using hx, by simp⟩
      · rintro ⟨i, hi, rfl⟩; simp [hi]

end Arith

namespace FirstOrder
namespace Arith

open LO.Arith

variable {T : Theory ℒₒᵣ} [𝐏𝐀⁻ wkn T]

instance : 𝐑₀ wkn 𝐏𝐀⁻ := oRing_weakerThan_of.{0} _ _ fun _ _ _ ↦ inferInstance

instance : 𝐑₀ swkn 𝐏𝐀⁻ :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable
    R₀_unprovable_add_zero
    (Entailment.by_axm _ Theory.PeanoMinus.addZero)

end Arith
end FirstOrder

end LO

end «lp_nc_section_1»
