/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.Vorspiel.Vorspiel
import Mathlib.Algebra.GCDMonoid.Basic

/-! # Lemmata -/


namespace LO
namespace FirstOrder

namespace Structure

/-- Imported declaration from the Incompleteness formalization. -/
class Monotone (L : Language) (M : Type*) [LE M] [Structure L M] where
  monotone : ∀ {k} (f : L.Func k) (v₁ v₂ : Fin k → M), (∀ i, v₁ i ≤ v₂ i) →
    Structure.func f v₁ ≤ Structure.func f v₂

namespace Monotone

variable {L : Language} {M : Type*} [LE M] [Structure L M] [Monotone L M]

lemma term_monotone (t : Semiterm L ξ n) {e₁ e₂ : Fin n → M} {ε₁ ε₂ : ξ → M}
    (he : ∀ i, e₁ i ≤ e₂ i) (hε : ∀ i, ε₁ i ≤ ε₂ i) :
    t.valm M e₁ ε₁ ≤ t.valm M e₂ ε₂ := by
  induction t with
  | bvar x => exact he x
  | fvar x => exact hε x
  | func f v ih =>
    change Structure.func f (fun i => Semiterm.valm M e₁ ε₁ (v i)) ≤
      Structure.func f (fun i => Semiterm.valm M e₂ ε₂ (v i))
    exact Monotone.monotone f _ _ ih

end Monotone

end Structure

namespace Semiterm

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def arithCases {n} {C : Semiterm ℒₒᵣ ξ n → Sort w}
  (hbvar : ∀ x : Fin n, C #x)
  (hfvar : ∀ x : ξ, C &x)
  (hzero : C ‘0’)
  (hone  : C ‘1’)
  (hadd  : ∀ (t u : Semiterm ℒₒᵣ ξ n), C ‘!!t + !!u’)
  (hmul  : ∀ (t u : Semiterm ℒₒᵣ ξ n), C ‘!!t * !!u’) :
    ∀ (t : Semiterm ℒₒᵣ ξ n), C t
  | #x                        => hbvar x
  | &x                        => hfvar x
  | func Language.Zero.zero _ => by
      simpa [Matrix.empty_eq, Operator.const, Operator.operator, Operator.numeral,
        Operator.Zero.term_eq] using hzero
  | func Language.One.one _   => by
      simpa [Matrix.empty_eq, Operator.const, Operator.operator, Operator.numeral,
        Operator.One.term_eq] using hone
  | func Language.Add.add v   => by
    simpa [Operator.operator, Operator.Add.term_eq, Rew.func,
      ←Matrix.fun_eq_vec₂] using hadd (v 0) (v 1)
  | func Language.Mul.mul v   => by
    simpa [Operator.operator, Operator.Mul.term_eq, Rew.func,
      ←Matrix.fun_eq_vec₂] using hmul (v 0) (v 1)

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def arithRec {n} {C : Semiterm ℒₒᵣ ξ n → Sort w}
  (hbvar : ∀ x : Fin n, C #x)
  (hfvar : ∀ x : ξ, C &x)
  (hzero : C ‘0’)
  (hone  : C ‘1’)
  (hadd  : ∀ {t u : Semiterm ℒₒᵣ ξ n}, C t → C u → C ‘!!t + !!u’)
  (hmul  : ∀ {t u : Semiterm ℒₒᵣ ξ n}, C t → C u → C ‘!!t * !!u’) :
    ∀ (t : Semiterm ℒₒᵣ ξ n), C t
  | #x                        => hbvar x
  | &x                        => hfvar x
  | func Language.Zero.zero _ => by
      simpa [Matrix.empty_eq, Operator.const, Operator.operator, Operator.numeral,
        Operator.Zero.term_eq] using hzero
  | func Language.One.one _   => by
      simpa [Matrix.empty_eq, Operator.const, Operator.operator, Operator.numeral,
        Operator.One.term_eq] using hone
  | func Language.Add.add v   => by
    have ih0 := arithRec hbvar hfvar hzero hone hadd hmul (v 0)
    have ih1 := arithRec hbvar hfvar hzero hone hadd hmul (v 1)
    simpa [Operator.operator, Operator.Add.term_eq, Rew.func,
      ←Matrix.fun_eq_vec₂] using hadd ih0 ih1
  | func Language.Mul.mul v   => by
    have ih0 := arithRec hbvar hfvar hzero hone hadd hmul (v 0)
    have ih1 := arithRec hbvar hfvar hzero hone hadd hmul (v 1)
    simpa [Operator.operator, Operator.Mul.term_eq, Rew.func,
      ←Matrix.fun_eq_vec₂] using hmul ih0 ih1
  termination_by t => t.complexity

end Semiterm

end FirstOrder

namespace Arith

noncomputable section «lp_nc_section_1»

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐏𝐀⁻]

variable {a b c : M}

instance : Nonempty M := ⟨0⟩

@[simp] lemma numeral_two_eq_two : (ORingStruc.numeral 2 : M) = 2 := by simp [numeral_eq_natCast]

@[simp] lemma numeral_three_eq_three : (ORingStruc.numeral 3 :
    M) = 3 := by
  simp [numeral_eq_natCast]

@[simp] lemma numeral_four_eq_four : (ORingStruc.numeral 4 : M) = 4 := by simp [numeral_eq_natCast]

lemma lt_succ_iff_le {x y : M} : x < y + 1 ↔ x ≤ y := Iff.symm le_iff_lt_succ

lemma lt_iff_succ_le : a < b ↔ a + 1 ≤ b := by simp [le_iff_lt_succ]

lemma succ_le_iff_lt : a + 1 ≤ b ↔ a < b := by simp [le_iff_lt_succ]

lemma pos_iff_one_le : 0 < a ↔ 1 ≤ a := by simp [lt_iff_succ_le]

lemma one_lt_iff_two_le : 1 < a ↔ 2 ≤ a := by simp [lt_iff_succ_le, one_add_one_eq_two]

@[simp] lemma not_nonpos (a : M) : ¬a < 0 := by simp

lemma lt_two_iff_le_one : a < 2 ↔ a ≤ 1 := by
  simp [lt_iff_succ_le,
    show a + 1 ≤ 2 ↔ a ≤ 1 from by
      rw[show (2 : M) = 1 + 1 from one_add_one_eq_two.symm]; exact add_le_add_iff_right 1]

@[simp] lemma lt_one_iff_eq_zero : a < 1 ↔ a = 0 := ⟨by
  intro hx
  have : a ≤ 0 := by exact le_iff_lt_succ.mpr (show a < 0 + 1 from by simpa using hx)
  exact nonpos_iff_eq_zero.mp this,
  by rintro rfl; exact zero_lt_one⟩

lemma le_one_iff_eq_zero_or_one : a ≤ 1 ↔ a = 0 ∨ a = 1 :=
  ⟨by intro h; rcases h with (rfl | ltx)
      · simp
      · simp [show a = 0 from by simpa using ltx],
   by rintro (rfl | rfl) <;> simp⟩

lemma le_two_iff_eq_zero_or_one_or_two : a ≤ 2 ↔ a = 0 ∨ a = 1 ∨ a = 2 :=
  ⟨by intro h; rcases h with (rfl | lt)
      · simp
      · rcases lt_two_iff_le_one.mp lt with (rfl | lt)
        · simp
        · simp [show a = 0 from by simpa using lt],
   by rintro (rfl | rfl | rfl) <;> simp []⟩

lemma le_three_iff_eq_zero_or_one_or_two_or_three : a ≤ 3 ↔ a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 :=
  ⟨by intro h; rcases h with (rfl | lt)
      · simp
      · have : a ≤2 := by simpa [←le_iff_lt_succ, ←two_add_one_eq_three] using lt
        rcases this with (rfl| lt)
        · simp
        · rcases lt_two_iff_le_one.mp lt with (rfl | lt)
          · simp
          · simp [show a = 0 from by simpa using lt],
   by rintro (rfl | rfl | rfl | rfl) <;> simp [←two_add_one_eq_three]⟩

lemma two_mul_two_eq_four : 2 * 2 = (4 : M) := by
  rw [←one_add_one_eq_two, mul_add, add_mul, mul_one, ←add_assoc,
    one_add_one_eq_two, two_add_one_eq_three, three_add_one_eq_four]

lemma two_pow_two_eq_four : 2 ^ 2 = (4 : M) := by
  simp [sq, two_mul_two_eq_four]

lemma two_pos : (0 : M) < 2 := by exact _root_.two_pos

@[simp] lemma le_mul_self (a : M) : a ≤ a * a := by
  have : 0 ≤ a := by exact zero_le a
  rcases this with (rfl | pos) <;> simp [*, ←pos_iff_one_le]

@[simp] lemma le_sq (a : M) : a ≤ a ^ 2 := by simp [sq]

@[simp] lemma sq_le_sq :
    a ^ 2 ≤ b ^ 2 ↔ a ≤ b := by
  rw [sq, sq]
  exact (mul_self_le_mul_self_iff (zero_le a) (zero_le b)).symm

@[simp] lemma sq_lt_sq :
    a ^ 2 < b ^ 2 ↔ a < b := by
  rw [sq, sq]
  exact (mul_self_lt_mul_self_iff (zero_le a) (zero_le b)).symm

lemma le_mul_of_pos_right (h : 0 < b) :
    a ≤ a * b :=
  le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp h)

lemma le_mul_of_pos_left (h : 0 < b) :
    a ≤ b * a :=
  le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp h)

@[simp] lemma le_two_mul_left : a ≤ 2 * a := le_mul_of_pos_left (by simp)

lemma lt_mul_of_pos_of_one_lt_right (pos : 0 < a) (h : 1 < b) :
    a < a * b :=
  _root_.lt_mul_of_one_lt_right pos h

lemma lt_mul_of_pos_of_one_lt_left (pos : 0 < a) (h : 1 < b) :
    a < b * a :=
  _root_.lt_mul_of_one_lt_left pos h

lemma mul_le_mul_left (h : b ≤ c) : a * b ≤ a * c := mul_le_mul_of_nonneg_left h (by simp)

lemma mul_le_mul_right (h : b ≤ c) : b * a ≤ c * a := mul_le_mul_of_nonneg_right h (by simp)

theorem lt_of_mul_lt_mul_left (h : a * b < a * c) :
    b < c :=
  lt_of_mul_lt_mul_of_nonneg_left h (by simp)

theorem lt_of_mul_lt_mul_right (h : b * a < c * a) :
    b < c :=
  lt_of_mul_lt_mul_of_nonneg_right h (by simp)

lemma pow_three (x : M) : x^3 = x * x * x := by rw [← two_add_one_eq_three, pow_add, sq]; simp

lemma pow_four (x : M) :
    x^4 = x * x * x * x := by
  rw [← three_add_one_eq_four, pow_add, pow_three]; simp

lemma pow_four_eq_sq_sq (x : M) : x^4 = (x ^ 2) ^ 2 := by simp [pow_four, sq, mul_assoc]

scoped instance : CovariantClass M M (· * ·) (· ≤ ·) := ⟨by intro; exact mul_le_mul_left⟩

scoped instance : CovariantClass M M (· + ·) (· ≤ ·) := ⟨by intro; simp⟩

scoped instance : CovariantClass M M (Function.swap (· * ·)) (· ≤ ·) :=
  ⟨by intro; exact mul_le_mul_right⟩

@[simp] lemma one_lt_mul_self_iff {a : M} : 1 < a * a ↔ 1 < a :=
  ⟨(fun h ↦ by push Not at h ⊢; exact mul_le_one' h h).mtr, fun h ↦ one_lt_mul'' h h⟩

@[simp] lemma opos_lt_sq_pos_iff {a : M} : 0 < a ^ 2 ↔ 0 < a := by simp [sq, pos_iff_ne_zero]

@[simp] lemma one_lt_sq_iff {a : M} : 1 < a ^ 2 ↔ 1 < a := by simp [sq]

@[simp] lemma mul_self_eq_one_iff {a : M} : a * a = 1 ↔ a = 1 :=
  not_iff_not.mp (by simp [ne_iff_lt_or_gt])

@[simp] lemma sq_eq_one_iff {a : M} : a ^ 2 = 1 ↔ a = 1 := by simp [sq]

lemma lt_square_of_lt {a : M} (pos : 1 < a) : a < a ^ 2 := by
  rw [sq]; apply lt_mul_self pos

lemma two_mul_le_sq {i : M} (h : 2 ≤ i) : 2 * i ≤ i ^ 2 := by
  rw [sq]
  exact mul_le_mul_right h

lemma two_mul_le_sq_add_one (i : M) : 2 * i ≤ i ^ 2 + 1 := by
  rcases zero_le i with (rfl | pos)
  · simp
  · rcases pos_iff_one_le.mp pos with (rfl | lt)
    · simp [one_add_one_eq_two]
    · exact le_trans (two_mul_le_sq (one_lt_iff_two_le.mp lt)) (by simp)

lemma two_mul_lt_sq {i : M} (h : 2 < i) : 2 * i < i ^ 2 := by
  rw [sq]
  exact Arith.mul_lt_mul 2 i i h (pos_of_gt h)

lemma succ_le_double_of_pos {a : M} (h : 0 < a) : a + 1 ≤ 2 * a := by
  simpa [two_mul] using pos_iff_one_le.mp h

lemma two_mul_add_one_lt_two_mul_of_lt (h : a < b) : 2 * a + 1 < 2 * b := calc
  2 * a + 1 < 2 * (a + 1) := by simp [mul_add]
  _         ≤ 2 * b       := by simp [←lt_iff_succ_le, h]

@[simp] lemma le_add_add_left (a b c : M) : a ≤ a + b + c := by simp [add_assoc]

@[simp] lemma le_add_add_right (a b c : M) : b ≤ a + b + c := by simp [add_right_comm a b c]

lemma add_le_cancel (a : M) : AddLECancellable a := by intro b c; simp

open FirstOrder FirstOrder.Semiterm

@[simp] lemma val_npow (k : ℕ) (a : M) :
    (Operator.npow ℒₒᵣ k).val ![a] = a ^ k := by
  induction k
  · simp only [Operator.npow_zero, Operator.val_comp, Matrix.empty_eq, Structure.One.one,
      pow_zero]
  case succ k IH =>
    simp only [Operator.npow_succ, Fin.isValue, Operator.val_comp]
    rw [Matrix.fun_eq_vec₂ (v := fun i =>
      Operator.val ((Operator.npow ℒₒᵣ k :> ![Operator.bvar 0]) i) ![a]), pow_succ]
    simp [IH]

instance : Structure.Monotone ℒₒᵣ M := ⟨
  fun {k} f v₁ v₂ h ↦
  match k, f with
  | 0, Language.Zero.zero => by rfl
  | 0, Language.One.one   => by rfl
  | 2, Language.Add.add   => add_le_add (h 0) (h 1)
  | 2, Language.Mul.mul   => mul_le_mul (h 0) (h 1) (by simp) (by simp)⟩

@[simp] lemma zero_ne_add_one (x : M) : 0 ≠ x + (1 : M) := ne_of_lt (by simp)

@[simp] lemma nat_cast_inj {n m : ℕ} : (n : M) = (m : M) ↔ n = m := by
  induction n with
  | zero => cases m <;> simp
  | succ n ih => cases m <;> simp

@[simp] lemma coe_coe_lt {n m : ℕ} : (n : M) < (m : M) ↔ n < m := by
  induction n with
  | zero => cases m <;> simp
  | succ n ih => cases m <;> simp

/-- TODO: move -/
lemma coe_succ (x : ℕ) : ((x + 1 : ℕ) : M) = (x : M) + 1 := by simp

variable (M)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev natCast : NatCast M := inferInstance

variable {M}

@[simp] lemma natCast_nat (n : ℕ) : @Nat.cast ℕ (natCast ℕ) n = n := by
  induction n
  · rfl
  · unfold natCast; rw [coe_succ]; simp [*]

end «lp_nc_section_1»

end Arith

namespace FirstOrder
namespace Semiformula

open LO.Arith

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻] {L : Language} [L.LT]
variable [L.Zero] [L.One] [L.Add]

variable [Structure L M] [Structure.LT L M] [Structure.One L M] [Structure.Add L M]

@[simp] lemma eval_ballLTSucc' {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)} :
    Semiformula.Evalm M e ε (φ.ballLTSucc t) ↔
        ∀ x ≤ Semiterm.valm M e ε t, Semiformula.Evalm M (x :> e) ε φ := by
  simp [Semiformula.eval_ballLTSucc, lt_succ_iff_le]

@[simp] lemma eval_bexLTSucc' {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)} :
    Semiformula.Evalm M e ε (φ.bexLTSucc t) ↔
        ∃ x ≤ Semiterm.valm M e ε t, Semiformula.Evalm M (x :> e) ε φ := by
  simp [Semiformula.eval_bexLTSucc, lt_succ_iff_le]

end Semiformula
end FirstOrder
end LO
