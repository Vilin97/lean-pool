/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.Basic.IOpen

/-! # Pow2 -/


noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

variable {V : Type*} [ORingStruc V]

open FirstOrder FirstOrder.Arith

section «lp_section_1»

variable [V ⊧ₘ* 𝐈open]

/-- Imported declaration from the Incompleteness formalization. -/
def Pow2 (a : V) : Prop := 0 < a ∧ ∀ r ≤ a, 1 < r → r ∣ a → 2 ∣ r

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.pow2Def : Sg0.Semisentence 1 :=
  .mkSigma “a. 0 < a ∧ ∀ r <⁺ a, 1 < r → r ∣ a → 2 ∣ r” (by simp [])

lemma pow2_defined : Sg0-Predicate (Pow2 : V → Prop) via pow2Def := by
  intro v
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Pow2, pow2Def,
    le_iff_lt_succ, dvd_defined.df.iff, numeral_eq_natCast]

instance pow2_definable : Sg0-Predicate (Pow2 : V → Prop) := pow2_defined.to_definable

lemma _root_.LO.Arith.Pow2.pos {a : V} (h : Pow2 a) : 0 < a := h.1

lemma _root_.LO.Arith.Pow2.dvd {a : V} (h : Pow2 a) {r} (hr : r ≤ a) :
    1 < r → r ∣ a → 2 ∣ r :=
  h.2 r hr

@[simp] lemma pow2_one : Pow2 (1 : V) := ⟨by simp, by
  intro r hr hhr hd
  rcases show r = 0 ∨ r = 1 from le_one_iff_eq_zero_or_one.mp hr with (rfl | rfl)
  · simp
  · simp at hhr⟩

@[simp] lemma not_pow2_zero : ¬Pow2 (0 : V) := by
  intro h; have := h.pos; simp at this

lemma _root_.LO.Arith.Pow2.two_dvd {a : V} (h : Pow2 a) (lt : 1 < a) :
    2 ∣ a :=
  h.dvd (le_refl _) lt (by simp)

lemma _root_.LO.Arith.Pow2.two_dvd' {a : V} (h : Pow2 a) (lt : a ≠ 1) : 2 ∣ a :=
  h.dvd (le_refl _) (by
    by_contra A
    have A : a = 0 ∨ a = 1 := le_one_iff_eq_zero_or_one.mp (not_lt.mp A)
    rcases A with (rfl | rfl) <;> simp at h lt)
    (by simp)

lemma _root_.LO.Arith.Pow2.of_dvd {a b : V} (h : b ∣ a) : Pow2 a → Pow2 b := by
  intro ha
  have : 0 < b := by
    by_contra e
    have : a = 0 := by simpa [show b = 0 from by simpa using e] using h
    rcases this with rfl
    simpa using ha.pos
  exact ⟨this, fun r hr ltr hb ↦
    ha.dvd (show r ≤ a from le_trans hr (le_of_dvd ha.pos h)) ltr (dvd_trans hb h)⟩

lemma pow2_mul_two {a : V} : Pow2 (2 * a) ↔ Pow2 a :=
  ⟨by intro H
      have : ∀ r ≤ a, 1 < r → r ∣ a → 2 ∣ r := by
        intro r hr ltr dvd
        exact H.dvd (show r ≤ 2 * a from le_trans hr (le_mul_of_one_le_left (by simp) one_le_two))
          ltr (Dvd.dvd.mul_left dvd 2)
      exact ⟨by simpa using H.pos, this⟩,
   by intro H
      exact ⟨by simpa using H.pos, by
        intro r _ hr hd
        rcases two_prime.left_dvd_or_dvd_right_of_dvd_mul hd with (hd | hd)
        · exact hd
        · exact H.dvd (show r ≤ a from le_of_dvd H.pos hd) hr hd⟩⟩

lemma pow2_mul_four {a : V} : Pow2 (4 * a) ↔ Pow2 a := by
  simp [←two_mul_two_eq_four, mul_assoc, pow2_mul_two]

lemma _root_.LO.Arith.Pow2.elim {p : V} : Pow2 p ↔ p = 1 ∨ ∃ q, p = 2 * q ∧ Pow2 q :=
  ⟨by intro H
      by_cases hp : 1 < p
      · have : 2 ∣ p := H.two_dvd hp
        rcases this with ⟨q, rfl⟩
        right; exact ⟨q, rfl, pow2_mul_two.mp H⟩
      · have : p = 1 := le_antisymm (by simpa using hp) (pos_iff_one_le.mp H.pos)
        left; exact this,
   by rintro (rfl | ⟨q, rfl, hq⟩) <;> simp [pow2_one, pow2_mul_two, *]⟩

@[simp] lemma pow2_two : Pow2 (2 : V) := Pow2.elim.mpr (Or.inr ⟨1, by simp⟩)

lemma _root_.LO.Arith.Pow2.div_two {p : V} (h : Pow2 p) (ne : p ≠ 1) : Pow2 (p / 2) := by
  rcases Pow2.elim.mp h with (rfl | ⟨q, rfl, pq⟩)
  · simp at ne
  simpa

lemma _root_.LO.Arith.Pow2.two_mul_div_two {p : V} (h : Pow2 p) (ne : p ≠ 1) : 2 * (p / 2) = p := by
  rcases Pow2.elim.mp h with (rfl | ⟨q, rfl, _⟩)
  · simp at ne
  simp

lemma _root_.LO.Arith.Pow2.div_two_mul_two {p : V} (h : Pow2 p) (ne : p ≠ 1) : (p / 2) * 2 = p := by
  simp [mul_comm, h.two_mul_div_two ne]

lemma _root_.LO.Arith.Pow2.elim' {p : V} : Pow2 p ↔ p = 1 ∨ 1 < p ∧ ∃ q, p = 2 * q ∧ Pow2 q := by
  by_cases hp : 1 < p <;> simp only [hp, true_and, false_and, or_false]
  · exact Pow2.elim
  · have : p = 0 ∨ p = 1 := le_one_iff_eq_zero_or_one.mp (show p ≤ 1 from by simpa using hp)
    rcases this with (rfl | rfl) <;> simp


section «lp_section_2»

/-- $\mathrm{LenBit} (2^i, a) \iff \text{$i$th-bit of $a$ is $1$}$. -/
def LenBit (i a : V) : Prop := ¬2 ∣ (a / i)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.lenbitDef : Sg0.Semisentence 2 :=
  .mkSigma “i a. ∃ z <⁺ a, !divDef.val z a i ∧ ¬2 ∣ z” (by simp)

lemma lenbit_defined : Sg0-Relation (LenBit : V → V → Prop) via lenbitDef := by
  intro v; simp[lenbitDef, LenBit, numeral_eq_natCast]

@[simp] lemma lenbit_defined_iff (v) :
    Semiformula.Evalbm V v lenbitDef.val ↔ LenBit (v 0) (v 1) := lenbit_defined.df.iff v

instance lenbit_definable : Sg0-Relation (LenBit : V → V → Prop) := lenbit_defined.to_definable

lemma _root_.LO.Arith.LenBit.le {i a : V} (h : LenBit i a) : i ≤ a := by
  by_contra A; simp [LenBit, show a < i from by simpa using A] at h

lemma not_lenbit_of_lt {i a : V} (h : a < i) : ¬LenBit i a := by
  intro A; exact not_le.mpr h A.le

@[simp] lemma _root_.LO.Arith.LenBit.zero (a : V) : ¬LenBit 0 a := by simp [LenBit]

@[simp] lemma _root_.LO.Arith.LenBit.on_zero (a : V) : ¬LenBit a 0 := by simp [LenBit]

lemma _root_.LO.Arith.LenBit.one (a : V) : LenBit 1 a ↔ ¬2 ∣ a := by simp [LenBit]

lemma _root_.LO.Arith.LenBit.iff_rem {i a : V} : LenBit i a ↔ (a / i) % 2 = 1 := by
  simp only [LenBit, ←mod_eq_zero_iff_dvd]
  rcases mod_two (a / i) with (h | h)
  · rw [h]
    simp only [not_true_eq_false, zero_ne_one]
  · rw [h]
    simp only [one_ne_zero, not_false_eq_true]

lemma not_lenbit_iff_rem {i a : V} : ¬LenBit i a ↔ (a / i) % 2 = 0 := by
  simp [LenBit, ←mod_eq_zero_iff_dvd]

@[simp] lemma _root_.LO.Arith.LenBit.self {a : V} (pos : 0 < a) :
    LenBit a a := by
  simp [LenBit.iff_rem, pos]

lemma _root_.LO.Arith.LenBit.mod {i a k : V} (h : 2 * i ∣ k) : LenBit i (a % k) ↔ LenBit i a := by
  have : 0 ≤ i := zero_le i
  rcases (eq_or_lt_of_le this) with (rfl | pos)
  · simp
  rcases h with ⟨k', hk'⟩
  calc
    LenBit i (a % k) ↔ ((a % k) / i) % 2 = 1                            := LenBit.iff_rem
    _                  ↔ ((2 * k') * (a / k) + a % k / i) % 2 = 1       := by simp [mul_assoc]
    _                  ↔ (((2 * k') * (a / k) * i + a % k) / i) % 2 = 1 := by
      simp [div_mul_add_self, pos]
    _                  ↔ ((k * (a / k) + a % k) / i) % 2 = 1            := iff_of_eq (by
      congr 3
      simp [mul_right_comm _ (a / k), mul_right_comm 2 k' i, ←hk'])
    _                  ↔ LenBit i a                                     := by
      simp [div_add_mod a k, LenBit.iff_rem]

@[simp] lemma _root_.LO.Arith.LenBit.mod_two_mul_self {a i : V} :
    LenBit i (a % (2 * i)) ↔ LenBit i a :=
  LenBit.mod (by simp)

lemma _root_.LO.Arith.LenBit.add {i a b : V} (h : 2 * i ∣ b) : LenBit i (a + b) ↔ LenBit i a := by
  have : 0 ≤ i := zero_le i
  rcases (eq_or_lt_of_le this) with (rfl | pos)
  · simp
  rcases h with ⟨b', hb'⟩
  have hb' : b = 2 * b' * i := by simp [hb', mul_right_comm]
  calc
    LenBit i (a + b) ↔ ((a + b) / i) % 2 = 1    := LenBit.iff_rem
    _                ↔ (a / i + 2 * b') % 2 = 1 := by rw [hb', div_add_mul_self _ _ pos]
    _                ↔ LenBit i a               := by simp [LenBit.iff_rem]

lemma _root_.LO.Arith.LenBit.add_self {i a : V} (h : a < i) : LenBit i (a + i) := by
  have pos : 0 < i := by exact pos_of_gt h
  simp [LenBit.iff_rem, div_add_self_right _ pos, h]

lemma _root_.LO.Arith.LenBit.add_self_of_not_lenbit {a i : V} (pos : 0 < i) (h : ¬LenBit i a) :
    LenBit i (a + i) := by
  have : a / i % 2 = 0 := by simpa [LenBit.iff_rem] using h
  simp only [LenBit.iff_rem, div_add_self_right _ pos]
  rw [mod_add] <;> simp [this]

lemma _root_.LO.Arith.LenBit.add_self_of_lenbit {a i : V} (pos : 0 < i) (h : LenBit i a) :
    ¬LenBit i (a + i) := by
  have : a / i % 2 = 1 := by simpa [LenBit.iff_rem] using h
  simp only [LenBit.iff_rem, div_add_self_right _ pos]
  rw [mod_add] <;> simp [this, one_add_one_eq_two]

lemma _root_.LO.Arith.LenBit.sub_self_of_lenbit {a i : V} (pos : 0 < i) (h : LenBit i a) :
    ¬LenBit i (a - i) := by
  intro h'
  have : ¬LenBit i a := by simpa [sub_add_self_of_le h.le] using LenBit.add_self_of_lenbit pos h'
  contradiction

end «lp_section_2»

end «lp_section_1»

section «lp_section_3»

variable [V ⊧ₘ* 𝐈Sg0]

namespace Pow2

lemma mul {a b : V} (ha : Pow2 a) (hb : Pow2 b) : Pow2 (a * b) := by
  wlog hab : a ≤ b
  · simpa [mul_comm] using this hb ha (lt_of_not_ge hab).le
  suffices ∀ b : V, ∀ a ≤ b, Pow2 a → Pow2 b → Pow2 (a * b) by
    exact this b a hab ha hb
  intro b
  induction b using order_induction_sigma0
  · definability
  case ind IH a b IH =>
    intro a hab ha hb
    have : a = 1 ∨ 1 < a ∧ ∃ a', a = 2 * a' ∧ Pow2 a' := Pow2.elim'.mp ha
    rcases this with (rfl | ⟨lta, a, rfl, ha⟩)
    · simpa using hb
    · have : b = 1 ∨ 1 < b ∧ ∃ b', b = 2 * b' ∧ Pow2 b' := Pow2.elim'.mp hb
      rcases this with (rfl | ⟨ltb, b, rfl, hb⟩)
      · simpa using ha
      · have ltb : b < 2 * b := lt_two_mul_self (pos_iff_ne_zero.mpr <| by rintro rfl; simp at ltb)
        have hab : a ≤ b := le_of_mul_le_mul_left hab (by simp)
        have : Pow2 (a * b) := IH b ltb a hab (by assumption) (by assumption)
        suffices Pow2 (4 * a * b) by
          have : (2 * a) * (2 * b) = 4 * a * b := by
            simp [mul_assoc, mul_left_comm a 2 b, ←two_mul_two_eq_four]
          simpa [this]
        simpa [mul_assoc, pow2_mul_four] using this

@[simp] lemma mul_iff {a b : V} : Pow2 (a * b) ↔ Pow2 a ∧ Pow2 b :=
  ⟨fun h ↦ ⟨h.of_dvd (by simp), h.of_dvd (by simp)⟩, by rintro ⟨ha, hb⟩; exact ha.mul hb⟩

@[simp] lemma sq_iff {a : V} : Pow2 (a ^ 2) ↔ Pow2 a := by
  simp [_root_.sq]

lemma sq {a : V} : Pow2 a → Pow2 (a ^ 2) := by
  simp [_root_.sq]

lemma dvd_of_le {a b : V} (ha : Pow2 a) (hb : Pow2 b) : a ≤ b → a ∣ b := by
  suffices  ∀ b : V, ∀ a ≤ b, Pow2 a → Pow2 b → a ∣ b by
    intro hab; exact this b a hab ha hb
  intro b; induction b using order_induction_sigma0
  · definability
  case ind b IH =>
    intro a hab ha hb
    have : b = 1 ∨ 1 < b ∧ ∃ b', b = 2 * b' ∧ Pow2 b' := Pow2.elim'.mp hb
    rcases this with (rfl | ⟨ltb, b, rfl, hb⟩)
    · rcases le_one_iff_eq_zero_or_one.mp hab with (rfl | rfl) <;> simp
      · simp at ha
    · have : a = 1 ∨ 1 < a ∧ ∃ a', a = 2 * a' ∧ Pow2 a' := Pow2.elim'.mp ha
      rcases this with (rfl | ⟨lta, a, rfl, ha⟩)
      · simp
      · have ltb : b < 2 * b := lt_two_mul_self (pos_iff_ne_zero.mpr <| by rintro rfl; simp at ltb)
        have hab : a ≤ b := le_of_mul_le_mul_left hab (by simp)
        exact mul_dvd_mul_left 2 <| IH b ltb a hab (by assumption) (by assumption)

lemma le_iff_dvd {a b : V} (ha : Pow2 a) (hb : Pow2 b) : a ≤ b ↔ a ∣ b :=
  ⟨Pow2.dvd_of_le ha hb, le_of_dvd hb.pos⟩

lemma two_le {a : V} (pa : Pow2 a) (ne1 : a ≠ 1) : 2 ≤ a :=
  le_of_dvd pa.pos (pa.two_dvd' ne1)

lemma le_iff_lt_two {a b : V} (ha : Pow2 a) (hb : Pow2 b) : a ≤ b ↔ a < 2 * b := by
  constructor
  · intro h; exact lt_of_le_of_lt h (lt_two_mul_self hb.pos)
  · intro h
    by_cases ea : a = 1
    · rcases ea with rfl
      simpa [←pos_iff_one_le] using hb.pos
    · suffices a ∣ b from le_of_dvd hb.pos this
      have : a / 2 ∣ b := by
        have : 2 * (a / 2) ∣ 2 * b := by
          simpa [ha.two_mul_div_two ea] using dvd_of_le ha (by simpa using hb) (LT.lt.le h)
        exact (mul_dvd_mul_iff_left (by simp)).mp this
      rcases this with ⟨b', rfl⟩
      have hb' : Pow2 b' := (mul_iff.mp hb).2
      have : 2 ∣ b' := hb'.two_dvd' (by rintro rfl; simp [ha.two_mul_div_two ea] at h)
      rcases this with ⟨b'', rfl⟩
      simp [←mul_assoc, ha.div_two_mul_two ea]

lemma lt_iff_two_mul_le {a b : V} (ha : Pow2 a) (hb : Pow2 b) : a < b ↔ 2 * a ≤ b := by
  by_cases eb : b = 1
  · simp [eb, ←lt_two_iff_le_one]
  · rw [←hb.two_mul_div_two eb]; simp [le_iff_lt_two ha (hb.div_two eb)]

lemma sq_or_dsq {a : V} (pa : Pow2 a) : ∃ b, a = b ^ 2 ∨ a = 2 * b ^ 2 := by
  suffices ∃ b ≤ a, a = b ^ 2 ∨ a = 2 * b ^ 2 by
    rcases this with ⟨b, _, h⟩
    exact ⟨b, h⟩
  induction a using order_induction_sigma0
  · definability
  case ind a IH =>
    rcases Pow2.elim'.mp pa with (rfl | ⟨ha, a, rfl, pa'⟩)
    · exact ⟨1, by simp⟩
    · have : 0 < a := by simpa [←pos_iff_one_le] using one_lt_iff_two_le.mp ha
      rcases IH a (lt_mul_of_one_lt_left this one_lt_two) pa' with ⟨b, _, (rfl | rfl)⟩
      · exact ⟨b, le_trans (by simp) le_two_mul_left, by right; rfl⟩
      · exact ⟨2 * b, by
        simp only [zero_lt_two, mul_le_mul_iff_right₀]
        exact le_trans (by simp) le_two_mul_left,
        by left; simp [_root_.sq, mul_assoc, mul_left_comm]⟩

lemma sqrt {a : V} (h : Pow2 a) (hsq : (√a) ^ 2 = a) : Pow2 (√a) := by
  rw [←hsq] at h; simpa using h

@[simp] lemma not_three : ¬Pow2 (3 : V) := by
  intro h
  have : (2 : V) ∣ 3 := h.two_dvd (by simp [←two_add_one_eq_three])
  simp [←two_add_one_eq_three, ←mod_eq_zero_iff_dvd] at this

lemma four_le {i : V} (hi : Pow2 i) (lt : 2 < i) : 4 ≤ i := by
  by_contra A
  have : i ≤ 3 := by simpa [←three_add_one_eq_four, ←le_iff_lt_succ] using A
  rcases le_three_iff_eq_zero_or_one_or_two_or_three.mp this with (rfl | rfl | rfl | rfl) <;>
    simp at lt hi

lemma mul_add_lt_of_mul_lt_of_pos {a b p q : V} (hp : Pow2 p) (hq : Pow2 q)
    (h : a * p < q) (hb : b < p) (hbq : b < q) : a * p + b < q := by
  rcases zero_le a with (rfl | pos)
  · simp [hbq]
  have hpq : p < q :=
    lt_of_le_of_lt (le_mul_of_pos_left (a := p) pos) (by simpa [mul_comm a p] using h)
  have : p ∣ q := dvd_of_le hp hq (le_of_lt hpq)
  rcases this with ⟨q, rfl⟩
  have : a < q := lt_of_mul_lt_mul_right (a := p) (by simpa [mul_comm] using h)
  calc
    a * p + b < (a + 1) * p := by simp [add_mul, hb]
    _         ≤ p * q       := by
      rw [mul_comm p q]
      exact mul_le_mul_right (lt_iff_succ_le.mp this)

end Pow2

lemma _root_.LO.Arith.LenBit.mod_pow2 {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h : i < j) :
    LenBit i (a % j) ↔ LenBit i a :=
  LenBit.mod (by rw [←Pow2.le_iff_dvd] <;> simp [pi, pj, ←Pow2.lt_iff_two_mul_le, h])

lemma _root_.LO.Arith.LenBit.add_pow2 {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h : i < j) :
    LenBit i (a + j) ↔ LenBit i a :=
  LenBit.add (by rw [←Pow2.le_iff_dvd] <;> simp [pi, pj, ←Pow2.lt_iff_two_mul_le, h])

lemma _root_.LO.Arith.LenBit.add_pow2_iff_of_lt {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h :
    a < j) :
    LenBit i (a + j) ↔ i = j ∨ LenBit i a := by
  rcases show i < j ∨ i = j ∨ i > j from lt_trichotomy i j with (hij | rfl | hij)
  · simp [LenBit.add_pow2 pi pj hij, hij.ne]
  · simp [LenBit.add_self h]
  · have : a + j < i := calc
      a + j < 2 * j  := by simp[two_mul, h]
      _     ≤ i      := (pj.lt_iff_two_mul_le pi).mp hij
    simp [not_lenbit_of_lt this, not_lenbit_of_lt (show a < i from lt_trans h hij), hij.ne.symm]

lemma lenbit_iff_add_mul {i a : V} (hi : Pow2 i) :
    LenBit i a ↔ ∃ k, ∃ r < i, a = k * (2 * i) + i + r := by
  constructor
  · intro h
    have : 2 * ((a / i) / 2) + 1 = a / i := by
      simpa [LenBit.iff_rem.mp h] using div_add_mod (a / i) 2
    have : a = ((a / i) / 2) * (2 * i) + i + (a % i) := calc
      a = i * (a / i) + (a % i)                  := Eq.symm <| div_add_mod a i
      _ = i * (2 * ((a / i) / 2) + 1) + (a % i) := by simp [this]
      _ = ((a / i) / 2) * (2 * i) + i + (a % i) := by
        simp [mul_add, ←mul_assoc, mul_comm i 2, mul_comm (2 * i)]
    exact ⟨(a / i) / 2, a % i, by simp [hi.pos], this⟩
  · rintro ⟨k, r, h, rfl⟩
    simp [LenBit.iff_rem, ←mul_assoc, add_assoc, div_mul_add_self, hi.pos, h]

lemma not_lenbit_iff_add_mul {i a : V} (hi : Pow2 i) :
    ¬LenBit i a ↔ ∃ k, ∃ r < i, a = k * (2 * i) + r := by
  constructor
  · intro h
    have : 2 * ((a / i) / 2) = a / i := by
      simpa [not_lenbit_iff_rem.mp h] using div_add_mod (a / i) 2
    have : a = ((a / i) / 2) * (2 * i) + (a % i) := calc
      a = i * (a / i) + (a % i)              := Eq.symm <| div_add_mod a i
      _ = i * (2 * ((a / i) / 2)) + (a % i) := by simp [this]
      _ = ((a / i) / 2) * (2 * i) + (a % i) := by
        simp [←mul_assoc, mul_comm i 2, mul_comm (2 * i)]
    exact ⟨(a / i) / 2, a % i, by simp [hi.pos], this⟩
  · rintro ⟨k, r, h, rfl⟩
    simp [not_lenbit_iff_rem, ←mul_assoc, div_mul_add_self, hi.pos, h]

lemma lenbit_mul_add {i j a r : V} (pi : Pow2 i) (pj : Pow2 j) (hr : r < j) :
    LenBit (i * j) (a * j + r) ↔ LenBit i a := by
  by_cases h : LenBit i a
  · simp only [h, iff_true]
    rcases (lenbit_iff_add_mul pi).mp h with ⟨a, b, hb, rfl⟩
    have : b * j + r < i * j :=
      pj.mul_add_lt_of_mul_lt_of_pos (by simp[pi,
        pj]) (Arith.mul_lt_mul b i j hb pj.pos) hr (lt_of_lt_of_le hr <| le_mul_of_pos_left <|
            pi.pos)
    exact (lenbit_iff_add_mul (by simp [pi, pj])).mpr ⟨a, b * j + r, this, by simp [add_mul,
      add_assoc, mul_assoc]⟩
  · simp only [h, iff_false]
    rcases (not_lenbit_iff_add_mul pi).mp h with ⟨a, b, hb, rfl⟩
    have : b * j + r < i * j :=
      pj.mul_add_lt_of_mul_lt_of_pos (by simp[pi,
        pj]) (Arith.mul_lt_mul b i j hb pj.pos) hr (lt_of_lt_of_le hr <| le_mul_of_pos_left <|
            pi.pos)
    exact (not_lenbit_iff_add_mul (by simp [pi, pj])).mpr ⟨a, b * j + r, this, by simp [add_mul,
      add_assoc, mul_assoc]⟩

lemma lenbit_add_pow2_iff_of_not_lenbit {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h : ¬LenBit j a) :
    LenBit i (a + j) ↔ i = j ∨ LenBit i a := by
  rcases show i < j ∨ i = j ∨ i > j from lt_trichotomy i j with (hij | rfl | hij)
  · simp [LenBit.add_pow2 pi pj hij, hij.ne]
  · simp [LenBit.add_self_of_not_lenbit pi.pos, h]
  · simp only [ne_of_gt hij, false_or]
    have : 2 * j ∣ i := Pow2.dvd_of_le (by simp [pj]) pi <| (pj.lt_iff_two_mul_le pi).mp hij
    rcases this with ⟨i, rfl⟩
    rcases (not_lenbit_iff_add_mul pj).mp h with ⟨a, r, hr, rfl⟩
    have pi' : Pow2 i := (Pow2.mul_iff.mp pi).2
    have pj' : Pow2 j := (Pow2.mul_iff.mp (Pow2.mul_iff.mp pi).1).2
    calc
      LenBit (2 * j * i) (a * (2 * j) + r + j) ↔ LenBit (i * (2 * j)) (a * (2 * j) + (r + j)) := by
        simp [mul_comm (2 * j), add_assoc]
      _                                        ↔ LenBit i a                                   :=
        lenbit_mul_add pi' (by simpa using pj') (by simp [two_mul, hr])
      _                                        ↔ LenBit (i * (2 * j)) (a * (2 * j) + r)       :=
        Iff.symm <| lenbit_mul_add pi' (by simpa using pj') (lt_of_lt_of_le hr <| by simp)
      _                                        ↔ LenBit (2 * j * i) (a * (2 * j) + r)         := by
        simp [mul_comm]

lemma lenbit_sub_pow2_iff_of_lenbit {a i j : V} (pi : Pow2 i) (pj : Pow2 j) (h : LenBit j a) :
    LenBit i (a - j) ↔ i ≠ j ∧ LenBit i a := by
  generalize ha' : a - j = a'
  have h' : ¬LenBit j a' := by simpa [←ha'] using LenBit.sub_self_of_lenbit pj.pos h
  have : a = a' + j := by simp [←ha', sub_add_self_of_le h.le]
  rcases this with rfl
  have : LenBit i (a' + j) ↔ i = j ∨ LenBit i a' := lenbit_add_pow2_iff_of_not_lenbit pi pj h'
  rw [this]
  simp only [and_or_left, ne_eq]
  constructor
  · intro hi
    exact Or.inr ⟨by rintro rfl; exact h' hi, hi⟩
  · rintro (⟨hij, hij'⟩ | ⟨_, hi⟩)
    · contradiction
    · exact hi

end «lp_section_3»

end Arith
end LO

end «lp_nc_section_1»
