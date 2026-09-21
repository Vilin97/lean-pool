/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Family

import LeanPool.ConwayRefinement.CombinatorialGames.Tactic.OrdinalAlias
import Mathlib.Tactic.Abel

/-!
# Natural operations on ordinals

The goal of this file is to define natural addition and multiplication on ordinals, also known as
the Hessenberg sum and product, and provide a basic API. The natural addition of two ordinals
`a + b` is recursively defined as the least ordinal greater than `a' + b` and `a + b'` for `a' < a`
and `b' < b`. The natural multiplication `a * b` is likewise recursively defined as the least
ordinal such that `a * b + a' * b'` is greater than `a' * b + a * b'` for any `a' < a` and
`b' < b`.

These operations give the ordinals a `CommSemiring` + `IsStrictOrderedRing` structure. To make the
best use of it, we define them on a type alias `NatOrdinal`.

An equivalent characterization explains the relevance of these operations to game theory: they are
the restrictions of surreal addition and multiplication to the ordinals.

## Implementation notes

To reduce API duplication, we opt not to implement operations on `NatOrdinal` on `Ordinal`. The
order isomorphisms `NatOrdinal.of` and `NatOrdinal.val` allow us to cast between them whenever
needed.

For similar reasons, most results about ordinals and games are written using `NatOrdinal` rather
than `Ordinal` (except when `Nimber` would make more sense).
-/

universe u v

open Order Set

public noncomputable section

/-! ### Basic casts between `Ordinal` and `NatOrdinal` -/

ordinal_alias!
  /-- A type synonym for ordinals with natural addition and multiplication. -/ NatOrdinal

namespace NatOrdinal

variable {a b c d a' b' c' : NatOrdinal.{u}}

/-! ### Natural addition -/

private def add (a b : NatOrdinal.{u}) : NatOrdinal.{u} :=
  max (⨆ x : Iio a, succ (add x.1 b)) (⨆ x : Iio b, succ (add a x.1))
termination_by (a, b)
decreasing_by all_goals cases x; decreasing_tactic

#adaptation_note /-- noncomputable is now needed -/ in
/-- Natural addition on ordinals `a + b`, also known as the Hessenberg sum, is recursively defined
as the least ordinal greater than `a' + b` and `a + b'` for all `a' < a` and `b' < b`. In contrast
to normal ordinal addition, it is commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
@[no_expose] noncomputable instance : Add NatOrdinal := ⟨add⟩

theorem add_def (a b : NatOrdinal) :
    a + b = max (⨆ x : Iio a, succ (x.1 + b)) (⨆ x : Iio b, succ (a + x.1)) := by
  change add .. = _
  rw [add]
  rfl

theorem lt_add_iff : a < b + c ↔ (∃ b' < b, a ≤ b' + c) ∨ ∃ c' < c, a ≤ b + c' := by
  rw [add_def]
  simp [NatOrdinal.lt_iSup_iff]

theorem add_le_iff : b + c ≤ a ↔ (∀ b' < b, b' + c < a) ∧ ∀ c' < c, b + c' < a := by
  rw [← not_lt, lt_add_iff]
  simp

instance : AddLeftStrictMono NatOrdinal where
  elim _a _b _c h := lt_add_iff.2 (.inr ⟨_, h, le_rfl⟩)

instance : AddRightStrictMono NatOrdinal where
  elim _a _b _c h := lt_add_iff.2 (.inl ⟨_, h, le_rfl⟩)

instance : AddLeftMono NatOrdinal :=
  addLeftMono_of_addLeftStrictMono _

instance : AddRightMono NatOrdinal :=
  addRightMono_of_addRightStrictMono _

private theorem add_comm' (a b : NatOrdinal) : a + b = b + a := by
  rw [add_def, add_def, max_comm]
  congr with x <;> cases x <;> exact congrArg _ (add_comm' ..)
termination_by (a, b)

private theorem add_zero' (a : NatOrdinal) : a + 0 = a := by
  rw [add_def, ciSup_of_empty fun _ : Iio 0 ↦ _, max_bot_right]
  convert iSup_succ a with x
  cases x
  exact add_zero' _
termination_by a

private theorem iSup_add_of_monotone (f : NatOrdinal.{u} → NatOrdinal.{u}) (h : Monotone f) :
    ⨆ x : Iio (a + b), f x = max (⨆ a' : Iio a, f (a'.1 + b)) (⨆ b' : Iio b, f (a + b'.1)) := by
  apply (max_le _ _).antisymm'
  · rw [iSup_le_iff]
    rintro ⟨i, hi⟩
    obtain ⟨x, hx, hi⟩ | ⟨x, hx, hi⟩ := lt_add_iff.1 hi
    · exact le_max_of_le_left ((h hi).trans <| le_iSup (fun x : Iio a ↦ _) ⟨x, hx⟩)
    · exact le_max_of_le_right ((h hi).trans <| le_iSup (fun x : Iio b ↦ _) ⟨x, hx⟩)
  all_goals
    refine csSup_le_csSup' (bddAbove_of_small _) fun _ ↦ ?_
    aesop

private theorem add_assoc' (a b c : NatOrdinal) : a + b + c = a + (b + c) := by
  rw [add_def, add_def a (b + c)]
  rw [iSup_add_of_monotone (fun _ ↦ succ _) (succ_mono.comp add_right_mono),
    iSup_add_of_monotone (fun _ ↦ succ _) (succ_mono.comp add_left_mono), max_assoc]
  congr with x <;> cases x <;> exact congrArg _ (add_assoc' ..)
termination_by (a, b, c)

instance : AddCommMonoid NatOrdinal where
  add_zero := private add_zero'
  zero_add x := by rw [add_comm', add_zero']
  add_comm := private add_comm'
  add_assoc := private add_assoc'
  nsmul := nsmulRec

instance : IsOrderedCancelAddMonoid NatOrdinal where
  add_le_add_left _ _ := add_le_add_left
  le_of_add_le_add_left a b c h := by
    by_contra! h'
    exact h.not_gt (add_lt_add_right h' a)

theorem le_add_left : a ≤ b + a := by simp
theorem le_add_right : a ≤ a + b := by simp

@[simp]
theorem add_eq_zero_iff : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · repeat rw [← le_zero_iff]
    exact ⟨le_add_right.trans_eq h, le_add_left.trans_eq h⟩
  · simp +contextual

private theorem succ_eq_add_one' (a : NatOrdinal) : succ a = a + 1 := by
  rw [add_def, ciSup_unique (s := fun _ : Iio 1 ↦ _), Iio_one_default_eq, add_zero,
    eq_comm, max_eq_right_iff, iSup_le_iff]
  rintro ⟨i, hi⟩
  rwa [← succ_eq_add_one', succ_le_succ_iff, succ_le_iff]
termination_by a

instance : SuccAddOrder NatOrdinal := ⟨by exact succ_eq_add_one'⟩

@[simp] theorem of_add_one (a : Ordinal) : of (a + 1) = of a + 1 := succ_eq_add_one _
@[simp] theorem val_add_one (a : NatOrdinal) : val (a + 1) = val a + 1 := (succ_eq_add_one a).symm

instance : AddMonoidWithOne NatOrdinal where
  natCast n := of n
  natCast_succ n := by simp

@[simp] theorem of_natCast (n : ℕ) : of n = n := rfl
@[simp] theorem val_natCast (n : ℕ) : val n = n := rfl

@[simp]
theorem natCast_image_Iio (n : ℕ) : Nat.cast '' Iio n = Iio (n : NatOrdinal) :=
  Ordinal.natCast_image_Iio n

@[simp]
theorem forall_lt_natCast {P : NatOrdinal → Prop} {n : ℕ} : (∀ a < ↑n, P a) ↔ ∀ a < n, P a := by
  change (∀ a ∈ Iio _, _) ↔ ∀ a ∈ Iio _, _
  simp [← natCast_image_Iio]

@[simp]
theorem exists_lt_natCast {P : NatOrdinal → Prop} {n : ℕ} : (∃ a < ↑n, P a) ↔ ∃ a < n, P a := by
  change (∃ a ∈ Iio _, _) ↔ ∃ a ∈ Iio _, _
  simp [← natCast_image_Iio]

theorem lt_omega0 {o : NatOrdinal} : o < of .omega0 ↔ ∃ n : ℕ, o = n :=
  Ordinal.lt_omega0

theorem natCast_lt_omega0 (n : ℕ) : n < of .omega0 :=
  Ordinal.natCast_lt_omega0 n

instance : CharZero NatOrdinal where
  cast_injective m n h := by
    apply_fun val at h
    simpa using h

@[simp]
theorem of_add_natCast (a : Ordinal) (n : ℕ) : of (a + n) = of a + n := by
  induction n with
  | zero => simp
  | succ n IH => simp [← add_assoc, IH]

@[simp]
theorem val_add_natCast (a : NatOrdinal) (n : ℕ) : val (a + n) = val a + n :=
  (of_add_natCast _ n).symm

/-- A version of `oadd_le_add` stated in terms of `Ordinal`. -/
theorem oadd_le_add' (a b : Ordinal) : a + b ≤ val (of a + of b) := by
  induction b using Ordinal.limitRecOn with
  | zero => simp
  | add_one c IH => simpa [← add_assoc] using add_le_add_left IH 1
  | limit c hc IH =>
    rw [(Ordinal.isNormal_add_right a).apply_of_isSuccLimit hc, Ordinal.iSup_le_iff]
    rintro ⟨i, hi⟩
    exact (IH i hi).trans (add_le_add_right hi.le (of a))

theorem oadd_le_add (a b : NatOrdinal) : of (a.val + b.val) ≤ a + b :=
  oadd_le_add' ..

/-! ### Natural multiplication -/

private def mul (a b : NatOrdinal.{u}) : NatOrdinal.{u} :=
  sInf {c | ∀ a' < a, ∀ b' < b, mul a' b + mul a b' < c + mul a' b'}
termination_by (a, b)

#adaptation_note /-- noncomputable is now needed -/ in
/-- Natural multiplication on ordinals `a * b`, also known as the Hessenberg product, is recursively
defined as the least ordinal such that `a * b + a' * b'` is greater than `a' * b + a * b'` for all
`a' < a` and `b < b'`. In contrast to normal ordinal multiplication, it is commutative and
distributive (over natural addition).

Natural multiplication can equivalently be characterized as the ordinal resulting from multiplying
the Cantor normal forms of `a` and `b` as if they were polynomials in `ω`. Addition of exponents is
done via natural addition. -/
@[no_expose] noncomputable instance : Mul NatOrdinal := ⟨mul⟩

theorem mul_def (a b : NatOrdinal) :
    a * b = sInf {c | ∀ a' < a, ∀ b' < b, a' * b + a * b' < c + a' * b'} := by
  change mul .. = _
  rw [mul]
  rfl

/-- The set in the definition of `mul` is nonempty. -/
private theorem mul_nonempty (a b : NatOrdinal.{u}) :
    {c : NatOrdinal.{u} | ∀ a' < a, ∀ b' < b, a' * b + a * b' < c + a' * b'}.Nonempty := by
  obtain ⟨c, hc⟩ : BddAbove ((fun x ↦ x.1 * b + a * x.2) '' Set.Iio a ×ˢ Set.Iio b) :=
    bddAbove_of_small _
  exact ⟨_, fun x hx y hy ↦
    (lt_succ_of_le <| hc <| Set.mem_image_of_mem _ <| Set.mk_mem_prod hx hy).trans_le le_add_right⟩

theorem mul_add_lt (ha : a' < a) (hb : b' < b) : a' * b + a * b' < a * b + a' * b' := by
  rw [mul_def a b]
  exact csInf_mem (mul_nonempty a b) a' ha b' hb

theorem mul_add_le (ha : a' ≤ a) (hb : b' ≤ b) : a' * b + a * b' ≤ a * b + a' * b' := by
  obtain rfl | ha := ha.eq_or_lt; · rfl
  obtain rfl | hb := hb.eq_or_lt; · rw [add_comm]
  exact (mul_add_lt ha hb).le

theorem lt_mul_iff : c < a * b ↔ ∃ a' < a, ∃ b' < b, c + a' * b' ≤ a' * b + a * b' := by
  refine ⟨fun h ↦ ?_, fun ⟨a', ha, b', hb, h⟩ ↦ ?_⟩
  · rw [mul_def] at h
    simpa using notMem_of_lt_csInf h ⟨0, fun _ _ => bot_le⟩
  · rw [← add_lt_add_iff_right]
    exact h.trans_lt (mul_add_lt ha hb)

theorem mul_le_iff : a * b ≤ c ↔ ∀ a' < a, ∀ b' < b, a' * b + a * b' < c + a' * b' := by
  simpa using lt_mul_iff.not

private theorem mul_comm' (a b : NatOrdinal) : a * b = b * a := by
  rw [mul_def, mul_def]
  congr with x; constructor <;> intro H c hc d hd
  · rw [add_comm, ← mul_comm', ← mul_comm' a, ← mul_comm' d]
    exact H _ hd _ hc
  · rw [add_comm, mul_comm', mul_comm' c, mul_comm' c]
    exact H _ hd _ hc
termination_by (a, b)

instance : CommMagma NatOrdinal where
  mul_comm := private mul_comm'

private theorem mul_zero' (a : NatOrdinal) : a * 0 = 0 := by
  rw [← le_zero_iff, mul_le_iff]
  simp

instance : MulZeroClass NatOrdinal where
  mul_zero := private mul_zero'
  zero_mul a := by rw [mul_comm', mul_zero']

private theorem mul_one' (a : NatOrdinal) : a * 1 = a := by
  rw [mul_def]
  convert csInf_Ici
  ext b
  refine ⟨fun H ↦ le_of_forall_lt (a := a) fun c hc ↦ ?_, fun ha c hc ↦ ?_⟩
  · simpa [mul_one' c] using H c hc
  · simpa [mul_one' c] using hc.trans_le ha
termination_by a

instance : MulZeroOneClass NatOrdinal where
  mul_one := private mul_one'
  one_mul a := by rw [mul_comm', mul_one']

instance : PosMulStrictMono NatOrdinal where
  mul_lt_mul_of_pos_left a ha b c h := lt_mul_iff.2 ⟨0, ha, b, h, by simp⟩

instance : MulPosStrictMono NatOrdinal where
  mul_lt_mul_of_pos_right a ha b c h := lt_mul_iff.2 ⟨b, h, 0, ha, by simp⟩

instance : MulLeftMono NatOrdinal where
  elim a b c h := by
    obtain rfl | h₁ := h.eq_or_lt; · simp
    obtain rfl | h₂ := eq_zero_or_pos a; · simp
    exact (mul_lt_mul_of_pos_left h₁ h₂).le

instance : MulRightMono NatOrdinal where
  elim a b c h := by convert mul_le_mul_right h a using 1 <;> exact mul_comm ..

private theorem mul_add (a b c : NatOrdinal) : a * (b + c) = a * b + a * c := by
  refine le_antisymm (mul_le_iff.2 fun a' ha d hd => ?_)
    (add_le_iff.2 ⟨fun d hd => ?_, fun d hd => ?_⟩)
  · rw [mul_add]
    rcases lt_add_iff.1 hd with (⟨b', hb, hd⟩ | ⟨c', hc, hd⟩)
    · have := add_lt_add_of_lt_of_le (mul_add_lt ha hb) (mul_add_le ha.le hd)
      rw [mul_add, mul_add] at this
      grind
    · have := add_lt_add_of_le_of_lt (mul_add_le ha.le hd) (mul_add_lt ha hc)
      rw [mul_add, mul_add] at this
      grind
  · rcases lt_mul_iff.1 hd with ⟨a', ha, b', hb, hd⟩
    have := add_lt_add_of_le_of_lt hd (mul_add_lt ha (add_lt_add_left hb c))
    rw [mul_add, mul_add, mul_add a'] at this
    grind
  · rcases lt_mul_iff.1 hd with ⟨a', ha, c', hc, hd⟩
    have := add_lt_add_of_lt_of_le (mul_add_lt ha (add_lt_add_right hc b)) hd
    rw [mul_add, mul_add, mul_add a'] at this
    grind
termination_by (a, b, c)

instance : Distrib NatOrdinal where
  left_distrib := private mul_add
  right_distrib a b c := by rw [mul_comm, mul_add, mul_comm, mul_comm c]

theorem mul_add_lt₃ (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' * b * c + a * b' * c + a * b * c' + a' * b' * c' <
      a * b * c + a' * b' * c + a' * b * c' + a * b' * c' := by
  simpa only [add_mul, ← add_assoc] using mul_add_lt (mul_add_lt ha hb) hc

theorem mul_add_le₃ {a' b' c' : NatOrdinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' * b * c + a * b' * c + a * b * c' + a' * b' * c' ≤
      a * b * c + a' * b' * c + a' * b * c' + a * b' * c' := by
  simpa only [add_mul, ← add_assoc] using mul_add_le (mul_add_le ha hb) hc

private theorem mul_add_lt₃' {a' b' c' : NatOrdinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' * (b * c) + a * (b' * c) + a * (b * c') + a' * (b' * c') <
      a * (b * c) + a' * (b' * c) + a' * (b * c') + a * (b' * c') := by
  simp only [mul_comm _ (_ * _)]
  convert mul_add_lt₃ hb hc ha using 1 <;> abel_nf

theorem lt_mul_iff₃ : d < a * b * c ↔ ∃ a' < a, ∃ b' < b, ∃ c' < c,
    d + a' * b' * c + a' * b * c' + a * b' * c' ≤
      a' * b * c + a * b' * c + a * b * c' + a' * b' * c' := by
  refine ⟨fun h ↦ ?_, fun ⟨a', ha, b', hb, c', hc, h⟩ ↦ ?_⟩
  · rcases lt_mul_iff.1 h with ⟨e, he, c', hc, H₁⟩
    rcases lt_mul_iff.1 he with ⟨a', ha, b', hb, H₂⟩
    refine ⟨a', ha, b', hb, c', hc, ?_⟩
    have := add_le_add H₁ (mul_add_le H₂ hc.le)
    simp only [add_mul, add_assoc] at this
    rw [add_left_comm, add_left_comm d, add_left_comm, add_le_add_iff_left,
      add_left_comm (a * b' * c), add_left_comm (a' * b * c), add_left_comm (a * b * c'),
      add_le_add_iff_left, add_left_comm (a * b * c'), add_left_comm (a * b * c')] at this
    simpa only [add_assoc]
  · have := h.trans_lt (mul_add_lt₃ ha hb hc)
    repeat rw [add_lt_add_iff_right] at this
    assumption

theorem mul_le_iff₃ : a * b * c ≤ d ↔ ∀ a' < a, ∀ b' < b, ∀ c' < c,
    a' * b * c + a * b' * c + a * b * c' + a' * b' * c' <
      d + a' * b' * c + a' * b * c' + a * b' * c' := by
  simpa using lt_mul_iff₃.not

private theorem mul_le_iff₃' : a * (b * c) ≤ d ↔ ∀ a' < a, ∀ b' < b, ∀ c' < c,
    a' * (b * c) + a * (b' * c) + a * (b * c') + a' * (b' * c') <
      d + a' * (b' * c) + a' * (b * c') + a * (b' * c') := by
  simp only [mul_comm _ (_ * _), mul_le_iff₃]
  constructor <;> intro h a' ha b' hb c' hc
  · convert h b' hb c' hc a' ha using 1 <;> abel_nf
  · convert h c' hc a' ha b' hb using 1 <;> abel_nf

private theorem mul_assoc (a b c : NatOrdinal) : a * b * c = a * (b * c) := by
  apply le_antisymm
  · rw [mul_le_iff₃]
    intro a' ha b' hb c' hc
    repeat rw [mul_assoc]
    exact mul_add_lt₃' ha hb hc
  · rw [mul_le_iff₃']
    intro a' ha b' hb c' hc
    repeat rw [← mul_assoc]
    exact mul_add_lt₃ ha hb hc
termination_by (a, b, c)

instance : CommSemiring NatOrdinal where
  mul_assoc := private mul_assoc

instance : IsStrictOrderedRing NatOrdinal where

/-- A version of `omul_le_mul` stated in terms of `Ordinal`. -/
theorem omul_le_mul' (a b : Ordinal) : a * b ≤ val (of a * of b) := by
  induction b using Ordinal.limitRecOn with
  | zero => simp
  | add_one c IH => simpa [mul_add_one] using (add_left_mono IH).trans (oadd_le_add' ..)
  | limit c hc IH =>
    obtain rfl | ha := eq_zero_or_pos a
    · simp
    · rw [(Ordinal.isNormal_mul_right ha).apply_of_isSuccLimit hc, Ordinal.iSup_le_iff]
      rintro ⟨i, hi⟩
      exact (IH i hi).trans (mul_le_mul_right hi.le (of a))

theorem omul_le_mul (a b : NatOrdinal) : of (a.val * b.val) ≤ a * b :=
  omul_le_mul' ..

end NatOrdinal
