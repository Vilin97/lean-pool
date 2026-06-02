/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/

import LeanPool.ZFLean.Integers

/-! # ZFC Rational Numbers

This file defines the rational numbers in ZFC, based on the integers and using the `ZFInt` type.

-/

namespace ZFSet
/-- Imported ZFLean declaration. -/
abbrev ZFInt' := {x : ZFInt // x ≠ 0}

/-- The equivalence relation on `ℤ × ℤ⋆` that defines the rational numbers. -/
protected abbrev qrel (p q : ZFInt × ZFInt') : Prop := p.1 * q.2 = p.2 * q.1

protected theorem qrel_eq : Equivalence ZFSet.qrel where
  refl x := ZFInt.mul_comm x.1 x.2
  symm h := by
    unfold ZFSet.qrel at h ⊢
    rw [ZFInt.mul_comm, ←h, ZFInt.mul_comm]
  trans := by
    rintro ⟨p, q, hq⟩ ⟨u, v, hv⟩ ⟨s, t, ht⟩ hpq huv
    dsimp [ZFSet.qrel] at hpq huv ⊢
    -- have : p * v * u * t = q * u * s * v := by
    have : p * t * u * v = q * s * u * v := by
      suffices p * v * u * t = q * u * s * v by
        rw [
          mul_assoc, mul_assoc,
          mul_comm t, mul_comm u,
          ←mul_assoc, ←mul_assoc,
          this,
          mul_assoc, mul_assoc,
          mul_comm u, mul_assoc, mul_comm v,
          ←mul_assoc, ←mul_assoc]
      rw [hpq, mul_assoc, huv, mul_comm v s, ← mul_assoc]
    conv at this =>
      conv => lhs; rw [mul_assoc]
      conv => rhs; rw [mul_assoc]
    by_cases u_mul_v : u * v = 0
    · rw [ZFInt.mul_comm] at u_mul_v
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero u_mul_v hv
      rw [ZFInt.mul_zero, ZFInt.mul_comm] at hpq
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero hpq hv
      rw [ZFInt.zero_mul] at huv
      symm at huv
      obtain ⟨⟩ := ZFInt.mul_eq_zero_of_ne_zero huv hv
      rw [ZFInt.mul_zero, ZFInt.zero_mul]
    · rwa [ZFInt.mul_right_cancel_iff u_mul_v] at this

/-- `ℤ × ℤ⋆` equipped with `qrel` is a setoid. -/
protected instance instSetoidZFIntZFInt' : Setoid (ZFInt × ZFInt') where
  r := ZFSet.qrel
  iseqv := ZFSet.qrel_eq

/-- `ℚ` is defined as `ℤ × ℤ⋆` quotiented by `qrel` -/
abbrev ZFRat := Quotient ZFSet.instSetoidZFIntZFInt'

namespace ZFRat
/-- Imported ZFLean declaration. -/
def mk : ZFInt × ZFInt' → ZFRat := Quotient.mk''

@[simp]
theorem mk_eq (x : ZFInt × ZFInt') : @Eq ZFRat ⟦x⟧ (mk x) := rfl

@[simp]
theorem mk_out : ∀ x : ZFRat, mk x.out = x := Quotient.out_eq

theorem eq {x y : ZFInt × ZFInt'} : mk x = mk y ↔ ZFSet.qrel x y := Quotient.eq

theorem sound {x y : ZFInt × ZFInt'} (h : ZFSet.qrel x y) : mk x = mk y := Quotient.sound h
theorem exact {x y : ZFInt × ZFInt'} : mk x = mk y → ZFSet.qrel x y := Quotient.exact
/-- Imported ZFLean declaration. -/
abbrev zero : ZFRat := mk (0, ⟨1, ZFInt.one_ne_zero⟩)
/-- Imported ZFLean declaration. -/
abbrev one : ZFRat := mk (1, ⟨1, ZFInt.one_ne_zero⟩)

protected instance : Zero ZFRat := ⟨zero⟩
protected instance : One ZFRat := ⟨one⟩

instance : Inhabited ZFRat := ⟨0⟩

theorem zero_eq : (0 : ZFRat) = mk (0, ⟨1, ZFInt.one_ne_zero⟩) := rfl
theorem one_eq : (1 : ZFRat) = mk (1, ⟨1, ZFInt.one_ne_zero⟩) := rfl

theorem mk_eq_zero_iff {n m} : ZFRat.mk (n,m) = 0 ↔ n = 0 where
  mp := by
    intro h
    rw [zero_eq, eq, ZFSet.qrel] at h
    simpa only [mul_one, ne_eq, mul_zero] using h
  mpr := by
    rintro rfl
    apply ZFRat.sound
    rw [ZFSet.qrel, mul_one, mul_zero]

theorem mk_eq_one_iff {n m} : ZFRat.mk (n,m) = 1 ↔ n = m where
  mp := by
    intro h
    rw [one_eq, eq, ZFSet.qrel] at h
    simpa only [ne_eq, mul_one] using h
  mpr := by
    rintro rfl
    apply ZFRat.sound
    rw [ZFSet.qrel, mul_one]

theorem one_ne_zero : (1 : ZFRat) ≠ 0 := by
  intro h
  rw [one_eq, zero_eq, eq, ZFSet.qrel, mul_one, mul_zero] at h
  nomatch ZFInt.one_ne_zero h
/-- Imported ZFLean declaration. -/
noncomputable abbrev add (n m : ZFRat) : ZFRat :=
  Quotient.liftOn₂ n m (fun ⟨a, b⟩ ⟨c, d⟩ ↦
    mk (a * d + b * c, ⟨b.1 * d.1, fun c ↦ nomatch d.2 (ZFInt.mul_eq_zero_of_ne_zero c b.2)⟩))
    fun ⟨x₁, x₂, hx₂⟩ ⟨y₁, y₂, hy₂⟩ ⟨u₁, u₂, hu₂⟩ ⟨v₁, v₂, hv₂⟩ hxu hyv ↦ sound (by
      have h1 : x₁ * u₂ = x₂ * u₁ := hxu
      have h2 : y₁ * v₂ = y₂ * v₁ := hyv
      simp only [ZFSet.qrel]
      conv_lhs =>
        rw [right_distrib]
        conv =>
          lhs
          rw [
            ←mul_assoc, mul_assoc x₁, mul_comm y₂, ←mul_assoc,
            h1, mul_assoc x₂, mul_comm u₁, ←mul_assoc, mul_assoc (x₂ * y₂)]
        conv =>
          rhs
          rw [
            mul_comm u₂, ←mul_assoc, mul_assoc x₂, h2,
            ←mul_assoc, mul_assoc, mul_comm v₁, ←mul_assoc, mul_assoc (x₂ * y₂)]
      rw [←left_distrib])

protected noncomputable instance : Add ZFRat := ⟨ZFRat.add⟩
theorem add_eq (n m : ZFInt × ZFInt') :
  mk n + mk m = mk (n.1 * m.2 + n.2 * m.1,
    ⟨n.2.1 * m.2.1, fun c ↦ nomatch m.2.2 (ZFInt.mul_eq_zero_of_ne_zero c n.2.2)⟩) := rfl

theorem add_assoc (n m k : ZFRat) : n + (m + k) = n + m + k := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  induction k using Quotient.ind
  rename_i n m k
  obtain ⟨n₁, n₂, hn₂⟩ := n
  obtain ⟨m₁, m₂, hm₂⟩ := m
  obtain ⟨k₁, k₂, hk₂⟩ := k
  apply ZFRat.sound
  ring

theorem add_comm (n m : ZFRat) : n + m = m + n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  rename_i n m
  obtain ⟨n₁, n₂, hn₂⟩ := n
  obtain ⟨m₁, m₂, hm₂⟩ := m
  apply ZFRat.sound
  ring

lemma add_left_comm (n m k : ZFRat) : n + (m + k) = m + (n + k) := by
  rw [add_assoc, add_assoc, add_comm n]

lemma add_right_comm (n m k : ZFRat) : (n + m) + k = (n + k) + m := by
  rw [← add_assoc, add_comm m, add_assoc]

theorem add_zero {x : ZFRat} : x + 0 = x := by
  induction x using Quotient.ind
  simp_rw [mk_eq, zero_eq, ZFRat.add_eq, mul_one, ne_eq, mul_zero, ZFInt.add_zero]

theorem zero_add {x : ZFRat} : 0 + x = x := by
  rw [add_comm, add_zero]
/-- Imported ZFLean declaration. -/
protected abbrev neg (n : ZFRat) : ZFRat := Quotient.liftOn n (fun ⟨x, y⟩ => mk (-x, y))
  fun ⟨x, y, hy⟩ ⟨u, v, hv⟩ h ↦ sound (ZFSet.qrel_eq.symm (by
    dsimp [HasEquiv.Equiv, instHasEquivOfSetoid, ZFSet.instSetoidZFIntZFInt'] at h
    simp only [ZFSet.qrel] at h ⊢
    rw [←ZFInt.neg_mul_distrib, mul_comm, ←h, ZFInt.neg_mul_distrib, mul_comm]))

protected instance : Neg ZFRat := ⟨ZFRat.neg⟩
theorem neg_eq (n : ZFInt × ZFInt') : -mk n = mk (-n.1, n.2) := rfl

theorem neg_neg (n : ZFRat) : -(-n) = n := by
  induction n using Quotient.ind
  apply sound
  rw [_root_.neg_neg]
  exact eq.mp rfl

theorem neg_zero : -(0 : ZFRat) = 0 := rfl

theorem neg_inj {a b : ZFRat} : -a = -b ↔ a = b :=
  ⟨fun h => by rw [← neg_neg a, ← neg_neg b, h], congrArg _⟩

theorem neg_eq_zero {a : ZFRat} : -a = 0 ↔ a = 0 := ZFRat.neg_inj (b := 0)
theorem neg_ne_zero {a : ZFRat} : -a ≠ 0 ↔ a ≠ 0 := not_congr neg_eq_zero

theorem add_left_neg {a : ZFRat} : -a + a = 0 := by
  induction a using Quotient.ind
  apply sound
  ring

theorem add_right_neg (a : ZFRat) : a + -a = 0 := by
  rw [add_comm]
  exact add_left_neg

theorem neg_eq_of_add_eq_zero {a b : ZFRat} (h : a + b = 0) : -a = b := by
  rw [← @add_zero (-a), ← h, add_assoc, add_left_neg, zero_add]

theorem eq_neg_of_eq_neg {a b : ZFRat} (h : a = -b) : b = -a := by
  rw [h, neg_neg]

theorem eq_neg_comm {a b : ZFRat} : a = -b ↔ b = -a := ⟨eq_neg_of_eq_neg, eq_neg_of_eq_neg⟩

theorem neg_eq_comm {a b : ZFRat} : -a = b ↔ -b = a := by
  rw [eq_comm, eq_neg_comm, eq_comm]

theorem neg_add_cancel_left (a b : ZFRat) : -a + (a + b) = b := by
  rw [add_assoc, add_left_neg, zero_add]

theorem add_neg_cancel_left (a b : ZFRat) : a + (-a + b) = b := by
  rw [add_assoc, add_right_neg, zero_add]

theorem add_neg_cancel_right (a b : ZFRat) : a + b + -b = a := by
  rw [← add_assoc, add_right_neg, add_zero]

theorem neg_add_cancel_right (a b : ZFRat) : a + -b + b = a := by
  rw [← add_assoc, add_left_neg, add_zero]

theorem add_left_cancel {a b c : ZFRat} (h : a + b = a + c) : b = c := by
  have h₁ : -a + (a + b) = -a + (a + c) := by rw [h]
  simp only [add_assoc, add_left_neg, zero_add] at h₁
  exact h₁

theorem neg_add {a b : ZFRat} : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_right_neg, add_comm a, add_assoc, ← add_assoc b, add_right_neg, add_zero, add_right_neg]


/-- Rational subtraction in the ZF rational model. -/
noncomputable abbrev sub (n m : ZFRat) : ZFRat := n + -m
/-- Imported ZFLean declaration. -/
protected noncomputable instance : Sub ZFRat := ⟨ZFRat.sub⟩
theorem sub_eq (n m : ZFInt × ZFInt') :
  mk n - mk m = mk (n.1 * m.2 - m.1 * n.2, ⟨n.2 * m.2,
    fun c ↦ nomatch m.2.2 (ZFInt.mul_eq_zero_of_ne_zero c n.2.2)⟩) := by
  apply sound
  ring

theorem sub_eq_add_neg {a b : ZFRat} : a - b = a + -b := rfl

theorem add_neg_one (i : ZFRat) : i + -1 = i - 1 := rfl

theorem sub_self (a : ZFRat) : a - a = 0 := by rw [sub_eq_add_neg, add_right_neg]

theorem sub_zero (a : ZFRat) : a - 0 = a := by rw [sub_eq_add_neg, neg_zero, add_zero]

theorem zero_sub (a : ZFRat) : 0 - a = -a := by rw [sub_eq_add_neg, zero_add]

theorem sub_eq_zero_of_eq {a b : ZFRat} (h : a = b) : a - b = 0 := by rw [h, sub_self]

theorem eq_of_sub_eq_zero {a b : ZFRat} (h : a - b = 0) : a = b := by
  have : 0 + b = b := by rw [zero_add]
  have : a - b + b = b := by rwa [h]
  rwa [sub_eq_add_neg, neg_add_cancel_right] at this

theorem sub_eq_zero {a b : ZFRat} : a - b = 0 ↔ a = b := ⟨eq_of_sub_eq_zero, sub_eq_zero_of_eq⟩

theorem sub_sub (a b c : ZFRat) : a - b - c = a - (b + c) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, add_assoc]

theorem neg_sub (a b : ZFRat) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]

theorem sub_sub_self (a b : ZFRat) : a - (a - b) = b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_neg_cancel_left]

theorem sub_neg (a b : ZFRat) : a - -b = a + b := by rw [sub_eq_add_neg, neg_neg]
theorem sub_add_cancel (a b : ZFRat) : a - b + b = a := neg_add_cancel_right a b

theorem add_sub_cancel (a b : ZFRat) : a + b - b = a := add_neg_cancel_right a b

theorem add_sub_assoc (a b c : ZFRat) : a + b - c = a + (b - c) := by
  rw [sub_eq_add_neg, ← add_assoc, ← sub_eq_add_neg]

theorem sub_left_cancel (a b c : ZFRat) : a - c = b - c → a = b := by
  intro h
  rwa [← sub_eq_zero, sub_sub, sub_eq_zero, ← add_sub_assoc, add_comm, add_sub_cancel] at h

theorem sub_right_cancel (a b c : ZFRat) : c - a = c - b → a = b := by
  rw [← neg_sub a, ← neg_sub b, neg_inj]
  apply sub_left_cancel

theorem add_eq_sub_iff {a b c : ZFRat} : a + b = c ↔ a = c - b where
  mp := fun h => by rw [← h, add_sub_cancel]
  mpr := fun h => by rw [h, sub_add_cancel]


private noncomputable abbrev nsmul : ℕ → ZFRat → ZFRat
  | 0, _ => 0
  | n+1, m => m + nsmul n m

private noncomputable abbrev zsmul (n : ℤ) (x : ZFRat) : ZFRat :=
  match n with
  | .ofNat n => nsmul n x
  | .negSucc n => -nsmul (n+1) x
/-- Imported ZFLean declaration. -/
noncomputable abbrev mul (n m : ZFRat) : ZFRat :=
  Quotient.liftOn₂ n m
    (fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ ↦ mk (a * c,
      ⟨b * d, fun c ↦ nomatch hd (ZFInt.mul_eq_zero_of_ne_zero c hb)⟩))
    fun ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩ ⟨i, j, hi⟩ h h' ↦ by
      apply sound
      unfold_projs at h h'
      simp only [ZFSet.qrel] at h h' ⊢
      ac_change (a * f) * (c * j) = (b * e) * (d * i)
      rw [h, h']

noncomputable instance : Mul ZFRat := ⟨ZFRat.mul⟩
theorem mul_eq (n m : ZFInt × ZFInt') :
  mk n * mk m = mk (n.1 * m.1, ⟨n.2 * m.2,
    fun c ↦ nomatch m.2.2 (ZFInt.mul_eq_zero_of_ne_zero c n.2.2)⟩) := rfl

theorem mul_comm (n m : ZFRat) : n * m = m * n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  apply sound
  ring

theorem left_distrib (a b c : ZFRat) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply sound
  ring

theorem right_distrib (a b c : ZFRat) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm, mul_comm b c]

theorem zero_mul (a : ZFRat) : 0 * a = 0 := by
  induction a using Quotient.ind
  apply sound
  ring

theorem mul_zero (a : ZFRat) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem mul_assoc (a b c : ZFRat) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply sound
  ring

theorem one_mul (a : ZFRat) : 1 * a = a := by
  induction a using Quotient.ind
  apply sound
  ring

theorem mul_one (a : ZFRat) : a * 1 = a := by
  rw [mul_comm, one_mul]

theorem mul_eq_zero_iff {a b : ZFRat} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    induction a using Quotient.ind
    induction b using Quotient.ind
    simp_rw [mk_eq, mul_eq, zero_eq, eq, ZFSet.qrel, ZFInt.mul_zero, ZFInt.mul_one] at h ⊢
    rwa [←ZFInt.mul_eq_zero_iff]
  · rintro (h | h)
    · rw [h, zero_mul]
    · rw [h, mul_zero]


noncomputable instance : CommRing ZFRat where
  zero := 0
  one := 1
  add := add
  add_assoc _ _ _ := by rw [add_assoc]
  zero_add _ := zero_add
  add_zero _ := add_zero
  nsmul := ZFSet.ZFRat.nsmul
  nsmul_zero _ := rfl
  nsmul_succ _ _ := add_comm _ _
  add_comm := add_comm
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  zsmul := ZFSet.ZFRat.zsmul
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := add_comm _ _
  zsmul_neg' _ _ := rfl
  neg_add_cancel _ := add_left_neg


/-- The subtype of nonzero ZF rational numbers. -/
abbrev ZFRat' := {x : ZFRat // x ≠ 0}
/-- Imported ZFLean declaration. -/
protected noncomputable abbrev inv : ZFRat' → ZFRat' := fun ⟨x, hx⟩ ↦ by
  let a := x.out.1
  let hb := x.out.2.2
  set b := x.out.2.1
  have : a ≠ 0 := by
    intro contr
    have : mk (0, ⟨b, hb⟩) = x := by
      have : x.out = (0, ⟨b, hb⟩) := Prod.ext contr rfl
      rw [←this]
      exact mk_out x
    obtain rfl : x = 0 := by
      rw [←this, zero_eq, eq, ZFSet.qrel, ZFInt.mul_one, ZFInt.mul_zero]
    contradiction
  exact ⟨mk (b, ⟨a, this⟩), by
    intro h
    rw [mk_eq_zero_iff] at h
    contradiction⟩

noncomputable instance : Inv ZFRat' := ⟨ZFRat.inv⟩
open Classical in
noncomputable instance : Inv ZFRat where
  inv x := if hx : x ≠ 0 then ZFRat.inv ⟨x, hx⟩ else 0

theorem inv_eq {a : ZFRat} (ha : a ≠ 0) : a⁻¹ = (⟨a, ha⟩ : ZFRat')⁻¹ := by
  dsimp [Inv.inv]
  rw [dif_pos ha]

/-- Division by a nonzero ZF rational. -/
noncomputable abbrev hdiv (n : ZFRat) (m : ZFRat') : ZFRat := n * m⁻¹
open Classical in
/-- Division on ZF rational numbers, with division by zero sent to zero. -/
noncomputable abbrev div (n m : ZFRat) : ZFRat :=
  if hm : m ≠ 0 then hdiv n ⟨m, hm⟩ else 0
/-- Imported ZFLean declaration. -/
noncomputable instance : HDiv ZFRat ZFRat' ZFRat := ⟨hdiv⟩
/-- Imported ZFLean declaration. -/
noncomputable instance : Div ZFRat := ⟨div⟩


theorem div_eq {n m : ZFRat} (hm : m ≠ 0) : n / m = n / (⟨m, hm⟩:ZFRat') := rfl
theorem div_eq_mul_inv {n m : ZFRat} (hm : m ≠ 0) : n / m = n * (⟨m, hm⟩:ZFRat')⁻¹ := by
  dsimp [HDiv.hDiv, Div.div]
  rw [div, dif_pos hm]

@[simp]
theorem mul_inv' {a : ZFRat'} : a.1 * a⁻¹ = 1 := by
  obtain ⟨a, ha⟩ := a
  induction a using Quotient.ind
  rename_i a
  apply sound
  rw [ZFSet.qrel]
  simp only [mk_eq, ZFInt.mul_one, ne_eq]
  change ZFSet.qrel ⟨a.1, ⟨a.2.1, a.2.2⟩⟩ (mk a).out
  rw [←eq]
  symm
  apply mk_out
theorem mul_inv {a : ZFRat} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_eq ha, @mul_inv' (⟨a, ha⟩ : ZFRat')]

theorem inv_mul' {a : ZFRat'} : a⁻¹ * a.1 = 1 := by
  rw [mul_comm]
  exact mul_inv'
theorem inv_mul {a : ZFRat} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv ha

noncomputable instance : RatCast ZFRat where
  ratCast q := ((q.num : ZFRat) / (q.den : ZFRat))

private noncomputable def qsmul (k : ℚ) (m : ZFRat) : ZFRat := (k : ZFRat) * m

private noncomputable def nnqsmul : ℚ≥0 → ZFRat → ZFRat :=
  fun ⟨k, _⟩ m ↦ qsmul k m

open Classical in
noncomputable instance : DivisionRing ZFRat where
  exists_pair_ne := ⟨1, 0, one_ne_zero⟩
  mul_inv_cancel _ := mul_inv
  inv_zero := by
    simp only [Inv.inv, ne_eq, not_true_eq_false, dite_false]
  div_eq_mul_inv := by
    intro a b
    by_cases hb : b = 0
    · subst b
      dsimp [HDiv.hDiv, Div.div, div, Inv.inv]
      iterate 2 rw [dite_cond_eq_false (eq_false (fun a ↦ a rfl))]
      rw [mul_zero]
    · rw [div_eq_mul_inv hb, ←inv_eq]
  qsmul := qsmul
  nnqsmul := nnqsmul
  ratCast_def _ := rfl
  qsmul_def _ _ := by rfl
  nnqsmul_def := by
    rintro ⟨k, hk⟩ m
    unfold nnqsmul qsmul
    dsimp
    unfold_projs
    have : (↑k.num.natAbs : ZFRat) = ↑k.num := by
      unfold Int.natAbs
      cases k using Rat.casesOn with
      | mk' n d hd _ =>
        simp only [Rat.le_iff, Rat.num_ofNat, MulZeroClass.zero_mul, Rat.den_ofNat, Nat.cast_one,
          _root_.mul_one] at hk
        dsimp
        have : n = Int.ofNat n.natAbs := by
          rw [Int.ofNat_eq_natCast, ←Int.eq_natAbs_of_nonneg hk]
        rw [this]
        rfl
    dsimp [NNRat.cast, NNRatCast.nnratCast, NNRat.castRec]
    rw [this]
    rfl

noncomputable instance : Field ZFRat := {}

end ZFRat
end ZFSet
