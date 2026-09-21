/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Nat.Log

/-!
# Dyadic numbers

A dyadic (rational) number is a rational number whose denominator is a power of two. We provide
the `CommRing` structure, as well as proving some auxiliary theorems on them.
-/

@[expose] public section

/-! ### For Mathlib -/

theorem le_of_le_of_lt_of_lt {α β : Type*} [PartialOrder α] [Preorder β] {x y : α}
    {f : α → β} (h : x < y → f x < f y) (hxy : x ≤ y) : f x ≤ f y := by
  obtain rfl | h' := hxy.eq_or_lt
  · rfl
  · exact (h h').le

theorem Nat.pow_log_eq_self_iff {b n : ℕ} (hb : b ≠ 0) :
    b ^ Nat.log b n = n ↔ n ∈ Set.range (b ^ ·) := by
  constructor
  · aesop
  · rintro ⟨n, rfl⟩
    rw [← Nat.one_le_iff_ne_zero, le_iff_eq_or_lt] at hb
    obtain rfl | hb := hb
    · simp
    · rw [Nat.log_pow hb]

theorem pos_of_mem_powers {n : ℕ} (h : n ∈ Submonoid.powers 2) : 0 < n := by
  obtain ⟨n, rfl⟩ := h
  exact pow_pos (Nat.succ_pos 1) n

theorem ne_zero_of_mem_powers {n : ℕ} (h : n ∈ Submonoid.powers 2) : n ≠ 0 :=
  (pos_of_mem_powers h).ne'

theorem dvd_iff_le_of_mem_powers {m n : ℕ}
    (hm : m ∈ Submonoid.powers 2) (hn : n ∈ Submonoid.powers 2) : m ∣ n ↔ m ≤ n := by
  obtain ⟨m, rfl⟩ := hm
  obtain ⟨n, rfl⟩ := hn
  simp_all [pow_dvd_pow_iff, pow_le_pow_iff_right₀]

namespace Dyadic

attribute [coe] toRat

instance : Coe Dyadic Rat where
  coe := toRat

@[norm_cast] alias coe_le_coe := toRat_le_toRat_iff
@[norm_cast] alias coe_lt_coe := toRat_lt_toRat_iff
@[norm_cast] alias coe_inj := toRat_inj

/-- Numerator of a dyadic number. -/
abbrev num (x : Dyadic) : ℤ := x.toRat.num
/-- Denominator of a dyadic number. -/
abbrev den (x : Dyadic) : ℕ := x.toRat.den

theorem den_ne_zero (x : Dyadic) : x.den ≠ 0 := Rat.den_ne_zero x
theorem den_pos (x : Dyadic) : 0 < x.den := Rat.den_pos x
theorem one_le_den (x : Dyadic) : 1 ≤ x.den := x.den_pos
theorem den_mem_powers (x : Dyadic) : x.den ∈ Submonoid.powers 2 := by
  fun_cases toRat x with
  | case1 -- zero
  | case3 => exact one_mem _ -- integer
  | case2 => apply pow_mem; exact Submonoid.mem_powers 2 -- dyadic rational

@[simp]
theorem den_le_one_iff_eq_one {x : Dyadic} : x.den ≤ 1 ↔ x.den = 1 := by
  simp_rw [Nat.le_one_iff_eq_zero_or_eq_one, x.den_ne_zero, false_or]

@[simp]
theorem one_lt_den_iff_ne_one {x : Dyadic} : 1 < x.den ↔ x.den ≠ 1 := by
  simp [← den_le_one_iff_eq_one]

theorem den_ne_one_of_den_lt {x y : Dyadic} (h : x.den < y.den) : y.den ≠ 1 := by
  simpa using (one_le_den x).trans_lt h

@[ext] theorem ext {x y : Dyadic} (h : (x : ℚ) = y) : x = y := toRat_inj.1 h

@[norm_cast] alias coe_natCast := toRat_natCast
@[simp, norm_cast] theorem num_natCast (n : ℕ) : (n : Dyadic).num = n :=
  congrArg Rat.num (toRat_natCast n)
@[simp, norm_cast] theorem den_natCast (n : ℕ) : (n : Dyadic).den = 1 :=
  congrArg Rat.den (toRat_natCast n)

@[simp] theorem coe_ofNat (n : ℕ) : (ofNat(n) : Dyadic).toRat = n :=
  toRat_natCast n
@[simp] theorem num_ofNat (n : ℕ) : (ofNat(n) : Dyadic).num = n :=
  num_natCast n
@[simp] theorem den_ofNat (n : ℕ) : (ofNat(n) : Dyadic).den = 1 :=
  den_natCast n

@[simp] theorem natCast_lt_coe {x : ℕ} {y : Dyadic} : x < y.toRat ↔ x < y := by norm_cast
@[simp] theorem natCast_le_coe {x : ℕ} {y : Dyadic} : x ≤ y.toRat ↔ x ≤ y := by norm_cast
@[simp] theorem coe_lt_natCast {x : Dyadic} {y : ℕ} : x.toRat < y ↔ x < y := by norm_cast
@[simp] theorem coe_le_natCast {x : Dyadic} {y : ℕ} : x.toRat ≤ y ↔ x ≤ y := by norm_cast

@[simp, norm_cast] theorem coe_eq_natCast {x : Dyadic} {y : ℕ} : x.toRat = y ↔ x = y := by
  rw [← toRat_natCast, toRat_inj]
@[simp, norm_cast] theorem natCast_eq_coe {x : ℕ} {y : Dyadic} : x = y.toRat ↔ x = y := by
  rw [← toRat_natCast, toRat_inj]

@[norm_cast] alias coe_intCast := toRat_intCast
@[simp, norm_cast] theorem num_intCast (n : ℤ) : (n : Dyadic).num = n :=
  congrArg Rat.num (coe_intCast n)
@[simp, norm_cast] theorem den_intCast (n : ℤ) : (n : Dyadic).den = 1 :=
  congrArg Rat.den (coe_intCast n)

@[simp] theorem intCast_lt_coe {x : ℤ} {y : Dyadic} : x < y.toRat ↔ x < y := by norm_cast
@[simp] theorem intCast_le_coe {x : ℤ} {y : Dyadic} : x ≤ y.toRat ↔ x ≤ y := by norm_cast
@[simp] theorem coe_lt_intCast {x : Dyadic} {y : ℤ} : x.toRat < y ↔ x < y := by norm_cast
@[simp] theorem coe_le_intCast {x : Dyadic} {y : ℤ} : x.toRat ≤ y ↔ x ≤ y := by norm_cast
@[simp] theorem coe_eq_intCast {x : Dyadic} {y : ℤ} : x.toRat = y ↔ x = y := by norm_cast
@[simp] theorem intCast_eq_coe {x : ℤ} {y : Dyadic} : x = y.toRat ↔ x = y := by norm_cast

instance : Inhabited Dyadic := ⟨0⟩

@[simp, norm_cast] theorem coe_zero : (0 : Dyadic).toRat = 0 := rfl
@[simp] theorem num_zero : (0 : Dyadic).num = 0 := rfl
@[simp] theorem den_zero : (0 : Dyadic).den = 1 := rfl

@[simp] theorem zero_lt_coe {x : Dyadic} : 0 < x.toRat ↔ 0 < x := by norm_cast
@[simp] theorem zero_le_coe {x : Dyadic} : 0 ≤ x.toRat ↔ 0 ≤ x := by norm_cast
@[simp] theorem coe_lt_zero {x : Dyadic} : x.toRat < 0 ↔ x < 0 := by norm_cast
@[simp] theorem coe_le_zero {x : Dyadic} : x.toRat ≤ 0 ↔ x ≤ 0 := by norm_cast
alias coe_eq_zero := toRat_eq_zero_iff
@[simp] theorem zero_eq_coe {x : Dyadic} : 0 = x.toRat ↔ 0 = x := by norm_cast

@[simp, norm_cast] theorem coe_one : (1 : Dyadic).toRat = 1 := rfl
@[simp] theorem num_one : (1 : Dyadic).num = 1 := rfl
@[simp] theorem den_one : (1 : Dyadic).den = 1 := rfl

@[simp] theorem one_lt_coe {x : Dyadic} : 1 < x.toRat ↔ 1 < x := by norm_cast
@[simp] theorem one_le_coe {x : Dyadic} : 1 ≤ x.toRat ↔ 1 ≤ x := by norm_cast
@[simp] theorem coe_lt_one {x : Dyadic} : x.toRat < 1 ↔ x < 1 := by norm_cast
@[simp] theorem coe_le_one {x : Dyadic} : x.toRat ≤ 1 ↔ x ≤ 1 := by norm_cast
@[simp] theorem coe_eq_one {x : Dyadic} : x.toRat = 1 ↔ x = 1 := by norm_cast
@[simp] theorem one_eq_coe {x : Dyadic} : 1 = x.toRat ↔ 1 = x := by norm_cast

instance : Nontrivial Dyadic where
  exists_pair_ne := ⟨0, 1, by decide⟩

@[simp] theorem num_neg (x : Dyadic) : (-x).num = -x.num := congrArg Rat.num (toRat_neg x)
@[simp] theorem den_neg (x : Dyadic) : (-x).den = x.den := (congrArg Rat.den (toRat_neg x) :)

@[norm_cast] alias coe_neg := toRat_neg
@[norm_cast] alias coe_add := toRat_add
@[norm_cast] alias coe_sub := toRat_sub
@[norm_cast] alias coe_mul := toRat_mul
@[norm_cast] alias coe_pow := toRat_pow

instance : SMul Nat Dyadic where
  smul x y := x * y

@[norm_cast] theorem coe_nsmul (x : ℕ) (y : Dyadic) : (x • y).toRat = x • y.toRat :=
  (coe_mul x y).trans (by simp)

instance : SMul Int Dyadic where
  smul x y := x * y

@[norm_cast] theorem coe_zsmul (x : ℤ) (y : Dyadic) : (x • y).toRat = x • y.toRat :=
  (coe_mul x y).trans (by simp)

/-- The dyadic number ½. -/
def half : Dyadic := (1 : Dyadic) >>> 1

@[simp, norm_cast] theorem coe_half : half.toRat = 2⁻¹ := (Rat.inv_def 2).symm
@[simp] theorem num_half : half.num = 1 := rfl
@[simp] theorem num_den : half.den = 2 := rfl

/-- Constructor for the fraction `m / n`. -/
protected def mkRat (m : ℤ) {n : ℕ} (h : n ∈ Submonoid.powers 2) : Dyadic :=
  ofIntWithPrec m (Submonoid.log ⟨n, h⟩)

@[simp, norm_cast]
theorem coe_mkRat (m : ℤ) {n : ℕ} (h : n ∈ Submonoid.powers 2) :
    (Dyadic.mkRat m h).toRat = mkRat m n := by
  rw [Dyadic.mkRat, toRat_ofIntWithPrec_eq_mul_two_pow, zpow_neg,
    ← Nat.cast_two, zpow_natCast, ← Nat.cast_pow, ← Submonoid.pow_coe,
    Submonoid.pow_log_eq_self, Rat.mkRat_eq_div, div_eq_mul_inv]

@[simp] theorem mkRat_self (x : Dyadic) : Dyadic.mkRat x.num x.den_mem_powers = x := by ext; simp

@[simp]
theorem mkRat_one (m : ℤ) (h : 1 ∈ Submonoid.powers 2) : Dyadic.mkRat m h = m := by
  ext; simp [Rat.mkRat_one]

@[simp]
theorem mkRat_lt_mkRat {m n : ℤ} {k : ℕ} (h₁ h₂ : k ∈ Submonoid.powers 2) :
    Dyadic.mkRat m h₁ < Dyadic.mkRat n h₂ ↔ m < n := by
  have hk : 0 < (k : ℚ) := by
    rw [Rat.natCast_pos, Nat.pos_iff_ne_zero]
    obtain ⟨n, rfl⟩ := h₁
    simp
  rw [← coe_lt_coe]
  simp [Rat.mkRat_eq_div, div_lt_div_iff_of_pos_right hk]

instance : LinearOrder Dyadic where
  le_refl := Dyadic.le_refl
  le_trans := @Dyadic.le_trans
  le_antisymm := @Dyadic.le_antisymm
  le_total := Dyadic.le_total
  lt_iff_le_not_ge := Std.LawfulOrderLT.lt_iff
  toDecidableLE := Dyadic.instDecidableLE
  toDecidableLT := Dyadic.instDecidableLT
  toDecidableEq := instDecidableEqDyadic

@[simp]
theorem mkRat_le_mkRat {m n : ℤ} {k : ℕ} (h₁ h₂ : k ∈ Submonoid.powers 2) :
    Dyadic.mkRat m h₁ ≤ Dyadic.mkRat n h₂ ↔ m ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 (mkRat_lt_mkRat h₁ h₂)

theorem mkRat_add_mkRat_self {m n : ℤ} {k : ℕ} (h₁ h₂ : k ∈ Submonoid.powers 2) :
    Dyadic.mkRat m h₁ + Dyadic.mkRat n h₂ = .mkRat (m + n) h₁ := by
  ext; simp [Rat.mkRat_eq_div, add_div]

instance : CommRing Dyadic where
  add_assoc := add_assoc
  zero_add := Dyadic.zero_add
  add_zero := Dyadic.add_zero
  add_comm := add_comm
  mul_comm := mul_comm
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := Dyadic.zero_mul
  mul_zero := Dyadic.mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  natCast_succ _ := by
    rw [← coe_inj, coe_natCast, Rat.natCast_add, coe_add, coe_natCast]
    rfl
  intCast_negSucc _ := by
    rw [← coe_inj, coe_intCast, coe_neg, coe_natCast, ← Int.cast_natCast,
      ← Rat.intCast_neg, Int.neg_ofNat_succ]
  nsmul n x := n • x
  nsmul_zero x := by ext; simp [coe_nsmul]
  nsmul_succ n x := by ext; simp [add_one_mul, coe_nsmul]
  zsmul n x := n • x
  zsmul_zero' x := by ext; simp [coe_zsmul]
  zsmul_succ' n x := by ext; simp [add_one_mul, coe_zsmul]
  zsmul_neg' n x := by
    change _ * _ = -(_ * _)
    rw [← neg_mul, ← coe_inj, coe_mul, coe_mul, coe_intCast, coe_neg, coe_intCast,
      ← Rat.intCast_neg, Int.neg_ofNat_succ]
  npow n x := x ^ n
  npow_zero x := by ext; simp
  npow_succ n x := by ext; simp [pow_succ]

instance : IsStrictOrderedRing Dyadic where
  add_le_add_left := by simp [← toRat_le_toRat_iff]
  le_of_add_le_add_left := by simp [← toRat_le_toRat_iff]
  mul_lt_mul_of_pos_left x hx y z h := by
    rw [← coe_lt_coe] at hx h ⊢
    rw [coe_mul, coe_mul]
    rw [coe_zero] at hx
    exact mul_lt_mul_of_pos_left h hx
  mul_lt_mul_of_pos_right x hx y z h := by
    rw [← coe_lt_coe] at hx h ⊢
    rw [coe_mul, coe_mul]
    rw [coe_zero] at hx
    exact mul_lt_mul_of_pos_right h hx
  zero_le_one := by decide

instance : DenselyOrdered Dyadic where
  dense x y h := by
    use half * (x + y)
    simp_rw [← coe_lt_coe] at *
    constructor
    · simpa [inv_mul_eq_div] using left_lt_add_div_two.2 h
    · simpa [inv_mul_eq_div] using add_div_two_lt_right.2 h

instance : Archimedean Dyadic where
  arch x y h := by
    rw [← coe_lt_coe, coe_zero] at h
    obtain ⟨n, hn⟩ := exists_lt_nsmul h x.toRat
    refine ⟨n, ?_⟩
    rw [← coe_le_coe, nsmul_eq_mul, coe_mul, coe_natCast, ← nsmul_eq_mul]
    exact hn.le

theorem even_den {x : Dyadic} (hx : x.den ≠ 1) : Even x.den := by
  obtain ⟨n, hn⟩ := x.den_mem_powers
  rw [← hn]
  cases n
  · simp_all
  · rw [even_iff_two_dvd]
    exact dvd_mul_left ..

theorem odd_num {x : Dyadic} (hx : x.den ≠ 1) : Odd x.num := by
  rw [← Int.not_even_iff_odd]
  have hd := even_den hx
  rw [even_iff_two_dvd] at *
  rw [← Int.natAbs_dvd_natAbs]
  exact (Nat.not_coprime_of_dvd_of_dvd one_lt_two · hd x.toRat.reduced)

theorem intCast_num_eq_self_of_den_eq_one {x : Dyadic} (hx : x.den = 1) : x.num = x := by
  ext
  rw [coe_intCast]
  exact Rat.coe_int_num_of_den_eq_one hx

theorem den_mkRat_le (x : ℤ) {n : ℕ} (hn : n ≠ 0) : (mkRat x n).den ≤ n := by
  rw [← Rat.normalize_eq_mkRat hn, Rat.normalize_eq hn]
  exact Nat.div_le_self n _

theorem den_mkRat_lt {x : Dyadic} {n : ℤ} (hn : 2 ∣ n) (hd : x.den ≠ 1) :
    (mkRat n x.den).den < x.den := by
  rw [← Rat.normalize_eq_mkRat x.den_ne_zero, Rat.normalize_eq]
  apply Nat.div_lt_self x.den_pos
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ x.den_pos) (Nat.dvd_gcd _ (even_den hd).two_dvd)
  rwa [← Int.natAbs_dvd_natAbs] at hn

theorem den_add_self_lt {x : Dyadic} (hx : x.den ≠ 1) : (x + x).den < x.den := by
  suffices x + x = Dyadic.mkRat (2 * x.num) x.den_mem_powers by
    rw [this, den, Dyadic.coe_mkRat]
    exact den_mkRat_lt (Int.dvd_mul_right 2 x.num) hx
  ext
  simp [Rat.mkRat_eq_div, Rat.num_div_den, mul_div_assoc, ← two_mul]

theorem eq_mkRat_of_den_le {x : Dyadic} {n : ℕ} (h : x.den ≤ n) (hn : n ∈ Submonoid.powers 2) :
    ∃ m, x = .mkRat m hn := by
  use x.num * (n / x.den)
  ext
  rw [← x.mkRat_self, coe_mkRat, coe_mkRat,
    Rat.mkRat_eq_iff x.den_ne_zero (ne_zero_of_mem_powers hn), mkRat_self, Int.mul_assoc]
  congr
  exact (Nat.div_mul_cancel ((dvd_iff_le_of_mem_powers x.den_mem_powers hn).2 h)).symm

instance : CanLift Dyadic Int Int.cast (·.den = 1) where
  prf x hx := ⟨x.num, Dyadic.ext (coe_intCast x.num ▸ x.toRat.den_eq_one_iff.mp hx)⟩

theorem den_add_le_den_right {x y : Dyadic} (h : x.den ≤ y.den) : (x + y).den ≤ y.den := by
  obtain ⟨n, hn⟩ := eq_mkRat_of_den_le h y.den_mem_powers
  conv_lhs => rw [← y.mkRat_self, hn, mkRat_add_mkRat_self]
  rw [den, Dyadic.coe_mkRat]
  exact den_mkRat_le _ y.den_ne_zero

/-- Coercion as a `RingHom`. -/
@[simps]
def coeRingHom : Dyadic →+* ℚ where
  toFun := Dyadic.toRat
  map_zero' := rfl
  map_one' := rfl
  map_add' := coe_add
  map_mul' := coe_mul

end Dyadic
end
