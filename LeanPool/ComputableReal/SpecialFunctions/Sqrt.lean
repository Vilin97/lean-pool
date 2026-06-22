/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import LeanPool.ComputableReal.IsComputable
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Verified rational bounds for square roots

Rational lower and upper bounds for `Real.sqrt` of a rational interval are built via integer square
roots (`boundedSqrt`/`sqrtq`), shown to converge, and assembled into `ComputableℝSeq.Sqrt.sqrt`.
This yields an `IsComputable` instance for `Real.sqrt` and the golden ratio constants. The bound
functions are executable; the packaged sequence mentions `Real.sqrt` itself as its reference
value, so `sqrt` and the instances are `noncomputable` Lean terms.
-/

namespace ComputableℝSeq

open scoped QInterval

namespace Sqrt

private theorem mul_le_of_le_one_of_le' {a b c : ℝ} (ha : a ≤ 1) (hbc : b ≤ c)
    (hb : 0 ≤ b) (_hc : 0 ≤ c) : a * b ≤ c :=
  (mul_le_of_le_one_left hb ha).trans hbc

theorem boundedSqrt_le_rsqrt (y : ℚ) (n : ℕ) (b : ℕ) (hb : 0 < b) :
    mkRat (Int.sqrt (y.num * b^n)) ((y.den * b^n).sqrt + 1) ≤ Real.sqrt y := by
  simp only [Rat.mkRat_eq_div, Nat.cast_add, Nat.cast_one]
  rify
  by_cases hy : y ≤ 0
  · have h₁ : √↑y = 0 := by
      rw [Real.sqrt_eq_zero']
      exact Rat.cast_nonpos.mpr hy
    have h₂ : Int.sqrt (y.num * b ^ n) = 0 := by
      rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
      exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr hy) (by positivity)
    simp [h₁, h₂]
  push Not at hy
  rw [Rat.cast_def, Real.sqrt_div' _ (Nat.cast_nonneg' y.den)]
  conv_rhs =>
    equals √(↑(y.num * b^n)) / √(↑(y.den * b^n)) =>
      rw [div_eq_div_iff (by positivity) (by positivity)]
      push_cast
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      ring
  apply div_le_div₀
  · exact Real.sqrt_nonneg _
  · have h₄ : 0 < y.num * b ^ n := by positivity
    have hcast : (((y.num * b ^ n).toNat : ℕ) : ℝ) = ((y.num * b ^ n : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h₄.le]
    rw [Int.sqrt.eq_1]
    have hle := @Real.nat_sqrt_le_real_sqrt (y.num * b ^ n).toNat
    rw [hcast] at hle
    exact_mod_cast hle
  · simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_nonneg, Real.sqrt_mul, Real.sqrt_pos,
      Nat.cast_pos, ← Nat.ne_zero_iff_zero_lt, ne_eq, Rat.den_ne_zero, not_false_eq_true,
      mul_pos_iff_of_pos_left]
    positivity
  · exact Real.real_sqrt_le_nat_sqrt_succ

theorem rsqrt_le_boundedSqrt (y : ℚ) (n : ℕ) (b : ℕ) (hb : 0 < b) :
    Real.sqrt y ≤ mkRat (Int.sqrt (y.num * b^n) + 1) (y.den * b^n).sqrt := by
  simp only [Rat.mkRat_eq_div, Int.cast_add, Int.cast_one]
  rify
  by_cases hy : y ≤ 0
  · have h₁ : √↑y = 0 := by
      rw [Real.sqrt_eq_zero']
      exact Rat.cast_nonpos.mpr hy
    have h₂ : Int.sqrt (y.num * b ^ n) = 0 := by
      rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
      exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr hy) (by positivity)
    simp [h₁, h₂]
  push Not at hy
  rw [Rat.cast_def, Real.sqrt_div' _ (Nat.cast_nonneg' y.den)]
  conv_lhs =>
    equals √(↑(y.num * b^n)) / √(↑(y.den * b^n)) =>
      rw [div_eq_div_iff (by positivity) (by positivity)]
      push_cast
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      ring
  apply div_le_div₀
  · have h₁ : 0 < (y.num * b ^ n).sqrt := by
      suffices 0 < Nat.sqrt (Int.toNat (y.num) * b ^ n) by
        rw [Int.sqrt.eq_1]
        norm_cast
        convert this
        conv_rhs => apply (Int.toNat_natCast _).symm
        push_cast
        congr
        exact (Int.toNat_of_nonneg ((Rat.num_pos.mpr hy).le)).symm
      by_contra h₁
      simp [← Nat.ne_zero_iff_zero_lt, Nat.sqrt_eq_zero, hy, hb.ne'] at h₁
    positivity
  · have h₄ : 0 < y.num * b ^ n := by positivity
    have hcast : (((y.num * b ^ n).toNat : ℕ) : ℝ) = ((y.num * b ^ n : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h₄.le]
    rw [Int.sqrt.eq_1]
    have hle := @Real.real_sqrt_le_nat_sqrt_succ (y.num * b ^ n).toNat
    rw [hcast] at hle
    exact_mod_cast hle
  · simp [← Nat.ne_zero_iff_zero_lt, Nat.sqrt_eq_zero, hb.ne']
  · exact Real.nat_sqrt_le_real_sqrt

/-- A version of square roots for rational intervals, that give an interval containing the actual
 square root, that are at most b^-n wider than the true interval. -/
def boundedSqrt (x : ℚInterval) (n : ℕ) (b : ℕ) (hb : 0 < b) : ℚInterval :=
  ⟨⟨
    let q := x.fst;
    mkRat (Int.sqrt (q.num * b^n)) ((q.den * b^n).sqrt + 1),
    let q := x.snd;
    mkRat (Int.sqrt (q.num * b^n) + 1) (q.den * b^n).sqrt⟩,
  by
    dsimp
    rify
    trans Real.sqrt (x.snd)
    · trans Real.sqrt (x.fst)
      · apply boundedSqrt_le_rsqrt _ _ _ hb
      · apply Real.sqrt_le_sqrt
        exact_mod_cast x.2
    · apply rsqrt_le_boundedSqrt _ _ _ hb
    ⟩

/-- Definition of `sqrtq`. -/
def sqrtq (x : ℚInterval) (n : ℕ) : ℚInterval :=
  --shortcut with an if to slightly speed things up
  if x.snd ≤ 0 then 0 else boundedSqrt x n 4 (by norm_num)

theorem sqrt_lb_def (q : ℚInterval) (n : ℕ) :
    (sqrtq q n).fst = if q.snd ≤ 0 then 0 else
      mkRat (Int.sqrt (q.fst.num * 4^n)) ((q.fst.den * 4^n).sqrt + 1) := by
  rw [sqrtq, apply_ite (fun (x : ℚInterval) ↦ x.fst)]
  rfl

theorem sqrt_ub_def (q : ℚInterval) (n : ℕ) :
    (sqrtq q n).snd = if q.snd ≤ 0 then 0 else
       mkRat (Int.sqrt (q.snd.num * 4 ^ n) + 1) (q.snd.den * 4 ^ n).sqrt := by
  rw [sqrtq, apply_ite (fun (x : ℚInterval) ↦ x.snd)]
  rfl

theorem sqrtq_nonneg (q : ℚInterval) (n : ℕ) : 0 ≤ (sqrtq q n).fst := by
  rw [sqrt_lb_def]
  split_ifs
  · rfl
  · rw [Rat.mkRat_eq_div]
    have := Int.sqrt_nonneg (q.toProd.1.num * 4 ^ n)
    positivity

theorem lb_le_sqrt_lb (q : ℚInterval) (n : ℕ) : (sqrtq q n).fst ≤ Real.sqrt q.fst := by
  rw [sqrtq]
  split_ifs with h
  · simp
  · apply boundedSqrt_le_rsqrt q.toProd.1
    norm_num

theorem sqrt_ub_le_ub (q : ℚInterval) (n : ℕ) : Real.sqrt q.snd ≤ (sqrtq q n).snd := by
  rw [sqrtq]
  split_ifs with h
  · have := Real.sqrt_eq_zero'.mpr (Rat.cast_nonpos.mpr h)
    simp [this]
  · apply rsqrt_le_boundedSqrt q.toProd.2
    norm_num

/-- This equality is a generally true way to "split a denominator", but is particularly useful
as an approximation when ε is small compared to y, and we wish to approximate
`x / (y + ε)` with `x / y`. -/
lemma denom_err (x y ε : ℝ) (hy : y ≠ 0) (hyε : y + ε ≠ 0) :
    x / (y + ε) = x / y - (x / y) * ε / (y + ε) := by
  field_simp
  ring_nf

theorem sqrt_le_mkRat_add (q : ℚ) (n : ℕ) :
    Real.sqrt q ≤ mkRat (Int.sqrt (q.num * 4^n)) ((q.den * 4^n).sqrt + 1) + 2 * Real.sqrt q / 2^n
      := by
  nth_rewrite 4 [← Rat.mkRat_self q]
  nth_rewrite 1 [← Rat.mkRat_self q]
  simp only [Rat.mkRat_eq_div, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Nat.cast_nonneg,
    Real.sqrt_div', Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one]
  have hd := Rat.den_pos q
  generalize q.num = x, q.den = y at *
  clear q
  rcases le_or_gt x 0 with h|h
  · have h₁ : √↑x = 0 := by
      rw [Real.sqrt_eq_zero']
      exact Int.cast_nonpos.mpr h
    have h₂ : Int.sqrt (x * 4 ^ n) = 0 := by
      rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
      exact Int.mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    simp [h₁, h₂]
  · obtain ⟨z,hz⟩ := Int.eq_ofNat_of_zero_le h.le
    subst x
    conv_rhs =>
      enter [1,1,1,1]
      tactic => norm_cast
    rw [Int.sqrt_natCast]
    simp only [Int.cast_natCast]
    /-
    x/(y+ε) = (x/y) - (x/y - x/(y+ε)) = (x/y) - x*(1/y - 1/(y+ε)) = x/y - x*((y+ε) - y)/(y*(y+ε))
      = x/y - (x/y)*(ε/(y+ε)). The error is thus at most (x/y)*ε/(y+ε), which is upper bounded by
      ≤ (sqrt q) * 1 / 4^n.
    Similarly for the numerator.
    -/
    have h₁ := @Real.floor_real_sqrt_eq_nat_sqrt (z * 4^n)
    rify at h₁
    rw [← h₁, ← Int.self_sub_fract]
    clear h₁
    have h₂ := Int.fract_lt_one √(↑z * 4 ^ n)
    have h₃ := Int.fract_nonneg √(↑z * 4 ^ n)
    generalize Int.fract √(↑z * 4 ^ n) = ε₁ at *
    have h₁ := @Real.floor_real_sqrt_eq_nat_sqrt (y * 4^n)
    rify at h₁
    rw [← h₁, ← Int.self_sub_fract]
    clear h₁
    have h₄ := Int.fract_lt_one √(↑y * 4 ^ n)
    have h₅ := Int.fract_nonneg √(↑y * 4 ^ n)
    rw [sub_add_comm]
    rw [← sub_sub_cancel 1 (Int.fract _)] at h₄ h₅
    generalize 1 - Int.fract √(↑y * 4 ^ n) = ε₂ at *
    simp only [sub_lt_self_iff, sub_nonneg] at h₄ h₅
    rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_mul' _ (by positivity),
      show (4 ^ n = ((2 ^ n) ^ 2 : ℝ)) by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]]
    simp only [Nat.ofNat_nonneg, pow_nonneg, Real.sqrt_sq]
    rw [_root_.add_comm ε₂, sub_div, denom_err _ _ _ (by positivity) (by positivity)]
    rw [show √↑z * 2 ^ n / (√↑y * 2 ^ n) = √↑z / √↑y by field_simp]
    suffices (√↑z / √↑y * ε₂ / (√↑y * 2 ^ n + ε₂) ≤ √↑z / √↑y / 2 ^ n)
      ∧ (ε₁ / (√↑y * 2 ^ n + ε₂) ≤ √↑z / √↑y / 2 ^ n) by
      rcases this
      rw [← mul_div 2]
      linarith
    replace h : 1 ≤ √↑z := Real.one_le_sqrt.mpr (by norm_cast at h ⊢)
    replace hd : 1 ≤ √↑y := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hd)
    constructor
    · apply div_le_div₀
      · positivity
      · exact mul_le_of_le_one_right (by positivity) h₅
      · positivity
      · trans √↑y * 2 ^ n
        · exact le_mul_of_one_le_left (by positivity) hd
        · exact le_add_of_nonneg_right h₄.le
    · rw [div_div]
      apply div_le_div₀
      · positivity
      · exact h₂.le.trans h
      · positivity
      · exact le_add_of_nonneg_right h₄.le

theorem mkRat_sub_le_sqrt (q : ℚ) (n : ℕ) :
    (if q ≤ 0 then 0 else
      mkRat (Int.sqrt (q.num * 4 ^ n) + 1) (q.den * 4 ^ n).sqrt
    ) - 7 * Real.sqrt q / 2^n ≤ Real.sqrt q := by
  split_ifs with h
  · rify at h
    simp [Real.sqrt_eq_zero'.mpr h]
  push Not at h
  replace h : 0 < q.num := Rat.num_pos.mpr h
  nth_rewrite 4 [← Rat.mkRat_self q]
  nth_rewrite 3 [← Rat.mkRat_self q]
  simp only [Rat.mkRat_eq_div, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Nat.cast_nonneg,
    Real.sqrt_div']
  have hd := Rat.den_pos q
  generalize q.num = x, q.den = y at *
  clear q
  obtain ⟨z,hz⟩ := Int.eq_ofNat_of_zero_le h.le
  subst x
  conv_lhs =>
    enter [1,1,1,1]
    tactic => norm_cast
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
  replace h : 1 ≤ √↑z := Real.one_le_sqrt.mpr (by norm_cast at h ⊢)
  have h2pow : (1 : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.one_le_two_pow
  have h₁ := @Real.floor_real_sqrt_eq_nat_sqrt (z * 4^n)
  rify at h₁
  rw [← h₁, ← Int.self_sub_fract]
  clear h₁
  have h₄ := Int.fract_lt_one √(↑z * 4 ^ n)
  have h₅ := Int.fract_nonneg √(↑z * 4 ^ n)
  rw [sub_add_comm]
  rw [← sub_sub_cancel 1 (Int.fract _)] at h₄ h₅
  generalize 1 - Int.fract √(↑z * 4 ^ n) = ε₂ at *
  simp only [sub_lt_self_iff, sub_nonneg] at h₄ h₅
  --Have to special-case the y=1 case. Otherwise the denominator 1 / (√y * 2^n - ε₁) looks like it
  -- "could be" arbitrarily close to zero, and so cause a big blowup in error.
  by_cases hd' : y = 1
  · subst y
    simp only [one_mul, Nat.cast_one, Real.sqrt_one, div_one,
      tsub_le_iff_right, ge_iff_le]
    rw [show (4 ^ n = ((2 ^ n) ^ 2 : ℕ)) by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_right_comm], Nat.sqrt_eq']
    rw [Real.sqrt_mul' _ (by positivity), show (4 ^ n = ((2 ^ n) ^ 2 : ℝ)) by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm],
      Real.sqrt_sq (by positivity), Nat.cast_pow, Nat.cast_ofNat, add_div]
    simp only [isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
      not_false_eq_true, IsUnit.mul_div_cancel_right, _root_.add_comm ( _ / _ ),
        add_le_add_iff_left]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  replace hd' : 2 ≤ y := by omega
  replace hd : 1 ≤ √↑y := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hd)
  have h₁ := @Real.floor_real_sqrt_eq_nat_sqrt (y * 4^n)
  rify at h₁
  rw [← h₁, ← Int.self_sub_fract]
  clear h₁
  have h₂ := Int.fract_lt_one √(↑y * 4 ^ n)
  have h₃ := Int.fract_nonneg √(↑y * 4 ^ n)
  generalize Int.fract √(↑y * 4 ^ n) = ε₁ at *
  rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_mul' _ (by positivity),
      show (4 ^ n = ((2 ^ n) ^ 2 : ℝ)) by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]]
  simp only [Nat.ofNat_nonneg, pow_nonneg, Real.sqrt_sq]
  rw [_root_.add_comm ε₂, add_div, sub_eq_add_neg _ ε₁, denom_err]
  rotate_left
  · positivity
  · nlinarith
  rw [show √↑z * 2 ^ n / (√↑y * 2 ^ n) = √↑z / √↑y by field_simp]
  simp only [_root_.mul_neg, neg_div, sub_neg_eq_add]
  suffices (√↑z / √↑y * ε₁ / (√↑y * 2 ^ n + -ε₁) ≤ 3 * (√↑z / √↑y / 2 ^ n))
    ∧ (ε₂ / (√↑y * 2 ^ n + -ε₁) ≤ 4 * (√↑z / √↑y / 2 ^ n)) by
    rcases this
    rw [← mul_div 7]
    linarith
  have hi₁ : 1 /3 ≤ √↑y - ε₁ := by
    suffices 4 / 3 ≤ √↑y by linarith
    trans √2
    · rw [Real.le_sqrt' (by positivity)]
      norm_num
    · exact Real.sqrt_le_sqrt (Nat.ofNat_le_cast.mpr hd')
  have hi₂ : 0 < √↑y * 2 ^ n - ε₁ := by
    apply lt_of_lt_of_le (show 0 < (1 / 3 : ℝ) by norm_num)
    apply hi₁.trans <| sub_le_sub_right (le_mul_of_one_le_right (by positivity) h2pow) _
  constructor
  · ring_nf
    rw [mul_assoc, mul_assoc _ _ 3, mul_le_mul_iff_of_pos_left (by positivity)]
    apply mul_le_of_le_one_of_le' h₂.le ?_ (by positivity) (by positivity)
    rw [inv_le_iff_one_le_mul₀ hi₂]
    have hbound : (2 : ℝ) ^ n ≤ 3 * (√↑y * 2 ^ n - ε₁) :=
      calc (2 : ℝ) ^ n = 3 * (1/3 * (2^n)) := by ring
        _ ≤ 3 * ((√↑y - ε₁) * 2 ^ n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi₁ (by positivity)) zero_le_three
        _ = 3 * (√↑y * 2 ^ n - ε₁ * 2 ^ n) := by ring
        _ ≤ 3 * (√↑y * 2 ^ n - ε₁) :=
          mul_le_mul_of_nonneg_left (tsub_le_tsub_left (le_mul_of_one_le_right h₃ h2pow) _) (by
            positivity)
    have hinv : (2 : ℝ)⁻¹ ^ n * 2 ^ n = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hbound (show (0:ℝ) ≤ 2⁻¹ ^ n by positivity), hinv]
  · rw [div_div, mul_div, ← sub_eq_add_neg]
    rw [div_le_div_iff₀ hi₂ (by positivity)]
    apply mul_le_of_le_one_of_le' h₅ ?_ (by positivity) (by positivity)
    conv_rhs =>
      equals (√↑z * √↑y * 2 ^ n) + √↑z * (3 * √↑y * 2 ^ n - 4 * ε₁) =>
        ring_nf
    suffices 0 ≤ 3 * √↑y * 2 ^ n - 4 * ε₁ by nlinarith
    have : √↑y ≤ √↑y * 2 ^ n := le_mul_of_one_le_right (by positivity) h2pow
    linarith

/-- The square root lower bound has an error that can be composed into one part `2 * √r / 2^n`
that decays with n, but depends on the value; and one part `(x.snd - x.fst) / √r`, that
is proportional to width of the input interval. -/
theorem sqrt_le_sqrtq_add (r : ℝ) (x : ℚInterval) (n : ℕ) (hq : x.fst ≤ r ∧ r ≤ x.snd) (hx : 0 <
  x.fst) :
    √r ≤ (sqrtq x n).fst + 2 * √r / 2^n + (x.snd - x.fst) / (2 * √x.fst) := by
  have hxp : (0 : ℝ) < x.fst := by exact Rat.cast_pos.mpr hx
  have hx₂ : 0 < x.snd := by rify; linarith
  have hrp : 0 < r := by linarith
  have hx21 := sub_nonneg_of_le <| hq.1.trans hq.2
  have hrx1 := sub_nonneg_of_le hq.1
  suffices (√r - √x.fst) * (1 - 2 / 2^n) ≤ (x.snd - x.fst) / (2 * √x.fst) by
    have h₁ := sqrt_le_mkRat_add x.fst n
    have h₂ := sqrt_lb_def x n
    rw [if_neg (Rat.not_le.mpr hx₂)] at h₂
    rw [← h₂] at h₁
    ring_nf at *
    linarith
  by_cases hn : n = 0 ∨ n = 1
  · rcases hn with rfl|rfl
    · norm_num1
      trans 0
      · simpa using Real.sqrt_le_sqrt hq.1
      · positivity
    · norm_num
      positivity
  replace hn : 2 ≤ n := by omega
  have h₃ : √r - √x.fst = (r - x.fst) / (√r + √x.fst) := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt hrp.le, Real.sq_sqrt hxp.le]
  have h₄ : (0 : ℝ) ≤ 1 - 2 / 2 ^ n := by
    have h2n : 2 ≤ 2^n := hn.trans Nat.lt_two_pow_self.le
    rify at h2n
    rw [sub_nonneg, div_le_one (by positivity)]
    exact h2n
  trans (x.snd - x.fst) / (2 * √x.fst) * (1 - 2 / 2^n)
  · rw [h₃]
    refine mul_le_mul_of_nonneg_right ?_ h₄
    apply div_le_div₀ hx21
    · linarith
    · positivity
    · linarith [Real.sqrt_le_sqrt hq.1]
  · apply mul_le_of_le_one_right
    · positivity
    · rw [tsub_le_iff_right, le_add_iff_nonneg_right]
      positivity

/-- Similar to `sqrt_le_sqrtq_add`, but doesn't require `0 < x.fst`. -/
theorem sqrt_le_sqrtq_add' (r : ℝ) (x : ℚInterval) (n : ℕ) (hq : x.fst ≤ r ∧ r ≤ x.snd) (hr : 0 <
  r) :
    √r ≤ (sqrtq x n).fst + 2 * √r / 2^n + (x.snd - x.fst) / √r := by
  have hx₂ : 0 < x.snd := by rify; linarith
  have hx21 := sub_nonneg_of_le <| hq.1.trans hq.2
  have hrx1 := sub_nonneg_of_le hq.1
  suffices (√r - √x.fst) * (1 - 2 / 2^n) ≤ (x.snd - x.fst) / √r by
    have h₁ := sqrt_le_mkRat_add x.fst n
    have h₂ := sqrt_lb_def x n
    rw [if_neg (Rat.not_le.mpr hx₂)] at h₂
    rw [← h₂] at h₁
    ring_nf at *
    linarith
  by_cases hn : n = 0 ∨ n = 1
  · rcases hn with rfl|rfl
    · norm_num1
      trans 0
      · simpa using Real.sqrt_le_sqrt hq.1
      · positivity
    · norm_num
      positivity
  replace hn : 2 ≤ n := by omega
  have h₃ : √r - √x.fst ≤ (r - x.fst) / (√r + √x.fst) := by
    by_cases hxp : 0 ≤ x.fst
    · apply le_of_eq
      field_simp
      ring_nf
      rw [Real.sq_sqrt hr.le, Real.sq_sqrt (Rat.cast_nonneg.mpr hxp)]
    · replace hxp : x.fst < (0 : ℝ) := Rat.cast_lt_zero.mpr (Rat.not_le.mp hxp)
      simp only [Real.sqrt_eq_zero_of_nonpos (hxp.le), sub_zero, add_zero]
      rw [le_div_iff₀ (by positivity), Real.mul_self_sqrt hr.le]
      linarith
  have h₄ : (0 : ℝ) ≤ 1 - 2 / 2 ^ n := by
    have h2n : 2 ≤ 2^n := hn.trans Nat.lt_two_pow_self.le
    rify at h2n
    rw [sub_nonneg, div_le_one (by positivity)]
    exact h2n
  trans (x.snd - x.fst) / (√r) * (1 - 2 / 2^n)
  · refine mul_le_mul_of_nonneg_right ?_ h₄
    apply h₃.trans
    apply div_le_div₀ hx21
    · linarith
    · positivity
    · linarith [Real.sqrt_nonneg x.fst]
  · apply mul_le_of_le_one_right
    · positivity
    · rw [tsub_le_iff_right, le_add_iff_nonneg_right]
      positivity

theorem sqrtq_sub_le_sqrt (r : ℝ) (x : ℚInterval) (n : ℕ) (hq : x.fst ≤ r ∧ r ≤ x.snd) (hx : 0 <
  x.fst)
    (hn : 3 ≤ n) : (sqrtq x n).snd - (7 * √r / 2^n) - (x.snd - x.fst) / √x.fst ≤ √r := by
  have hxp : (0 : ℝ) < x.fst := by exact Rat.cast_pos.mpr hx
  have hx₂ : 0 < x.snd := by rify; linarith
  have hxp₂ : (0 : ℝ) < x.snd := by linarith
  have hrp : 0 < r := by linarith
  have hx21 := sub_nonneg_of_le <| hq.1.trans hq.2
  have hrx1 := sub_nonneg_of_le hq.1
  suffices (√x.snd - √r) * (1 + 7 / 2^n) ≤ (x.snd - x.fst) / √x.fst by
    have h₁ := mkRat_sub_le_sqrt x.snd n
    have h₂ := sqrt_ub_def x n
    rw [if_neg (Rat.not_le.mpr hx₂)] at h₂ h₁
    rw [← h₂] at h₁
    ring_nf at *
    linarith
  have h₃ : √x.snd - √r = (x.snd - r) / (√x.snd + √r) := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt hrp.le, Real.sq_sqrt hxp₂.le]
  have h₄ : (0 : ℝ) ≤ 1 + 7 / 2 ^ n := by positivity
  trans (x.snd - x.fst) / √x.fst * ((1 + 7 / 2^n) / 2)
  · suffices (√↑x.toProd.2 - √r) * (1 + 7 / 2 ^ n) ≤ (↑x.toProd.2 - ↑x.toProd.1) / (2 *
    √↑x.toProd.1) * (1 + 7 / 2 ^ n) by
      convert this using 1
      ring_nf
    rw [h₃]
    refine mul_le_mul_of_nonneg_right ?_ h₄
    apply div_le_div₀ hx21
    · linarith
    · positivity
    · linarith [Real.sqrt_le_sqrt hq.1, Real.sqrt_le_sqrt hq.2]
  · apply mul_le_of_le_one_right
    · positivity
    · have : (7 / 2^n : ℝ) ≤ 1 := by
        rw [div_le_one₀ (by norm_num)]
        apply le_trans (b := 8) (by norm_num)
        have := Real.monotone_rpow_of_base_ge_one (one_le_two) (Nat.ofNat_le_cast.mpr hn)
        norm_num at this
        exact this
      linarith

theorem sqrtq_sub_le_sqrt' (r : ℝ) (x : ℚInterval) (n : ℕ) (hq : x.fst ≤ r ∧ r ≤ x.snd) (hr : 0 < r)
    (hn : 3 ≤ n) : (sqrtq x n).snd - (7 * √r / 2^n) - (x.snd - x.fst) / √r ≤ √r := by
  have hx₂ : 0 < x.snd := by rify; linarith
  have hxp₂ : (0 : ℝ) < x.snd := by linarith
  have hx21 := sub_nonneg_of_le <| hq.1.trans hq.2
  have hrx1 := sub_nonneg_of_le hq.1
  suffices (√x.snd - √r) * (1 + 7 / 2^n) ≤ (x.snd - x.fst) / √r by
    have h₁ := mkRat_sub_le_sqrt x.snd n
    have h₂ := sqrt_ub_def x n
    rw [if_neg (Rat.not_le.mpr hx₂)] at h₂ h₁
    rw [← h₂] at h₁
    ring_nf at *
    linarith
  have h₃ : √x.snd - √r = (x.snd - r) / (√x.snd + √r) := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt hr.le, Real.sq_sqrt hxp₂.le]
  have h₄ : (0 : ℝ) ≤ 1 + 7 / 2 ^ n := by positivity
  trans (x.snd - x.fst) / √r * ((1 + 7 / 2^n) / 2)
  · suffices (√↑x.toProd.2 - √r) * (1 + 7 / 2 ^ n) ≤ (↑x.toProd.2 - ↑x.toProd.1) / (2 * √r) * (1 +
    7 / 2 ^ n) by
      convert this using 1
      ring_nf
    rw [h₃]
    refine mul_le_mul_of_nonneg_right ?_ h₄
    apply div_le_div₀ hx21
    · linarith
    · positivity
    · linarith [Real.sqrt_le_sqrt hq.1, Real.sqrt_le_sqrt hq.2]
  · apply mul_le_of_le_one_right
    · positivity
    · have : (7 / 2^n : ℝ) ≤ 1 := by
        rw [div_le_one₀ (by norm_num)]
        apply le_trans (b := 8) (by norm_num)
        have := Real.monotone_rpow_of_base_ge_one (one_le_two) (Nat.ofNat_le_cast.mpr hn)
        norm_num at this
        exact this
      linarith

theorem TLUW_lower : TendstoLocallyUniformlyWithout
    (fun n (x : ℚ) => ↑((fun n q =>
      mkRat (Int.sqrt (q.num * 4 ^ n)) ((q.den * 4 ^ n).sqrt + 1)) n x))
    (fun q => √↑q) := by
  rw [TendstoLocallyUniformlyWithout]
  intro ε hε x
  dsimp
  rcases lt_or_ge x 0 with h|h
  · use Set.Iic 0, Iic_mem_nhds h, 0
    intro b _ y hy
    change y ≤ (0:ℝ) at hy
    have h₂ : Int.sqrt (y.num * 4 ^ b) = 0 := by
      rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
      exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr <| Rat.cast_nonpos.mp hy) (by
        positivity)
    simp [Real.sqrt_eq_zero'.mpr hy, h₂, hε]
  · set tm := max (2 * x) 1
    have htm₀ : 0 < tm := by positivity
    have htm : x < tm := by
      by_cases 0 < x
      · exact lt_sup_of_lt_left (by linarith)
      · exact lt_sup_of_lt_right (by linarith)
    use Set.Ioo (-1) tm, Ioo_mem_nhds (by linarith) htm
    set ε' := (ε / (2 * tm.sqrt)) with hε'
    set a := Int.clog 2 (1 / ε') with ha
    use a.toNat
    rintro b hb q ⟨hq₁, hq₂⟩
    by_cases hq₃ : q ≤ 0
    · have h₂ : Int.sqrt (q.num * 4 ^ b) = 0 := by
        rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
        exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr hq₃) (by positivity)
      simp [Real.sqrt_eq_zero'.mpr (Rat.cast_nonpos.mpr hq₃), h₂, hε]
    push Not at hq₃
    suffices 2 * √↑q / 2 ^ b < ε by
      have hb₁ := boundedSqrt_le_rsqrt q b 4 (by norm_num)
      rw [Nat.cast_ofNat] at hb₁
      have hb₂ := sqrt_le_mkRat_add q b
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    replace hb : Int.clog 2 (1 / ε') ≤ b := Int.toNat_le.mp hb
    replace hb : 2 ^ (Int.clog 2 (1 / ε')) ≤ (2 : ℝ) ^ (b : ℤ) := zpow_le_zpow_right₀ (one_le_two)
      hb
    replace hb := le_trans (Int.self_le_zpow_clog Nat.one_lt_two (1 / ε')) hb
    rw [hε', zpow_natCast] at hb
    have hqtm := Real.sqrt_lt_sqrt (Rat.cast_nonneg.mpr hq₃.le) hq₂
    have hq0 := Real.sqrt_pos_of_pos (Rat.cast_pos.mpr hq₃)
    simp only [one_div, inv_div] at hb
    rw [div_le_iff₀ (by positivity)] at hb
    rw [div_lt_iff₀ (by positivity), _root_.mul_comm ε]
    linarith

theorem TLUW_upper : TendstoLocallyUniformlyWithout
    (fun n (x : ℚ) => ↑((fun n q =>
      if q ≤ 0 then 0 else mkRat (Int.sqrt (q.num * 4 ^ n) + 1) (q.den * 4 ^ n).sqrt) n x))
    (fun q => √↑q) := by
  rw [TendstoLocallyUniformlyWithout]
  intro ε hε x
  dsimp
  rcases lt_or_ge x 0 with h|h
  · use Set.Iic 0, Iic_mem_nhds h, 0
    intro b _ y hy
    change y ≤ (0:ℝ) at hy
    have hy' := Rat.cast_nonpos.mp hy
    have h₂ : Int.sqrt (y.num * 4 ^ b) = 0 := by
      rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
      exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr <| hy') (by positivity)
    simp [Real.sqrt_eq_zero'.mpr hy, hε, hy']
  · set tm := max (2 * x) 1
    have htm₀ : 0 < tm := by positivity
    have htm : x < tm := by
      by_cases 0 < x
      · exact lt_sup_of_lt_left (by linarith)
      · exact lt_sup_of_lt_right (by linarith)
    use Set.Ioo (-1) tm, Ioo_mem_nhds (by linarith) htm
    set ε' := (ε / (7 * tm.sqrt)) with hε'
    set a := Int.clog 2 (1 / ε') with ha
    use a.toNat
    rintro b hb q ⟨hq₁, hq₂⟩
    by_cases hq₃ : q ≤ 0
    · have h₂ : Int.sqrt (q.num * 4 ^ b) = 0 := by
        rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
        exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr hq₃) (by positivity)
      simp [Real.sqrt_eq_zero'.mpr (Rat.cast_nonpos.mpr hq₃), hε, hq₃]
    have hb₂ := mkRat_sub_le_sqrt q b
    rw [if_neg hq₃] at hb₂ ⊢
    push Not at hq₃
    suffices 7 * √↑q / 2 ^ b < ε by
      have hb₁ := rsqrt_le_boundedSqrt q b 4 (by norm_num)
      rw [Nat.cast_ofNat] at hb₁
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    replace hb : Int.clog 2 (1 / ε') ≤ b := Int.toNat_le.mp hb
    replace hb : 2 ^ (Int.clog 2 (1 / ε')) ≤ (2 : ℝ) ^ (b : ℤ) := zpow_le_zpow_right₀ (one_le_two)
      hb
    replace hb := le_trans (Int.self_le_zpow_clog Nat.one_lt_two (1 / ε')) hb
    rw [hε', zpow_natCast] at hb
    have hqtm := Real.sqrt_lt_sqrt (Rat.cast_nonneg.mpr hq₃.le) hq₂
    have hq0 := Real.sqrt_pos_of_pos (Rat.cast_pos.mpr hq₃)
    simp only [one_div, inv_div] at hb
    rw [div_le_iff₀ (by positivity)] at hb
    rw [div_lt_iff₀ (by positivity), _root_.mul_comm ε]
    linarith

/-- Definition of `sqrt`. -/
noncomputable def sqrt : ComputableℝSeq → ComputableℝSeq :=
  ofTendstoLocallyUniformlyContinuous
  (f := Real.sqrt)
  (hf := Real.continuous_sqrt)
  (fImpl := fun n q ↦ sqrtq q n)
  (fImpl_l := fun n q ↦ mkRat (Int.sqrt (q.num * 4^n)) ((q.den * 4^n).sqrt + 1))
  (fImpl_u := fun n q ↦ if q ≤ 0 then 0 else mkRat (Int.sqrt (q.num * 4^n) + 1) (q.den * 4^n).sqrt)
  (hImplDef := by
    rintro n ⟨⟨q₁, q₂⟩, hq⟩
    dsimp [sqrtq]
    split_ifs
    · have h : Int.sqrt (q₁.num * 4 ^ n) = 0 := by
        rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
        exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr (by linarith)) (by positivity)
      simp [h]; rfl
    · rfl
  )
  (hTLU_l := TLUW_lower) (hTLU_u := TLUW_upper)
  (hlb := by
    intro n ⟨⟨q₁, q₂⟩, hq⟩ x ⟨hx₁, hx₂⟩
    have := lb_le_sqrt_lb ⟨⟨q₁, q₂⟩, hq⟩ n
    rw [sqrtq, boundedSqrt] at this
    split_ifs at this with h
    · have h0 : Int.sqrt (q₁.num * 4 ^ n) = 0 := by
        rw [Int.sqrt.eq_1, Int.ofNat_eq_zero, Nat.sqrt_eq_zero, Int.toNat_eq_zero]
        exact Int.mul_nonpos_of_nonpos_of_nonneg (Rat.num_nonpos.mpr (by linarith)) (by positivity)
      simp [h0]
    · exact le_trans this (Real.sqrt_le_sqrt hx₁)
    )
  (hub := by
    intro n ⟨⟨q₁, q₂⟩, hq⟩ x ⟨hx₁, hx₂⟩
    dsimp at *
    split_ifs with h
    · suffices √x = 0 by
        simp [this]
      rw [Real.sqrt_eq_zero']
      exact le_trans hx₂ (Rat.cast_nonpos.mpr h)
    · have := sqrt_ub_le_ub ⟨⟨q₁, q₂⟩, hq⟩ n
      rw [sqrtq, boundedSqrt, if_neg h] at this
      exact le_trans (Real.sqrt_le_sqrt hx₂) this
  )

end Sqrt

end ComputableℝSeq

namespace IsComputable

noncomputable instance instComputableSqrt (x : ℝ) [hx : IsComputable x] : IsComputable (x.sqrt) :=
  .lift (Real.sqrt) ComputableℝSeq.Sqrt.sqrt
    (by apply ComputableℝSeq.val_ofTendstoLocallyUniformlyContinuous) hx

noncomputable instance instComputableGoldenRatio : IsComputable Real.goldenRatio :=
  inferInstanceAs (IsComputable ((1 + √5) / 2))

noncomputable instance instComputableGoldenConj : IsComputable Real.goldenConj :=
  inferInstanceAs (IsComputable ((1 - √5) / 2))

end IsComputable
