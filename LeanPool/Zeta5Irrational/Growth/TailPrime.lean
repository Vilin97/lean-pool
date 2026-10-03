/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Data.Int.Star
import Mathlib.Tactic.ENatToNat
public import LeanPool.Zeta5Irrational.Growth.InnerPrime
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # The inner tail: `-L_p ≤ p (x F(x) + 27/16) + O(x²)`

For an explicit level `k` (the rounded minimiser of the quadratic majorant) the discrete bound of
`inner_Lp_le` is at most `p (x F(x) + 27/16) + C(x)`, where
`F(x) = 4λ + 2λ{x} - 12λ{αx}`, `λ = 37/40`, `α = 3/40`, `x = K/p`.
-/

public section

open Finset

namespace Zeta5Irrational

/-! ### Elementary facts -/

lemma sum_range_tri (t : ℚ) (L : ℕ) :
    ∑ i ∈ range L, ((t - 2 * i) / 2) = (L : ℚ) * (t - L + 1) / 2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma psiR_le (k β : ℤ) : psiR k β ≤ ((k - β + 1 : ℤ) : ℚ) ^ 2 / 8 := by
  unfold psiR
  set t := k - β with ht
  have hsum :
    ∑ i ∈ range (lrow k β), (((k : ℚ) - 2 * i - β) / 2) =
      (lrow k β : ℚ) * ((t : ℚ) - lrow k β + 1) / 2 := by
    rw [← sum_range_tri]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht]; push_cast; ring
  rw [hsum]
  unfold lrow
  rcases le_or_gt (t + 1) 0 with h | h
  · have : ((k - β + 1) / 2).toNat = 0 := by omega
    rw [this]; simp only [Nat.cast_zero, zero_mul, zero_div]; positivity
  · rcases Int.emod_two_eq_zero_or_one t with h2 | h2
    · have e : (((k - β + 1) / 2).toNat : ℚ) = (t : ℚ) / 2 := by
        have : (((k - β + 1) / 2).toNat : ℤ) * 2 = t := by omega
        have : ((((k - β + 1) / 2).toNat : ℤ) : ℚ) * 2 = (t : ℚ) := by exact_mod_cast this
        push_cast at this; linarith
      rw [e]; push_cast; nlinarith [sq_nonneg ((t : ℚ) + 1)]
    · have e : (((k - β + 1) / 2).toNat : ℚ) = ((t : ℚ) + 1) / 2 := by
        have : (((k - β + 1) / 2).toNat : ℤ) * 2 = t + 1 := by omega
        have : ((((k - β + 1) / 2).toNat : ℤ) : ℚ) * 2 = (t : ℚ) + 1 := by exact_mod_cast this
        push_cast at this; linarith
      rw [e]; push_cast; nlinarith [sq_nonneg ((t : ℚ) + 1)]

lemma sum_aCnt {p m v : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) : ∑ c ∈ Icc 1 m, aCnt p v c = v := by
  unfold aCnt
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero,
    Finset.sum_const_zero, add_zero, add_zero, Finset.sum_const, Finset.sum_const, smul_eq_mul,
    smul_eq_mul, mul_one, mul_one]
  have h1 : (Icc 1 m).filter (fun c => c ≤ v) = Icc 1 (min m v) := by
    ext c;
    simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have h2 : (Icc 1 m).filter (fun c => p - v ≤ c) = Icc (max 1 (p - v)) m := by
    ext c;
    simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [h1, h2, Nat.card_Icc, Nat.card_Icc]
  omega

lemma aCnt_range {p m v c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (_hc1 : 1 ≤ c) (hcm : c ≤ m) :
    (if m < v then 1 else 0) ≤ aCnt p v c ∧ aCnt p v c ≤ (if m < v then 1 else 0) + 1 := by
  unfold aCnt; split_ifs <;> omega

/-- **Popoviciu**: values in an interval of length `7` have `∑ φ² ≤ (∑ φ)²/m + 49m/4`. -/
lemma popoviciu {ι : Type*} (s : Finset ι) (φ : ι → ℝ) (L : ℝ)
    (hφ : ∀ c ∈ s, L ≤ φ c ∧ φ c ≤ L + 7) (hs : 0 < s.card) :
    ∑ c ∈ s, φ c ^ 2 ≤ (∑ c ∈ s, φ c) ^ 2 / s.card + 49 * s.card / 4 := by
  set m : ℝ := (s.card : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast hs
  have h1 : ∑ c ∈ s, (φ c - L) ^ 2 ≤ 7 * ∑ c ∈ s, (φ c - L) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have := hφ c hc
    nlinarith
  set U := ∑ c ∈ s, (φ c - L) with hU
  have hsumφ : ∑ c ∈ s, φ c = U + m * L := by
    rw [hU, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  have hsq : ∑ c ∈ s, φ c ^ 2 = ∑ c ∈ s, (φ c - L) ^ 2 + 2 * L * U + m * L ^ 2 := by
    rw [hU, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show m * L ^ 2 = ∑ _c ∈ s, L ^ 2 by rw [Finset.sum_const, nsmul_eq_mul]]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_; ring
  rw [hsq, hsumφ]
  have h2 : 7 * U ≤ U ^ 2 / m + 49 * m / 4 := by
    rw [div_add' _ _ _ hm0.ne', le_div_iff₀ hm0]
    nlinarith [sq_nonneg (U - 7 * m / 2)]
  have e : (U + m * L) ^ 2 / m = U ^ 2 / m + 2 * L * U + m * L ^ 2 := by field_simp; ring
  rw [e]
  linarith

/-- The continuous layer function `J(u) = ∑_{j ≤ 1000} (u - j/2)⁺`. -/
noncomputable def Jc (u : ℝ) : ℝ :=
  ∑ j ∈ (Icc 1 1000 : Finset ℕ), max 0 (u - (j : ℝ) / 2)

lemma layer_eq {p : ℕ} (hp : 0 < p) (h : ℕ) : layer p 1000 h = (p : ℝ) * Jc ((h : ℝ) / p) := by
  unfold layer Jc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [mul_max_of_nonneg _ _ hpR.le, mul_zero, mul_sub, mul_div_cancel₀ _ hpR.ne']
  congr 1; ring

/-- `2 J(u) = 2u² - u + η(1 - η)/2` with `η = {2u}`, for `0 ≤ u ≤ 500`. -/
lemma two_Jc_eq {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 500) :
    2 * Jc u = 2 * u ^ 2 - u + Int.fract (2 * u) * (1 - Int.fract (2 * u)) / 2 := by
  set μ := ⌊2 * u⌋₊ with hμ
  have hμ1 : (μ : ℝ) ≤ 2 * u := Nat.floor_le (by linarith)
  have hμ2 : 2 * u < μ + 1 := Nat.lt_floor_add_one _
  have hμ1000 : μ ≤ 1000 := by
    have : (μ : ℝ) ≤ 1000 := by linarith
    exact_mod_cast this
  have hfr : Int.fract (2 * u) = 2 * u - μ := by
    rw [Int.fract,
      show ⌊2 * u⌋ = (μ : ℤ) by
        rw [hμ, ← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by linarith))]]
    push_cast; ring
  have hsplit : Jc u = ∑ j ∈ (Icc 1 μ : Finset ℕ), (u - (j : ℝ) / 2) := by
    unfold Jc
    rw [←
      Finset.sum_subset (Finset.Icc_subset_Icc_right hμ1000)
        (fun j hj hjn => by
          simp only [Finset.mem_Icc, not_and, not_le] at hj hjn
          have := hjn hj.1
          have : (μ : ℝ) + 1 ≤ j := by exact_mod_cast this
          exact max_eq_left (by linarith))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := (Finset.mem_Icc.mp hj).2
    have : (j : ℝ) ≤ μ := by exact_mod_cast this
    exact max_eq_right (by linarith)
  have hclosed : ∑ j ∈ (Icc 1 μ : Finset ℕ), (u - (j : ℝ) / 2) = μ * u - (μ : ℝ) * (μ + 1) / 4 := by
    induction μ with
    | zero => simp
    | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring
  rw [hsplit, hclosed, hfr]
  ring

lemma phi_bounds {p m v v' c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p) (hc1 : 1 ≤ c)
    (hcm : c ≤ m) :
    6 * (if m < v' then (1 : ℝ) else 0) - (if m < v then (1 : ℝ) else 0) - 1 ≤
        6 * (aCnt p v' c : ℝ) - aCnt p v c ∧
      6 * (aCnt p v' c : ℝ) - aCnt p v c ≤
        6 * (if m < v' then (1 : ℝ) else 0) - (if m < v then (1 : ℝ) else 0) - 1 + 7 := by
  have r1 := aCnt_range hm hv hc1 hcm
  have r2 := aCnt_range hm hv' hc1 hcm
  split_ifs at r1 r2 ⊢ <;>
    · have e1 : ((aCnt p v c : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show aCnt p v c ≤ 2 by omega)
      have e2 : ((aCnt p v' c : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show aCnt p v' c ≤ 2 by omega)
      first
      | ( have f1 : (1 : ℝ) ≤ aCnt p v c := by exact_mod_cast (show 1 ≤ aCnt p v c by omega)
          have f2 : (1 : ℝ) ≤ aCnt p v' c := by exact_mod_cast (show 1 ≤ aCnt p v' c by omega)
          constructor <;> linarith)
      | ( have f1 : (1 : ℝ) ≤ aCnt p v c := by exact_mod_cast (show 1 ≤ aCnt p v c by omega)
          have f2 : (aCnt p v' c : ℝ) ≤ 1 := by exact_mod_cast (show aCnt p v' c ≤ 1 by omega)
          have f3 : (0 : ℝ) ≤ aCnt p v' c := by positivity
          constructor <;> linarith)
      | ( have f1 : (aCnt p v c : ℝ) ≤ 1 := by exact_mod_cast (show aCnt p v c ≤ 1 by omega)
          have f2 : (1 : ℝ) ≤ aCnt p v' c := by exact_mod_cast (show 1 ≤ aCnt p v' c by omega)
          have f3 : (0 : ℝ) ≤ aCnt p v c := by positivity
          constructor <;> linarith)
      | ( have f1 : (aCnt p v c : ℝ) ≤ 1 := by exact_mod_cast (show aCnt p v c ≤ 1 by omega)
          have f2 : (aCnt p v' c : ℝ) ≤ 1 := by exact_mod_cast (show aCnt p v' c ≤ 1 by omega)
          have f3 : (0 : ℝ) ≤ aCnt p v c := by positivity
          have f4 : (0 : ℝ) ≤ aCnt p v' c := by positivity
          constructor <;> linarith)

lemma hIn_le_sq (n p : ℕ) (k τ : ℤ)
    (hk : k = τ + (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4) - 1) (a a' : ℕ) :
    hIn n p k a a' ≤ ((τ : ℝ) - (6 * (a' : ℝ) - a)) ^ 2 / 8 := by
  unfold hIn
  have h1 :=
    psiR_le k (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 + 6 * (a' : ℤ) - a)
  have hz :
    k - (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 + 6 * (a' : ℤ) - a) + 1 =
      τ - (6 * (a' : ℤ) - a) :=
    by rw [hk]; ring
  rw [hz] at h1
  have h2 := (Rat.cast_le (K := ℝ)).mpr h1
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_intCast] at h2
  refine h2.trans (le_of_eq ?_)
  push_cast; ring

lemma layer_le {p : ℕ} (hp0 : 0 < p) (H : ℕ) (hu500 : (H : ℝ) / p ≤ 500) :
    2 * layer p 1000 H ≤ 2 * (H : ℝ) ^ 2 / p - H + p / 8 := by
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp0
  have hu0 : (0 : ℝ) ≤ (H : ℝ) / p := by positivity
  rw [layer_eq hp0]
  have e := two_Jc_eq hu0 hu500
  set η := Int.fract (2 * ((H : ℝ) / p)) with hη
  have hη0 : 0 ≤ η := Int.fract_nonneg _
  have hη1 : η < 1 := Int.fract_lt_one _
  have hηb : η * (1 - η) ≤ 1 / 4 := by nlinarith [sq_nonneg (η - 1 / 2)]
  have : 2 * ((p : ℝ) * Jc ((H : ℝ) / p)) = p * (2 * Jc ((H : ℝ) / p)) := by ring
  rw [this, e]
  have e2 : (p : ℝ) * (2 * ((H : ℝ) / p) ^ 2 - (H : ℝ) / p) = 2 * (H : ℝ) ^ 2 / p - H := by
    field_simp
  have e3 :
    (p : ℝ) * (2 * ((H : ℝ) / p) ^ 2 - (H : ℝ) / p + η * (1 - η) / 2) =
      2 * (H : ℝ) ^ 2 / p - H + p * (η * (1 - η)) / 2 :=
    by rw [← e2]; ring
  rw [e3]
  have := mul_le_mul_of_nonneg_left hηb hpR0.le
  linarith

lemma quad_le {hR SR m τ : ℝ} (hm0 : 0 < m) (h1 : τ ≤ (SR + 2 * hR) / m + 1 / 2)
    (h2 : (SR + 2 * hR) / m + 1 / 2 < τ + 1) :
    -hR * τ + (m * τ ^ 2 - 2 * τ * SR + SR ^ 2 / m) / 4 ≤ -hR * SR / m - hR ^ 2 / m + m / 16 := by
  set τs := (SR + 2 * hR) / m with hτs
  have hd : (τ - τs) ^ 2 ≤ 1 / 4 := by nlinarith
  have e :
    -hR * τ + (m * τ ^ 2 - 2 * τ * SR + SR ^ 2 / m) / 4 =
      -hR * SR / m - hR ^ 2 / m + m * (τ - τs) ^ 2 / 4 :=
    by rw [hτs]; field_simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left hd hm0.le
  linarith

lemma diff_le {hR SR p : ℝ} (hp : 1 < p) (hh0 : 0 ≤ hR) (hhS : 0 ≤ hR + SR) :
    2 * hR ^ 2 / p - hR ^ 2 / ((p - 1) / 2) - hR * SR / ((p - 1) / 2) + 2 * hR * SR / p ≤ 0 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have e :
    2 * hR ^ 2 / p - hR ^ 2 / ((p - 1) / 2) - hR * SR / ((p - 1) / 2) + 2 * hR * SR / p =
      -(2 * (hR * (hR + SR))) / (p * (p - 1)) :=
    by field_simp; ring
  rw [e]
  apply div_nonpos_of_nonpos_of_nonneg
  · have := mul_nonneg hh0 hhS; linarith
  · positivity

/-- `F(x) = 4λ + 2λ{x} - 12λ{αx}`. -/
@[expose] noncomputable def Ftail (x : ℝ) : ℝ :=
  4 * (37 / 40) + 2 * (37 / 40) * Int.fract x - 12 * (37 / 40) * Int.fract (3 / 40 * x)

/-- The additive error of the tail bound. -/
@[expose] noncomputable def Ctail (n p : ℕ) : ℝ :=
  4 * (37 * n : ℝ) / p + ((ktopI n p - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1

/-- Sum the quadratic class bound using the seven-unit range of the counts. -/
lemma tail_class_sum_le (n p v v' : ℕ) (k τ : ℤ)
    (hodd : 2 * (p / 2) + 1 = p) (hvp : v < p) (hv'p : v' < p)
    (hm : 0 < p / 2)
    (hk : k = τ + (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4) - 1) :
    2 * ∑ c ∈ Icc 1 (p / 2), hIn n p k (aCnt p v c) (aCnt p v' c) ≤
      ((p / 2 : ℕ) * (τ : ℝ) ^ 2 - 2 * τ * (6 * (v' : ℝ) - v) +
        (6 * (v' : ℝ) - v) ^ 2 / (p / 2 : ℕ) + 49 * (p / 2 : ℕ) / 4) / 4 := by
  let m := p / 2
  let SR : ℝ := 6 * (v' : ℝ) - v
  set φ : ℕ → ℝ := fun c => 6 * (aCnt p v' c : ℝ) - aCnt p v c with hφ
  have hIn_le : ∀ c, hIn n p k (aCnt p v c) (aCnt p v' c) ≤ ((τ : ℝ) - φ c) ^ 2 / 8 := fun c =>
    hIn_le_sq n p k τ hk _ _
  have hcard : ((Icc 1 m).card : ℝ) = m := by rw [Nat.card_Icc]; simp
  have hSphi : ∑ c ∈ Icc 1 m, φ c = SR := by
    rw [hφ, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e1 := sum_aCnt hodd hvp
    have e2 := sum_aCnt hodd hv'p
    have e1' : ∑ c ∈ Icc 1 m, (aCnt p v c : ℝ) = v := by exact_mod_cast e1
    have e2' : ∑ c ∈ Icc 1 m, (aCnt p v' c : ℝ) = v' := by exact_mod_cast e2
    rw [e1', e2']
  have hpop : ∑ c ∈ Icc 1 m, φ c ^ 2 ≤ SR ^ 2 / m + 49 * m / 4 := by
    have hm1 : 0 < (Icc 1 m).card := by rw [Nat.card_Icc]; omega
    have :=
      popoviciu (Icc 1 m) φ
        (6 * (if m < v' then (1 : ℝ) else 0) - (if m < v then (1 : ℝ) else 0) - 1)
        (fun c hc => phi_bounds hodd hvp hv'p (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2)
        hm1
    rw [hcard, hSphi] at this
    exact this
  have hsq :
    ∑ c ∈ Icc 1 m, ((τ : ℝ) - φ c) ^ 2 =
      (m : ℝ) * (τ : ℝ) ^ 2 - 2 * τ * SR + ∑ c ∈ Icc 1 m, φ c ^ 2 := by
    have :
      ∑ c ∈ Icc 1 m, ((τ : ℝ) - φ c) ^ 2 = ∑ c ∈ Icc 1 m, ((τ : ℝ) ^ 2 - 2 * τ * φ c + φ c ^ 2) :=
      by refine Finset.sum_congr rfl fun c _ => ?_; ring
    rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ←
      Finset.mul_sum, hSphi, hcard]
  have hclass :
    2 * ∑ c ∈ Icc 1 m, hIn n p k (aCnt p v c) (aCnt p v' c) ≤
      ((m : ℝ) * (τ : ℝ) ^ 2 - 2 * τ * SR + SR ^ 2 / m + 49 * m / 4) / 4 := by
    have := Finset.sum_le_sum fun c (_ : c ∈ Icc 1 m) => hIn_le c
    rw [← Finset.sum_div, hsq] at this
    linarith
  exact hclass

/-- The integral level obtained by rounding the quadratic minimizer. -/
noncomputable def tailLevel (n p : ℕ) : ℤ :=
  ⌊(6 * ((3 * n % p : ℕ) : ℝ) - ((40 * n % p : ℕ) : ℝ) +
      2 * (37 * n : ℝ)) / ((p / 2 : ℕ) : ℝ) + 1 / 2⌋ +
    (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4) - 1

/-- The rounded minimizer lies in the admissible interval of integral levels. -/
lemma tailLevel_mem (n p : ℕ) (hodd : 2 * (p / 2) + 1 = p)
    (hp7 : 7 ≤ p) (hin : 3 * p ≤ 40 * n) :
    kloI n p ≤ tailLevel n p ∧ tailLevel n p ≤ ktopI n p := by
  -- notation
  have hp0 : 0 < p := by omega
  have hpR : (7 : ℝ) ≤ p := by exact_mod_cast hp7
  set m := p / 2 with hmdef
  have hmR : (m : ℝ) = ((p : ℝ) - 1) / 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) = p := by exact_mod_cast hodd
    push_cast at this; linarith
  have hm0 : (0 : ℝ) < m := by rw [hmR]; linarith
  set v := 40 * n % p with hv
  set v' := 3 * n % p with hv'
  have hvp : v < p := Nat.mod_lt _ hp0
  have hv'p : v' < p := Nat.mod_lt _ hp0
  set q := 40 * n / p with hq
  set q' := 3 * n / p with hq'
  have hdivK : (40 * n : ℝ) = q * p + v := by
    have := Nat.div_add_mod (40 * n) p
    have h' : ((p * q + v : ℕ) : ℝ) = ((40 * n : ℕ) : ℝ) := by rw [this]
    push_cast at h'; linarith
  have hdivN : (3 * n : ℝ) = q' * p + v' := by
    have := Nat.div_add_mod (3 * n) p
    have h' : ((p * q' + v' : ℕ) : ℝ) = ((3 * n : ℕ) : ℝ) := by rw [this]
    push_cast at h'; linarith
  set hR : ℝ := (37 * n : ℝ) with hhR
  set SR : ℝ := 6 * (v' : ℝ) - v with hSR
  set τs : ℝ := (SR + 2 * hR) / m with hτs
  set τ : ℤ := ⌊τs + 1 / 2⌋ with hτ
  have hδ1 : (τ : ℝ) ≤ τs + 1 / 2 := Int.floor_le _
  have hδ2 : τs + 1 / 2 < τ + 1 := Int.lt_floor_add_one _
  set B : ℤ := 12 * (q' : ℤ) - 2 * (q : ℤ) - 4 with hB
  set k : ℤ := τ + B - 1 with hk
    -- basic size facts
  have hqlt : (40 * n : ℝ) < ((q : ℝ) + 1) * p := by
    have := Nat.lt_div_mul_add (a := 40 * n) hp0
    have : ((40 * n : ℕ) : ℝ) < ((q * p + p : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hq'le : (q' : ℝ) * p ≤ 3 * n := by
    rw [hdivN]; have : (0 : ℝ) ≤ v' := by positivity
    linarith
  have hnin : (3 : ℝ) * p ≤ 40 * n := by exact_mod_cast hin
  have hvR : (v : ℝ) < p := by exact_mod_cast hvp
  have hv'R : (v' : ℝ) < p := by exact_mod_cast hv'p
  have hv0 : (0 : ℝ) ≤ v := by positivity
  have hv'0 : (0 : ℝ) ≤ v' := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq'0 : (0 : ℝ) ≤ q' := by positivity
  have hτsm : τs * m = SR + 2 * hR := by
    rw [hτs];
    field_simp
      -- `τs` bounds
  have hτs_lo : 8 ≤ τs := by
    have : 8 * (m : ℝ) ≤ SR + 2 * hR := by rw [hmR, hSR, hhR]; linarith
    rw [hτs, le_div_iff₀ hm0]; linarith
  have h40 : 40 * (q' : ℝ) ≤ 3 * q + 3 := by
    have e1 : 40 * ((q' : ℝ) * p) ≤ 120 * n := by linarith
    have e2 : 120 * (n : ℝ) < 3 * ((q : ℝ) * p) + 3 * p := by linarith
    have : (40 * (q' : ℝ) - 3 * q - 3) * p < 0 := by ring_nf; ring_nf at e1 e2; linarith
    by_contra hc
    rw [not_le] at hc
    have :=
      mul_nonneg (show (0 : ℝ) ≤ 40 * q' - 3 * q - 3 by linarith) (show (0 : ℝ) ≤ p by linarith)
    linarith
  have hτs_hi : τs ≤ 10 * (q : ℝ) + 24 - 12 * q' := by
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 7 := by linarith
    have f1 := mul_nonneg hq0 hp1
    have f2 := mul_le_mul_of_nonneg_right h40 (show (0 : ℝ) ≤ (p : ℝ) - 1 by linarith)
    have : (SR + 2 * hR) ≤ (10 * (q : ℝ) + 24 - 12 * q') * m := by
      rw [hmR, hSR, hhR]; ring_nf;
      ring_nf at f1 f2 hqlt; nlinarith
    rw [hτs, div_le_iff₀ hm0];
    linarith
      -- `k` is admissible
  have hk1 : kloI n p ≤ k := by
    have : (1 : ℝ) ≤ τ := by
      have : (8 : ℝ) + 1 / 2 - 1 < τ := by linarith
      have h1 : (8 : ℤ) ≤ τ := by
        have : (7 : ℝ) < τ := by linarith
        exact_mod_cast (show (7 : ℤ) < τ by exact_mod_cast this)
      exact_mod_cast (show (1 : ℤ) ≤ τ by omega)
    have hτ1 : (1 : ℤ) ≤ τ := by exact_mod_cast this
    have hklo : kloI n p = -2 * (q : ℤ) - 6 := rfl
    rw [hklo, hk, hB]
    have hq0Z : (0 : ℤ) ≤ q := by positivity
    have hq'0Z : (0 : ℤ) ≤ q' := by positivity
    generalize (q : ℤ) = Q at *
    generalize (q' : ℤ) = Q' at *
    omega
  have hk2 : k ≤ ktopI n p := by
    have hτle : (τ : ℝ) ≤ 10 * (q : ℝ) + 24 - 12 * q' + 1 / 2 := by linarith
    have : τ ≤ 10 * (q : ℤ) + 24 - 12 * (q' : ℤ) := by
      have : (τ : ℝ) < 10 * (q : ℝ) + 24 - 12 * q' + 1 := by linarith
      have : (τ : ℝ) < ((10 * (q : ℤ) + 24 - 12 * (q' : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
      have := (Int.cast_lt (R := ℝ)).mp this
      omega
    have hktop : ktopI n p = 8 * (q : ℤ) + 20 := rfl
    rw [hktop, hk, hB]
    have hq0Z : (0 : ℤ) ≤ q := by positivity
    generalize (q : ℤ) = Q at *
    generalize (q' : ℤ) = Q' at *
    omega
  change kloI n p ≤ k ∧ k ≤ ktopI n p
  exact ⟨hk1, hk2⟩

variable {p : ℕ} [hp : Fact p.Prime]

section

variable {n : ℕ} (hn : 33 ≤ n) (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p)
  (hsmall : ¬p * Mcut ≤ 40 * n) (hin : 3 * p ≤ 40 * n) (hsq : 2 * (40 * n) < p ^ 2)
  (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)

include hn hodd hp7 hsmall hin hsq hdeg in
/-- **The tail bound**: `-L_p ≤ p (x F(x) + 27/16) + C`. -/
theorem tail_Lp_le :
    -(Lp n p : ℝ) ≤ (p : ℝ) * ((40 * n / p : ℝ) * Ftail (40 * n / p) + 27 / 16) + Ctail n p := by
  -- notation
  have hp0 : 0 < p := by omega
  have hpR : (7 : ℝ) ≤ p := by exact_mod_cast hp7
  set m := p / 2 with hmdef
  have hmR : (m : ℝ) = ((p : ℝ) - 1) / 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) = p := by exact_mod_cast hodd
    push_cast at this; linarith
  have hm0 : (0 : ℝ) < m := by rw [hmR]; linarith
  set v := 40 * n % p with hv
  set v' := 3 * n % p with hv'
  have hvp : v < p := Nat.mod_lt _ hp0
  have hv'p : v' < p := Nat.mod_lt _ hp0
  set q := 40 * n / p with hq
  set q' := 3 * n / p with hq'
  have hdivK : (40 * n : ℝ) = q * p + v := by
    have := Nat.div_add_mod (40 * n) p
    have h' : ((p * q + v : ℕ) : ℝ) = ((40 * n : ℕ) : ℝ) := by rw [this]
    push_cast at h'; linarith
  have hdivN : (3 * n : ℝ) = q' * p + v' := by
    have := Nat.div_add_mod (3 * n) p
    have h' : ((p * q' + v' : ℕ) : ℝ) = ((3 * n : ℕ) : ℝ) := by rw [this]
    push_cast at h'; linarith
  set hR : ℝ := (37 * n : ℝ) with hhR
  set SR : ℝ := 6 * (v' : ℝ) - v with hSR
  set τs : ℝ := (SR + 2 * hR) / m with hτs
  set τ : ℤ := ⌊τs + 1 / 2⌋ with hτ
  have hδ1 : (τ : ℝ) ≤ τs + 1 / 2 := Int.floor_le _
  have hδ2 : τs + 1 / 2 < τ + 1 := Int.lt_floor_add_one _
  set B : ℤ := 12 * (q' : ℤ) - 2 * (q : ℤ) - 4 with hB
  set k : ℤ := τ + B - 1 with hk
    -- basic size facts
  have hqlt : (40 * n : ℝ) < ((q : ℝ) + 1) * p := by
    have := Nat.lt_div_mul_add (a := 40 * n) hp0
    have : ((40 * n : ℕ) : ℝ) < ((q * p + p : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hq'le : (q' : ℝ) * p ≤ 3 * n := by
    rw [hdivN]; have : (0 : ℝ) ≤ v' := by positivity
    linarith
  have hnin : (3 : ℝ) * p ≤ 40 * n := by exact_mod_cast hin
  have hvR : (v : ℝ) < p := by exact_mod_cast hvp
  have hv'R : (v' : ℝ) < p := by exact_mod_cast hv'p
  have hv0 : (0 : ℝ) ≤ v := by positivity
  have hv'0 : (0 : ℝ) ≤ v' := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq'0 : (0 : ℝ) ≤ q' := by positivity
  have hτsm : τs * m = SR + 2 * hR := by
    rw [hτs];
    field_simp
      -- `τs` bounds
  have hkLevel : k = tailLevel n p := rfl
  obtain ⟨hk1, hk2⟩ := tailLevel_mem n p hodd hp7 hin
  rw [← hkLevel] at hk1 hk2
  have main :=
    inner_Lp_le hn hodd hp7 hsmall hin hsq hdeg k hk1
      hk2
        -- the class sum
  have hclass := tail_class_sum_le n p v v' k τ hodd hvp hv'p
    (by exact_mod_cast hm0) (by rw [hk, hB])
  have hpR0 : (0 : ℝ) < p := by linarith
  have hu500 : ((37 * n : ℕ) : ℝ) / p ≤ 500 := by
    rw [div_le_iff₀ hpR0]
    have : (40 * n : ℝ) < 400 * p := by
      unfold Mcut at hsmall; rw [not_le] at hsmall
      exact_mod_cast (show 40 * n < 400 * p by linarith)
    push_cast; linarith
  have hlay := layer_le hp0 (37 * n) hu500
  have e37 : ((37 * n : ℕ) : ℝ) = hR := by rw [hhR]; push_cast; ring
  rw [e37] at hlay
  have hquad := quad_le (hR := hR) (SR := SR) (τ := (τ : ℝ)) hm0 hδ1 hδ2
  have hdiff :=
    diff_le (hR := hR) (SR := SR) (p := (p : ℝ)) (by linarith) (by rw [hhR]; positivity)
      (by rw [hhR, hSR]; linarith)
  rw [←
    hmR] at hdiff
        -- the target
  have hfK : Int.fract ((40 * n / p : ℝ)) = (v : ℝ) / p := by
    have := Int.fract_div_natCast_eq_div_natCast_mod (k := ℝ) (m := 40 * n) (n := p)
    push_cast at this; exact this
  have hfN : Int.fract ((3 : ℝ) / 40 * (40 * n / p)) = (v' : ℝ) / p := by
    have := Int.fract_div_natCast_eq_div_natCast_mod (k := ℝ) (m := 3 * n) (n := p)
    have e : (3 : ℝ) / 40 * (40 * n / p) = ((3 * n : ℕ) : ℝ) / (p : ℕ) := by push_cast; ring
    rw [e]; exact this
  have hT :
    (p : ℝ) * ((40 * n / p : ℝ) * Ftail (40 * n / p) + 27 / 16) =
      4 * hR - 2 * hR * SR / p + 27 * p / 16 :=
    by unfold Ftail; rw [hfK, hfN, hSR, hhR]; field_simp; ring
  have hE :
    ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) ≤ ((ktopI n p - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) :=
  by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast (show k - kloI n p ≤ ktopI n p - kloI n p by omega)
  have hkR : (k : ℝ) = τ + 12 * (q' : ℝ) - 2 * q - 5 := by rw [hk, hB]; push_cast; ring
  have hCt :
    Ctail n p =
      4 * hR / p + ((ktopI n p - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1 :=
    by unfold Ctail; rw [hhR]
  have h4 : 0 ≤ 4 * hR / p := by positivity
  rw [hT, hCt]
  have hmain := main
  rw [hkR, e37] at hmain
  simp only [← hq, ← hq', ← hmdef, ← hv, ← hv'] at hmain
  have hmR16 : (m : ℝ) / 16 + 49 * m / 16 = 25 * (p : ℝ) / 16 - 25 / 16 := by rw [hmR]; ring
  have s1 :
    -(Lp n p : ℝ) ≤
      2 * layer p 1000 hR - hR * τ + 5 * hR +
              2 * ∑ x ∈ Icc 1 m, hIn n p k (aCnt p v x) (aCnt p v' x) +
            ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) +
          2 * Bmax n p +
        1 := by
    have :
      -2 * hR * (q : ℝ) + 12 * hR * q' - hR * ((τ : ℝ) + 12 * q' - 2 * q - 5) =
        -hR * τ + 5 * hR :=
      by ring
    linarith
  have s2 :
    -(Lp n p : ℝ) ≤
      2 * layer p 1000 hR + 5 * hR + (-hR * SR / m - hR ^ 2 / m + m / 16) + 49 * m / 16 +
            ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) +
          2 * Bmax n p +
        1 := by
    have :
      ((m : ℝ) * (τ : ℝ) ^ 2 - 2 * τ * SR + SR ^ 2 / m + 49 * m / 4) / 4 =
        ((m : ℝ) * (τ : ℝ) ^ 2 - 2 * τ * SR + SR ^ 2 / m) / 4 + 49 * m / 16 :=
      by ring
    linarith
  have s3 :
    -(Lp n p : ℝ) ≤
      2 * hR ^ 2 / p + 4 * hR + p / 8 - hR * SR / m - hR ^ 2 / m + (25 * (p : ℝ) / 16 - 25 / 16) +
            ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) +
          2 * Bmax n p +
        1 := by
    have : -hR * SR / m = -(hR * SR / m) := by ring
    linarith
  have s4 :
    -(Lp n p : ℝ) ≤
      4 * hR - 2 * hR * SR / p + 27 * p / 16 + ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) +
          2 * Bmax n p +
        1 :=
    by linarith
  linarith

end

end Zeta5Irrational
