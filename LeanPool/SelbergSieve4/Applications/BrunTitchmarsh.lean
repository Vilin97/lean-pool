/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Order.Interval.Finset.SuccPred
import LeanPool.SelbergSieve4.Selberg
import LeanPool.SelbergSieve4.Applications.PrimeCountingUpperBound
open PrimeUpperBound
open scoped Nat ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega
  BigOperators

noncomputable section
namespace BrunTitchmarsh

/-- Sieve that removes primes at most `z` from the interval `[x, x + y]`. -/
def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z) : SelbergSieve := {
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp[if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simpa [hp.ne_zero] using
      (inv_lt_one_of_one_lt₀ (by norm_cast; exact hp.one_lt) : (p : ℝ)⁻¹ < 1)
  level := z
  one_le_level := hz
}

/-- Number of primes in the real interval `[a, b]`. -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter (Nat.Prime) |>.card

theorem primesBetween_eq_ncard {a b : ℝ} (hb : 0 ≤ b) :
    primesBetween a b = Set.ncard {p : ℕ | a ≤ p ∧ p ≤ b ∧ p.Prime} := by
  unfold primesBetween
  rw [← Set.ncard_coe_finset]
  congr
  ext p
  simp only [Finset.coe_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hb,
    Set.mem_setOf_eq, and_assoc]

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

open Classical in
theorem siftedSum_eq_card :
    (primeInterSieve x y z hz).siftedSum =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
        (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  apply PrimeUpperBound.siftedSum_eq
  · exact fun _ _ => rfl
  · exact hz
  · rfl

open Classical in
theorem primesBetween_subset :
  (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (Nat.Prime) ⊆
    (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
    (Finset.Icc 1 (Nat.floor z)) := by
  intro p hp_mem
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp_mem
  rw [Finset.mem_union]
  rcases hp_mem with ⟨hp_range, hp⟩
  by_cases hpz : p ≤ z
  · right
    exact Finset.mem_Icc.mpr ⟨hp.one_le, (Nat.le_floor_iff (by linarith)).mpr hpz⟩
  · left
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hp_range, ?_⟩
    intro q hq hqz
    rw[hp.dvd_iff_eq (hq.ne_one)]
    rintro rfl
    exact hpz hqz

theorem primesBetween_le_siftedSum_add :
    primesBetween x (x+y) ≤ (primeInterSieve x y z hz).siftedSum + z := by
  classical
  trans ↑(((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)) ∪
        (Finset.Icc 1 (Nat.floor z))).card
  · rw[primesBetween]
    norm_cast
    apply Finset.card_le_card
    apply primesBetween_subset
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card
    + ↑(Finset.Icc 1 (Nat.floor z)).card
  · norm_cast
    apply Finset.card_union_le
  rw[siftedSum_eq_card]
  gcongr
  rw[Nat.card_Icc]
  simp only [add_tsub_cancel_right]
  apply Nat.floor_le
  linarith

section Remainder

theorem Ioc_filter_dvd_eq (d a b : ℕ) (hd : d ≠ 0) :
  Finset.filter (fun x => d ∣ x) (Finset.Ioc a b) =
    Finset.image (fun x => x * d) (Finset.Ioc (a / d) (b / d)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
  constructor
  · intro hn
    use  n/d
    rcases hn with ⟨⟨han, hnb⟩, hd⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.div_lt_div_of_lt_of_dvd hd han
    · exact Nat.div_le_div_right hnb
    · exact Nat.div_mul_cancel hd
  · rintro ⟨r, ⟨ha, ha'⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine (Nat.div_lt_iff_lt_mul ?_).mp ha
      omega
    · exact Nat.mul_le_of_le_div d r b ha'
    · exact Nat.dvd_mul_left d r

theorem card_Ioc_filter_dvd (d a b : ℕ) (hd : d ≠ 0) :
    (Finset.filter (fun x => d ∣ x) (Finset.Ioc a b)).card = b / d - a / d  := by
  rw [Ioc_filter_dvd_eq _ _ _ hd]
  rw [Finset.card_image_of_injective _ <| mul_left_injective₀ hd]
  simp

theorem multSum_eq (hx : 0 < x) (d : ℕ) (hd : d ≠ 0) :
    (primeInterSieve x y z hz).multSum d = ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) := by
  unfold Sieve.multSum
  rw[primeInterSieve]
  simp only [Finset.sum_boole, Nat.cast_inj]
  trans ↑(Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) |>.filter (d ∣ ·) |>.card)
  · rw [← Finset.Icc_succ_left_eq_Ioc]
    congr
    simpa [Nat.pred_eq_sub_one] using
      (Nat.succ_pred_eq_of_pos (Nat.ceil_pos.mpr hx)).symm
  · rw[card_Ioc_filter_dvd _ _ _ hd]

theorem rem_eq (hx : 0 < x) (d : ℕ) (hd : d ≠ 0) :
    (primeInterSieve x y z hz).rem d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) - (↑d)⁻¹ * y := by
  unfold Sieve.rem
  rw[multSum_eq x y z hz hx d hd]
  simp [primeInterSieve, if_neg hd]

theorem natCeil_le_self_add_one (x : ℝ) (hx : 0 ≤ x) : Nat.ceil x ≤ x + 1 := by
  trans Nat.floor x + 1
  · norm_cast
    exact Nat.ceil_le_floor_add_one x
  gcongr
  apply Nat.floor_le hx

theorem floor_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧  ↑((Nat.floor x)) = x + C := by
  use ↑(Nat.floor x) - x
  constructor
  · rw[abs_le]
    constructor
    · simp only [neg_le_sub_iff_le_add]
      linarith [Nat.lt_floor_add_one x]
    · simp only [tsub_le_iff_right]
      linarith [Nat.floor_le hx]
  · ring

theorem ceil_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧  ↑((Nat.ceil x)) = x + C := by
  use ↑(Nat.ceil x) - x
  constructor
  · rw[abs_le]
    constructor
    · simp only [neg_le_sub_iff_le_add]
      linarith [Nat.le_ceil x]
    · simp only [tsub_le_iff_right]
      rw[add_comm]
      exact natCeil_le_self_add_one x hx
  · ring

theorem nat_div_approx (a b : ℕ) : ∃ C, |C| ≤ 1 ∧ ↑(a/b) = (a/b : ℝ) + C := by
  rw[←Nat.floor_div_eq_div (K:=ℝ)]
  apply floor_approx (a/b:ℝ) (by positivity)

theorem floor_div_approx (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    ∃ C, |C| ≤ 2 ∧  ↑((Nat.floor x)/d) = x / d + C := by
  by_cases hd : d = 0
  · simp [hd]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := nat_div_approx (Nat.floor x) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := floor_approx x hx
  rw[hC₁, hC₂]
  use  C₁ + C₂/d
  refine ⟨?_, by ring⟩
  have : |C₁ + C₂/d| ≤ |C₁| + |C₂/d| := abs_add_le C₁ (C₂ / ↑d)
  have : |C₂/d| ≤ |C₂| := by
    rw[abs_div]
    apply div_le_self
    · exact abs_nonneg C₂
    · simp only [Nat.abs_cast, Nat.one_le_cast]
      omega
  linarith

theorem abs_rem_le (hx : 0 < x) (hy : 0 < y) {d : ℕ} (hd : d ≠ 0) :
    |(primeInterSieve x y z hz).rem d| ≤ 5 := by
  rw[rem_eq x y z hz hx _ hd]
  have hpush : ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) =
      (↑(⌊x + y⌋₊ / d) - ↑((⌈x⌉₊ - 1) / d) : ℝ) := by
    rw [Nat.cast_sub]
    gcongr
    rw[Nat.le_floor_iff]
    · rw[←add_le_add_iff_right 1]
      norm_cast
      rw [Nat.sub_add_cancel]
      · linarith [natCeil_le_self_add_one x (le_of_lt hx)]
      · simp [hx]
    · linarith
  rw[hpush]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := floor_div_approx (x + y) (by linarith) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := nat_div_approx (Nat.ceil x - 1) d
  obtain ⟨C₃, hC₃_le, hC₃⟩ := ceil_approx (x) (by linarith)
  rw[hC₁, hC₂, Nat.cast_sub, hC₃]
  · ring_nf
    have hinv : |(d:ℝ)⁻¹| ≤ 1 := by
      rw[abs_inv]
      simp only [Nat.abs_cast]
      apply Nat.cast_inv_le_one
    have hmul : |(↑d)⁻¹*C₃| ≤ |C₃| := by
      rw[inv_mul_eq_div, abs_div]
      apply div_le_self
      · exact abs_nonneg _
      · simp only [Nat.abs_cast, Nat.one_le_cast]
        omega
    calc
      |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + C₁ - C₂|
          = |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)| := by ring_nf
      _ ≤ |(↑d)⁻¹ - (↑d)⁻¹*C₃| + |C₁ - C₂| := abs_add_le _ _
      _ ≤ (|(↑d)⁻¹| + |(↑d)⁻¹*C₃|) + (|C₁| + |C₂|) := by
        exact add_le_add (abs_sub _ _) (abs_sub _ _)
      _ ≤ (1 + |C₃|) + (2 + 1) := by
        gcongr
      _ ≤ 5 := by
        linarith
  · simp [hx]

end Remainder

theorem _root_.BrunTitchmarsh.boudingSum_ge :
    (primeInterSieve x y z hz).selbergBoundingSum ≥ Real.log z / 2 := by
  apply boundingSum_ge_log
  · rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff]
    · exact Nat.le_floor hp
    · exact hpp

theorem _root_.BrunTitchmarsh.primeSieve_rem_sum_le (hx : 0 < x) (hy : 0 < y) :
    ∑ d ∈ (primeInterSieve x y z hz).prodPrimes.divisors,
      (if (d : ℝ) ≤ z then (3:ℝ) ^ ω d * |(primeInterSieve x y z hz).rem d| else 0)
      ≤ 5 * z * (1+Real.log z)^3 := by
  apply rem_sum_le_of_const (primeInterSieve x y z hz) 5 ?_
  intro d hd
  exact abs_rem_le x y z hz hx hy (ne_of_gt hd)

theorem _root_.BrunTitchmarsh.siftedSum_le (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    (primeInterSieve x y z (le_of_lt hz)).siftedSum ≤
      2 * y / Real.log z + 5 * z * (1+Real.log z)^3  := by
  apply le_trans (SelbergSieve.selberg_bound_simple ..)
  calc _ ≤ y / (Real.log z / 2) + 5 * z * (1+Real.log z)^3 := ?_
       _ = _ := by ring
  gcongr
  · linarith [Real.log_pos hz]
  · rfl
  · apply boudingSum_ge
  · apply primeSieve_rem_sum_le x y z (le_of_lt hz) hx hy

theorem _root_.BrunTitchmarsh.primesBetween_le (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1+Real.log z)^3 := by
  have : z ≤ z * (1+Real.log z)^3 := by
    apply le_mul_of_one_le_right
    · linarith
    apply one_le_pow₀
    linarith [Real.log_nonneg (by linarith)]
  linarith [siftedSum_le x y z hx hy hz,
    primesBetween_le_siftedSum_add x y z (le_of_lt hz)]

end BrunTitchmarsh
