/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Radical.NatInt
import LeanPool.Redhill.Common.Conjectures

/-!
# Browkin and Brzeziński's 1994 result
-/


namespace BB94

open Nat Finset

/-- The coefficient of `x^j` in the paper's `f_k(x)`. This is [OEIS A111125](https://oeis.org/A111125). -/
def C (k j : ℕ) : ℕ :=
  (k + j).choose (2 * j) + 2 * (k + j).choose (2 * j + 1)

section

variable {k j : ℕ}

lemma C_eq_zero_iff : C k j = 0 ↔ k < j := by
  simp_rw [C, Nat.add_eq_zero_iff, mul_eq_zero, two_ne_zero, false_or, choose_eq_zero_iff]
  lia

lemma C_pos_iff : 0 < C k j ↔ j ≤ k := by
  rw [← not_iff_not, not_lt, le_zero, C_eq_zero_iff, not_le]

alias ⟨_, C_eq_zero_of_lt⟩ := C_eq_zero_iff

@[simp]
lemma C_zero : C k 0 = 2 * k + 1 := by
  simp [C, add_comm]

@[simp]
lemma C_self : C k k = 1 := by
  simp [C, two_mul]

lemma C_add_two_add_one :
    C (k + 2) (j + 1) = 2 * C (k + 1) (j + 1) + C (k + 1) j - C k (j + 1) := by
  grind [C]

lemma C_mono_right : Monotone (C · j) := fun k₁ k₂ h ↦ by
  simp only [C]
  gcongr

lemma C_le : C k (j + 1) ≤ 2 * C (k + 1) (j + 1) + C (k + 1) j :=
  calc
    _ ≤ C (k + 1) (j + 1) := C_mono_right (Nat.le_add_right ..)
    _ ≤ _ := by lia

theorem sum_range_C_mul (x y : ℤ) :
    x ^ (2 * k + 1) + y ^ (2 * k + 1) =
    ∑ j ∈ range (k + 1), C k j * (x + y) ^ (2 * j + 1) * (-x * y) ^ (k - j) := by
  induction k using twoStepInduction with
  | zero => simp
  | one => simp [show range 2 = {0, 1} by decide]; ring
  | more k ih₀ ih₁ =>
    set s := x + y
    set p := -x * y
    have decomp :
        x^(2*(k+2)+1) + y^(2*(k+2)+1) =
        2 * (p * (x^(2*(k+1)+1) + y^(2*(k+1)+1)) - C (k+1) 0 * s * p^(k+2)) +
        s^2 * (x^(2*(k+1)+1) + y^(2*(k+1)+1)) -
        (p^2 * (x^(2*k+1) + y^(2*k+1)) - C k 0 * s * p^(k+2)) +
        C (k+2) 0 * s * p ^ (k+2) := by
      simp [C_zero]
      ring
    conv_rhs =>
      rw [sum_range_succ']
      enter [1, 2, j]
      rw [C_add_two_add_one, cast_sub C_le, cast_add, cast_mul, cast_two, mul_assoc, sub_mul,
        add_mul, mul_assoc]
    rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, decomp]
    clear decomp
    congr
    · symm
      rw [sum_range_succ, C_eq_zero_of_lt (by lia), cast_zero, zero_mul, add_zero]
      let g (j : ℕ) := C (k + 1) j * (s ^ (2 * j + 1) * p ^ (k + 2 - j))
      change ∑ j ∈ range (k + 1), g (j + 1) = _
      have g0 : g 0 = C (k + 1) 0 * s * p ^ (k + 2) := by simp [g, mul_assoc]
      rw [range_eq_Ico, sum_Ico_add', zero_add, ← g0, eq_sub_iff_add_eq',
        ← sum_range_eq_add_Ico _ (by lia), ih₁, mul_sum]
      congr! 1 with j hj
      rw [mem_range] at hj
      simp_rw [g, show k + 2 - j = k + 1 - j + 1 by lia]
      ring
    · rw [ih₁, mul_sum]
      congr! 1 with j hj
      rw [show k + 2 - (j + 1) = k + 1 - j by lia]
      ring
    · symm
      iterate 2 rw [sum_range_succ, C_eq_zero_of_lt (by lia), cast_zero, zero_mul, add_zero]
      let g (j : ℕ) := C k j * (s ^ (2 * j + 1) * p ^ (k + 2 - j))
      change ∑ j ∈ range k, g (j + 1) = _
      have g0 : g 0 = C k 0 * s * p ^ (k + 2) := by simp [g, mul_assoc]
      rw [range_eq_Ico, sum_Ico_add', zero_add, ← g0, eq_sub_iff_add_eq',
        ← sum_range_eq_add_Ico _ (by lia), ih₀, mul_sum]
      congr! 1 with j hj
      rw [mem_range] at hj
      simp_rw [g, show k + 2 - j = k - j + 2 by lia]
      ring
    · simp

end

/-- The sequence of `n+3`-tuples providing a lower bound of `2n+1` on the quality
(i.e. `2n-5` for `n`-tuples where `n ≥ 3`). `k` moves between tuples and `i` is the tuple index. -/
def tup (n k : ℕ) (i : Fin (n + 3)) : ℤ :=
  i.lastCases 1 fun i' ↦
    i'.lastCases (-(2 ^ k) ^ (2 * n + 1)) fun j ↦
      C n j.1 * (2 ^ k - 1) ^ (2 * j.1 + 1) * (2 ^ k) ^ (n - j.1)

variable {n k : ℕ}

@[simp]
lemma tup_last : tup n k (Fin.last _) = 1 := by simp [tup]

@[simp]
lemma tup_second_last : tup n k (Fin.last _).castSucc = -(2 ^ k) ^ (2 * n + 1) := by simp [tup]

@[simp]
lemma tup_except_last_two {i : Fin (n + 1)} :
    tup n k i.castSucc.castSucc = C n i.1 * (2 ^ k - 1) ^ (2 * i.1 + 1) * (2 ^ k) ^ (n - i.1) := by
  simp [tup]

lemma injective_tup : (tup n).Injective := fun i j e ↦ by
  simpa using congr($e (Fin.last _).castSucc)

lemma sum_tup : ∑ i, tup n k i = 0 := by
  rw [Fin.sum_univ_castSucc, tup_last, Fin.sum_univ_castSucc, tup_second_last]
  simp_rw [tup_except_last_two,
    Fin.sum_univ_eq_sum_range fun j ↦ (C n j : ℤ) * (2 ^ k - 1) ^ (2 * j + 1) * (2 ^ k) ^ (n - j)]
  conv_lhs =>
    enter [1, 1, 2, j]
    rw [sub_eq_add_neg]
    enter [2]
    rw [← mul_one (2 ^ k), ← neg_mul_neg]
  rw [← sum_range_C_mul, neg_one_pow_eq_ite]
  grind

lemma gcd_tup : univ.gcd (tup n k) = 1 := by
  rw [← insert_eq_of_mem (mem_univ (Fin.last (n + 2))), gcd_insert]
  simp [tup]

lemma tup_sign {i : Fin (n + 3)} (hk : k ≠ 0) : 0 < tup n k i ↔ i ≠ (Fin.last _).castSucc := by
  cases i using Fin.lastCases with
  | last => simp [tup_last]; grind
  | cast i =>
    cases i using Fin.lastCases with
    | last => simp [tup_second_last]
    | cast i =>
      suffices (0 : ℤ) < (C n i.1) * (2 ^ k - 1) ^ (2 * i.1 + 1) * (2 ^ k) ^ (n - i.1) by
        simp [this]
      have : 0 < C n i.1 := by rw [C_pos_iff]; lia
      have : 0 < (2 : ℤ) ^ k - 1 := by
        rw [sub_pos]
        exact (one_lt_pow₀ one_lt_two hk)
      positivity

lemma SSC_tup (hk : k ≠ 0) : SSC (tup n k) := fun b n₁ n₂ ↦ by
  by_cases hb : (Fin.last _).castSucc ∈ b
  · rw [← @sum_tup n k, ← sum_add_sum_compl b, Ne, left_eq_add, ← Ne]
    refine (sum_pos (fun i mi ↦ ?_) n₂).ne'
    rw [mem_compl] at mi
    rw [tup_sign hk]
    exact (ne_of_mem_of_not_mem hb mi).symm
  · refine (sum_pos (fun i mi ↦ ?_) n₁).ne'
    rw [tup_sign hk]
    exact ne_of_mem_of_not_mem mi hb

lemma tup_mem_nConjectureTuples (hk : k ≠ 0) : tup n k ∈ nConjectureTuples (n + 3) := by
  simp [nConjectureTuples, sum_tup, SSC_tup hk, gcd_tup]

section Quality

lemma maxAbs_tup : maxAbs (tup n k) = (2 ^ k) ^ (2 * n + 1) := by
  obtain rfl | hk := eq_or_ne k 0
  · rw [show (2 ^ 0) ^ (2 * n + 1) = (tup n 0 (Fin.last _)).natAbs by simp]
    refine maxAbs_eq_of_forall_le fun i ↦ ?_
    cases i using Fin.lastCases with
    | last => rfl
    | cast i => cases i using Fin.lastCases <;> simp
  rw [show (2 ^ k) ^ (2 * n + 1) = (tup n k (Fin.last _).castSucc).natAbs by simp]
  refine maxAbs_eq_of_forall_le fun i ↦ ?_
  obtain rfl | hi := eq_or_ne i (Fin.last _).castSucc
  · rfl
  conv_rhs =>
    rw [← Int.natAbs_neg, ← zero_sub, ← @sum_tup n k, ← sum_add_sum_compl {(Fin.last _).castSucc},
      sum_singleton, add_sub_cancel_left]
  zify
  have nng (j) (mj : j ∈ ({(Fin.last _).castSucc} : Finset _)ᶜ) : 0 ≤ tup n k j := by
    rw [mem_compl, mem_singleton] at mj
    exact ((tup_sign hk).mpr mj).le
  rw [abs_sum_of_nonneg nng, abs_of_nonneg ((tup_sign hk).mpr hi).le]
  exact single_le_sum nng (by simpa using hi)

open Real UniqueFactorizationMonoid UniqueFactorizationDomain

lemma radical_prod_tup_dvd :
    radical (∏ i, tup n k i) ∣ (∏ j ∈ range (n + 1), C n j) * (2 ^ k - 1) * 2 := by
  rw [Fin.prod_univ_castSucc, tup_last, mul_one, Fin.prod_univ_castSucc, tup_second_last, mul_neg,
    radical_neg]
  simp_rw [tup_except_last_two, prod_mul_distrib, prod_pow_eq_pow_sum, mul_assoc, ← pow_add,
    ← pow_mul, ← mul_assoc]
  obtain rfl | hk := eq_or_ne k 0
  · simp
  iterate 2 refine radical_mul_dvd.trans (mul_dvd_mul ?_ ?_)
  · norm_cast
    rw [Fin.prod_univ_eq_prod_range]
    exact radical_dvd_self
  · rw [radical_pow _ (by simp)]
    exact radical_dvd_self
  · rw [radical_pow _ (by positivity)]
    exact radical_dvd_self

lemma one_lt_radical_prod_tup (hk : k ≠ 0) : 1 < radical (∏ i, tup n k i) := by
  rw [Int.one_lt_radical_iff, Fin.prod_univ_castSucc, tup_last, mul_one, Fin.prod_univ_castSucc,
    tup_second_last, Int.natAbs_mul]
  have : 1 < (-(2 ^ k) ^ (2 * n + 1)).natAbs := by simp [hk]
  simp_rw [Nat.one_lt_mul_iff, zero_lt_one.trans this, this, or_true, and_true]
  zify
  rw [abs_prod]
  refine prod_pos fun i _ ↦ ?_
  rw [abs_pos]
  exact ((tup_sign hk).mpr (by simp)).ne'

lemma log_radical_prod_tup_le (hk : k ≠ 0) :
    Real.log (radical (∏ i, tup n k i) : ℤ) ≤
    Real.log (2 * ∏ j ∈ range (n + 1), C n j) + k * Real.log 2 := by
  set CP : ℕ := ∏ j ∈ range (n + 1), C n j
  have CP_pos : 0 < CP := prod_pos fun i mi ↦ by simp_all [C_pos_iff]
  rw [log_le_iff_le_exp (by exact_mod_cast Int.radical_pos _), exp_add, exp_log (by positivity),
    mul_comm (k : ℝ), exp_mul, exp_log zero_lt_two]
  norm_cast
  have : 0 < (2 : ℤ) ^ k - 1 := by
    rw [sub_pos]
    exact (one_lt_pow₀ one_lt_two hk)
  apply (Int.le_of_dvd (by positivity) (radical_prod_tup_dvd)).trans
  simp_rw [mul_rotate 2, CP, cast_mul, cast_pow, cast_ofNat]
  gcongr
  lia

lemma le_tupleQuality (hk : k ≠ 0) :
    .ofReal ((2 * n + 1) * (k * Real.log 2) /
      (Real.log (2 * ∏ j ∈ range (n + 1), C n j) + k * Real.log 2)) ≤ tupleQuality (tup n k) := by
  apply ENNReal.ofReal_le_ofReal
  rw [maxAbs_tup]
  apply div_le_div₀
  · positivity
  · simp
  · apply Real.log_pos
    exact_mod_cast one_lt_radical_prod_tup hk
  · exact log_radical_prod_tup_le hk

open Filter in
lemma liminf_tupleQuality_tup : (2 * n + 1 : ℕ) ≤ liminf (tupleQuality ∘ tup n) atTop := by
  refine le_of_eq_of_le ?_ <| liminf_le_liminf <|
    eventually_atTop.mpr ⟨1, fun k hk ↦ le_tupleQuality (by lia)⟩
  set Q : ℝ := log (2 * ∏ j ∈ range (n + 1), C n j)
  rw [← ENNReal.ofReal_natCast]
  refine (ENNReal.tendsto_ofReal ?_).liminf_eq.symm
  simp_rw [mul_div_assoc (2 * n + 1 : ℝ)]
  rw [← mul_one (2 * n + 1)]
  push_cast
  apply Tendsto.const_mul
  have l2n0 : Real.log 2 ≠ 0 := by positivity
  have key := tendsto_add_mul_div_add_mul_atTop_nhds 0 Q (Real.log 2) l2n0
  rw [div_self l2n0] at key
  convert key using 2 with k
  rw [zero_add, mul_comm]

end Quality

end BB94

open BB94

/-- Theorem 1.3 in the paper, Browkin and Brzeziński (1994). -/
theorem le_quality_nConjectureTuples {n : ℕ} (hn : 3 ≤ n) :
    (2 * n - 5 : ℕ) ≤ quality (nConjectureTuples n) := by
  rw [le_iff_exists_add'] at hn
  obtain ⟨n, rfl⟩ := hn
  exact quality_ge_of_liminf _ _ (Set.Ici_infinite 1) injective_tup.injOn
    (fun i (mi : 1 ≤ i) ↦ tup_mem_nConjectureTuples (by lia)) liminf_tupleQuality_tup
