/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.Assembly2
import LeanPool.Zeta5Irrational.Growth.Assembly1
public import LeanPool.Zeta5Irrational.PrimeSumStep
public import LeanPool.Zeta5Irrational.Growth.PieceIdx
public import LeanPool.Zeta5Irrational.Growth.InnerSum
public import LeanPool.Zeta5Irrational.Growth.OuterPrime
public import LeanPool.Zeta5Irrational.Constants
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic

/-! # Growth: the per-range sums as prime sums
-/

public section

open Finset Filter

namespace Zeta5Irrational

lemma range_sum_le {a b : ℕ} (F : ℕ → ℝ) (f : ℝ → ℝ) (K C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k ∈ Ioc a b, k.Prime → F k ≤ k * f (K / k) + C) :
    ∑ k ∈ Ioc a b, cPrime k * F k ≤
      ∑ k ∈ Ioc a b, (k : ℝ) * cPrime k * f (K / k) + C * Chebyshev.theta b := by
  have hθ : ∑ k ∈ Ioc a b, cPrime k ≤ Chebyshev.theta b := by
    refine le_trans ?_ (sum_cPrime_le_theta b)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; simp only [Finset.mem_Ioc] at hk ⊢; omega
    · intro k _ _; exact cPrime_nonneg' k
  have hterm : ∀ k ∈ Ioc a b, cPrime k * F k ≤ (k : ℝ) * cPrime k * f (K / k) + C * cPrime k := by
    intro k hk
    by_cases hp : k.Prime
    · have := h k hk hp
      have hc := cPrime_nonneg' k
      nlinarith [mul_le_mul_of_nonneg_left this hc]
    · simp [cPrime, hp]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hθ hC]

/-- Facts about primes above `n/10` for large `n`. -/
lemma big_prime_facts {n k : ℕ} (hn : 10400 ≤ n) (hk : n / 10 < k) (hp : k.Prime) :
    7 ≤ k ∧
      2 * (k / 2) + 1 = k ∧
        ¬k * Mcut ≤ 40 * n ∧
          2 * (40 * n) < k ^ 2 ∧
            5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < k ^ 2 ∧ (n : ℝ) ≤ 10 * k := by
  have h10 : n + 1 ≤ 10 * k := by omega
  have hsq : 10400 * n + 700 ≤ k ^ 2 * 100 := by nlinarith
  have hodd' : 2 * (k / 2) + 1 = k := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      have : 2 ∣ k := ⟨j, by omega⟩
      rcases hp.eq_one_or_self_of_dvd 2 this with h | h
      · omega
      · omega
    · omega
  refine ⟨by omega, hodd', by unfold Mcut; omega, by omega, by omega, ?_⟩
  exact_mod_cast (show n ≤ 10 * k by omega)

/-- **Range 2** (inner tail). -/
lemma range2_le {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (n / 10) (2 * n), cPrime k * (-(Lp n k : ℝ)) ≤
      psum (fun x => x * Ftail x + 27 / 16) 20 400 (Kr n) +
        10 ^ 7 * Chebyshev.theta (2 * n : ℕ) := by
  have hps :
    psum (fun x => x * Ftail x + 27 / 16) 20 400 (Kr n) =
      ∑ k ∈ Ioc (n / 10) (2 * n),
        (k : ℝ) * cPrime k * ((fun x => x * Ftail x + 27 / 16) (Kr n / k)) := by
    unfold psum
    rw [show (400 : ℝ) = ((400 : ℕ) : ℝ) by norm_num, show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num,
      floor_Kr_div n 400 (by norm_num), floor_Kr_div n 20 (by norm_num),
      show 40 * n / 400 = n / 10 by omega, show 40 * n / 20 = 2 * n by omega]
  rw [hps]
  refine
    range_sum_le (fun k => -(Lp n k : ℝ)) (fun x => x * Ftail x + 27 / 16) (Kr n) (10 ^ 7)
      (by norm_num) fun k hk hp => ?_
  have hk' := Finset.mem_Ioc.mp hk
  obtain ⟨hp7, hodd, hsmall, hsq, hdeg, hn10⟩ := big_prime_facts hn hk'.1 hp
  have := Fact.mk hp
  have h := tail_Lp_le (p := k) (n := n) (by omega) hodd hp7 hsmall (by omega) hsq hdeg
  have hC :=
    Ctail_le (n := n) (p := k) hp.pos
      (by
        unfold Mcut at hsmall; rw [not_le] at hsmall
        exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by linarith))
      hn10
  have e : Kr n / k = 40 * n / k := by simp [Kr]
  simp only [e]
  linarith

/-- The inner table as a function. -/
@[expose] noncomputable def fIn (x : ℝ) : ℝ :=
  gIn (pieceIdx tIn 125 x) x

lemma tIn_zero : tIn 0 = 3 := by simp [tIn, tInL]

lemma tIn_last : tIn 125 = 20 := by simp [tIn, tInL]

/-- **Range 3** (inner table). -/
lemma range3_le {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (2 * n) (40 * n / 3), cPrime k * (-(Lp n k : ℝ)) ≤
      psum fIn 3 20 (Kr n) + 10 ^ 8 * Chebyshev.theta (40 * n / 3 : ℕ) := by
  have hps :
    psum fIn 3 20 (Kr n) = ∑ k ∈ Ioc (2 * n) (40 * n / 3), (k : ℝ) * cPrime k * fIn (Kr n / k) := by
    unfold psum
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num,
      floor_Kr_div n 3 (by norm_num), floor_Kr_div n 20 (by norm_num),
      show 40 * n / 20 = 2 * n by omega]
  rw [hps]
  refine range_sum_le (fun k => -(Lp n k : ℝ)) fIn (Kr n) (10 ^ 8) (by norm_num) fun k hk hp => ?_
  have hk' := Finset.mem_Ioc.mp hk
  obtain ⟨hp7, hodd, hsmall, hsq, hdeg, hn10⟩ := big_prime_facts hn (by omega) hp
  have := Fact.mk hp
  have hin : 3 * k ≤ 40 * n := by have := Nat.div_mul_le_self (40 * n) 3; omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hp.pos
  set x : ℝ := 40 * n / k with hx
  have hx3 : 3 ≤ x := by rw [hx, le_div_iff₀ hkR]; exact_mod_cast (show 3 * k ≤ 40 * n by omega)
  have hx20 : x < 20 := by
    rw [hx, div_lt_iff₀ hkR];
    exact_mod_cast (show 40 * n < 20 * k by omega)
  obtain ⟨hi, hx1, hx2⟩ :=
    pieceIdx_spec tIn_mono (x := x) (by rw [tIn_zero]; exact hx3) (by rw [tIn_last]; exact hx20)
  set i := pieceIdx tIn 125 x with hidef
  have hmem : x ∈ Set.Ico (tIn i) (tIn (i + 1)) := ⟨hx1, hx2⟩
  have hkr := inner_table_k i hi x hmem
  have hfl : ⌊x⌋₊ = 40 * n / k := by
    rw [hx, show (40 * n : ℝ) / k = ((40 * n : ℕ) : ℝ) / (k : ℕ) by push_cast; ring,
      Nat.floor_div_eq_div]
  rw [hfl] at hkr
  have hk1 : kloI n k ≤ kIn i := hkr.1
  have hk2 : kIn i ≤ ktopI n k := hkr.2
  have h := table_Lp_le (p := k) (n := n) (by omega) hodd hp7 hsmall hin hsq hdeg (kIn i) hk1 hk2
  have htab := inner_table i hi x hmem
  have hq20 : 40 * n / k ≤ 20 := by
    have : 40 * n < 20 * k := by omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))
  have hC := Ctab_le (n := n) (p := k) hq20 hk1 hk2
  unfold fIn
  rw [← hidef, ← htab]
  rw [← hx] at h
  linarith

/-- **Range 4** (outer range). -/
lemma range4_le {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (40 * n / 3) (2 * (37 * n)), cPrime k * (-(Lp n k : ℝ)) ≤
      psum Eout (20 / 37) 3 (Kr n) + 10 ^ 5 * Chebyshev.theta (2 * (37 * n) : ℕ) := by
  have hps :
    psum Eout (20 / 37) 3 (Kr n) =
      ∑ k ∈ Ioc (40 * n / 3) (2 * (37 * n)), (k : ℝ) * cPrime k * Eout (Kr n / k) := by
    unfold psum
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, floor_Kr_div n 3 (by norm_num), floor_Kr_outer,
      show 74 * n = 2 * (37 * n) by ring]
  rw [hps]
  refine
    range_sum_le (fun k => -(Lp n k : ℝ)) Eout (Kr n) (10 ^ 5) (by norm_num) fun k hk hp => ?_
  have hk' := Finset.mem_Ioc.mp hk
  obtain ⟨hp7, hodd, _, hsq, _, _⟩ := big_prime_facts hn (by omega) hp
  have := Fact.mk hp
  have hout : 40 * n < 3 * k := by
    have := Nat.lt_div_mul_add (a := 40 * n) (show 0 < 3 by norm_num); omega
  have h := outer_Lp_le (p := k) (n := n) (by omega) hodd hp7 hout hsq
  have hq2 : 40 * n / k ≤ 2 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))
  have hC := Cout_le (n := n) (p := k) hq2
  have e : Kr n / k = 40 * n / k := by simp [Kr]
  rw [e]
  linarith

end Zeta5Irrational
