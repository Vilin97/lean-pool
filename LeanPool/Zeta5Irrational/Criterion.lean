/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Qian Tang
-/

/- Copyright (c) 2026 Qian Tang; the degree-general decay proof is adapted from
Zeta32 at 669c92bf7a3728e0de9ad80c373bc29fb5ca3d58 (Apache-2.0). -/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # An irrationality criterion via integer polynomials

This file proves the elementary reduction used in the paper
"ζ(5) is irrational" (A. Fauzan, 17 September 2026), Section 1.1 / proof of Theorem 1.1:

If `ξ` is a real number and for all sufficiently large `n` there is an integer polynomial `Q`
of degree at most `d n` with `0 < Q(ξ) ≤ ε n`, where `b ^ (d n) * ε n → 0` for every positive
integer `b`, then `ξ` is irrational.

The point is that if `ξ = a / b` then `b ^ (d n) * Q(a / b)` is a positive integer, hence at
least `1`, while it tends to zero.
-/

public section

open Polynomial Filter Topology

namespace Zeta5Irrational

/-- Clearing denominators: for `p : ℤ[X]` of degree at most `d`, the number `b ^ d * p(a / b)`
is the integer `∑ k, coeff k * a ^ k * b ^ (d - k)`. -/
lemma pow_mul_aeval_div_eq_intCast (p : ℤ[X]) {d : ℕ} (hd : p.natDegree ≤ d) (a b : ℤ)
    (hb : b ≠ 0) :
    (b : ℝ) ^ d * aeval ((a : ℝ) / b) p =
      ((∑ k ∈ Finset.range (d + 1), p.coeff k * a ^ k * b ^ (d - k) : ℤ) : ℝ) := by
  have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hlt : (p.map (algebraMap ℤ ℝ)).natDegree < d + 1 :=
    lt_of_le_of_lt natDegree_map_le (by omega)
  rw [aeval_def, eval₂_eq_eval_map, eval_eq_sum_range' hlt, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hpow : (b : ℝ) ^ d = (b : ℝ) ^ (d - k) * (b : ℝ) ^ k := by rw [← pow_add]; congr 1; omega
  rw [coeff_map, hpow, div_pow]
  simp only [algebraMap_int_eq, eq_intCast]
  field_simp

/-- **Irrationality criterion.** Let `ξ : ℝ`, `d : ℕ → ℕ` and `ε : ℕ → ℝ` be such that
`b ^ (d n) * ε n → 0` for every positive integer `b`. If for all sufficiently large `n` there is
an integer polynomial `Q` with `natDegree Q ≤ d n` and `0 < Q(ξ) ≤ ε n`, then `ξ` is
irrational. -/
theorem irrational_of_eventually_exists_int_poly (ξ : ℝ) (d : ℕ → ℕ) (ε : ℕ → ℝ)
    (hε : ∀ b : ℕ, 0 < b → Tendsto (fun n => (b : ℝ) ^ d n * ε n) atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.natDegree ≤ d n ∧ 0 < aeval ξ Q ∧ aeval ξ Q ≤ ε n) :
    Irrational ξ := by
  rintro ⟨q, hq⟩
  have hξ : ξ = ((q.num : ℤ) : ℝ) / ((q.den : ℤ) : ℝ) := by
    rw [← hq, Rat.cast_def, Int.cast_natCast]
  have hb0 : 0 < q.den := q.den_pos
  have hbR : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hb0
  have hsmall : ∀ᶠ n in atTop, (q.den : ℝ) ^ d n * ε n < 1 :=
    (hε q.den hb0).eventually (gt_mem_nhds one_pos)
  obtain ⟨n, ⟨Q, hdeg, hpos, hle⟩, hlt⟩ :=
    (h.and hsmall).exists
      -- the integer `m = b ^ d * Q(a / b)`
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : ℝ) = (q.den : ℝ) ^ d n * aeval ξ Q := by
    refine ⟨∑ k ∈ Finset.range (d n + 1), Q.coeff k * q.num ^ k * (q.den : ℤ) ^ (d n - k), ?_⟩
    have key := pow_mul_aeval_div_eq_intCast Q hdeg q.num (q.den : ℤ) (by exact_mod_cast hb0.ne')
    rw [hξ, ← key]
    simp only [Int.cast_natCast]
  have hm_pos : (0 : ℝ) < m := by rw [hm]; exact mul_pos (pow_pos hbR _) hpos
  have hm_ge : (1 : ℝ) ≤ m := by
    have : (0 : ℤ) < m := by exact_mod_cast hm_pos
    exact_mod_cast this
  have hm_lt : (m : ℝ) < 1 := by
    rw [hm]
    calc
      (q.den : ℝ) ^ d n * aeval ξ Q ≤ (q.den : ℝ) ^ d n * ε n :=
        mul_le_mul_of_nonneg_left hle (pow_nonneg hbR.le _)
      _ < 1 := hlt
  linarith

/-- Gaussian decay dominates every fixed linear power exponent. -/
theorem tendsto_pow_mul_exp_neg_sq_of_pos_degree {c : ℝ} (hc : 0 < c) (D b : ℕ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ (D * n) * Real.exp (-c * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hrw : ∀ n : ℕ, (b : ℝ) ^ (D * n) * Real.exp (-c * (n : ℝ) ^ 2) =
      Real.exp ((D * n) * Real.log b - c * (n : ℝ) ^ 2) := by
    intro n
    have hbpow : (0 : ℝ) < (b : ℝ) ^ (D * n) := pow_pos hbR _
    rw [← Real.exp_log hbpow, ← Real.exp_add, Real.log_pow]
    congr 1
    push_cast
    ring
  simp_rw [hrw]
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun n => (Real.exp_pos _).le) ?_ hexp
  filter_upwards [eventually_ge_atTop (⌈(D * Real.log b + 1) / c⌉₊)] with n hn
  apply Real.exp_le_exp.mpr
  have hn' : (D * Real.log b + 1) / c ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hn'' : D * Real.log b + 1 ≤ c * n := by
    rw [div_le_iff₀ hc] at hn'
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hn'' hn0]

/-- The decay `b ^ (37 n) * exp (-c n²) → 0` for every `c > 0`. -/
theorem tendsto_pow_mul_exp_neg_sq_of_pos {c : ℝ} (hc : 0 < c) (b : ℕ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ (37 * n) * Real.exp (-c * (n : ℝ) ^ 2)) atTop (𝓝 0) :=
  tendsto_pow_mul_exp_neg_sq_of_pos_degree hc 37 b hb

/-- The specific decay used in the paper: `b ^ (37 n) * exp (-(139/5) n²) → 0`. -/
theorem tendsto_pow_mul_exp_neg_sq (b : ℕ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ (37 * n) * Real.exp (-(139 / 5) * (n : ℝ) ^ 2)) atTop (𝓝 0) :=
  tendsto_pow_mul_exp_neg_sq_of_pos (by norm_num) b hb

end Zeta5Irrational
