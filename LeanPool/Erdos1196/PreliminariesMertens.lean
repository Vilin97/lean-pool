/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc.
-/
import LeanPool.Erdos1196.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.AbelSummation

/-!
# Arithmetic preliminaries for primitive sets above `x`

This file collects the exact divisor identities, factorial decompositions, and bounded-error
Mertens estimate used later in the normalization and tail-sum arguments.

## Main statements

* `mertensEstimate`
-/

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The fractional-part correction in the standard factorial proof of Mertens' estimate. -/
private noncomputable def mertensFractionalError (t : ℕ) : ℝ :=
  (1 / t) * ∑ m ∈ Finset.Icc 1 t, Λ m * ((t : ℝ) / m - ((t / m : ℕ) : ℝ))

/--
On a positive index `m`, scaling the real quotient `(t : ℝ) / m` by `1 / t` recovers division by
`m`.
-/
private lemma one_div_mul_mul_natCast_div {a : ℝ} {t m : ℕ} (ht : t ≠ 0) :
    (1 / (t : ℝ)) * (a * ((t : ℝ) / m)) = a / (m : ℝ) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  grind only

/-- The truncation error from replacing `t / m` by the integer quotient is `↑(t % m) / m`. -/
private lemma truncation_eq_mod_div {t m : ℕ} :
    ((t : ℝ) / m - ↑(t / m)) = ↑(t % m) / m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  · have hmR : (m : ℝ) ≠ 0 := by
      exact_mod_cast hm.ne'
    apply (eq_div_iff hmR).2
    have hdecomp : (↑(t % m) : ℝ) + ↑(t / m) * m = t := by
      have h : (↑(t % m + m * (t / m)) : ℝ) = t := by
        exact_mod_cast (Nat.mod_add_div t m)
      simpa [Nat.cast_add, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using h
    grind only

/-- The floor-truncation term in the Mertens decomposition is the fractional part of `t / m`. -/
private lemma truncation_eq_fract {t m : ℕ} :
    ((t : ℝ) / m - ↑(t / m)) = Int.fract ((t : ℝ) / m) := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  exact truncation_eq_mod_div

/--
Rearranging the multiple count gives the factorial identity
`∑_{m ≤ N} Λ(m) * ⌊N / m⌋ = log (N!)`.
-/
private lemma sum_vonMangoldt_mul_div_eq_log_factorial (N : ℕ) :
    (Finset.Icc 1 N).sum (fun m => Λ m * ((N / m : ℕ) : ℝ)) =
      Real.log (Nat.factorial N) := by
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  have hlogsum :
      (Finset.Icc 1 N).sum (fun n => Real.log (n : ℝ)) =
        Real.log (∏ n ∈ Finset.Icc 1 N, (n : ℝ)) := by
    symm
    refine Real.log_prod ?_
    intro n hn
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hn).1))
  have hprodRange : (∏ i ∈ Finset.range N, ((i + 1 : ℕ) : ℝ)) = Nat.factorial N := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial N
  have hprod : (∏ n ∈ Finset.Icc 1 N, (n : ℝ)) = Nat.factorial N := by
    rw [← Finset.Ico_add_one_right_eq_Icc 1 N, Finset.prod_Ico_eq_prod_range]
    simpa [Nat.succ_eq_add_one, add_comm] using hprodRange
  calc
    (Finset.Icc 1 N).sum (fun m => Λ m * ((N / m : ℕ) : ℝ)) =
        ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
          rw [hI]
    _ = ∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta) n := by
          simpa using
            (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt N).symm
    _ = ∑ n ∈ Finset.Ioc 0 N, Real.log (n : ℝ) := by
          simp [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log]
    _ = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
          rw [← hI]
    _ = Real.log (Nat.factorial N) := by
          rw [hlogsum, hprod]

/-- Writing `N!` as a product of the integers `1, …, N` turns `log (N!)` into a sum of logs. -/
private lemma log_factorial_eq_sum_range (N : ℕ) :
    Real.log (Nat.factorial N) = ∑ i ∈ Finset.range N, Real.log ((i + 1 : ℕ) : ℝ) := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, Real.log_prod]
  grind only

/-- The lower integral comparison `∫_1^N log t dt ≤ log N!`. -/
private lemma integral_log_le_log_factorial {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x ≤ Real.log (Nat.factorial N) := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    have hx1 : (0 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)) hx.1
    exact Real.log_le_log hx1 hxy
  calc
    ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x
      ≤ ∑ i ∈ Finset.Ico 1 N, Real.log ((i + 1 : ℕ) : ℝ) :=
        MonotoneOn.integral_le_sum_Ico (f := Real.log) hN hmono
    _ = ∑ i ∈ Finset.range N, Real.log ((i + 1 : ℕ) : ℝ) := by
        have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
        rw [Finset.sum_Ico_eq_sum_range]
        rw [← hpred, Finset.sum_range_succ']
        simp [Nat.cast_add, add_left_comm, add_comm]
    _ = Real.log (Nat.factorial N) := (log_factorial_eq_sum_range N).symm

/-- The upper integral comparison `log N! ≤ log N + ∫_1^N log t dt`. -/
private lemma log_factorial_le_log_add_integral_log {N : ℕ} (hN : 1 ≤ N) :
    Real.log (Nat.factorial N) ≤ Real.log N + ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    have hx1 : (0 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)) hx.1
    exact Real.log_le_log hx1 hxy
  have hsum :
      ∑ i ∈ Finset.Ico 1 N, Real.log (i : ℝ) ≤ ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x :=
    MonotoneOn.sum_le_integral_Ico (f := Real.log) hN hmono
  have hsum' : ∑ i ∈ Finset.Ico 1 N, Real.log (i : ℝ) = Real.log (Nat.factorial (N - 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simpa [Nat.cast_add, add_comm] using (log_factorial_eq_sum_range (N - 1)).symm
  have hfacNat : Nat.factorial N = N * Nat.factorial (N - 1) := by
    have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
    simpa [Nat.succ_eq_add_one, hpred] using (Nat.factorial_succ (N - 1))
  have hfac :
      Real.log (Nat.factorial N) = Real.log N + Real.log (Nat.factorial (N - 1)) := by
    rw [hfacNat, Nat.cast_mul, Real.log_mul]
    · exact_mod_cast Nat.ne_of_gt hN
    · exact_mod_cast Nat.factorial_ne_zero (N - 1)
  grind only

/-- Elementary two-sided bounds for `log N! / N`. -/
private lemma abs_log_factorial_div_sub_log_le_one {N : ℕ} (hN : 1 ≤ N) :
    |Real.log (Nat.factorial N) / N - Real.log N| ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hint :
      ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x = (N : ℝ) * Real.log N - N + 1 := by
    simp [integral_log]
  have hlower :
      Real.log N - 1 ≤ Real.log (Nat.factorial N) / N := by
    apply (le_div_iff₀ hNpos).2
    have hcomp : (N : ℝ) * Real.log N - N + 1 ≤ Real.log (Nat.factorial N) := by
      simpa [hint] using integral_log_le_log_factorial hN
    linarith
  have hupper :
      Real.log (Nat.factorial N) / N ≤ Real.log N := by
    apply (div_le_iff₀ hNpos).2
    have hcomp :
        Real.log (Nat.factorial N) ≤ Real.log N + ((N : ℝ) * Real.log N - N + 1) := by
      simpa [hint] using log_factorial_le_log_add_integral_log hN
    have hlog : Real.log N ≤ N - 1 := by
      simpa using Real.log_le_sub_one_of_pos hNpos
    linarith
  grind only [= abs.eq_1, = max_def]

/-- The factorial decomposition of the Mertens partial sums. -/
private lemma mertensPartialSum_eq_log_factorial_div_add_fractional (t : ℕ) :
    mertensPartialSum t = Real.log (Nat.factorial t) / t + mertensFractionalError t := by
  by_cases ht : t = 0
  · subst ht
    simp [mertensPartialSum, mertensFractionalError]
  · rw [mertensPartialSum, mertensFractionalError]
    calc
      ∑ m ∈ Finset.Icc 1 t, Λ m / (m : ℝ) =
          ∑ m ∈ Finset.Icc 1 t,
            ((1 / (t : ℝ)) * (Λ m * (((t / m : ℕ) : ℝ))) +
              (1 / (t : ℝ)) * (Λ m * ((t : ℝ) / m - ↑(t / m)))) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            calc
              Λ m / (m : ℝ) = (1 / (t : ℝ)) * (Λ m * ((t : ℝ) / m)) := by
                symm
                exact one_div_mul_mul_natCast_div (a := Λ m) ht
              _ = (1 / (t : ℝ)) * (Λ m * (((t / m : ℕ) : ℝ))) +
                    (1 / (t : ℝ)) * (Λ m * ((t : ℝ) / m - ↑(t / m))) := by
                    ring
      _ = (1 / (t : ℝ)) * ∑ m ∈ Finset.Icc 1 t, Λ m * (((t / m : ℕ) : ℝ)) +
            (1 / (t : ℝ)) *
              ∑ m ∈ Finset.Icc 1 t,
                Λ m * ((t : ℝ) / m - ↑(t / m)) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = Real.log (Nat.factorial t) / t + mertensFractionalError t := by
            rw [sum_vonMangoldt_mul_div_eq_log_factorial]
            rw [mertensFractionalError]
            ring_nf

/-- The fractional correction term is nonnegative. -/
private lemma mertensFractionalError_nonneg {t : ℕ} (ht : 1 ≤ t) :
    0 ≤ mertensFractionalError t := by
  rw [mertensFractionalError]
  refine mul_nonneg ?_ (Finset.sum_nonneg ?_)
  · exact one_div_nonneg.mpr (show (0 : ℝ) ≤ t by positivity)
  · intro m hm
    rw [truncation_eq_fract]
    exact mul_nonneg
      ArithmeticFunction.vonMangoldt_nonneg
      (Int.fract_nonneg _)

/-- The fractional correction term is uniformly bounded by Chebyshev's estimate. -/
private lemma mertensFractionalError_le {t : ℕ} (ht : 2 ≤ t) :
    mertensFractionalError t ≤ Real.log 4 + 4 := by
  rw [mertensFractionalError]
  have hsum :
      ∑ m ∈ Finset.Icc 1 t, Λ m * ((t : ℝ) / m - ↑(t / m))
        ≤ ∑ m ∈ Finset.Icc 1 t, Λ m := by
    refine Finset.sum_le_sum ?_
    intro m hm
    rw [truncation_eq_fract]
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := m), (Int.fract_lt_one ((t : ℝ) / m)).le]
  have hcheb : Chebyshev.psi t ≤ (Real.log 4 + 4) * t := by
    simpa using
      Chebyshev.psi_le_const_mul_self (x := (t : ℝ)) (show 0 ≤ (t : ℝ) by positivity)
  have hI : Finset.Icc 1 t = Finset.Ioc 0 t := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  calc
    (1 / t : ℝ) * ∑ m ∈ Finset.Icc 1 t, Λ m * ((t : ℝ) / m - ↑(t / m))
      ≤ (1 / t : ℝ) * ∑ m ∈ Finset.Icc 1 t, Λ m :=
        mul_le_mul_of_nonneg_left hsum
          (one_div_nonneg.mpr (show (0 : ℝ) ≤ t by positivity))
    _ = Chebyshev.psi t / t := by
        simp [hI, Chebyshev.psi, Nat.floor_natCast, div_eq_mul_inv, mul_comm]
    _ ≤ Real.log 4 + 4 := by
        have htR : 0 < (t : ℝ) := by positivity
        exact (div_le_iff₀ htR).mpr hcheb

/-- Bounded-error form of Mertens' estimate:
`∑_{q ≤ t} Λ(q) / q = log t + O(1)` on the natural numbers. -/
lemma mertensEstimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃t : ℕ⦄, 2 ≤ t →
        |mertensPartialSum t - Real.log (t : ℝ)| ≤ C := by
  refine ⟨Real.log 4 + 5, by positivity, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := by omega
  rw [mertensPartialSum_eq_log_factorial_div_add_fractional t]
  calc
    |Real.log (Nat.factorial t) / t + mertensFractionalError t - Real.log (t : ℝ)|
      = |(Real.log (Nat.factorial t) / t - Real.log (t : ℝ)) + mertensFractionalError t| := by
          congr
          ring
    _ ≤ |Real.log (Nat.factorial t) / t - Real.log (t : ℝ)| + |mertensFractionalError t| :=
        abs_add_le _ _
    _ = |Real.log (Nat.factorial t) / t - Real.log (t : ℝ)| + mertensFractionalError t := by
        rw [abs_of_nonneg (mertensFractionalError_nonneg ht1)]
    _ ≤ 1 + (Real.log 4 + 4) := by
        gcongr
        · exact abs_log_factorial_div_sub_log_le_one ht1
        · exact mertensFractionalError_le ht
    _ = Real.log 4 + 5 := by ring

end PrimitiveSetsAboveX
