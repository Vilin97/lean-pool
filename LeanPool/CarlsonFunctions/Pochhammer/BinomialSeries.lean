/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Binomial series for the ascending Pochhammer symbol

The generating function \(\sum_n (a)_n t^n / n! = (1-t)^{-a}\) for \(\|t\| < 1\), written in
Mathlib's `ascPochhammer` and `Ring.multichoose` language.
-/

open scoped Topology

public noncomputable section

namespace Complex

/-- Ascending Pochhammer symbols divided by factorials are the binomial-ring multichoose
coefficients. -/
theorem ascPochhammer_eval_div_factorial (a : ℂ) (n : ℕ) :
    (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) = Ring.multichoose a n := by
  refine Eq.symm ?_
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).2
  rw [mul_comm]
  simpa [Polynomial.ascPochhammer_smeval_cast,
    Polynomial.ascPochhammer_smeval_eq_eval] using
      (Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n)

/-- The binomial series \(\sum (a)_n t^n / n! = (1-t)^{-a}\) inside the unit disk. -/
theorem hasSum_ascPochhammer_mul_pow_div_factorial (a t : ℂ) (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ ↦
      (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * t ^ n)
      (1 / (1 - t) ^ a) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).hasSum
    (show t ∈ Metric.eball (0 : ℂ) 1 by
      simp only [Metric.mem_eball, edist_zero_right]
      rw [enorm_eq_nnnorm]
      exact_mod_cast ht)
  have hmulti : HasSum (fun n : ℕ ↦ Ring.multichoose a n * t ^ n)
      (1 / (1 - t) ^ a) := by
    simpa [FormalMultilinearSeries.ofScalars, Ring.multichoose_eq] using h
  convert hmulti using 1 with n
  funext n
  congr 1
  exact ascPochhammer_eval_div_factorial a n

/-- The binomial series of `hasSum_ascPochhammer_mul_pow_div_factorial` is absolutely
summable inside the unit disk. -/
theorem summable_norm_ascPochhammer_mul_pow_div_factorial (a t : ℂ) (ht : ‖t‖ < 1) :
    Summable fun n : ℕ =>
      ‖(ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * t ^ n‖ := by
  have hp := Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a
  have htball : t ∈ Metric.eball (0 : ℂ) 1 := by
    simp only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast ht
  have hx : t ∈ Metric.eball (0 : ℂ)
      (FormalMultilinearSeries.ofScalars ℂ
        fun n ↦ Ring.choose (a + n - 1) n).radius :=
    (Metric.eball_subset_eball hp.r_le) htball
  have hnorm :=
    (FormalMultilinearSeries.ofScalars ℂ
      fun n ↦ Ring.choose (a + n - 1) n).summable_norm_apply hx
  refine hnorm.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [← Ring.multichoose_eq, ← ascPochhammer_eval_div_factorial]

end Complex

end
