/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Interfaces
public import LeanPool.Zeta32.FstarDefs
public import LeanPool.Zeta32.Analytic.Energy.LogNorm
public import LeanPool.Zeta32.Analytic.Energy.Stirling
public import LeanPool.Zeta32.Analytic.Contour.Kernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! the proof notes (5′), layout (4,5,3): with `t = 1/2 + iy`, `y = nx`,

    S_n |t R_n(t) w(y)| ≤ exp(c₀ + 7 log(n+1)) (1+|x|)^7 exp(−3n W(|x|)),

from the sum–integral comparison for `log ∏|t+j|` (LogNorm), the scaling of `∫₀^b log|u + i n x|
du`, the
Stirling bound for `S_n`, `|w(y)| ≤ 4π(|r|+π) e^{−2π|y|}`, and the identity
`5 log 5 − 1 + 4∫₀¹ log|u+ix| − ∫₀⁵ log|u+ix| − 2π|x| = −3 W(|x|)`.
The wfun bound follows Zeta32/Analytic/Contour/Kernel.lean and the structure follows
Li2Unified/Modular/Base/OriginalProductLog.lean, OriginalScaledProductLog.lean. -/

public section

open Real MeasureTheory Set
open scoped BigOperators

namespace Zeta32.Analytic.EnergyI
noncomputable section

/-! ### The kernel bound -/

-- adapted from Zeta32/Analytic/Contour/Kernel.lean
theorem inv_cosh_sq_le' (x : ℝ) : 1 / Real.cosh x ^ 2 ≤ 4 * Real.exp (-(2 * |x|)) := by
  exact Zeta32.Analytic.Contour.inv_cosh_sq_le x

theorem norm_wfun_le (r : ℚ) (y : ℝ) :
    ‖wfun r y‖ ≤ 4 * π * (|(r : ℝ)| + π) * Real.exp (-(2 * π) * |y|) := by
  unfold wfun
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
    have := Real.cosh_pos (π * y); positivity)]
  have h1 : ‖2 * (r : ℂ) - 2 * π * Complex.I * (Real.tanh (π * y) : ℂ)‖ ≤ 2 * |(r : ℝ)| + 2 * π
    := by
    refine (norm_sub_le _ _).trans ?_
    have e1 : ‖2 * (r : ℂ)‖ = 2 * |(r : ℝ)| := by
      rw [norm_mul, Complex.norm_ofNat, show ((r : ℂ)) = ((r : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖2 * π * Complex.I * (Real.tanh (π * y) : ℂ)‖ ≤ 2 * π := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have ht : |Real.tanh (π * y)| ≤ 1 := by
        rw [abs_le]; constructor
        · exact (Real.neg_one_lt_tanh _).le
        · exact (Real.tanh_lt_one _).le
      have := Real.pi_pos
      nlinarith
    linarith
  have h2 := inv_cosh_sq_le' (π * y)
  rw [abs_mul, abs_of_pos Real.pi_pos] at h2
  have hpi := Real.pi_pos
  have hc : 0 ≤ π / 2 / Real.cosh (π * y) ^ 2 := by
    have := Real.cosh_pos (π * y); positivity
  calc π / 2 / Real.cosh (π * y) ^ 2 * ‖2 * (r : ℂ) - 2 * π * Complex.I * (Real.tanh (π * y) : ℂ)‖
      ≤ π / 2 / Real.cosh (π * y) ^ 2 * (2 * |(r : ℝ)| + 2 * π) := mul_le_mul_of_nonneg_left h1 hc
    _ = π / 2 * (1 / Real.cosh (π * y) ^ 2) * (2 * |(r : ℝ)| + 2 * π) := by ring
    _ ≤ π / 2 * (4 * Real.exp (-(2 * (π * |y|)))) * (2 * |(r : ℝ)| + 2 * π) := by
        gcongr
    _ = 4 * π * (|(r : ℝ)| + π) * Real.exp (-(2 * π) * |y|) := by ring_nf

/-! ### The products -/

theorem prod_log_norm_eq_sum (m : ℕ) (y : ℝ) :
    Real.log ‖∏ j ∈ Finset.Icc 1 m, ((1/2 : ℂ) + Complex.I * (y : ℂ) + (j : ℂ))‖ =
      ∑ i ∈ Finset.range m, Real.log ‖(((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ := by
  have hnonzero : ∀ j ∈ Finset.Icc 1 m, ‖(1/2 : ℂ) + Complex.I * (y : ℂ) + (j : ℂ)‖ ≠ 0 := by
    intro j _
    apply norm_ne_zero_iff.mpr
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  rw [norm_prod, Real.log_prod hnonzero]
  calc
    (∑ j ∈ Finset.Icc 1 m, Real.log ‖(1/2 : ℂ) + Complex.I * (y : ℂ) + (j : ℂ)‖) =
        ∑ i ∈ Finset.range m, Real.log ‖(1/2 : ℂ) + Complex.I * (y : ℂ) + ((i + 1 : ℕ) : ℂ)‖ := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      simpa only [Nat.add_sub_cancel, Nat.add_comm 1] using
        (Finset.sum_Ico_eq_sum_range
          (fun j : ℕ => Real.log ‖(1/2 : ℂ) + Complex.I * (y : ℂ) + (j : ℂ)‖) 1 (m + 1))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      push_cast
      ring

theorem prod_ne_zero (m : ℕ) (y : ℝ) :
    ∏ j ∈ Finset.Icc 1 m, ((1/2 : ℂ) + Complex.I * (y : ℂ) + (j : ℂ)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j _ h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]

/-! ### The external field identity -/

theorem integral_log_norm_abs (b x : ℝ) :
    (∫ t : ℝ in (0:ℝ)..b, Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) =
      ∫ t : ℝ in (0:ℝ)..b, Real.log ‖(t : ℂ) + ((|x| : ℝ) : ℂ) * Complex.I‖ := by
  apply intervalIntegral.integral_congr
  intro t _
  simp only [log_norm_real_add_imag, sq_abs]

/-- `5 log 5 − 1 + 4 I₁ − I₅ − 2π|x| = −3 W(|x|)`. -/
theorem external_field_eq (x : ℝ) :
    5 * Real.log 5 - 1 + 4 * (∫ t : ℝ in (0:ℝ)..1, Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) -
      (∫ t : ℝ in (0:ℝ)..5, Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) - 2 * π * |x| =
      -(3 * Wt |x|) := by
  rw [integral_log_norm_abs 1 x, integral_log_norm_abs 5 x,
    integral_log_norm_real_add_imag (abs_nonneg x),
    integral_log_norm_real_add_imag (abs_nonneg x)]
  have h25 : Real.log (5 ^ 2 + |x| ^ 2) = 2 * Real.log 5 + Real.log (1 + |x| ^ 2 / 25) := by
    rw [show (5:ℝ) ^ 2 + |x| ^ 2 = 5 ^ 2 * (1 + |x| ^ 2 / 25) by ring, Real.log_mul (by norm_num)
      (by positivity), Real.log_pow]
    push_cast; ring
  rw [h25]
  unfold Wt
  simp only [one_pow, one_div]
  ring

/-! ### The pointwise bound -/

/-- The single-variable Heine factor `|t R_n(t) w(y)|`, `t = 1/2 + iy`. -/
@[expose]
def psiH (r : ℚ) (n : ℕ) (y : ℝ) : ℝ :=
  ‖((1/2 : ℂ) + Complex.I * (y : ℂ)) * Rfun n ((1/2 : ℂ) + Complex.I * (y : ℂ)) * wfun r y‖

theorem psiH_nonneg (r : ℚ) (n : ℕ) (y : ℝ) : 0 ≤ psiH r n y := norm_nonneg _

/-- The constant `c₀ = 7 + log(4π(|r|+π)) + 6 log 2`. -/
def cPt (r : ℚ) : ℝ := 7 + Real.log (4 * π * (|(r : ℝ)| + π)) + 6 * Real.log 2

/-- the proof notes (5′). -/
theorem pointwise_bound (r : ℚ) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    (Sn n : ℝ) * psiH r n ((n : ℝ) * x) ≤
      Real.exp (cPt r + 7 * Real.log ((n : ℝ) + 1)) *
        ((1 + |x|) ^ 7 * Real.exp (-(3 * (n : ℝ)) * Wt |x|)) := by
  set y := (n : ℝ) * x with hy
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpi := Real.pi_pos
  set t : ℂ := (1/2 : ℂ) + Complex.I * (y : ℂ) with ht
  set P1 := ∏ j ∈ Finset.Icc 1 n, (t + (j : ℂ)) with hP1
  set P5 := ∏ j ∈ Finset.Icc 1 (5 * n), (t + (j : ℂ)) with hP5
  have hP1ne : P1 ≠ 0 := prod_ne_zero n y
  have hP5ne : P5 ≠ 0 := prod_ne_zero (5 * n) y
  have htne : t ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [ht] at this
  have hSn : 0 < (Sn n : ℝ) := by exact_mod_cast Sn_pos n
  -- the modulus
  have hpsi : psiH r n y = ‖t‖ * (‖P1‖ ^ 4 / ‖P5‖) * ‖wfun r y‖ := by
    unfold psiH Rfun
    rw [← ht, norm_mul, norm_mul, norm_div, norm_pow]
  set A := (Sn n : ℝ) * (‖t‖ * (‖P1‖ ^ 4 / ‖P5‖)) with hA
  have hnt : 0 < ‖t‖ := norm_pos_iff.mpr htne
  have hn1 : 0 < ‖P1‖ := norm_pos_iff.mpr hP1ne
  have hn5 : 0 < ‖P5‖ := norm_pos_iff.mpr hP5ne
  have hApos : 0 < A := by positivity
  have hlogA : Real.log A = Real.log (Sn n : ℝ) + Real.log ‖t‖ + 4 * Real.log ‖P1‖ - Real.log
    ‖P5‖ := by
    have hq : 0 < ‖P1‖ ^ 4 / ‖P5‖ := by positivity
    rw [hA, Real.log_mul hSn.ne' (by positivity), Real.log_mul hnt.ne' hq.ne',
      Real.log_div (by positivity) hn5.ne', Real.log_pow]
    push_cast; ring
  -- the four estimates
  have hS := Sn_log_upper n hn
  have ht_le : ‖t‖ ≤ ((n : ℝ) + 1) * (1 + |x|) := by
    rw [ht]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hy, abs_mul,
      abs_of_pos hn0]
    norm_num
    nlinarith [abs_nonneg x]
  have hlogt : Real.log ‖t‖ ≤ Real.log ((n : ℝ) + 1) + Real.log (1 + |x|) := by
    rw [← Real.log_mul (by linarith) (by positivity)]
    exact Real.log_le_log (norm_pos_iff.mpr htne) ht_le
  have hsum1 := log_norm_sum_le_integral_add_error n y
  have hsum5 := (log_norm_sum_comparison (5 * n) y).1
  rw [← prod_log_norm_eq_sum] at hsum1 hsum5
  rw [← ht] at hsum1 hsum5
  have hsc1 := integral_log_norm_scale hn0 1 x
  have hsc5 := integral_log_norm_scale hn0 5 x
  rw [mul_one, ← hy] at hsc1
  rw [← hy] at hsc5
  have hcast5 : ((5 * n : ℕ) : ℝ) = (n : ℝ) * 5 := by push_cast; ring
  rw [hcast5, hsc5] at hsum5
  rw [hsc1] at hsum1
  rw [← hP1] at hsum1
  rw [← hP5] at hsum5
  have hext := external_field_eq x
  have hlog1 : Real.log ((n : ℝ) + 3 / 2 + |y|) ≤ Real.log 2 + Real.log ((n : ℝ) + 1) + Real.log
    (1 + |x|) := by
    rw [← Real.log_mul (by norm_num) (by linarith), ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [hy, abs_mul, abs_of_pos hn0]
    nlinarith [abs_nonneg x]
  have hw := norm_wfun_le r y
  have hyabs : |y| = (n : ℝ) * |x| := by rw [hy, abs_mul, abs_of_pos hn0]
  -- assemble
  have hexp : Real.log A + Real.log (4 * π * (|(r : ℝ)| + π)) - 2 * π * |y| ≤
      cPt r + 7 * Real.log ((n : ℝ) + 1) + 7 * Real.log (1 + |x|) - 3 * (n : ℝ) * Wt |x| := by
    rw [hlogA]
    unfold cPt
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
    have hext' := congrArg (fun z => (n : ℝ) * z) hext
    rw [hyabs]
    linarith
  have hCw : 0 < 4 * π * (|(r : ℝ)| + π) := by positivity
  calc (Sn n : ℝ) * psiH r n y = A * ‖wfun r y‖ := by rw [hpsi, hA]; ring
    _ ≤ A * (4 * π * (|(r : ℝ)| + π) * Real.exp (-(2 * π) * |y|)) :=
        mul_le_mul_of_nonneg_left hw hApos.le
    _ = Real.exp (Real.log A + Real.log (4 * π * (|(r : ℝ)| + π)) - 2 * π * |y|) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hApos, Real.exp_log hCw,
          show -(2 * π) * |y| = -(2 * π * |y|) by ring, Real.exp_neg]
        field_simp
    _ ≤ Real.exp (cPt r + 7 * Real.log ((n : ℝ) + 1) + 7 * Real.log (1 + |x|) - 3 * (n : ℝ) * Wt
      |x|) :=
        Real.exp_le_exp.mpr hexp
    _ = Real.exp (cPt r + 7 * Real.log ((n : ℝ) + 1)) *
        ((1 + |x|) ^ 7 * Real.exp (-(3 * (n : ℝ)) * Wt |x|)) := by
        rw [show cPt r + 7 * Real.log ((n : ℝ) + 1) + 7 * Real.log (1 + |x|) - 3 * (n : ℝ) * Wt
          |x| =
          (cPt r + 7 * Real.log ((n : ℝ) + 1)) + (7 * Real.log (1 + |x|) + (-(3 * (n : ℝ)) * Wt
            |x|))
          by ring, Real.exp_add, Real.exp_add,
          show 7 * Real.log (1 + |x|) = Real.log ((1 + |x|) ^ 7) by rw [Real.log_pow]; norm_num,
          Real.exp_add, Real.exp_log (by positivity)]

end
end Zeta32.Analytic.EnergyI

end
