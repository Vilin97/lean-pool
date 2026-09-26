/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Stage11Amortization
public import LeanPool.ParameterFreeGradient.O3.Stage4AlgebraRadius
public import LeanPool.ParameterFreeGradient.O3.Stage3Anchor

/-!
# Stage 11R: normalization to the frozen condition number

This file contains only the scalar bridge from the factor-four endpoint of
the executable controller amortization to `conditionBar = max 1 condition`.
The constants are explicit and independent of the problem instance.
-/

@[expose] public section

namespace O3

theorem condition_le_conditionBar (P : AdmissibleInstance d p) :
    P.condition ≤ P.conditionBar := le_max_right _ _

theorem one_le_conditionBar (P : AdmissibleInstance d p) :
    1 ≤ P.conditionBar := le_max_left _ _

theorem conditionBar_nonneg (P : AdmissibleInstance d p) :
    0 ≤ P.conditionBar := (zero_le_one.trans (one_le_conditionBar P))

theorem condition_nonneg (P : AdmissibleInstance d p) :
    0 ≤ P.condition := by
  unfold AdmissibleInstance.condition
  exact div_nonneg
    (mul_nonneg P.L_pos.le
      (minimizerDistance_nonneg_of_nonempty P.minimizer_nonempty))
    P.eps_pos.le

theorem condition_rpow_le_conditionBar_rpow (P : AdmissibleInstance d p)
    {a : ℝ} (ha : 0 ≤ a) :
    P.condition ^ a ≤ P.conditionBar ^ a :=
  Real.rpow_le_rpow (condition_nonneg P) (condition_le_conditionBar P) ha

theorem four_mul_rpow_le_conditionBar_rpow (P : AdmissibleInstance d p)
    {a : ℝ} (ha : 0 ≤ a) :
    (4 * P.condition) ^ a ≤ 4 ^ a * P.conditionBar ^ a := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (condition_nonneg P)]
  exact mul_le_mul_of_nonneg_left (condition_rpow_le_conditionBar_rpow P ha)
    (Real.rpow_nonneg (by norm_num) _)

theorem sqrt_four_condition_le (P : AdmissibleInstance d p) :
    Real.sqrt (4 * P.condition) ≤ 2 * Real.sqrt P.conditionBar := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show Real.sqrt 4 = 2 by norm_num [Real.sqrt_eq_iff_mul_self_eq_of_pos]]
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (condition_le_conditionBar P)) (by norm_num)

theorem log_exp_one_add_conditionBar_ge_one (P : AdmissibleInstance d p) :
    1 ≤ Real.log (Real.exp 1 + P.conditionBar) := by
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hle : Real.exp 1 ≤ Real.exp 1 + P.conditionBar := by
    linarith [conditionBar_nonneg P]
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (Real.exp 1 + P.conditionBar) :=
      Real.strictMonoOn_log.monotoneOn hpos
        (add_pos_of_pos_of_nonneg hpos (conditionBar_nonneg P)) hle

theorem belowWeight_four_condition_le (P : AdmissibleInstance d p) :
    belowWrapperWeight (4 * P.condition) ≤
      4 * belowWrapperWeight P.conditionBar := by
  unfold belowWrapperWeight
  have hK := condition_nonneg P
  have hB := conditionBar_nonneg P
  have hsqrt := sqrt_four_condition_le P
  have harg : Real.exp 1 + 4 * P.condition ≤
      Real.exp 1 + 4 * P.conditionBar := by
    linarith [condition_le_conditionBar P]
  have hpoly : Real.exp 1 + 4 * P.conditionBar ≤
      (Real.exp 1 + P.conditionBar) ^ 2 := by
    have he : 2 < Real.exp 1 := by
      convert Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num) using 1;
        norm_num
    nlinarith [one_le_conditionBar P]
  have hleft : 0 < Real.exp 1 + 4 * P.condition := by positivity
  have hright : 0 < (Real.exp 1 + P.conditionBar) ^ 2 := by positivity
  have hlog : Real.log (Real.exp 1 + 4 * P.condition) ≤
      Real.log ((Real.exp 1 + P.conditionBar) ^ 2) :=
    Real.strictMonoOn_log.monotoneOn hleft hright (harg.trans hpoly)
  rw [Real.log_pow] at hlog
  have hlognonneg : 0 ≤ Real.log (Real.exp 1 + 4 * P.condition) := by
    apply Real.log_nonneg
    have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hbarlog : 0 ≤ Real.log (Real.exp 1 + P.conditionBar) :=
    (zero_le_one.trans (log_exp_one_add_conditionBar_ge_one P))
  have hmul := mul_le_mul hsqrt hlog hlognonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _))
  calc
    Real.sqrt (4 * P.condition) * Real.log (Real.exp 1 + 4 * P.condition)
        ≤ 2 * Real.sqrt P.conditionBar *
            (2 * Real.log (Real.exp 1 + P.conditionBar)) := by simpa using hmul
    _ = 4 * (Real.sqrt P.conditionBar *
          Real.log (Real.exp 1 + P.conditionBar)) := by ring

/-- Universal coefficient for converting the exact binary-log ceiling of the
anchor to the natural-log overhead used in the frozen theorem. -/
noncomputable def anchorLogConstant : ℝ := 2 + 1 / Real.log 2

theorem anchorLogConstant_pos : 0 < anchorLogConstant := by
  unfold anchorLogConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem anchor_ceiling_le_log_overhead {L M0 : ℝ}
    (hM0 : 0 < M0) (hM0L : M0 ≤ L) :
    (1 + Nat.ceil (Real.logb 2 (L / M0)) : ℕ) ≤
      anchorLogConstant * Real.log (Real.exp 1 + L / M0) := by
  have hx : 1 ≤ L / M0 := (le_div_iff₀ hM0).2 (by simpa using hM0L)
  have hxpos : 0 < L / M0 := zero_lt_one.trans_le hx
  have hlogx : 0 ≤ Real.log (L / M0) := Real.log_nonneg hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : 0 ≤ Real.logb 2 (L / M0) := by
    rw [Real.logb]
    positivity
  have hceil := Nat.ceil_lt_add_one hlogb
  have hnat : ((1 + Nat.ceil (Real.logb 2 (L / M0)) : ℕ) : ℝ) ≤
      2 + Real.logb 2 (L / M0) := by
    norm_num
    linarith
  have hlogmono : Real.log (L / M0) ≤
      Real.log (Real.exp 1 + L / M0) := by
    exact Real.strictMonoOn_log.monotoneOn hxpos
      (add_pos (Real.exp_pos 1) hxpos)
      (by linarith [Real.exp_pos (1 : ℝ)])
  have hone := show 1 ≤ Real.log (Real.exp 1 + L / M0) by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log (Real.exp 1 + L / M0) :=
        Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
          (add_pos (Real.exp_pos 1) hxpos)
          (by linarith)
  rw [Real.logb] at hnat
  unfold anchorLogConstant
  have hdiv : Real.log (L / M0) / Real.log 2 ≤
      (1 / Real.log 2) * Real.log (Real.exp 1 + L / M0) := by
    rw [div_eq_mul_inv, one_div]
    rw [mul_comm (Real.log (L / M0))]
    exact mul_le_mul_of_nonneg_left hlogmono (inv_nonneg.mpr hlog2.le)
  norm_num at hnat ⊢
  have hlogOverhead : 0 ≤ Real.log (Real.exp 1 + L / M0) :=
    zero_le_one.trans hone
  rw [Real.logb] at ⊢
  calc
    (1 : ℝ) + Nat.ceil (Real.log (L / M0) / Real.log 2)
        ≤ 2 + Real.log (L / M0) / Real.log 2 := hnat
    _ ≤ 2 * Real.log (Real.exp 1 + L / M0) +
          (1 / Real.log 2) * Real.log (Real.exp 1 + L / M0) := by
      nlinarith
    _ = (2 + (Real.log 2)⁻¹) *
          Real.log (Real.exp 1 + L / M0) := by ring

theorem admissible_M0_le_L (P : AdmissibleInstance d p) : P.M0 ≤ P.L := by
  have hsec := secantScale_le (p := p) (q := conjugateExponent p)
    (L := P.L) P.smooth P.secant.1
  calc
    P.M0 = lpNorm (conjugateExponent p) (P.grad P.z0 - P.grad P.x0) /
        lpNorm p (P.z0 - P.x0) := P.secant.2.2.1
    _ = secantScale p (conjugateExponent p) P.grad P.x0 P.z0 := rfl
    _ ≤ P.L := hsec

theorem admissible_log_overhead_ge_one (P : AdmissibleInstance d p) :
    1 ≤ Real.log (Real.exp 1 + P.L / P.M0) := by
  have hx : 0 < P.L / P.M0 := div_pos P.L_pos P.secant.2.2.2
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (Real.exp 1 + P.L / P.M0) :=
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
        (add_pos (Real.exp_pos 1) hx) (by linarith)

/-- The positive constant accounting for the initial query and logarithmic anchor overhead. -/
noncomputable def anchorPrefixConstant : ℝ := 1 + anchorLogConstant

theorem anchorPrefixConstant_pos : 0 < anchorPrefixConstant := by
  unfold anchorPrefixConstant
  linarith [anchorLogConstant_pos]

/-- The controller prefix consists of the initial query plus all anchor
observations.  This is the exact bridge from the anchor's ceiling count to the
additive term in the frozen wrapper bounds. -/
theorem anchor_prefix_le_log_overhead (P : AdmissibleInstance d p)
    {observations : OracleTrace d}
    (hcount : observations.length ≤
      1 + Nat.ceil (Real.logb 2 (P.L / P.M0))) :
    ((1 + observations.length : ℕ) : ℝ) ≤
      anchorPrefixConstant * Real.log (Real.exp 1 + P.L / P.M0) := by
  have hanchor := anchor_ceiling_le_log_overhead P.secant.2.2.2
    (admissible_M0_le_L P)
  have hx : 1 ≤ P.L / P.M0 :=
    (le_div_iff₀ P.secant.2.2.2).2 (by simpa using admissible_M0_le_L P)
  have hlog : 1 ≤ Real.log (Real.exp 1 + P.L / P.M0) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log (Real.exp 1 + P.L / P.M0) :=
        Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
          (add_pos (Real.exp_pos 1) (zero_lt_one.trans_le hx)) (by linarith)
  have hcountReal : ((observations.length : ℕ) : ℝ) ≤
      (1 + Nat.ceil (Real.logb 2 (P.L / P.M0)) : ℕ) := by exact_mod_cast hcount
  unfold anchorPrefixConstant
  norm_num at hcountReal hanchor ⊢
  nlinarith

theorem euclidean_envelope_normalized (P : AdmissibleInstance d p)
    {pre total A : ℝ} (hA : 0 ≤ A)
    (henvelope : total ≤ pre + A * euclideanWrapperWeight (4 * P.condition))
    (hprefix : pre ≤ anchorPrefixConstant *
      Real.log (Real.exp 1 + P.L / P.M0)) :
    total ≤ (anchorPrefixConstant + 2 * A) * Real.sqrt P.conditionBar +
      (anchorPrefixConstant + 2 * A) *
        Real.log (Real.exp 1 + P.L / P.M0) := by
  have hw : euclideanWrapperWeight (4 * P.condition) ≤
      2 * Real.sqrt P.conditionBar := by
    simpa [euclideanWrapperWeight] using sqrt_four_condition_le P
  have hmain : 0 ≤ Real.sqrt P.conditionBar := Real.sqrt_nonneg _
  have hlog : 0 ≤ Real.log (Real.exp 1 + P.L / P.M0) := by
    apply Real.log_nonneg
    have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hx : 0 ≤ P.L / P.M0 :=
      div_nonneg P.L_pos.le P.secant.2.2.2.le
    linarith
  have hAC : 0 ≤ anchorPrefixConstant := anchorPrefixConstant_pos.le
  have hAw := mul_le_mul_of_nonneg_left hw hA
  calc
    total ≤ pre + A * euclideanWrapperWeight (4 * P.condition) := henvelope
    _ ≤ anchorPrefixConstant * Real.log (Real.exp 1 + P.L / P.M0) +
        A * (2 * Real.sqrt P.conditionBar) := add_le_add hprefix hAw
    _ ≤ (anchorPrefixConstant + 2 * A) * Real.sqrt P.conditionBar +
        (anchorPrefixConstant + 2 * A) *
          Real.log (Real.exp 1 + P.L / P.M0) := by
      have hex1 := mul_nonneg hAC hmain
      have hex2 := mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA) hlog
      nlinarith

theorem below_envelope_normalized (P : AdmissibleInstance d p)
    {pre total A : ℝ} (hA : 0 ≤ A)
    (henvelope : total ≤ pre + A * belowWrapperWeight (4 * P.condition))
    (hprefix : pre ≤ anchorPrefixConstant *
      Real.log (Real.exp 1 + P.L / P.M0)) :
    total ≤ (anchorPrefixConstant + 4 * A) *
        (P.conditionBar ^ (1 / 2 : ℝ)) *
          Real.log (Real.exp 1 + P.conditionBar) +
      (anchorPrefixConstant + 4 * A) *
        Real.log (Real.exp 1 + P.L / P.M0) := by
  have hw := belowWeight_four_condition_le P
  have hsqrt : P.conditionBar ^ (1 / 2 : ℝ) = Real.sqrt P.conditionBar := by
    rw [Real.sqrt_eq_rpow]
  have hmain : 0 ≤ P.conditionBar ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (conditionBar_nonneg P) _
  have hbarlog : 0 ≤ Real.log (Real.exp 1 + P.conditionBar) :=
    zero_le_one.trans (log_exp_one_add_conditionBar_ge_one P)
  have hoverlog : 0 ≤ Real.log (Real.exp 1 + P.L / P.M0) := by
    apply Real.log_nonneg
    have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hx : 0 ≤ P.L / P.M0 :=
      div_nonneg P.L_pos.le P.secant.2.2.2.le
    linarith
  have hAw := mul_le_mul_of_nonneg_left hw hA
  unfold belowWrapperWeight at hAw
  rw [← hsqrt] at hAw
  have hAC : 0 ≤ anchorPrefixConstant := anchorPrefixConstant_pos.le
  calc
    total ≤ pre + A * belowWrapperWeight (4 * P.condition) := henvelope
    _ ≤ anchorPrefixConstant * Real.log (Real.exp 1 + P.L / P.M0) +
        A * (4 * (P.conditionBar ^ (1 / 2 : ℝ) *
          Real.log (Real.exp 1 + P.conditionBar))) := add_le_add hprefix hAw
    _ ≤ (anchorPrefixConstant + 4 * A) *
          P.conditionBar ^ (1 / 2 : ℝ) *
            Real.log (Real.exp 1 + P.conditionBar) +
        (anchorPrefixConstant + 4 * A) *
          Real.log (Real.exp 1 + P.L / P.M0) := by
      have hex1 := mul_nonneg hAC (mul_nonneg hmain hbarlog)
      have hex2 := mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hA) hoverlog
      nlinarith

theorem above_envelope_normalized (P : AdmissibleInstance d p)
    {a pre total A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A)
    (henvelope : total ≤ pre + A * aboveWrapperWeight a (4 * P.condition))
    (hprefix : pre ≤ anchorPrefixConstant *
      Real.log (Real.exp 1 + P.L / P.M0)) :
    total ≤ (anchorPrefixConstant + 4 ^ a * A) * P.conditionBar ^ a +
      (anchorPrefixConstant + 4 ^ a * A) *
        Real.log (Real.exp 1 + P.L / P.M0) := by
  have hw : aboveWrapperWeight a (4 * P.condition) ≤
      4 ^ a * P.conditionBar ^ a := by
    simpa [aboveWrapperWeight] using four_mul_rpow_le_conditionBar_rpow P ha
  have hpow : 0 ≤ P.conditionBar ^ a := Real.rpow_nonneg (conditionBar_nonneg P) _
  have hfour : 0 ≤ (4 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
  have hoverlog : 0 ≤ Real.log (Real.exp 1 + P.L / P.M0) := by
    apply Real.log_nonneg
    have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hx : 0 ≤ P.L / P.M0 :=
      div_nonneg P.L_pos.le P.secant.2.2.2.le
    linarith
  have hAw := mul_le_mul_of_nonneg_left hw hA
  have hAC : 0 ≤ anchorPrefixConstant := anchorPrefixConstant_pos.le
  calc
    total ≤ pre + A * aboveWrapperWeight a (4 * P.condition) := henvelope
    _ ≤ anchorPrefixConstant * Real.log (Real.exp 1 + P.L / P.M0) +
        A * ((4 : ℝ) ^ a * P.conditionBar ^ a) := add_le_add hprefix hAw
    _ ≤ (anchorPrefixConstant + (4 : ℝ) ^ a * A) * P.conditionBar ^ a +
        (anchorPrefixConstant + (4 : ℝ) ^ a * A) *
          Real.log (Real.exp 1 + P.L / P.M0) := by
      have hex1 := mul_nonneg hAC hpow
      have hex2 := mul_nonneg (mul_nonneg hfour hA) hoverlog
      nlinarith

end O3
