/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingSchedule
import LeanPool.NavierStokesAndEuler.NavierStokes.MomentRepair
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Quantitative bounds for the constructed outgoing pulse

All profiles and moments in this file are those of `OutgoingSchedule` and
`LocalizedMomentRepair`. In particular the correction bumps are not an
additional choice. Their log-coordinate translates are identified below.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.OutgoingPulseBounds

open OutgoingSchedule

theorem slope_bounds (c : Parameters) (y : ℝ) :
    -c.lam ≤ slope c.dropLength c.lam y ∧
      slope c.dropLength c.lam y ≤ 3 / 5 := by
  have h0 := sigma_nonneg y
  have h1 := sigma_le_one y
  have h2 := sigma_nonneg (y - (c.dropLength + 1))
  have h3 := sigma_le_one (y - (c.dropLength + 1))
  have ha := mul_nonneg c.lam_pos.le h2
  have hb := mul_nonneg c.lam_pos.le (sub_nonneg.mpr h3)
  dsimp [OutgoingSchedule.slope]
  constructor <;> nlinarith

theorem logAmplitude_bounds (c : Parameters) {y : ℝ} (hy : 0 ≤ y) :
    -y ≤ logAmplitude c.dropLength c.lam y ∧
      logAmplitude c.dropLength c.lam y ≤ y := by
  have hc : Continuous (fun t => slope c.dropLength c.lam t - 1 / 2) :=
    (slope_contDiff _ _).continuous.sub continuous_const
  have hl : ∀ t, (-1 : ℝ) ≤ slope c.dropLength c.lam t - 1 / 2 := by
    intro t
    linarith [(slope_bounds c t).1, c.lam_lt]
  have hu : ∀ t, slope c.dropLength c.lam t - 1 / 2 ≤ (1 : ℝ) := by
    intro t
    linarith [(slope_bounds c t).2]
  constructor
  · have h := intervalIntegral.integral_mono_on (μ := volume) hy
      (continuous_const.intervalIntegrable 0 y) (hc.intervalIntegrable 0 y)
      (fun t _ => hl t)
    simpa [logAmplitude, primitive] using h
  · have h := intervalIntegral.integral_mono_on (μ := volume) hy
      (hc.intervalIntegrable 0 y) (continuous_const.intervalIntegrable 0 y)
      (fun t _ => hu t)
    simpa [logAmplitude, primitive] using h

theorem radialAmplitude_bounds (c : Parameters) {y : ℝ} (hy : 0 ≤ y) :
    c.P * Real.exp (-y) ≤ radialAmplitude c.P c.dropLength c.lam y ∧
      radialAmplitude c.P c.dropLength c.lam y ≤ c.P * Real.exp y := by
  obtain ⟨hl, hu⟩ := logAmplitude_bounds c hy
  exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hl) c.P_pos.le,
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu) c.P_pos.le⟩

theorem integral_stops {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (hab : a ≤ b) (hz : ∀ t, a ≤ t → g t = 0) :
    (∫ t in (0 : ℝ)..b, g t) = ∫ t in (0 : ℝ)..a, g t := by
  have hzero : (∫ t in a..b, g t) = 0 := by
    calc
      _ = ∫ _t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hz t (uIcc_of_le hab ▸ ht).1
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 a) (hg.intervalIntegrable a b)
  rw [hzero, add_zero] at h
  exact h.symm

theorem dropEnd_le_pulseStart (c : Parameters) : Real.exp c.m ≤ c.pulseStart := by
  have h := c.pulseStart_ge_hold
  dsimp [Parameters.holdStart, Parameters.dropLength] at h
  linarith

theorem prefixM_fixed_interval (c : Parameters) :
    prefixM c = 4 + ∫ y in (0 : ℝ)..Real.exp c.m,
      Real.exp y * dropCoefficient c.m y := by
  unfold prefixM
  congr 1
  apply integral_stops
    (Real.continuous_exp.mul (dropCoefficient_contDiff c.m_pos).continuous)
    (dropEnd_le_pulseStart c)
  intro t ht
  simp only [Pi.mul_apply]
  rw [dropCoefficient_late c.m_pos ht, mul_zero]

theorem prefixJ_fixed_interval (c : Parameters) :
    prefixJ c = (5 / 2) * Real.sqrt 2 * c.P +
      ∫ y in (0 : ℝ)..Real.exp c.m,
        Real.sqrt 2 * Real.exp (3 * y / 2) *
          radialAmplitude c.P c.dropLength c.lam y * dropCoefficient c.m y := by
  unfold prefixJ
  congr 1
  apply integral_stops
    (((continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).div_const 2))).mul
      (radialAmplitude_contDiff _ _ _).continuous).mul
      (dropCoefficient_contDiff c.m_pos).continuous)
    (dropEnd_le_pulseStart c)
  intro t ht
  simp only [Pi.mul_apply, Function.comp_apply, id_eq]
  rw [dropCoefficient_late c.m_pos ht, mul_zero]

theorem prefixM_bounds (c : Parameters) :
    0 ≤ prefixM c ∧ prefixM c ≤ 4 + 4 * Real.exp c.m * Real.exp (Real.exp c.m) := by
  rw [prefixM_fixed_interval]
  have hc : Continuous (fun y => Real.exp y * dropCoefficient c.m y) :=
    Real.continuous_exp.mul (dropCoefficient_contDiff c.m_pos).continuous
  have hpos := intervalIntegral.integral_nonneg (μ := volume) (Real.exp_pos c.m).le
    (fun y _ => mul_nonneg (Real.exp_pos y).le (dropCoefficient_bounds c.m y).1)
  have hup := intervalIntegral.integral_mono_on (μ := volume) (Real.exp_pos c.m).le
    (hc.intervalIntegrable 0 _) (continuous_const.intervalIntegrable 0 _)
    (fun y hy => show Real.exp y * dropCoefficient c.m y ≤
        4 * Real.exp (Real.exp c.m) from by
      calc
        _ ≤ Real.exp (Real.exp c.m) * 4 := mul_le_mul
          (Real.exp_le_exp.mpr hy.2) (dropCoefficient_bounds c.m y).2
          (dropCoefficient_bounds c.m y).1 (Real.exp_pos _).le
        _ = _ := by ring)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hup
  constructor <;> nlinarith

theorem prefixJ_bounds (c : Parameters) :
    0 ≤ prefixJ c ∧
      prefixJ c ≤ (5 / 2) * Real.sqrt 2 * c.P +
        4 * Real.sqrt 2 * c.P * Real.exp c.m * Real.exp (3 * Real.exp c.m) := by
  rw [prefixJ_fixed_interval]
  let K := Real.exp c.m
  have hK : 0 < K := Real.exp_pos _
  have hs : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have he : ∀ y, 0 ≤ radialAmplitude c.P c.dropLength c.lam y :=
    fun y => (mul_pos c.P_pos (Real.exp_pos _)).le
  have hc : Continuous (fun y => Real.sqrt 2 * Real.exp (3 * y / 2) *
      radialAmplitude c.P c.dropLength c.lam y * dropCoefficient c.m y) :=
    (((continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).div_const 2))).mul
      (radialAmplitude_contDiff _ _ _).continuous).mul
      (dropCoefficient_contDiff c.m_pos).continuous)
  have hpos := intervalIntegral.integral_nonneg (μ := volume) hK.le
    (fun y _ => mul_nonneg (mul_nonneg (mul_nonneg hs (Real.exp_pos (3 * y / 2)).le)
      (he y)) (dropCoefficient_bounds c.m y).1)
  have hup := intervalIntegral.integral_mono_on (μ := volume) hK.le
    (hc.intervalIntegrable 0 K) (continuous_const.intervalIntegrable 0 K)
    (fun y hy => show Real.sqrt 2 * Real.exp (3 * y / 2) *
        radialAmplitude c.P c.dropLength c.lam y * dropCoefficient c.m y ≤
        4 * Real.sqrt 2 * c.P * Real.exp (3 * K) from by
      have hr := (radialAmplitude_bounds c hy.1).2
      have hE : radialAmplitude c.P c.dropLength c.lam y ≤ c.P * Real.exp K :=
        hr.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy.2) c.P_pos.le)
      have hpow : Real.exp (3 * y / 2) ≤ Real.exp (2 * K) :=
        Real.exp_le_exp.mpr (by linarith [hy.2])
      calc
        _ ≤ (Real.sqrt 2 * Real.exp (2 * K)) * (c.P * Real.exp K) * 4 :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hpow hs) hE
            (he y) (mul_nonneg hs (Real.exp_pos _).le))
            (dropCoefficient_bounds c.m y).2 (dropCoefficient_bounds c.m y).1
            (mul_nonneg (mul_nonneg hs (Real.exp_pos _).le)
              (mul_nonneg c.P_pos.le (Real.exp_pos _).le))
        _ = 4 * Real.sqrt 2 * c.P * (Real.exp (2 * K) * Real.exp K) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 3 ; ring)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hup
  change 0 ≤ (5 / 2) * Real.sqrt 2 * c.P + _ ∧ _
  constructor
  · have hP := c.P_pos
    exact add_nonneg (by positivity) hpos
  · dsimp [K]
      at hup
    nlinarith

/-! ## Decay along the explicitly timed shaped wait -/

/-- Beta, given by `c.exponents i + 1`. -/
noncomputable def beta (c : Parameters) (i : Fin 2) : ℝ := c.exponents i + 1

theorem beta_bounds (c : Parameters) (i : Fin 2) :
    0 < beta c i ∧ beta c i ≤ 1 / 2 := by
  fin_cases i <;> norm_num [beta, Parameters.exponents] <;>
    constructor <;> linarith [c.lam_pos, c.lam_lt]

theorem beta_small_bounds (c : Parameters) (hc : c.lam ≤ 1 / 120) (i : Fin 2) :
    2 / 5 ≤ beta c i ∧ 29 ≤ 60 * beta c i := by
  fin_cases i <;> norm_num [beta, Parameters.exponents] <;> constructor <;> linarith

/-- Hold amplitude, given by `radialAmplitude c.P c.dropLength c.lam c.holdStart`. -/
noncomputable def holdAmplitude (c : Parameters) : ℝ :=
  radialAmplitude c.P c.dropLength c.lam c.holdStart

theorem holdAmplitude_pos (c : Parameters) : 0 < holdAmplitude c :=
  mul_pos c.P_pos (Real.exp_pos _)

theorem pulseAmplitude_split (c : Parameters) :
    pulseAmplitude c = holdAmplitude c * Real.exp (-(1 / 2 + c.lam) * c.wait) := by
  have h := radialAmplitude_hold (P := c.P) (lam := c.lam) c.dropLength_pos.le
    (show c.dropLength + 2 ≤ c.holdStart from le_rfl) c.pulseStart_ge_hold
  simpa [pulseAmplitude, holdAmplitude, Parameters.pulseStart] using h

/-- Hold scale, with branches according to `i = 0`. -/
noncomputable def holdScale (c : Parameters) (i : Fin 2) : ℝ :=
  if i = 0 then Real.exp c.holdStart * holdAmplitude c
  else Real.sqrt 2 * Real.exp (3 * c.holdStart / 2) * holdAmplitude c ^ 2

/-- Scale floor, with branches according to `i = 0`. -/
noncomputable def scaleFloor (P m : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then P else
    Real.sqrt 2 * P ^ 2 * Real.exp (-(Real.exp m + 12) / 2)

theorem scaleFloor_pos {P : ℝ} (hP : 0 < P) (m : ℝ) (i : Fin 2) :
    0 < scaleFloor P m i := by
  unfold scaleFloor
  split_ifs <;> positivity

theorem holdScale_lower (c : Parameters) (i : Fin 2) :
    scaleFloor c.P c.m i ≤ holdScale c i := by
  have he := (radialAmplitude_bounds c c.holdStart_pos.le).1
  change c.P * Real.exp (-c.holdStart) ≤ holdAmplitude c at he
  have hexp : Real.exp c.holdStart * Real.exp (-c.holdStart) = 1 := by
    rw [← Real.exp_add]; simp
  fin_cases i
  · norm_num [scaleFloor, holdScale]
    calc
      c.P = Real.exp c.holdStart * (c.P * Real.exp (-c.holdStart)) := by
        calc
          _ = c.P * (Real.exp c.holdStart * Real.exp (-c.holdStart)) := by rw [hexp]; ring
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
  · simp only [scaleFloor, holdScale]
    have hs := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg c.P_pos.le (Real.exp_pos _).le) he 2)
      (mul_nonneg (Real.sqrt_nonneg 2) (Real.exp_pos (3 * c.holdStart / 2)).le)
    calc
      _ = Real.sqrt 2 * Real.exp (3 * c.holdStart / 2) *
          (c.P * Real.exp (-c.holdStart)) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        have hex : Real.exp (3 * c.holdStart / 2) * Real.exp (2 * -c.holdStart) =
            Real.exp (-(Real.exp c.m + 12) / 2) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [Parameters.holdStart, Parameters.dropLength]
          ring
        rw [← hex]
        ring_nf; norm_num
      _ ≤ _ := hs

theorem momentScale_split (c : Parameters) (i : Fin 2) :
    momentScale c i = holdScale c i * Real.exp (beta c i * c.wait) := by
  rw [momentScale, pulseAmplitude_split]
  fin_cases i <;> norm_num [holdScale, beta, Parameters.exponents, Parameters.pulseStart]
  · rw [Real.exp_add]
    have he : Real.exp c.wait * Real.exp (-(1 / 2 + c.lam) * c.wait) =
        Real.exp ((-(1 / 2 + c.lam) + 1) * c.wait) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (Real.exp c.holdStart * holdAmplitude c) *
          (Real.exp c.wait * Real.exp (-(1 / 2 + c.lam) * c.wait)) := by ring_nf
      _ = _ := by rw [he]; congr 2 ; ring
  · rw [mul_pow, ← Real.exp_nat_mul]
    have he : Real.exp (3 * (c.holdStart + c.wait) / 2) *
        Real.exp (2 * (-(1 / 2 + c.lam) * c.wait)) =
        Real.exp (3 * c.holdStart / 2) *
          Real.exp ((-(1 / 2 + 2 * c.lam) + 1) * c.wait) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc
      _ = Real.sqrt 2 * holdAmplitude c ^ 2 *
          (Real.exp (3 * (c.holdStart + c.wait) / 2) *
            Real.exp (2 * (-(1 / 2 + c.lam) * c.wait))) := by ring_nf
      _ = _ := by rw [he]; ring_nf

theorem exp_log_inverse_nat {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log (1 / lam)) = lam ^ n := by
  rw [one_div, Real.log_inv]
  rw [neg_mul_neg, Real.exp_nat_mul, Real.exp_log hlam]

theorem wait_decay (c : Parameters) (hwait : c.wait = 60 * Real.log (1 / c.lam))
    (hsmall : c.lam ≤ 1 / 120) (i : Fin 2) :
    Real.exp (-(beta c i * c.wait)) ≤ c.lam ^ 29 := by
  have hlog : 0 ≤ Real.log (1 / c.lam) := Real.log_nonneg (by
    apply (le_div_iff₀ c.lam_pos).mpr
    linarith [c.lam_lt])
  rw [← exp_log_inverse_nat c.lam_pos 29]
  apply Real.exp_le_exp.mpr
  rw [hwait]
  have h := mul_le_mul_of_nonneg_right (beta_small_bounds c hsmall i).2 hlog
  nlinarith

theorem pulseAmplitude_small (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) :
    pulseAmplitude c ≤ c.P * Real.exp (Real.exp c.m + 12) * c.lam ^ 30 := by
  rw [pulseAmplitude_split]
  have hhold := (radialAmplitude_bounds c c.holdStart_pos.le).2
  change holdAmplitude c ≤ c.P * Real.exp c.holdStart at hhold
  have hw : 0 ≤ c.wait := by linarith [c.wait_gt]
  have hdec : Real.exp (-(1 / 2 + c.lam) * c.wait) ≤ c.lam ^ 30 := by
    rw [← exp_log_inverse_nat c.lam_pos 30]
    apply Real.exp_le_exp.mpr
    have hprod := mul_nonneg c.lam_pos.le hw
    rw [hwait] at hprod ⊢
    nlinarith
  have h := mul_le_mul hhold hdec (Real.exp_pos _).le
    (mul_nonneg c.P_pos.le (Real.exp_pos _).le)
  convert! h using 1; dsimp [Parameters.holdStart, Parameters.dropLength]; congr 2; ring_nf

/-- Prefix numerator bound, with branches according to `i = 0`. -/
noncomputable def prefixNumeratorBound (P m : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then 4 + 4 * Real.exp m * Real.exp (Real.exp m) else
    (5 / 2) * Real.sqrt 2 * P + 4 * Real.sqrt 2 * P * Real.exp m * Real.exp (3 * Real.exp m)

/-- Prefix bound, given by `prefixNumeratorBound P m i / scaleFloor P m i`. -/
noncomputable def prefixBound (P m : ℝ) (i : Fin 2) : ℝ :=
  prefixNumeratorBound P m i / scaleFloor P m i

theorem prefixNumeratorBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) (i : Fin 2) :
    0 < prefixNumeratorBound P m i := by
  unfold prefixNumeratorBound
  split_ifs <;> positivity

theorem prefixBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) (i : Fin 2) :
    0 < prefixBound P m i :=
  div_pos (prefixNumeratorBound_pos hP m i) (scaleFloor_pos hP m i)

theorem prefixCoefficient_nonneg (c : Parameters) (i : Fin 2) :
    0 ≤ prefixCoefficient c i := by
  apply div_nonneg _ (momentScale_pos c i).le
  split_ifs
  · exact (prefixM_bounds c).1
  · exact (prefixJ_bounds c).1

theorem prefixCoefficient_decay (c : Parameters) (i : Fin 2) :
    prefixCoefficient c i ≤ prefixBound c.P c.m i * Real.exp (-(beta c i * c.wait)) := by
  have hn : (if i = 0 then prefixM c else prefixJ c) ≤ prefixNumeratorBound c.P c.m i := by
    unfold prefixNumeratorBound
    split_ifs
    · exact (prefixM_bounds c).2
    · exact (prefixJ_bounds c).2
  have hfloor := scaleFloor_pos c.P_pos c.m i
  have hsc : scaleFloor c.P c.m i * Real.exp (beta c i * c.wait) ≤ momentScale c i := by
    rw [momentScale_split]
    exact mul_le_mul_of_nonneg_right (holdScale_lower c i) (Real.exp_pos _).le
  calc
    prefixCoefficient c i ≤ prefixNumeratorBound c.P c.m i / momentScale c i :=
      div_le_div_of_nonneg_right hn (momentScale_pos c i).le
    _ ≤ prefixNumeratorBound c.P c.m i /
        (scaleFloor c.P c.m i * Real.exp (beta c i * c.wait)) :=
      div_le_div_of_nonneg_left (prefixNumeratorBound_pos c.P_pos c.m i).le
        (mul_pos hfloor (Real.exp_pos _)) hsc
    _ = _ := by rw [Real.exp_neg]; unfold prefixBound; field_simp

theorem prefixCoefficient_small (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam))
    (hsmall : c.lam ≤ 1 / 120) (i : Fin 2) :
    |prefixCoefficient c i| ≤ prefixBound c.P c.m i * c.lam ^ 29 := by
  rw [abs_of_nonneg (prefixCoefficient_nonneg c i)]
  exact (prefixCoefficient_decay c i).trans
    (mul_le_mul_of_nonneg_left (wait_decay c hwait hsmall i)
      (prefixBound_pos c.P_pos c.m i).le)

/-! The mass average is divided by the actual angular profile, including its
parameter shape. These bounds therefore include the shape's first derivative. -/

/-- Parameter polynomial, given by `eta * (1 + eta ^ 2)`. -/
noncomputable def parameterPolynomial (eta : ℝ) : ℝ := eta * (1 + eta ^ 2)

theorem parameterPolynomial_bound {eta : ℝ} (heta : |eta| ≤ 1) :
    |parameterPolynomial eta| ≤ 2 := by
  have hs : eta ^ 2 ≤ 1 := by
    have h := sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr heta
    simpa using h
  rw [parameterPolynomial, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + eta ^ 2)]
  nlinarith [abs_nonneg eta]

theorem parameterPolynomial_hasDerivAt (eta : ℝ) :
    HasDerivAt parameterPolynomial (1 + 3 * eta ^ 2) eta := by
  convert! (hasDerivAt_id eta).mul ((hasDerivAt_const eta (1 : ℝ)).add
    ((hasDerivAt_id eta).pow 2)) using 1; dsimp [parameterPolynomial]; ring

theorem parameterPolynomial_derivative_bound {eta : ℝ} (heta : |eta| ≤ 1) :
    |deriv parameterPolynomial eta| ≤ 4 := by
  rw [(parameterPolynomial_hasDerivAt eta).deriv,
    abs_of_nonneg (by positivity : 0 ≤ 1 + 3 * eta ^ 2)]
  have hs : eta ^ 2 ≤ 1 := by
    have h := sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr heta
    simpa using h
  nlinarith

theorem normalized_mass_prefix (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    massMoment c amp eta c.pulseStart /
        (Real.exp c.pulseStart * angular c.P c.dropLength c.lam (c.pulseStart, eta)) =
      prefixCoefficient c 0 * parameterPolynomial eta := by
  rw [massMoment_at_pulseStart]
  simp only [angular, shape, prefixCoefficient, momentScale, ↓reduceIte,
    pulseAmplitude, parameterPolynomial]
  have he := Real.exp_pos c.pulseStart
  have hr : 0 < radialAmplitude c.P c.dropLength c.lam c.pulseStart := pulseAmplitude_pos c
  have hp : 0 < 1 + eta ^ 2 := by positivity
  field_simp

theorem normalized_mass_prefix_small (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    (amp : ℝ → ℝ) {eta : ℝ} (heta : |eta| ≤ 1) :
    |massMoment c amp eta c.pulseStart /
        (Real.exp c.pulseStart * angular c.P c.dropLength c.lam (c.pulseStart, eta))| ≤
      (2 * prefixBound c.P c.m 0) * c.lam ^ 29 := by
  rw [normalized_mass_prefix, abs_mul]
  have h := mul_le_mul (prefixCoefficient_small c hwait hsmall 0)
    (parameterPolynomial_bound heta) (abs_nonneg _)
    (mul_nonneg (prefixBound_pos c.P_pos c.m 0).le (pow_nonneg c.lam_pos.le 29))
  nlinarith

/-! ## The actual bump is one fixed template in log coordinates -/

/-- Template lower, given by `Real.exp (-(3 / 20 : ℝ))`. -/
noncomputable def templateLower : ℝ := Real.exp (-(3 / 20 : ℝ))
/-- Template upper, given by `Real.exp (3 / 20 : ℝ)`. -/
noncomputable def templateUpper : ℝ := Real.exp (3 / 20 : ℝ)
/-- Radial template, given by `LocalizedMomentRepair.bump templateLower templateUpper`. -/
noncomputable def radialTemplate : ℝ → ℝ :=
  LocalizedMomentRepair.bump templateLower templateUpper
/-- Log template, given by `radialTemplate (Real.exp z)`. -/
noncomputable def logTemplate (z : ℝ) : ℝ := radialTemplate (Real.exp z)

theorem templateLower_pos : 0 < templateLower := Real.exp_pos _
theorem templateLower_lt_upper : templateLower < templateUpper := by
  apply Real.exp_lt_exp.mpr
  norm_num

theorem radialTemplate_contDiff : ContDiff ℝ ∞ radialTemplate :=
  LocalizedMomentRepair.bump_contDiff _ _

theorem radialTemplate_hasCompactSupport : HasCompactSupport radialTemplate :=
  LocalizedMomentRepair.bump_hasCompactSupport _ _ templateLower_lt_upper

theorem radialTemplate_nonneg (x : ℝ) : 0 ≤ radialTemplate x :=
  LocalizedMomentRepair.bump_nonneg _ _ _

theorem radialTemplate_support (x : ℝ) (hx : radialTemplate x ≠ 0) :
    templateLower < x ∧ x < templateUpper :=
  LocalizedMomentRepair.bump_tsupport_subset_open _ _ templateLower_lt_upper (subset_closure hx)

theorem logTemplate_contDiff : ContDiff ℝ ∞ logTemplate :=
  radialTemplate_contDiff.comp contDiff_id.exp

theorem logTemplate_support : support logTemplate ⊆ Icc (-1 : ℝ) 1 := by
  intro z hz
  have h := radialTemplate_support (Real.exp z) hz
  change Real.exp (-(3 / 20 : ℝ)) < Real.exp z ∧ Real.exp z < Real.exp (3 / 20 : ℝ) at h
  have hl := Real.exp_lt_exp.mp h.1
  have hu := Real.exp_lt_exp.mp h.2
  constructor <;> linarith

theorem logTemplate_hasCompactSupport : HasCompactSupport logTemplate :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc logTemplate_support

theorem logTemplate_jet_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |iteratedDeriv k logTemplate y| ≤ C :=
  LocalizedMomentRepair.smooth_compact_derivative_bound logTemplate
    logTemplate_contDiff logTemplate_hasCompactSupport k

theorem bump_scale {k : ℝ} (hk : k ≠ 0) (l u x : ℝ) :
    LocalizedMomentRepair.bump (k * l) (k * u) (k * x) =
      LocalizedMomentRepair.bump l u x := by
  unfold LocalizedMomentRepair.bump
  congr 1
  calc
    _ = (k * (x - (l + u) / 2)) / (k * ((u - l) / 4)) := by
      congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ hk

/-- Center, given by `c.pulseLength - if j = 0 then 3 else 1`. -/
noncomputable def center (c : Parameters) (j : Fin 2) : ℝ :=
  c.pulseLength - if j = 0 then 3 else 1

theorem lower_scale (c : Parameters) (j : Fin 2) :
    c.lower j = Real.exp (center c j) * templateLower := by
  change Real.exp (c.pulseLength - if j = 0 then 63 / 20 else 23 / 20) =
    Real.exp (center c j) * Real.exp (-(3 / 20 : ℝ))
  rw [← Real.exp_add]
  apply congrArg Real.exp
  fin_cases j <;> norm_num [center] <;> ring

theorem upper_scale (c : Parameters) (j : Fin 2) :
    c.upper j = Real.exp (center c j) * templateUpper := by
  change Real.exp (c.pulseLength - if j = 0 then 57 / 20 else 17 / 20) =
    Real.exp (center c j) * Real.exp (3 / 20 : ℝ)
  rw [← Real.exp_add]
  apply congrArg Real.exp
  fin_cases j <;> norm_num [center] <;> ring

theorem bump_log_translate (c : Parameters) (j : Fin 2) (y : ℝ) :
    LocalizedMomentRepair.bump (c.lower j) (c.upper j) (Real.exp y) =
      logTemplate (y - center c j) := by
  rw [lower_scale, upper_scale]
  have he : Real.exp y = Real.exp (center c j) * Real.exp (y - center c j) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, bump_scale (Real.exp_ne_zero _)]
  rfl

/-- Template mass, given by `∫ x, radialTemplate x`. -/
noncomputable def templateMass : ℝ := ∫ x, radialTemplate x
/-- Row moment, given by `∫ x, x ^ a * radialTemplate x`. -/
noncomputable def rowMoment (a : ℝ) : ℝ := ∫ x, x ^ a * radialTemplate x
/-- Row floor, given by `Real.exp (-1) * templateMass`. -/
noncomputable def rowFloor : ℝ := Real.exp (-1) * templateMass

theorem templateMass_pos : 0 < templateMass := by
  apply integral_pos_of_integrable_nonneg_nonzero radialTemplate_contDiff.continuous
    (radialTemplate_contDiff.continuous.integrable_of_hasCompactSupport
      radialTemplate_hasCompactSupport) radialTemplate_nonneg
    (x := (templateLower + templateUpper) / 2)
  rw [radialTemplate, LocalizedMomentRepair.bump_at_center]
  norm_num

theorem rowFloor_pos : 0 < rowFloor := mul_pos (Real.exp_pos _) templateMass_pos

theorem rowMoment_integrable (a : ℝ) : Integrable (fun x => x ^ a * radialTemplate x) :=
  LocalizedMomentRepair.integrable_power_mul_bump a _ _ templateLower_pos templateLower_lt_upper

theorem rowMoment_bounds {a : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 0) :
    rowFloor ≤ rowMoment a ∧ rowMoment a ≤ Real.exp 1 * templateMass := by
  have hm : Integrable radialTemplate :=
      radialTemplate_contDiff.continuous.integrable_of_hasCompactSupport
    radialTemplate_hasCompactSupport
  have hp : ∀ x, radialTemplate x ≠ 0 → Real.exp (-1) ≤ x ^ a ∧ x ^ a ≤ Real.exp 1 := by
    intro x hx
    have hs := radialTemplate_support x hx
    have hxpos := templateLower_pos.trans hs.1
    have hl : -(3 / 20 : ℝ) < Real.log x := by
      simpa only [templateLower, Real.log_exp] using Real.log_lt_log templateLower_pos hs.1
    have hu : Real.log x < (3 / 20 : ℝ) := by
      simpa only [templateUpper, Real.log_exp] using Real.log_lt_log hxpos hs.2
    have hab : |a| ≤ 1 := abs_le.mpr ⟨ha, by linarith⟩
    have hlb : |Real.log x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hh : |Real.log x * a| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg a, abs_nonneg (Real.log x)]
    rw [Real.rpow_def_of_pos hxpos]
    exact ⟨Real.exp_le_exp.mpr (abs_le.mp hh).1,
      Real.exp_le_exp.mpr (abs_le.mp hh).2⟩
  constructor
  · have h := integral_mono (hm.const_mul (Real.exp (-1))) (rowMoment_integrable a)
      (fun x => show Real.exp (-1) * radialTemplate x ≤ x ^ a * radialTemplate x from by
        by_cases hx : radialTemplate x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_right (hp x hx).1 (radialTemplate_nonneg x))
    simpa only [integral_const_mul, rowFloor, templateMass, rowMoment] using h
  · have h := integral_mono (rowMoment_integrable a) (hm.const_mul (Real.exp 1))
      (fun x => show x ^ a * radialTemplate x ≤ Real.exp 1 * radialTemplate x from by
        by_cases hx : radialTemplate x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_right (hp x hx).2 (radialTemplate_nonneg x))
    simpa only [integral_const_mul, templateMass, rowMoment] using h

theorem power_bump_integral_scale (a : ℝ) {k l u : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hlu : l < u) :
    (∫ t : ℝ, t ^ a * LocalizedMomentRepair.bump (k * l) (k * u) t) =
      (k * k ^ a) * ∫ t : ℝ, t ^ a * LocalizedMomentRepair.bump l u t := by
  let g := fun t : ℝ => t ^ a * LocalizedMomentRepair.bump (k * l) (k * u) t
  have hcomp : (fun x => g (k * x)) =
      (fun x : ℝ => k ^ a * (x ^ a * LocalizedMomentRepair.bump l u x)) := by
    funext x
    dsimp [g]
    rw [bump_scale hk.ne']
    by_cases hb : LocalizedMomentRepair.bump l u x = 0
    · simp [hb]
    · have hx := LocalizedMomentRepair.bump_tsupport_subset_open l u hlu (subset_closure hb)
      rw [Real.mul_rpow hk.le (hl.trans hx.1).le]
      ring
  have h := Measure.integral_comp_mul_left g k
  rw [hcomp, integral_const_mul, abs_of_pos (inv_pos.mpr hk), smul_eq_mul] at h
  calc
    _ = k * (k⁻¹ * ∫ t, g t) := by rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
    _ = k * (k ^ a * ∫ t : ℝ, t ^ a * LocalizedMomentRepair.bump l u t) := by rw [← h]
    _ = _ := by ring

theorem actual_matrix_entry (c : Parameters) (i j : Fin 2) :
    LocalizedMomentRepair.matrix c.exponents c.lower c.upper i j =
      rowMoment (c.exponents i) * Real.exp (beta c i * center c j) := by
  change (∫ t : ℝ, t ^ c.exponents i * LocalizedMomentRepair.bump (c.lower j) (c.upper j) t) = _
  rw [lower_scale, upper_scale,
    power_bump_integral_scale (c.exponents i) (Real.exp_pos _) templateLower_pos
        templateLower_lt_upper]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
  dsimp [rowMoment, radialTemplate, beta]
  rw [mul_comm]
  congr 2
  ring

/-- The actual moment matrix, with each row normalized at the first center. -/
noncomputable def normalizedMatrix (c : Parameters) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => Real.exp (-(beta c i * center c 0)) *
    LocalizedMomentRepair.matrix c.exponents c.lower c.upper i j

theorem normalizedMatrix_entry (c : Parameters) (i j : Fin 2) :
    normalizedMatrix c i j = rowMoment (c.exponents i) *
      (if j = 0 then 1 else Real.exp (2 * beta c i)) := by
  rw [normalizedMatrix, actual_matrix_entry]
  calc
    _ = rowMoment (c.exponents i) *
        Real.exp (beta c i * (center c j - center c 0)) := by
      rw [show beta c i * (center c j - center c 0) =
        -(beta c i * center c 0) + beta c i * center c j by ring, Real.exp_add]
      ring
    _ = _ := by fin_cases j <;> norm_num [center, mul_comm]

theorem rowMoment_lower (c : Parameters) (i : Fin 2) : rowFloor ≤ rowMoment (c.exponents i) := by
  apply (rowMoment_bounds ?_ ?_).1
  all_goals fin_cases i <;> norm_num [Parameters.exponents] <;> linarith [c.lam_pos, c.lam_lt]

theorem rowMoment_pos (c : Parameters) (i : Fin 2) : 0 < rowMoment (c.exponents i) :=
  rowFloor_pos.trans_le (rowMoment_lower c i)

theorem separation_exponential_bounds (c : Parameters) (i : Fin 2) :
    1 ≤ Real.exp (2 * beta c i) ∧ Real.exp (2 * beta c i) ≤ Real.exp 1 := by
  constructor
  · exact Real.one_le_exp_iff.mpr (by linarith [(beta_bounds c i).1])
  · exact Real.exp_le_exp.mpr (by linarith [(beta_bounds c i).2])

theorem separation_exponential_gap (c : Parameters) :
    2 * c.lam ≤ Real.exp (2 * beta c 0) - Real.exp (2 * beta c 1) := by
  have hid : 2 * beta c 0 = 2 * beta c 1 + 2 * c.lam := by
    norm_num [beta, Parameters.exponents]
    ring
  rw [hid, Real.exp_add]
  have he := Real.add_one_le_exp (2 * c.lam)
  have hb := (separation_exponential_bounds c 1).1
  nlinarith [mul_nonneg (by linarith : 0 ≤ Real.exp (2 * beta c 1) - 1)
    (by linarith [c.lam_pos] : 0 ≤ Real.exp (2 * c.lam) - 1)]

theorem normalizedMatrix_det_ne_zero (c : Parameters) : (normalizedMatrix c).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  simp only [normalizedMatrix_entry]
  norm_num
  have h0 := rowMoment_pos c 0
  have h1 := rowMoment_pos c 1
  have hg := separation_exponential_gap c
  have hgap : Real.exp (2 * beta c 1) - Real.exp (2 * beta c 0) < 0 := by
    linarith [c.lam_pos]
  have hprod := mul_neg_of_pos_of_neg (mul_pos h0 h1) hgap
  nlinarith

/-- A uniform inverse estimate from the actual exponential column separation. -/
noncomputable def inverseBound : ℝ := (1 + Real.exp 1) / rowFloor

theorem inverseBound_pos : 0 < inverseBound := div_pos (by positivity) rowFloor_pos

theorem two_row_solution_bound {k lam A0 A1 r0 r1 x0 x1 d0 d1 : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hlam' : lam ≤ 1)
    (hA0 : k ≤ A0) (hA1 : k ≤ A1)
    (hr0 : 0 ≤ r0) (hr0' : r0 ≤ Real.exp 1)
    (hgap : lam ≤ r0 - r1)
    (h0 : A0 * (x0 + r0 * x1) = d0) (h1 : A1 * (x0 + r1 * x1) = d1) :
    lam * |x0| ≤ ((1 + Real.exp 1) / k) * (|d0| + |d1|) ∧
      lam * |x1| ≤ ((1 + Real.exp 1) / k) * (|d0| + |d1|) := by
  have hA0p := hk.trans_le hA0
  have hA1p := hk.trans_le hA1
  have h0' : x0 + r0 * x1 = d0 / A0 := (eq_div_iff hA0p.ne').mpr (by nlinarith [h0])
  have h1' : x0 + r1 * x1 = d1 / A1 := (eq_div_iff hA1p.ne').mpr (by nlinarith [h1])
  have ha0 : |d0 / A0| ≤ |d0| / k := by
    rw [abs_div, abs_of_pos hA0p]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hk hA0
  have ha1 : |d1 / A1| ≤ |d1| / k := by
    rw [abs_div, abs_of_pos hA1p]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hk hA1
  have hdx : (r0 - r1) * x1 = d0 / A0 - d1 / A1 := by nlinarith [h0', h1']
  have hdiff := abs_sub (d0 / A0) (d1 / A1)
  rw [← hdx, abs_mul, abs_of_pos (hlam.trans_le hgap)] at hdiff
  have hx1 : lam * |x1| ≤ (|d0| + |d1|) / k := by
    have hx := mul_le_mul_of_nonneg_right hgap (abs_nonneg x1)
    rw [add_div]
    linarith
  have hx0eq : x0 = d0 / A0 - r0 * x1 := by linarith [h0']
  have hx0 : |x0| ≤ |d0 / A0| + r0 * |x1| := by
    rw [hx0eq]
    simpa only [abs_mul, abs_of_nonneg hr0] using abs_sub (d0 / A0) (r0 * x1)
  have hd : 0 ≤ (|d0| + |d1|) / k := div_nonneg (by positivity) hk.le
  have he : 0 ≤ Real.exp (1 : ℝ) := (Real.exp_pos _).le
  have h0d : |d0| / k ≤ (|d0| + |d1|) / k :=
    div_le_div_of_nonneg_right (by linarith [abs_nonneg d1]) hk.le
  have hsmall : lam * |d0 / A0| ≤ (|d0| + |d1|) / k := by
    have hmul := mul_le_mul_of_nonneg_right hlam' (abs_nonneg (d0 / A0))
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hx0 hlam.le
  have hrscaled : r0 * (lam * |x1|) ≤ Real.exp 1 * ((|d0| + |d1|) / k) :=
    mul_le_mul hr0' hx1 (mul_nonneg hlam.le (abs_nonneg x1)) he
  have hid : ((1 + Real.exp 1) / k) * (|d0| + |d1|) =
      (|d0| + |d1|) / k + Real.exp 1 * ((|d0| + |d1|) / k) := by ring
  constructor <;> rw [hid]
  · nlinarith
  · nlinarith

theorem normalized_solution_bound (c : Parameters) (x d : Fin 2 → ℝ)
    (h : (normalizedMatrix c).mulVec x = d) (j : Fin 2) :
    c.lam * |x j| ≤ inverseBound * (|d 0| + |d 1|) := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, normalizedMatrix_entry] at h0 h1
  norm_num at h0 h1
  have hb := two_row_solution_bound rowFloor_pos c.lam_pos (by linarith [c.lam_lt])
    (rowMoment_lower c 0) (rowMoment_lower c 1)
    (Real.exp_pos _).le (separation_exponential_bounds c 0).2
    (show c.lam ≤ Real.exp (2 * beta c 0) - Real.exp (2 * beta c 1) by
      linarith [separation_exponential_gap c, c.lam_pos])
    (show rowMoment (c.exponents 0) * (x 0 + Real.exp (2 * beta c 0) * x 1) = d 0 by
      nlinarith [h0])
    (show rowMoment (c.exponents 1) * (x 0 + Real.exp (2 * beta c 1) * x 1) = d 1 by
      nlinarith [h1])
  fin_cases j
  · exact hb.1
  · exact hb.2

theorem normalized_inverse_entry_bound (c : Parameters) (i j : Fin 2) :
    c.lam * |(normalizedMatrix c)⁻¹ i j| ≤ inverseBound := by
  let e : Fin 2 → ℝ := Pi.single j 1
  have h := MomentRepair.matrix_mul_coefficients (normalizedMatrix c)
    (normalizedMatrix_det_ne_zero c) e
  have hb := normalized_solution_bound c _ e h i
  have he : |e 0| + |e 1| = 1 := by fin_cases j <;> norm_num [e, Pi.single_apply]
  rw [he, mul_one] at hb
  have hc : MomentRepair.coefficients (normalizedMatrix c) e i = (normalizedMatrix c)⁻¹ i j := by
    fin_cases j <;> simp [MomentRepair.coefficients, Matrix.mulVec, dotProduct,
      e, Pi.single_apply]
  simpa only [hc] using hb

theorem normalized_inverse_norm_bound (c : Parameters) :
    c.lam * ‖fun i : Fin 2 => fun j : Fin 2 => (normalizedMatrix c)⁻¹ i j‖ ≤ inverseBound := by
  have hb : ‖fun i : Fin 2 => fun j : Fin 2 => c.lam * (normalizedMatrix c)⁻¹ i j‖ ≤
      inverseBound := by
    apply (pi_norm_le_iff_of_nonneg inverseBound_pos.le).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg inverseBound_pos.le).mpr
    intro j
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos c.lam_pos] using
      normalized_inverse_entry_bound c i j
  have he : (fun i : Fin 2 => fun j : Fin 2 => c.lam * (normalizedMatrix c)⁻¹ i j) =
      c.lam • (fun i : Fin 2 => fun j : Fin 2 => (normalizedMatrix c)⁻¹ i j) := rfl
  rwa [he, norm_smul, Real.norm_eq_abs, abs_of_pos c.lam_pos] at hb

/-- Normalized debt, given by `Real.exp (-(beta c i * center c 0)) * d i`. -/
noncomputable def normalizedDebt (c : Parameters) (d : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  Real.exp (-(beta c i * center c 0)) * d i

theorem actual_coefficients_normalized_system (c : Parameters) (d : Fin 2 → ℝ) :
    (normalizedMatrix c).mulVec
        (LocalizedMomentRepair.coefficients c.exponents c.lower c.upper d) =
      normalizedDebt c d := by
  have h := MomentRepair.matrix_mul_coefficients
    (LocalizedMomentRepair.matrix c.exponents c.lower c.upper)
    (LocalizedMomentRepair.matrix_det_ne_zero c.exponents c.lower c.upper
      c.exponents_injective c.lower_pos c.lower_lt_upper c.intervals_separated) d
  ext i
  have hi := congrFun h i
  change (∑ j : Fin 2, (Real.exp (-(beta c i * center c 0)) *
      LocalizedMomentRepair.matrix c.exponents c.lower c.upper i j) *
      LocalizedMomentRepair.coefficients c.exponents c.lower c.upper d j) = _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  exact congrArg (fun x => Real.exp (-(beta c i * center c 0)) * x) hi

theorem actual_coefficients_bound (c : Parameters) (d : Fin 2 → ℝ) (j : Fin 2) :
    c.lam * |LocalizedMomentRepair.coefficients c.exponents c.lower c.upper d j| ≤
      inverseBound * (|normalizedDebt c d 0| + |normalizedDebt c d 1|) :=
  normalized_solution_bound c _ _ (actual_coefficients_normalized_system c d) j

/-! ## Actual normalized debts -/

theorem mainPulse_hasCompactSupport : HasCompactSupport mainPulse := by
  have hs : support mainPulse ⊆ Icc (0 : ℝ) 11 := by
    intro z hz
    constructor
    · by_contra h
      exact hz (mainPulse_zero_left (by linarith))
    · by_contra h
      exact hz (mainPulse_zero_right (by linarith))
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs

theorem exists_mainPulse_bound : ∃ C : ℝ, 0 < C ∧ ∀ z, |mainPulse z| ≤ C := by
  obtain ⟨C, hC, hb⟩ := LocalizedMomentRepair.smooth_compact_derivative_bound mainPulse
    mainPulse_contDiff mainPulse_hasCompactSupport 0
  refine ⟨C + 1, by linarith, fun z => ?_⟩
  have h := hb z
  simpa only [iteratedDeriv_zero] using h.trans (by linarith : C ≤ C + 1)

/-- Main bound, given by `Classical.choose exists_mainPulse_bound`. -/
noncomputable def mainBound : ℝ := Classical.choose exists_mainPulse_bound
theorem mainBound_pos : 0 < mainBound := (Classical.choose_spec exists_mainPulse_bound).1
theorem mainPulse_abs_le (z : ℝ) : |mainPulse z| ≤ mainBound :=
  (Classical.choose_spec exists_mainPulse_bound).2 z

theorem mainMoment_log (c : Parameters) (i : Fin 2) :
    mainMoment c i = ∫ y in (0 : ℝ)..c.pulseLength,
      Real.exp (beta c i * y) * mainPulse (c.lam * y) := by
  have hlog : ContinuousOn Real.log (Ioi (0 : ℝ)) :=
    continuousOn_id.log (fun _ hx => ne_of_gt hx)
  have hR : ContinuousOn (fun x => mainPulse (c.lam * Real.log x)) (Ioi 0) :=
    mainPulse_contDiff.continuous.comp_continuousOn (continuousOn_const.mul hlog)
  have h := exp_weight_substitution hR (c.exponents i) 0 c.pulseLength
  simpa only [mainMoment, beta, zero_add, sub_zero, Real.log_exp] using h.symm

theorem mainMoment_log_short (c : Parameters) (i : Fin 2) :
    mainMoment c i = ∫ y in (0 : ℝ)..11 / c.lam,
      Real.exp (beta c i * y) * mainPulse (c.lam * y) := by
  rw [mainMoment_log]
  apply integral_stops
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (mainPulse_contDiff.continuous.comp (continuous_const.mul continuous_id)))
    (show 11 / c.lam ≤ c.pulseLength by
      exact div_le_div_of_nonneg_right (by norm_num) c.lam_pos.le)
  intro y hy
  have hp : 11 ≤ c.lam * y := by
    have h := (div_le_iff₀ c.lam_pos).mp hy
    nlinarith
  simp only [Pi.mul_apply, Function.comp_apply, id_eq]
  rw [mainPulse_zero_right hp, mul_zero]

theorem center_gap_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120) (i : Fin 2) :
    1 / (2 * c.lam) ≤ beta c i * (center c 0 - 11 / c.lam) := by
  have hb := (beta_small_bounds c hsmall i).1
  have hp : 0 ≤ 2 - 3 * c.lam := by linarith [c.lam_pos]
  have hm := mul_le_mul_of_nonneg_right hb hp
  have hnum : (1 / 2 : ℝ) ≤ beta c i * (2 - 3 * c.lam) := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hnum c.lam_pos.le
  have he : beta c i * (center c 0 - 11 / c.lam) =
      (beta c i * (2 - 3 * c.lam)) / c.lam := by
    simp only [center, Parameters.pulseLength]
    field_simp [c.lam_pos.ne']; ring_nf; simp
  rw [he]
  convert! hdiv using 1; ring

theorem normalized_mainMoment_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120) (i : Fin 2) :
    |Real.exp (-(beta c i * center c 0)) * mainMoment c i| ≤
      (11 * mainBound / c.lam) * Real.exp (-(1 / (2 * c.lam))) := by
  have heq : Real.exp (-(beta c i * center c 0)) * mainMoment c i =
      ∫ y in (0 : ℝ)..11 / c.lam,
        Real.exp (beta c i * (y - center c 0)) * mainPulse (c.lam * y) := by
    rw [mainMoment_log_short, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [show beta c i * (y - center c 0) =
      -(beta c i * center c 0) + beta c i * y by ring, Real.exp_add]
    ring
  rw [heq]
  have hlen : 0 ≤ 11 / c.lam := div_nonneg (by norm_num) c.lam_pos.le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 11 / c.lam)
    (f := fun y => Real.exp (beta c i * (y - center c 0)) * mainPulse (c.lam * y))
    (C := mainBound * Real.exp (-(1 / (2 * c.lam)))) ?_
  · rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hlen] at h
    convert! h using 1; ring
  · intro y hy
    have hy' : y ≤ 11 / c.lam := (uIoc_of_le hlen ▸ hy).2
    have harg : beta c i * (y - center c 0) ≤ -(1 / (2 * c.lam)) := by
      have hb := mul_le_mul_of_nonneg_left hy' (beta_bounds c i).1.le
      linarith [center_gap_bound c hsmall i]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(1 / (2 * c.lam))) * mainBound :=
        mul_le_mul (Real.exp_le_exp.mpr harg) (mainPulse_abs_le _)
          (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring

theorem prefixCoefficient_le_bound (c : Parameters) (i : Fin 2) :
    |prefixCoefficient c i| ≤ prefixBound c.P c.m i := by
  rw [abs_of_nonneg (prefixCoefficient_nonneg c i)]
  have he : Real.exp (-(beta c i * c.wait)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hw : 0 ≤ c.wait := by linarith [c.wait_gt]
    nlinarith [(beta_bounds c i).1]
  exact (prefixCoefficient_decay c i).trans (by
    nlinarith [prefixBound_pos c.P_pos c.m i])

theorem normalized_prefixCoefficient_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (i : Fin 2) :
    |Real.exp (-(beta c i * center c 0)) * prefixCoefficient c i| ≤
      prefixBound c.P c.m i * Real.exp (-(1 / (2 * c.lam))) := by
  have hgap := center_gap_bound c hsmall i
  have hmain : 0 ≤ beta c i * (11 / c.lam) :=
    mul_nonneg (beta_bounds c i).1.le (div_nonneg (by norm_num) c.lam_pos.le)
  have he : Real.exp (-(beta c i * center c 0)) ≤ Real.exp (-(1 / (2 * c.lam))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(1 / (2 * c.lam))) * prefixBound c.P c.m i :=
      mul_le_mul he (prefixCoefficient_le_bound c i) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- Affine debt, given by `-(q * prefixCoefficient c i + A * mainMoment c i)`. -/
noncomputable def affineDebt (c : Parameters) (q A : ℝ) (i : Fin 2) : ℝ :=
  -(q * prefixCoefficient c i + A * mainMoment c i)

/-- Affine coefficients, given by `LocalizedMomentRepair.coefficients c.exponents c.lower
c.upper (affineDebt c q A)`. -/
noncomputable def affineCoefficients (c : Parameters) (q A : ℝ) : Fin 2 → ℝ :=
  LocalizedMomentRepair.coefficients c.exponents c.lower c.upper (affineDebt c q A)

/-- Debt bound, given by `prefixBound P m i + 11 * mainBound`. -/
noncomputable def debtBound (P m : ℝ) (i : Fin 2) : ℝ :=
  prefixBound P m i + 11 * mainBound

theorem debtBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) (i : Fin 2) : 0 < debtBound P m i := by
  have hp := prefixBound_pos hP m i
  have hm := mainBound_pos
  unfold debtBound
  positivity

theorem affineDebt_normalized_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (q A : ℝ) (i : Fin 2) :
    |normalizedDebt c (affineDebt c q A) i| ≤
      (debtBound c.P c.m i / c.lam) * Real.exp (-(1 / (2 * c.lam))) * (|q| + |A|) := by
  have hD0 : prefixBound c.P c.m i ≤ debtBound c.P c.m i / c.lam := by
    apply (le_div_iff₀ c.lam_pos).mpr
    have hp := prefixBound_pos c.P_pos c.m i
    have hm := mainBound_pos
    dsimp [debtBound]
    nlinarith [c.lam_lt]
  have hD1 : 11 * mainBound / c.lam ≤ debtBound c.P c.m i / c.lam := by
    apply div_le_div_of_nonneg_right _ c.lam_pos.le
    have hp := prefixBound_pos c.P_pos c.m i
    dsimp [debtBound]
    linarith
  have hp := (normalized_prefixCoefficient_bound c hsmall i).trans
    (mul_le_mul_of_nonneg_right hD0 (Real.exp_pos _).le)
  have hm := (normalized_mainMoment_bound c hsmall i).trans
    (mul_le_mul_of_nonneg_right hD1 (Real.exp_pos _).le)
  have heq : normalizedDebt c (affineDebt c q A) i =
      -(q * (Real.exp (-(beta c i * center c 0)) * prefixCoefficient c i) +
        A * (Real.exp (-(beta c i * center c 0)) * mainMoment c i)) := by
    unfold normalizedDebt affineDebt
    ring
  rw [heq, abs_neg]
  calc
    _ ≤ |q * (Real.exp (-(beta c i * center c 0)) * prefixCoefficient c i)| +
        |A * (Real.exp (-(beta c i * center c 0)) * mainMoment c i)| := abs_add_le _ _
    _ ≤ |q| * ((debtBound c.P c.m i / c.lam) * Real.exp (-(1 / (2 * c.lam)))) +
        |A| * ((debtBound c.P c.m i / c.lam) * Real.exp (-(1 / (2 * c.lam)))) := by
      simp only [abs_mul] at hp hm ⊢
      exact add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg q))
        (mul_le_mul_of_nonneg_left hm (abs_nonneg A))
    _ = _ := by ring

theorem inverse_square_exp_absorption {lam : ℝ} (hlam : 0 < lam) :
    Real.exp (-(1 / (2 * lam))) / lam ^ 2 ≤ 64 * Real.exp (-(1 / (4 * lam))) := by
  have ht : 0 ≤ 1 / (8 * lam) := by positivity
  have hex : 1 / (8 * lam) ≤ Real.exp (1 / (8 * lam)) := by
    linarith [Real.add_one_le_exp (1 / (8 * lam))]
  have hsq := pow_le_pow_left₀ ht hex 2
  rw [← Real.exp_nat_mul] at hsq
  have hfac : 1 / lam ^ 2 ≤ 64 * Real.exp (1 / (4 * lam)) := by
    apply (div_le_iff₀ (sq_pos_of_pos hlam)).mpr
    have ht' : (1 / (8 * lam)) ^ 2 = 1 / (64 * lam ^ 2) := by ring
    have he' : (2 : ℝ) * (1 / (8 * lam)) = 1 / (4 * lam) := by ring
    norm_num only [Nat.cast_ofNat] at hsq
    rw [ht', he'] at hsq
    have h := (div_le_iff₀ (by positivity : 0 < 64 * lam ^ 2)).mp hsq
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hfac (Real.exp_pos (-(1 / (2 * lam)))).le
  have hsum : 1 / (4 * lam) + -(1 / (2 * lam)) = -(1 / (4 * lam)) := by ring
  calc
    _ = (1 / lam ^ 2) * Real.exp (-(1 / (2 * lam))) := by ring
    _ ≤ _ := hprod
    _ = _ := by rw [mul_assoc, ← Real.exp_add, hsum]

/-- Coefficient bound, given by `64 * inverseBound * (debtBound P m 0 + debtBound P m 1)`. -/
noncomputable def coefficientBound (P m : ℝ) : ℝ :=
  64 * inverseBound * (debtBound P m 0 + debtBound P m 1)

theorem coefficientBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < coefficientBound P m := by
  have h0 := debtBound_pos hP m 0
  have h1 := debtBound_pos hP m 1
  have hi := inverseBound_pos
  unfold coefficientBound
  positivity

theorem affineCoefficients_exp_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (q A : ℝ) (j : Fin 2) :
    |affineCoefficients c q A j| ≤
      coefficientBound c.P c.m * Real.exp (-(1 / (4 * c.lam))) * (|q| + |A|) := by
  have h0 := affineDebt_normalized_bound c hsmall q A 0
  have h1 := affineDebt_normalized_bound c hsmall q A 1
  have hc := actual_coefficients_bound c (affineDebt c q A) j
  change c.lam * |affineCoefficients c q A j| ≤ _ at hc
  have hsum := mul_le_mul_of_nonneg_left (add_le_add h0 h1) inverseBound_pos.le
  have hbase : |affineCoefficients c q A j| ≤
      (inverseBound * (debtBound c.P c.m 0 + debtBound c.P c.m 1)) *
        (Real.exp (-(1 / (2 * c.lam))) / c.lam ^ 2) * (|q| + |A|) := by
    apply (mul_le_mul_iff_right₀ c.lam_pos).mp
    refine hc.trans (hsum.trans_eq ?_)
    field_simp [c.lam_pos.ne']
  have hK : 0 ≤ inverseBound * (debtBound c.P c.m 0 + debtBound c.P c.m 1) :=
    mul_nonneg inverseBound_pos.le (add_nonneg (debtBound_pos c.P_pos c.m 0).le
      (debtBound_pos c.P_pos c.m 1).le)
  calc
    _ ≤ _ := hbase
    _ ≤ (inverseBound * (debtBound c.P c.m 0 + debtBound c.P c.m 1)) *
        (64 * Real.exp (-(1 / (4 * c.lam)))) * (|q| + |A|) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (inverse_square_exp_absorption c.lam_pos) hK)
        (by positivity)
    _ = _ := by unfold coefficientBound; ring

theorem pulse_coefficients_exp_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (amp : ℝ → ℝ) {eta : ℝ} (heta : |eta| ≤ 1) (j : Fin 2) :
    |LocalizedMomentRepair.coefficients c.exponents c.lower c.upper (debt c amp eta) j| ≤
      (2 * coefficientBound c.P c.m) * Real.exp (-(1 / (4 * c.lam))) * (1 + |amp eta|) := by
  have heq : debt c amp eta = affineDebt c (parameterPolynomial eta) (amp eta) := by
    ext i
    unfold debt affineDebt parameterPolynomial
    ring
  rw [heq]
  have h := affineCoefficients_exp_bound c hsmall (parameterPolynomial eta) (amp eta) j
  have hq := parameterPolynomial_bound heta
  have he := Real.exp_pos (-(1 / (4 * c.lam)))
  have hC := coefficientBound_pos c.P_pos c.m
  change |affineCoefficients c (parameterPolynomial eta) (amp eta) j| ≤ _
  refine h.trans ?_
  calc
    _ ≤ (coefficientBound c.P c.m * Real.exp (-(1 / (4 * c.lam)))) *
        (2 * (1 + |amp eta|)) :=
      mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (amp eta)])
        (mul_nonneg hC.le he.le)
    _ = _ := by ring

/-! ## Fixed radial jets and first parameter derivatives -/

theorem affineCoefficients_decomposition (c : Parameters) (q A : ℝ) (j : Fin 2) :
    affineCoefficients c q A j = q * affineCoefficients c 1 0 j +
      A * affineCoefficients c 0 1 j := by
  simp only [affineCoefficients, LocalizedMomentRepair.coefficients, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, affineDebt]
  ring

theorem debt_eq_affine (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    debt c amp eta = affineDebt c (parameterPolynomial eta) (amp eta) := by
  ext i
  unfold debt affineDebt parameterPolynomial
  ring

theorem pulse_coefficients_hasDerivAt (c : Parameters) {amp : ℝ → ℝ}
    {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta) (j : Fin 2) :
    HasDerivAt (fun t => LocalizedMomentRepair.coefficients c.exponents c.lower c.upper
      (debt c amp t) j) (affineCoefficients c (1 + 3 * eta ^ 2) amp' j) eta := by
  have heq : (fun t => LocalizedMomentRepair.coefficients c.exponents c.lower c.upper
      (debt c amp t) j) = (fun t => parameterPolynomial t * affineCoefficients c 1 0 j +
      amp t * affineCoefficients c 0 1 j) := by
    funext t
    rw [debt_eq_affine]
    exact affineCoefficients_decomposition c _ _ j
  rw [heq, affineCoefficients_decomposition c (1 + 3 * eta ^ 2) amp' j]
  exact ((parameterPolynomial_hasDerivAt eta).mul_const _).add (ha.mul_const _)

/-- Affine profile, given by `∑ j : Fin 2, affineCoefficients c q A j * logTemplate (y - center
c j)`. -/
noncomputable def affineProfile (c : Parameters) (q A y : ℝ) : ℝ :=
  ∑ j : Fin 2, affineCoefficients c q A j * logTemplate (y - center c j)

theorem affineProfile_contDiff (c : Parameters) (q A : ℝ) : ContDiff ℝ ∞ (affineProfile c q A) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (logTemplate_contDiff.comp (contDiff_id.sub contDiff_const))

theorem correction_log_eq_affineProfile (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    correction c amp eta (Real.exp y) = affineProfile c (parameterPolynomial eta) (amp eta) y := by
  unfold correction LocalizedMomentRepair.repair affineProfile
  apply Finset.sum_congr rfl
  intro j _
  rw [bump_log_translate, debt_eq_affine]
  rfl

theorem affineProfile_jet_formula (c : Parameters) (q A : ℝ) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (affineProfile c q A) y =
      ∑ j : Fin 2, affineCoefficients c q A j * iteratedDeriv k logTemplate (y - center c j) := by
  unfold affineProfile
  rw [LocalizedMomentRepair.iteratedDeriv_finite_sum Finset.univ
    (fun j x => affineCoefficients c q A j * logTemplate (x - center c j))
    (fun j => contDiff_const.mul (logTemplate_contDiff.comp (contDiff_id.sub contDiff_const)))]
  apply Finset.sum_congr rfl
  intro j _
  have hj : ContDiffAt ℝ k (fun x => logTemplate (x - center c j)) y :=
    ((logTemplate_contDiff.comp (contDiff_id.sub contDiff_const)).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
  rw [iteratedDeriv_const_mul _ hj]
  have heq : (fun x => logTemplate (x - center c j)) =
      (fun x => logTemplate (x + (-center c j))) := by
    funext x
    rw [sub_eq_add_neg]
  rw [heq, iteratedDeriv_comp_add_const]
  rfl

/-- Template jet bound, given by `1 + Classical.choose (logTemplate_jet_bound k)`. -/
noncomputable def templateJetBound (k : ℕ) : ℝ := 1 + Classical.choose (logTemplate_jet_bound k)

theorem templateJetBound_pos (k : ℕ) : 0 < templateJetBound k := by
  have h := (Classical.choose_spec (logTemplate_jet_bound k)).1
  unfold templateJetBound
  linarith

theorem logTemplate_jet_le (k : ℕ) (y : ℝ) : |iteratedDeriv k logTemplate y| ≤ templateJetBound k
    := by
  have h := (Classical.choose_spec (logTemplate_jet_bound k)).2 y
  unfold templateJetBound
  linarith

/-- Correction jet bound, given by `2 * coefficientBound P m * templateJetBound k`. -/
noncomputable def correctionJetBound (P m : ℝ) (k : ℕ) : ℝ :=
  2 * coefficientBound P m * templateJetBound k

theorem correctionJetBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) (k : ℕ) :
    0 < correctionJetBound P m k := by
  have hc := coefficientBound_pos hP m
  have hj := templateJetBound_pos k
  unfold correctionJetBound
  positivity

theorem affineProfile_jet_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (q A : ℝ) (k : ℕ) (y : ℝ) :
    |iteratedDeriv k (affineProfile c q A) y| ≤
      correctionJetBound c.P c.m k * Real.exp (-(1 / (4 * c.lam))) * (|q| + |A|) := by
  rw [affineProfile_jet_formula, Fin.sum_univ_two]
  have hC : 0 ≤ coefficientBound c.P c.m * Real.exp (-(1 / (4 * c.lam))) * (|q| + |A|) :=
    mul_nonneg (mul_nonneg (coefficientBound_pos c.P_pos c.m).le (Real.exp_pos _).le)
      (by positivity)
  have hb : ∀ j : Fin 2,
      |affineCoefficients c q A j * iteratedDeriv k logTemplate (y - center c j)| ≤
        (coefficientBound c.P c.m * Real.exp (-(1 / (4 * c.lam))) * (|q| + |A|)) *
          templateJetBound k := by
    intro j
    rw [abs_mul]
    exact mul_le_mul (affineCoefficients_exp_bound c hsmall q A j)
      (logTemplate_jet_le k _) (abs_nonneg _) hC
  calc
    _ ≤ |affineCoefficients c q A 0 * iteratedDeriv k logTemplate (y - center c 0)| +
        |affineCoefficients c q A 1 * iteratedDeriv k logTemplate (y - center c 1)| := abs_add_le _
            _
    _ ≤ _ := add_le_add (hb 0) (hb 1)
    _ = _ := by unfold correctionJetBound; ring

theorem affineProfile_jet_decomposition (c : Parameters) (q A : ℝ) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (affineProfile c q A) y =
      q * iteratedDeriv k (affineProfile c 1 0) y +
        A * iteratedDeriv k (affineProfile c 0 1) y := by
  rw [affineProfile_jet_formula, affineProfile_jet_formula, affineProfile_jet_formula]
  simp only [Fin.sum_univ_two]
  rw [affineCoefficients_decomposition c q A 0, affineCoefficients_decomposition c q A 1]
  ring

/-- Correction jet, given by `iteratedDeriv k (fun t => correction c amp eta (Real.exp t)) y`. -/
noncomputable def correctionJet (c : Parameters) (amp : ℝ → ℝ) (k : ℕ) (eta y : ℝ) : ℝ :=
  iteratedDeriv k (fun t => correction c amp eta (Real.exp t)) y

theorem correctionJet_eq (c : Parameters) (amp : ℝ → ℝ) (k : ℕ) (eta y : ℝ) :
    correctionJet c amp k eta y =
      iteratedDeriv k (affineProfile c (parameterPolynomial eta) (amp eta)) y := by
  unfold correctionJet
  congr 2
  funext t
  exact correction_log_eq_affineProfile c amp eta t

theorem correctionJet_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (amp : ℝ → ℝ) (k : ℕ) {eta : ℝ} (heta : |eta| ≤ 1) (y : ℝ) :
    |correctionJet c amp k eta y| ≤
      (2 * correctionJetBound c.P c.m k) * Real.exp (-(1 / (4 * c.lam))) * (1 + |amp eta|) := by
  rw [correctionJet_eq]
  refine (affineProfile_jet_bound c hsmall _ _ k y).trans ?_
  have hq := parameterPolynomial_bound heta
  calc
    _ ≤ (correctionJetBound c.P c.m k * Real.exp (-(1 / (4 * c.lam)))) *
        (2 * (1 + |amp eta|)) :=
      mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (amp eta)])
        (mul_nonneg (correctionJetBound_pos c.P_pos c.m k).le (Real.exp_pos _).le)
    _ = _ := by ring

theorem correctionJet_eta_hasDerivAt (c : Parameters) {amp : ℝ → ℝ}
    {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta) (k : ℕ) (y : ℝ) :
    HasDerivAt (fun t => correctionJet c amp k t y)
      (iteratedDeriv k (affineProfile c (1 + 3 * eta ^ 2) amp') y) eta := by
  have heq : (fun t => correctionJet c amp k t y) =
      (fun t => parameterPolynomial t * iteratedDeriv k (affineProfile c 1 0) y +
        amp t * iteratedDeriv k (affineProfile c 0 1) y) := by
    funext t
    rw [correctionJet_eq, affineProfile_jet_decomposition]
  rw [heq, affineProfile_jet_decomposition c (1 + 3 * eta ^ 2) amp' k y]
  exact ((parameterPolynomial_hasDerivAt eta).mul_const _).add (ha.mul_const _)

theorem correctionJet_eta_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta)
    (heta : |eta| ≤ 1) (k : ℕ) (y : ℝ) :
    |deriv (fun t => correctionJet c amp k t y) eta| ≤
      (4 * correctionJetBound c.P c.m k) * Real.exp (-(1 / (4 * c.lam))) * (1 + |amp'|) := by
  rw [(correctionJet_eta_hasDerivAt c ha k y).deriv]
  refine (affineProfile_jet_bound c hsmall _ _ k y).trans ?_
  have hq : |1 + 3 * eta ^ 2| ≤ 4 := by
    simpa only [(parameterPolynomial_hasDerivAt eta).deriv] using
        parameterPolynomial_derivative_bound heta
  calc
    _ ≤ (correctionJetBound c.P c.m k * Real.exp (-(1 / (4 * c.lam)))) *
        (4 * (1 + |amp'|)) :=
      mul_le_mul_of_nonneg_left (by linarith [abs_nonneg amp'])
        (mul_nonneg (correctionJetBound_pos c.P_pos c.m k).le (Real.exp_pos _).le)
    _ = _ := by ring

theorem normalized_mass_prefix_hasDerivAt (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    HasDerivAt (fun t => massMoment c amp t c.pulseStart /
      (Real.exp c.pulseStart * angular c.P c.dropLength c.lam (c.pulseStart, t)))
      (prefixCoefficient c 0 * (1 + 3 * eta ^ 2)) eta := by
  have heq : (fun t => massMoment c amp t c.pulseStart /
      (Real.exp c.pulseStart * angular c.P c.dropLength c.lam (c.pulseStart, t))) =
      (fun t => prefixCoefficient c 0 * parameterPolynomial t) := by
    funext t
    exact normalized_mass_prefix c amp t
  rw [heq]
  exact (parameterPolynomial_hasDerivAt eta).const_mul _

theorem normalized_mass_prefix_derivative_small (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    (amp : ℝ → ℝ) {eta : ℝ} (heta : |eta| ≤ 1) :
    |deriv (fun t => massMoment c amp t c.pulseStart /
        (Real.exp c.pulseStart * angular c.P c.dropLength c.lam (c.pulseStart, t))) eta| ≤
      (4 * prefixBound c.P c.m 0) * c.lam ^ 29 := by
  rw [(normalized_mass_prefix_hasDerivAt c amp eta).deriv, abs_mul]
  have hq : |1 + 3 * eta ^ 2| ≤ 4 := by
    simpa only [(parameterPolynomial_hasDerivAt eta).deriv] using
        parameterPolynomial_derivative_bound heta
  have hb := mul_le_mul (prefixCoefficient_small c hwait hsmall 0) hq
    (abs_nonneg _) (mul_nonneg (prefixBound_pos c.P_pos c.m 0).le (pow_nonneg c.lam_pos.le _))
  nlinarith

theorem individual_correction_jet_formula (c : Parameters) (amp : ℝ → ℝ)
    (eta : ℝ) (j : Fin 2) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (fun t =>
      LocalizedMomentRepair.coefficients c.exponents c.lower c.upper (debt c amp eta) j *
        LocalizedMomentRepair.bump (c.lower j) (c.upper j) (Real.exp t)) y =
      affineCoefficients c (parameterPolynomial eta) (amp eta) j *
        iteratedDeriv k logTemplate (y - center c j) := by
  have heq : (fun t =>
      LocalizedMomentRepair.coefficients c.exponents c.lower c.upper (debt c amp eta) j *
        LocalizedMomentRepair.bump (c.lower j) (c.upper j) (Real.exp t)) =
      (fun t => affineCoefficients c (parameterPolynomial eta) (amp eta) j *
        logTemplate (t - center c j)) := by
    funext t
    rw [bump_log_translate, debt_eq_affine]
    rfl
  rw [heq]
  have hj : ContDiffAt ℝ k (fun t => logTemplate (t - center c j)) y :=
    ((logTemplate_contDiff.comp (contDiff_id.sub contDiff_const)).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
  rw [iteratedDeriv_const_mul _ hj]
  congr 1
  simpa only [sub_eq_add_neg] using
    congrFun (iteratedDeriv_comp_add_const k logTemplate (-center c j)) y

theorem individual_correction_jet_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (amp : ℝ → ℝ) {eta : ℝ} (heta : |eta| ≤ 1) (j : Fin 2) (k : ℕ) (y : ℝ) :
    |iteratedDeriv k (fun t =>
      LocalizedMomentRepair.coefficients c.exponents c.lower c.upper (debt c amp eta) j *
        LocalizedMomentRepair.bump (c.lower j) (c.upper j) (Real.exp t)) y| ≤
      correctionJetBound c.P c.m k * Real.exp (-(1 / (4 * c.lam))) * (1 + |amp eta|) := by
  rw [individual_correction_jet_formula, abs_mul]
  have hc := pulse_coefficients_exp_bound c hsmall amp heta j
  rw [debt_eq_affine] at hc
  change |affineCoefficients c (parameterPolynomial eta) (amp eta) j| ≤ _ at hc
  have hpos : 0 ≤ (2 * coefficientBound c.P c.m) *
      Real.exp (-(1 / (4 * c.lam))) * (1 + |amp eta|) := by
    have hp := coefficientBound_pos c.P_pos c.m
    positivity
  have h := mul_le_mul hc (logTemplate_jet_le k (y - center c j)) (abs_nonneg _) hpos
  refine h.trans_eq ?_
  unfold correctionJetBound
  ring

theorem individual_correction_jet_eta_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta) (heta : |eta| ≤ 1)
    (j : Fin 2) (k : ℕ) (y : ℝ) :
    |deriv (fun s => iteratedDeriv k (fun t =>
      LocalizedMomentRepair.coefficients c.exponents c.lower c.upper (debt c amp s) j *
        LocalizedMomentRepair.bump (c.lower j) (c.upper j) (Real.exp t)) y) eta| ≤
      (2 * correctionJetBound c.P c.m k) * Real.exp (-(1 / (4 * c.lam))) * (1 + |amp'|) := by
  have heq : (fun s => iteratedDeriv k (fun t =>
      LocalizedMomentRepair.coefficients c.exponents c.lower c.upper (debt c amp s) j *
        LocalizedMomentRepair.bump (c.lower j) (c.upper j) (Real.exp t)) y) =
      (fun s => LocalizedMomentRepair.coefficients c.exponents c.lower c.upper (debt c amp s) j *
        iteratedDeriv k logTemplate (y - center c j)) := by
    funext s
    rw [individual_correction_jet_formula, debt_eq_affine]
    rfl
  rw [heq, ((pulse_coefficients_hasDerivAt c ha j).mul_const
    (iteratedDeriv k logTemplate (y - center c j))).deriv, abs_mul]
  have hq : |1 + 3 * eta ^ 2| ≤ 4 := by
    simpa only [(parameterPolynomial_hasDerivAt eta).deriv] using
        parameterPolynomial_derivative_bound heta
  have hc := affineCoefficients_exp_bound c hsmall (1 + 3 * eta ^ 2) amp' j
  have hp : 0 ≤ coefficientBound c.P c.m * Real.exp (-(1 / (4 * c.lam))) *
      (|1 + 3 * eta ^ 2| + |amp'|) := by
    have hP := coefficientBound_pos c.P_pos c.m
    positivity
  have h := mul_le_mul hc (logTemplate_jet_le k (y - center c j)) (abs_nonneg _) hp
  refine h.trans ?_
  have hfac := mul_le_mul_of_nonneg_left
    (show |1 + 3 * eta ^ 2| + |amp'| ≤ 4 * (1 + |amp'|) by linarith [abs_nonneg amp'])
    (mul_nonneg (mul_nonneg (coefficientBound_pos c.P_pos c.m).le
      (Real.exp_pos (-(1 / (4 * c.lam)))).le)
      (templateJetBound_pos k).le)
  unfold correctionJetBound
  convert! hfac using 1 <;> ring

/-- One constant controls the two prefix estimates and the first parameter
derivative for the exact family specified in the manuscript. -/
theorem paper_prefix_bounds (P m : ℝ) (hP : 0 < P) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : ℝ) (hlam : 0 < lam) (hsmall : lam ≤ 1 / 120),
      let c := paperParameters P m lam hP hm hlam (by linarith)
      pulseAmplitude c ≤ C * lam ^ 30 ∧
        ∀ (amp : ℝ → ℝ) (eta : ℝ), |eta| ≤ 1 →
          |massMoment c amp eta c.pulseStart /
            (Real.exp c.pulseStart * angular c.P c.dropLength c.lam (c.pulseStart, eta))| ≤ C * lam
                ^ 29 ∧
          |deriv (fun t => massMoment c amp t c.pulseStart /
            (Real.exp c.pulseStart * angular c.P c.dropLength c.lam (c.pulseStart, t))) eta| ≤ C *
                lam ^ 29 := by
  let C := P * Real.exp (Real.exp m + 12) + 4 * prefixBound P m 0
  have hb := prefixBound_pos hP m 0
  have he : 0 < P * Real.exp (Real.exp m + 12) := mul_pos hP (Real.exp_pos _)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro lam hlam hsmall
  let c := paperParameters P m lam hP hm hlam (by linarith)
  change pulseAmplitude c ≤ C * lam ^ 30 ∧ _
  have hwait : c.wait = 60 * Real.log (1 / c.lam) := rfl
  have hl : c.lam ≤ 1 / 120 := hsmall
  constructor
  · have h := pulseAmplitude_small c hwait
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam.le _)
    dsimp [C, c, paperParameters]
    linarith
  · intro amp eta heta
    constructor
    · refine (normalized_mass_prefix_small c hwait hl amp heta).trans ?_
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam.le _)
      change 2 * prefixBound P m 0 ≤ C
      dsimp [C]
      linarith
    · refine (normalized_mass_prefix_derivative_small c hwait hl amp heta).trans ?_
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam.le _)
      change 4 * prefixBound P m 0 ≤ C
      dsimp [C]
      linarith

/-- For every fixed radial derivative order there is a single constant independent
of `lam`, the amplitude function, the parameter, and the radial coordinate. -/
theorem paper_correction_bounds (P m : ℝ) (hP : 0 < P) (hm : 0 < m) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : ℝ) (hlam : 0 < lam) (hsmall : lam ≤ 1 / 120),
      let c := paperParameters P m lam hP hm hlam (by linarith)
      ∀ (amp : ℝ → ℝ) (eta y : ℝ), |eta| ≤ 1 →
        |correctionJet c amp k eta y| ≤ C * Real.exp (-(1 / (4 * lam))) * (1 + |amp eta|) ∧
        ∀ amp' : ℝ, HasDerivAt amp amp' eta →
          |deriv (fun t => correctionJet c amp k t y) eta| ≤
            C * Real.exp (-(1 / (4 * lam))) * (1 + |amp'|) := by
  refine ⟨4 * correctionJetBound P m k, mul_pos (by norm_num) (correctionJetBound_pos hP m k), ?_⟩
  intro lam hlam hsmall
  let c := paperParameters P m lam hP hm hlam (by linarith)
  dsimp only
  intro amp eta y heta
  constructor
  · have h := correctionJet_bound c hsmall amp k heta y
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    change 2 * correctionJetBound P m k ≤ 4 * correctionJetBound P m k
    linarith [correctionJetBound_pos hP m k]
  · intro amp' ha
    exact correctionJet_eta_bound c hsmall ha heta k y

end NavierStokes.OutgoingPulseBounds
