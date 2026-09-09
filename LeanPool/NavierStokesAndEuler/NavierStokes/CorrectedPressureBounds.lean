/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FuturePressureBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Pressure through the actual angular reset

The corrected pressure is the improper integral of the actual corrected field.
The difference from the clean pressure is an explicit finite partial-reset
integral.  Bounds use the first angular coefficient jet supplied by the proved
reset witness; no parity or second-jet estimate is assumed.
-/

@[expose] public section


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail
open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset
open NavierStokes.FuturePressureBounds

namespace NavierStokes.CorrectedPressureBounds

/-- Corrected pi, given by `-(1 / 2 : ℝ) * ∫ t in Ioi y, correctedAngular d w.coefficients (t,
eta) ^ 2`. -/
noncomputable def correctedPi {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ t in Ioi y, correctedAngular d w.coefficients (t, eta) ^ 2

/-- Edit density, given by `correctedAngular d w.coefficients p ^ 2 - finalAngular d p ^ 2`. -/
noncomputable def editDensity {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (p : ℝ × ℝ) : ℝ :=
  correctedAngular d w.coefficients p ^ 2 - finalAngular d p ^ 2

/-- Release square, given by `finalAngular d (d.releaseStart, 0) ^ 2`. -/
noncomputable def releaseSquare (d : TailData) : ℝ :=
  finalAngular d (d.releaseStart, 0) ^ 2

/-- Edit size, given by `K * d.core.lam ^ (28 : ℕ)`. -/
noncomputable def editSize (d : TailData) (K : ℝ) : ℝ := K * d.core.lam ^ (28 : ℕ)

theorem releaseSquare_pos (d : TailData) : 0 < releaseSquare d :=
  sq_pos_of_pos (finalAngular_pos d _)

theorem editSize_nonneg {d : TailData} {K : ℝ} (w : ResetWitness d K) :
    0 ≤ editSize d K :=
  (norm_nonneg (w.coefficients 0)).trans (w.coefficient_bound 0)

theorem witness_K_nonneg {d : TailData} {K : ℝ} (w : ResetWitness d K) : 0 ≤ K := by
  have he := editSize_nonneg w
  dsimp [editSize] at he
  exact nonneg_of_mul_nonneg_left he (pow_pos d.core.lam_pos 28)

theorem relative_abs_le_two_norm (c : Coeff) (t : ℝ) : |relative c t| ≤ 2 * ‖c‖ := by
  have h0 : |c 0| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 0
  have h1 : |c 1| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 1
  have hb (j : Fin 2) : |bump j t| ≤ 1 := by
    rw [abs_of_nonneg (bump_nonneg j t)]
    exact bump_le_one j t
  calc
    _ ≤ |c 0| * |bump 0 t| + |c 1| * |bump 1 t| := by
      simpa only [relative, abs_mul] using abs_add_le (c 0 * bump 0 t) (c 1 * bump 1 t)
    _ ≤ ‖c‖ * 1 + ‖c‖ * 1 := add_le_add
      (mul_le_mul h0 (hb 0) (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul h1 (hb 1) (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem relative_coefficient_bound {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta t : ℝ) :
    |relative (w.coefficients eta) t| ≤ 2 * editSize d K :=
  (relative_abs_le_two_norm _ _).trans
    (mul_le_mul_of_nonneg_left (w.coefficient_bound eta) (by norm_num))

theorem relative_eta_hasDerivAt {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta t : ℝ) :
    HasDerivAt (fun q => relative (w.coefficients q) t)
      (relative (deriv w.coefficients eta) t) eta := by
  have hc := (w.smooth.differentiable (by simp) eta).hasDerivAt
  simpa only [relative] using
    ((hasDerivAt_pi.mp hc 0).mul_const (bump 0 t)).fun_add
      ((hasDerivAt_pi.mp hc 1).mul_const (bump 1 t))

theorem relative_eta_bound {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta t : ℝ) :
    |relative (deriv w.coefficients eta) t| ≤ 2 * editSize d K :=
  (relative_abs_le_two_norm _ _).trans
    (mul_le_mul_of_nonneg_left (w.eta_derivative_bound eta) (by norm_num))

theorem corrected_square_comparison {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (p : ℝ × ℝ) :
    (1 / 4) * finalAngular d p ^ 2 ≤ correctedAngular d w.coefficients p ^ 2 ∧
      correctedAngular d w.coefficients p ^ 2 ≤ (9 / 4) * finalAngular d p ^ 2 := by
  have hr := abs_le.mp (w.small_jets p.2 (p.1 - correctionCenter d)).1
  have hsq : (1 / 4 : ℝ) ≤ (1 + relative (w.coefficients p.2)
      (p.1 - correctionCenter d)) ^ 2 ∧
      (1 + relative (w.coefficients p.2) (p.1 - correctionCenter d)) ^ 2 ≤ 9 / 4 := by
    constructor <;> nlinarith
  simp only [correctedAngular, mul_pow]
  constructor
  · simpa only [mul_comm (1 / 4 : ℝ)] using
      mul_le_mul_of_nonneg_left hsq.1 (sq_nonneg (finalAngular d p))
  · simpa only [mul_comm (9 / 4 : ℝ)] using
      mul_le_mul_of_nonneg_left hsq.2 (sq_nonneg (finalAngular d p))

theorem baseE_square_ratio (lam amp t r : ℝ) :
    baseE lam amp t ^ 2 = baseE lam amp r ^ 2 * Real.exp ((1 + 2 * lam) * (r - t)) := by
  simp only [baseE, mul_pow, ← Real.exp_nat_mul]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem window_square_bounds (d : TailData) {t : ℝ}
    (ht : t ∈ Icc (d.releaseStart - 4) d.releaseStart) (eta : ℝ) :
    releaseSquare d ≤ finalAngular d (t, eta) ^ 2 ∧
      finalAngular d (t, eta) ^ 2 ≤ Real.exp 5 * releaseSquare d := by
  have hdt : 0 ≤ d.releaseStart - t := sub_nonneg.mpr ht.2
  have hdt4 : d.releaseStart - t ≤ 4 := by linarith [ht.1]
  have h0 : 0 ≤ (1 + 2 * d.core.lam) * (d.releaseStart - t) :=
    mul_nonneg (by linarith [d.core.lam_pos]) hdt
  have h5 : (1 + 2 * d.core.lam) * (d.releaseStart - t) ≤ 5 := by
    have hm := mul_le_mul (show 1 + 2 * d.core.lam ≤ (6 / 5 : ℝ) by linarith [d.core.lam_lt])
      hdt4 hdt (by norm_num)
    linarith
  have htR : d.releaseStart ∈ Icc (d.releaseStart - 4) d.releaseStart := by
    constructor <;> linarith
  rw [original_matches_reference d eta ht, baseE_square_ratio _ _ t d.releaseStart]
  have hR : releaseSquare d = baseE d.core.lam (referenceAmplitude d) d.releaseStart ^ 2 := by
    rw [releaseSquare, original_matches_reference d 0 htR]
  rw [← hR]
  constructor
  · exact le_mul_of_one_le_right (releaseSquare_pos d).le (Real.one_le_exp_iff.mpr h0)
  · simpa only [mul_comm (Real.exp 5)] using
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h5) (releaseSquare_pos d).le

theorem editDensity_contDiff {d : TailData} {K : ℝ} (w : ResetWitness d K) :
    ContDiff ℝ ∞ (editDensity w) :=
  ((correctedAngular_contDiff d w.coefficients w.smooth).pow 2).sub
    ((finalAngular_contDiff d).pow 2)

theorem editDensity_eq {d : TailData} {K : ℝ} (w : ResetWitness d K) (t eta : ℝ) :
    editDensity w (t, eta) = baseE d.core.lam (referenceAmplitude d) t ^ 2 *
      ((1 + relative (w.coefficients eta) (t - correctionCenter d)) ^ 2 - 1) := by
  rw [editDensity, corrected_pressure_reference]
  unfold modifiedE
  ring

theorem editDensity_zero_outside {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta : ℝ) {t : ℝ}
    (ht : t ∉ Ioo (d.releaseStart - 4) d.releaseStart) : editDensity w (t, eta) = 0 := by
  rw [editDensity, correctedAngular_unchanged d w.coefficients eta ht, sub_self]

/-- Edit density eta, constructed using `2`. -/
noncomputable def editDensityEta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (p : ℝ × ℝ) : ℝ :=
  2 * baseE d.core.lam (referenceAmplitude d) p.1 ^ 2 *
    (1 + relative (w.coefficients p.2) (p.1 - correctionCenter d)) *
    relative (deriv w.coefficients p.2) (p.1 - correctionCenter d)

theorem editDensity_hasDerivAt_eta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (t eta : ℝ) :
    HasDerivAt (fun q => editDensity w (t, q)) (editDensityEta w (t, eta)) eta := by
  have heq : (fun q => editDensity w (t, q)) = fun q =>
      baseE d.core.lam (referenceAmplitude d) t ^ 2 *
        ((1 + relative (w.coefficients q) (t - correctionCenter d)) ^ 2 - 1) :=
    funext (editDensity_eq w t)
  rw [heq]
  convert! ((((relative_eta_hasDerivAt w eta (t - correctionCenter d)).const_add 1).pow
      2).sub_const 1).const_mul
    (baseE d.core.lam (referenceAmplitude d) t ^ 2) using 1
  dsimp [editDensityEta]
  ring

theorem editDensityEta_zero_outside {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta : ℝ) {t : ℝ}
    (ht : t ∉ Ioo (d.releaseStart - 4) d.releaseStart) : editDensityEta w (t, eta) = 0 := by
  simp only [editDensityEta, relative_zero_outside d _ ht, mul_zero]

theorem editDensityEta_continuous_t {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta : ℝ) : Continuous (fun t => editDensityEta w (t, eta)) := by
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_const.mul (((baseE_contDiff _ _).continuous).pow 2)
    · exact continuous_const.add ((relative_contDiff (w.coefficients eta)).continuous.comp
        (continuous_id.sub continuous_const))
  · exact (relative_contDiff (deriv w.coefficients eta)).continuous.comp
      (continuous_id.sub continuous_const)

theorem editDensity_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (t eta : ℝ) :
    |editDensity w (t, eta)| ≤ 5 * editSize d K * Real.exp 5 * releaseSquare d := by
  have hR := releaseSquare_pos d
  by_cases ht : t ∈ Ioo (d.releaseStart - 4) d.releaseStart
  · have hs := (w.small_jets eta (t - correctionCenter d)).1
    have hr := relative_coefficient_bound w eta (t - correctionCenter d)
    have hsize := editSize_nonneg w
    have hprod : |(1 + relative (w.coefficients eta) (t - correctionCenter d)) ^ 2 - 1| ≤
        5 * editSize d K := by
      rw [show (1 + relative (w.coefficients eta) (t - correctionCenter d)) ^ 2 - 1 =
        relative (w.coefficients eta) (t - correctionCenter d) *
          (2 + relative (w.coefficients eta) (t - correctionCenter d)) by ring, abs_mul]
      have ha : |2 + relative (w.coefficients eta) (t - correctionCenter d)| ≤ 5 / 2 := by
        have h := abs_add_le (2 : ℝ) (relative (w.coefficients eta) (t - correctionCenter d))
        norm_num at h
        linarith
      have hh := mul_le_mul hr ha (abs_nonneg _) (by positivity : 0 ≤ 2 * editSize d K)
      nlinarith
    rw [editDensity_eq, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hbase : baseE d.core.lam (referenceAmplitude d) t ^ 2 ≤ Real.exp 5 * releaseSquare d := by
      rw [← original_matches_reference d eta ⟨ht.1.le, ht.2.le⟩]
      exact (window_square_bounds d ⟨ht.1.le, ht.2.le⟩ eta).2
    have hb := mul_le_mul hbase hprod (abs_nonneg _) (by
        positivity : 0 ≤ Real.exp 5 * releaseSquare d)
    nlinarith
  · rw [editDensity_zero_outside w eta ht, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (editSize_nonneg w))
      (Real.exp_pos _).le) (releaseSquare_pos d).le

theorem editDensityEta_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (t eta : ℝ) :
    |editDensityEta w (t, eta)| ≤ 6 * editSize d K * Real.exp 5 * releaseSquare d := by
  have hR := releaseSquare_pos d
  by_cases ht : t ∈ Ioo (d.releaseStart - 4) d.releaseStart
  · have hs := (w.small_jets eta (t - correctionCenter d)).1
    have hr := relative_eta_bound w eta (t - correctionCenter d)
    have hsize := editSize_nonneg w
    have ha : |1 + relative (w.coefficients eta) (t - correctionCenter d)| ≤ 3 / 2 := by
      have h := abs_add_le (1 : ℝ) (relative (w.coefficients eta) (t - correctionCenter d))
      norm_num at h
      linarith
    have hbase : baseE d.core.lam (referenceAmplitude d) t ^ 2 ≤ Real.exp 5 * releaseSquare d := by
      rw [← original_matches_reference d eta ⟨ht.1.le, ht.2.le⟩]
      exact (window_square_bounds d ⟨ht.1.le, ht.2.le⟩ eta).2
    rw [editDensityEta, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg (baseE d.core.lam (referenceAmplitude d) t))]
    norm_num
    have h1 := mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ 2 by norm_num)
    have h2 := mul_le_mul h1 ha (abs_nonneg _) (by
        positivity : 0 ≤ 2 * (Real.exp 5 * releaseSquare d))
    have h3 := mul_le_mul h2 hr (abs_nonneg _)
      (by positivity : 0 ≤ 2 * (Real.exp 5 * releaseSquare d) * (3 / 2))
    nlinarith
  · rw [editDensityEta_zero_outside w eta ht, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (editSize_nonneg w))
      (Real.exp_pos _).le) (releaseSquare_pos d).le

theorem integral_Ioi_increment {f : ℝ → ℝ} (hf : Integrable f) (a y : ℝ) :
    (∫ t in Ioi y, f t) = (∫ t in Ioi a, f t) - ∫ t in a..y, f t := by
  have ha := intervalIntegral.integral_Iic_add_Ioi (b := a) hf.integrableOn hf.integrableOn
  have hy := intervalIntegral.integral_Iic_add_Ioi (b := y) hf.integrableOn hf.integrableOn
  have hd := intervalIntegral.integral_Iic_sub_Iic (a := a) (b := y)
    hf.integrableOn hf.integrableOn
  linarith

theorem correctedPi_increment {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (a y eta : ℝ) :
    correctedPi w y eta = correctedPi w a eta +
      (1 / 2) * ∫ t in a..y, correctedAngular d w.coefficients (t, eta) ^ 2 := by
  rw [correctedPi, integral_Ioi_increment (corrected_square_integrable w eta) a y,
    correctedPi]
  ring

theorem correctedPi_eq_before {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : y ≤ d.releaseStart - 4) (eta : ℝ) :
    correctedPi w y eta = Pi d y eta := corrected_future_pressure_eq w hy eta

theorem correctedPi_eq_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta : ℝ) :
    correctedPi w y eta = Pi d y eta := by
  unfold correctedPi Pi
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [correctedAngular_unchanged d w.coefficients eta]
  intro hmem
  exact (not_lt_of_ge (hy.trans ht.le)) hmem.2

theorem correctedPi_eq_partial {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    correctedPi w y eta = Pi d y eta +
      (1 / 2) * ∫ t in (d.releaseStart - 4)..y, editDensity w (t, eta) := by
  have hn : IntervalIntegrable (fun t => correctedAngular d w.coefficients (t, eta) ^ 2)
      volume (d.releaseStart - 4) y :=
    (corrected_square_integrable w eta).intervalIntegrable
  have ho : IntervalIntegrable (fun t => finalAngular d (t, eta) ^ 2)
      volume (d.releaseStart - 4) y :=
    (SchedulePressure.angular_square_integrable d eta).intervalIntegrable
  rw [correctedPi_increment w (d.releaseStart - 4) y eta,
    correctedPi_eq_before w le_rfl eta, Pi_increment d (d.releaseStart - 4) y eta]
  simp only [editDensity]
  rw [intervalIntegral.integral_sub hn ho]
  ring

/-- Pressure change, given by `correctedPi w y eta - Pi d y eta`. -/
noncomputable def pressureChange {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) : ℝ := correctedPi w y eta - Pi d y eta

theorem pressureChange_eq_partial {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    pressureChange w y eta = (1 / 2) * ∫ t in (d.releaseStart - 4)..y, editDensity w (t, eta) := by
  rw [pressureChange, correctedPi_eq_partial]
  ring

theorem pressureChange_zero_before {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : y ≤ d.releaseStart - 4) (eta : ℝ) :
    pressureChange w y eta = 0 := by rw [pressureChange, correctedPi_eq_before w hy, sub_self]

theorem pressureChange_zero_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta : ℝ) :
    pressureChange w y eta = 0 := by rw [pressureChange, correctedPi_eq_after w hy, sub_self]

/-- Joint smoothness of a finite integral with a variable upper limit. -/
theorem intervalPrimitive_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => ∫ t in a..p.1, f (t, p.2)) := by
  let g : (ℝ × ℝ) × ℝ → ℝ := fun z => f (a + (z.1.1 - a) * z.2, z.1.2)
  have hg : ContDiff ℝ ∞ g := hf.comp
    ((contDiff_const.add ((contDiff_fst.fst.sub contDiff_const).mul contDiff_snd)).prodMk
      contDiff_fst.snd)
  have heq : (fun p : ℝ × ℝ => ∫ t in a..p.1, f (t, p.2)) =
      fun p : ℝ × ℝ => (p.1 - a) * ∫ u in (0 : ℝ)..1, g (p, u) := by
    funext p
    have h := intervalIntegral.smul_integral_comp_mul_add
      (f := fun t => f (t, p.2)) (a := (0 : ℝ)) (b := 1) (p.1 - a) a
    simpa [g, smul_eq_mul, add_comm] using h.symm
  rw [heq]
  exact (contDiff_fst.sub contDiff_const).mul
    (TransportPrimitive.parameterIntegral_contDiff hg 0 1)

theorem cleanPi_joint_contDiff (d : TailData) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => Pi d p.1 p.2) := by
  have heq : (fun p : ℝ × ℝ => Pi d p.1 p.2) = fun p : ℝ × ℝ =>
      Pi d 0 p.2 + (1 / 2) * ∫ t in (0 : ℝ)..p.1, finalAngular d (t, p.2) ^ 2 := by
    funext p
    exact Pi_increment d 0 p.1 p.2
  rw [heq]
  exact ((Pi_contDiff_eta d 0).comp contDiff_snd).add
    (contDiff_const.mul (intervalPrimitive_contDiff ((finalAngular_contDiff d).pow 2) 0))

theorem pressureChange_joint_contDiff {d : TailData} {K : ℝ} (w : ResetWitness d K) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => pressureChange w p.1 p.2) := by
  have heq : (fun p : ℝ × ℝ => pressureChange w p.1 p.2) = fun p : ℝ × ℝ =>
      (1 / 2) * ∫ t in (d.releaseStart - 4)..p.1, editDensity w (t, p.2) := by
    funext p
    exact pressureChange_eq_partial w p.1 p.2
  rw [heq]
  exact contDiff_const.mul (intervalPrimitive_contDiff (editDensity_contDiff w) _)

theorem correctedPi_joint_contDiff {d : TailData} {K : ℝ} (w : ResetWitness d K) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => correctedPi w p.1 p.2) := by
  convert! (cleanPi_joint_contDiff d).add (pressureChange_joint_contDiff w) using 1
  funext p
  simp [pressureChange]

theorem correctedPi_hasDerivAt_y {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    HasDerivAt (fun t => correctedPi w t eta)
      ((1 / 2) * correctedAngular d w.coefficients (y, eta) ^ 2) y := by
  have hc : Continuous (fun t => correctedAngular d w.coefficients (t, eta) ^ 2) :=
    (((correctedAngular_contDiff d w.coefficients w.smooth).continuous.comp
      (continuous_id.prodMk continuous_const)).pow 2)
  have heq : (fun t => correctedPi w t eta) = fun t => correctedPi w 0 eta +
      (1 / 2) * primitive (fun v => correctedAngular d w.coefficients (v, eta) ^ 2) t := by
    funext t
    exact correctedPi_increment w 0 t eta
  rw [heq]
  exact ((primitive_hasDerivAt hc y).const_mul (1 / 2)).const_add _

theorem pressureChange_hasDerivAt_eta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    HasDerivAt (pressureChange w y)
      ((1 / 2) * ∫ t in (d.releaseStart - 4)..y, editDensityEta w (t, eta)) eta := by
  have hc (q : ℝ) : Continuous (fun t => editDensity w (t, q)) :=
    (editDensity_contDiff w).continuous.comp (continuous_id.prodMk continuous_const)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun q t => editDensity w (t, q)) (F' := fun q t => editDensityEta w (t, q))
    (x₀ := eta) (μ := volume) (a := d.releaseStart - 4) (b := y)
    (bound := fun _ => 6 * editSize d K * Real.exp 5 * releaseSquare d)
    (Metric.ball_mem_nhds eta (show (0 : ℝ) < 1 by norm_num))
    (Eventually.of_forall fun q => (hc q).aestronglyMeasurable)
    ((hc eta).intervalIntegrable _ _)
    ((editDensityEta_continuous_t w eta).aestronglyMeasurable)
    (Eventually.of_forall fun t _ q _ => by
      simpa only [Real.norm_eq_abs] using editDensityEta_abs_le w t q)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ q _ => editDensity_hasDerivAt_eta w t q)
  have heq : pressureChange w y = fun q =>
      (1 / 2) * ∫ t in (d.releaseStart - 4)..y, editDensity w (t, q) :=
    funext (pressureChange_eq_partial w y)
  rw [heq]
  exact h.2.const_mul (1 / 2)

theorem correctedPi_hasDerivAt_eta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    HasDerivAt (correctedPi w y)
      (deriv (Pi d y) eta + (1 / 2) *
        ∫ t in (d.releaseStart - 4)..y, editDensityEta w (t, eta)) eta := by
  have heq : correctedPi w y = fun q => Pi d y q + pressureChange w y q := by
    funext q
    simp [pressureChange]
  rw [heq]
  exact ((Pi_contDiff_eta d y).differentiable (by simp) eta).hasDerivAt.add
    (pressureChange_hasDerivAt_eta w y eta)

theorem correctedPi_deriv_eta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    deriv (correctedPi w y) eta = deriv (Pi d y) eta + deriv (pressureChange w y) eta := by
  rw [(correctedPi_hasDerivAt_eta w y eta).deriv,
    (pressureChange_hasDerivAt_eta w y eta).deriv]

theorem pressureChange_deriv_zero_before {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : y ≤ d.releaseStart - 4) (eta : ℝ) :
    deriv (pressureChange w y) eta = 0 := by
  have heq : pressureChange w y = fun _ => 0 := funext (pressureChange_zero_before w hy)
  rw [heq]
  simp

theorem pressureChange_deriv_zero_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta : ℝ) :
    deriv (pressureChange w y) eta = 0 := by
  have heq : pressureChange w y = fun _ => 0 := funext (pressureChange_zero_after w hy)
  rw [heq]
  simp

theorem cleanPi_eta_independent_after_flatten (d : TailData) {y : ℝ}
    (hy : d.flattenEnd ≤ y) (eta eta' : ℝ) : Pi d y eta = Pi d y eta' := by
  unfold Pi
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [finalAngular_eta_independent d eta eta' (hy.trans ht.le)]

theorem correctedPi_eta_independent_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta eta' : ℝ) :
    correctedPi w y eta = correctedPi w y eta' := by
  rw [correctedPi_eq_after w hy, correctedPi_eq_after w hy]
  exact cleanPi_eta_independent_after_flatten d ((releaseStart_gt_flattenEnd d).le.trans hy) _ _

theorem correctedPi_deriv_eta_zero_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta : ℝ) :
    deriv (correctedPi w y) eta = 0 := by
  have heq : correctedPi w y = fun _ => correctedPi w y 0 :=
    funext (fun q => correctedPi_eta_independent_after w hy q 0)
  rw [heq]
  simp

theorem half_partial_integral_abs_le {f : ℝ → ℝ} {B r y : ℝ}
    (hB : 0 ≤ B) (hy : y ∈ Icc (r - 4) r) (hbound : ∀ t, |f t| ≤ B) :
    |(1 / 2 : ℝ) * ∫ t in (r - 4)..y, f t| ≤ 2 * B := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := r - 4) (b := y) (f := f)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t)
  have hlen : |y - (r - 4)| ≤ 4 := by
    rw [abs_of_nonneg (by linarith [hy.1])]
    linarith [hy.2]
  rw [Real.norm_eq_abs] at hi
  rw [abs_mul]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left hlen hB]

theorem pressureChange_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    |pressureChange w y eta| ≤ 10 * editSize d K * Real.exp 5 * releaseSquare d := by
  have hsize := editSize_nonneg w
  have hR := releaseSquare_pos d
  by_cases hl : y ≤ d.releaseStart - 4
  · rw [pressureChange_zero_before w hl, abs_zero]
    positivity
  by_cases hr : d.releaseStart ≤ y
  · rw [pressureChange_zero_after w hr, abs_zero]
    positivity
  rw [pressureChange_eq_partial]
  have h := half_partial_integral_abs_le
    (B := 5 * editSize d K * Real.exp 5 * releaseSquare d)
    (by positivity) ⟨(le_of_not_ge hl), (le_of_not_ge hr)⟩
    (fun t => editDensity_abs_le w t eta)
  convert! h using 1
  ring

theorem pressureChange_deriv_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    |deriv (pressureChange w y) eta| ≤
      12 * editSize d K * Real.exp 5 * releaseSquare d := by
  have hsize := editSize_nonneg w
  have hR := releaseSquare_pos d
  by_cases hl : y ≤ d.releaseStart - 4
  · rw [pressureChange_deriv_zero_before w hl, abs_zero]
    positivity
  by_cases hr : d.releaseStart ≤ y
  · rw [pressureChange_deriv_zero_after w hr, abs_zero]
    positivity
  rw [(pressureChange_hasDerivAt_eta w y eta).deriv]
  have h := half_partial_integral_abs_le
    (B := 6 * editSize d K * Real.exp 5 * releaseSquare d)
    (by positivity) ⟨(le_of_not_ge hl), (le_of_not_ge hr)⟩
    (fun t => editDensityEta_abs_le w t eta)
  convert! h using 1
  ring

theorem clean_square_le_corrected {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (p : ℝ × ℝ) :
    finalAngular d p ^ 2 ≤ 4 * correctedAngular d w.coefficients p ^ 2 := by
  linarith [(corrected_square_comparison w p).1]

/-- The edit derivative is controlled by the actual local corrected field. -/
theorem pressureChange_deriv_abs_le_corrected {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    |deriv (pressureChange w y) eta| ≤
      (48 * Real.exp 5 * editSize d K) * correctedAngular d w.coefficients (y, eta) ^ 2 := by
  have hsize := editSize_nonneg w
  by_cases hl : y ≤ d.releaseStart - 4
  · rw [pressureChange_deriv_zero_before w hl, abs_zero]
    positivity
  by_cases hr : d.releaseStart ≤ y
  · rw [pressureChange_deriv_zero_after w hr, abs_zero]
    positivity
  have hR : releaseSquare d ≤ 4 * correctedAngular d w.coefficients (y, eta) ^ 2 :=
    ((window_square_bounds d ⟨le_of_not_ge hl, le_of_not_ge hr⟩ eta).1).trans
      (clean_square_le_corrected w _)
  apply (pressureChange_deriv_abs_le w y eta).trans
  have h := mul_le_mul_of_nonneg_left hR
    (show 0 ≤ 12 * editSize d K * Real.exp 5 by positivity)
  convert! h using 1
  ring

theorem correctedPi_nonpos {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) : correctedPi w y eta ≤ 0 := by
  unfold correctedPi
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)

theorem correctedPi_abs_eq {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    |correctedPi w y eta| = (1 / 2) *
      ∫ t in Ioi y, correctedAngular d w.coefficients (t, eta) ^ 2 := by
  rw [abs_of_nonpos (correctedPi_nonpos w y eta)]
  unfold correctedPi
  ring

theorem correctedPi_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y eta : ℝ} (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |correctedPi w y eta| ≤ ((9 / 2) * envelopeConstant) *
      correctedAngular d w.coefficients (y, eta) ^ 2 := by
  have hi : (∫ t in Ioi y, correctedAngular d w.coefficients (t, eta) ^ 2) ≤
      (9 / 4) * ∫ t in Ioi y, finalAngular d (t, eta) ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (corrected_square_integrable w eta).integrableOn
      ((SchedulePressure.angular_square_integrable d eta).const_mul (9 / 4)).integrableOn
      measurableSet_Ioi (fun t _ => (corrected_square_comparison w (t, eta)).2)
  have hI := hi.trans (mul_le_mul_of_nonneg_left (future_square_integral_le d hy heta)
    (show (0 : ℝ) ≤ 9 / 4 by norm_num))
  have he := mul_le_mul_of_nonneg_left (clean_square_le_corrected w (y, eta))
    envelopeConstant_pos.le
  have hI' := hI.trans (mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 9 / 4 by norm_num))
  rw [correctedPi_abs_eq]
  have h := mul_le_mul_of_nonneg_left hI' (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert! h using 1
  ring

theorem correctedPi_deriv_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y eta : ℝ} (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |deriv (correctedPi w y) eta| ≤
      (8 * envelopeConstant * |eta| + 48 * Real.exp 5 * editSize d K) *
        correctedAngular d w.coefficients (y, eta) ^ 2 := by
  have hc : |deriv (Pi d y) eta| ≤ (8 * envelopeConstant * |eta|) *
      correctedAngular d w.coefficients (y, eta) ^ 2 := by
    apply (Pi_deriv_abs_le d hy heta).trans
    have h := mul_le_mul_of_nonneg_left (clean_square_le_corrected w (y, eta))
      (show 0 ≤ (2 * envelopeConstant) * |eta| by
        exact mul_nonneg (mul_nonneg (by norm_num) envelopeConstant_pos.le) (abs_nonneg eta))
    convert! h using 1
    ring
  rw [correctedPi_deriv_eta]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ (8 * envelopeConstant * |eta|) * correctedAngular d w.coefficients (y, eta) ^ 2 +
        (48 * Real.exp 5 * editSize d K) * correctedAngular d w.coefficients (y, eta) ^ 2 :=
      add_le_add hc (pressureChange_deriv_abs_le_corrected w y eta)
    _ = _ := by ring

/-- Corrected constant, given by `13 * envelopeConstant + 48 * Real.exp 5`. -/
noncomputable def correctedConstant : ℝ := 13 * envelopeConstant + 48 * Real.exp 5

theorem correctedConstant_pos : 0 < correctedConstant := by
  have h := envelopeConstant_pos
  unfold correctedConstant
  positivity

theorem corrected_bounds {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y eta : ℝ} (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |correctedPi w y eta| ≤ correctedConstant * (1 + editSize d K) *
      correctedAngular d w.coefficients (y, eta) ^ 2 ∧
    |deriv (correctedPi w y) eta| ≤ correctedConstant * (1 + editSize d K) *
      correctedAngular d w.coefficients (y, eta) ^ 2 := by
  have hsize := editSize_nonneg w
  have hM := envelopeConstant_pos
  have he := Real.exp_pos (5 : ℝ)
  have hfirst : (9 / 2 : ℝ) * envelopeConstant ≤ correctedConstant * (1 + editSize d K) := by
    unfold correctedConstant
    nlinarith [mul_nonneg hM.le hsize, mul_nonneg he.le hsize]
  have hderiv : 8 * envelopeConstant * |eta| + 48 * Real.exp 5 * editSize d K ≤
      correctedConstant * (1 + editSize d K) := by
    have hη := mul_le_mul_of_nonneg_left heta (show 0 ≤ 8 * envelopeConstant by positivity)
    unfold correctedConstant
    nlinarith [mul_nonneg hM.le hsize]
  exact ⟨(correctedPi_abs_le w hy heta).trans
      (mul_le_mul_of_nonneg_right hfirst (sq_nonneg _)),
    (correctedPi_deriv_abs_le w hy heta).trans
      (mul_le_mul_of_nonneg_right hderiv (sq_nonneg _))⟩

theorem corrected_bounds_of_small {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (hsmall : editSize d K ≤ 1) {y eta : ℝ}
    (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |correctedPi w y eta| ≤ correctedConstant * correctedAngular d w.coefficients (y, eta) ^ 2 ∧
    |deriv (correctedPi w y) eta| ≤ correctedConstant * correctedAngular d w.coefficients (y, eta)
        ^ 2 := by
  have hM := envelopeConstant_pos
  have he := Real.exp_pos (5 : ℝ)
  have hfirst : (9 / 2 : ℝ) * envelopeConstant ≤ correctedConstant := by
    unfold correctedConstant
    nlinarith
  have hderiv : 8 * envelopeConstant * |eta| + 48 * Real.exp 5 * editSize d K ≤
      correctedConstant := by
    have hη := mul_le_mul_of_nonneg_left heta (show 0 ≤ 8 * envelopeConstant by positivity)
    have hs := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 48 * Real.exp 5 by positivity)
    unfold correctedConstant
    nlinarith
  exact ⟨(correctedPi_abs_le w hy heta).trans
      (mul_le_mul_of_nonneg_right hfirst (sq_nonneg _)),
    (correctedPi_deriv_abs_le w hy heta).trans
      (mul_le_mul_of_nonneg_right hderiv (sq_nonneg _))⟩

/-- The smallness condition follows from an explicit threshold depending only on K. -/
theorem exists_editSize_small_threshold (K : ℝ) (hK : 0 ≤ K) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.lam < lam0 → editSize d K ≤ 1 := by
  refine ⟨1 / (K + 1), by positivity, ?_⟩
  intro d hd
  have hLamOne : d.core.lam ≤ 1 := by linarith [d.core.lam_lt]
  have hp : d.core.lam ^ 28 ≤ d.core.lam := by
    rw [show (28 : ℕ) = 27 + 1 by rfl, pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (n := 27) d.core.lam_pos.le hLamOne) d.core.lam_pos.le
  have hprod : d.core.lam * (K + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < K + 1)).mp hd.le
  have h := mul_le_mul_of_nonneg_left hp hK
  unfold editSize
  nlinarith [d.core.lam_pos]

theorem releaseSquare_le_core_endpoint (d : TailData) {eta : ℝ} (heta : |eta| ≤ 1) :
    releaseSquare d ≤ (4 * Real.exp (6 / 5)) * finalAngular d (d.core.endpoint, eta) ^ 2 := by
  have hER : d.core.endpoint ≤ d.releaseStart :=
    ((flattenEnd_gt_core d).trans (releaseStart_gt_flattenEnd d)).le
  have hclock := clock_future_bound d (SchedulePressure.endpoint_pos d).le hER
  have hexp : Real.exp (-(4 / 5) * (d.releaseStart - d.core.endpoint)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hER)
  change SchedulePressure.clockWeight d d.releaseStart ≤ _
  calc
    _ ≤ SchedulePressure.clockWeight d d.core.endpoint * Real.exp (6 / 5) :=
      hclock.trans (mul_le_of_le_one_right
        (mul_nonneg (SchedulePressure.clockWeight_pos d _).le (Real.exp_pos _).le) hexp)
    _ ≤ (4 * finalAngular d (d.core.endpoint, eta) ^ 2) * Real.exp (6 / 5) :=
      mul_le_mul_of_nonneg_right (clock_le_four_angular_square d _ heta) (Real.exp_pos _).le
    _ = _ := by ring

theorem pressureChange_core_endpoint_bounds {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y : ℝ) {eta : ℝ} (heta : |eta| ≤ 1) :
    |pressureChange w y eta| ≤
      (40 * Real.exp 5 * Real.exp (6 / 5) * editSize d K) *
        finalAngular d (d.core.endpoint, eta) ^ 2 ∧
    |deriv (pressureChange w y) eta| ≤
      (48 * Real.exp 5 * Real.exp (6 / 5) * editSize d K) *
        finalAngular d (d.core.endpoint, eta) ^ 2 := by
  have hsize := editSize_nonneg w
  constructor
  · apply (pressureChange_abs_le w y eta).trans
    have h := mul_le_mul_of_nonneg_left (releaseSquare_le_core_endpoint d heta)
      (show 0 ≤ 10 * editSize d K * Real.exp 5 by positivity)
    convert! h using 1
    ring
  · apply (pressureChange_deriv_abs_le w y eta).trans
    have h := mul_le_mul_of_nonneg_left (releaseSquare_le_core_endpoint d heta)
      (show 0 ≤ 12 * editSize d K * Real.exp 5 by positivity)
    convert! h using 1
    ring

/-- Canonical forward pressure with the unchanged whole-axis pressure datum. -/
theorem correctedPi_eq_axisPressure_add {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    correctedPi w y eta = SchedulePressure.axisPressure d eta + (1 / 2) *
      ∫ t in Iic y, correctedAngular d w.coefficients (t, eta) ^ 2 := by
  have hi := corrected_square_integrable w eta
  have hz := w.pressure_neutral eta
  rw [integral_sub hi (SchedulePressure.angular_square_integrable d eta)] at hz
  have hsum := intervalIntegral.integral_Iic_add_Ioi (b := y) hi.integrableOn hi.integrableOn
  unfold correctedPi SchedulePressure.axisPressure
  linarith

theorem pressureChange_hasDerivAt_y {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    HasDerivAt (fun t => pressureChange w t eta) ((1 / 2) * editDensity w (y, eta)) y := by
  convert! (correctedPi_hasDerivAt_y w y eta).sub (Pi_hasDerivAt_y d y eta) using 1
  dsimp [editDensity]
  ring

end NavierStokes.CorrectedPressureBounds
