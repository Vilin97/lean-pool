/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformAngularReset
public import LeanPool.NavierStokesAndEuler.NavierStokes.TailEnergyBounds

@[expose] public section

/-!
# Actual energy cost of the scheduled angular reset

Pressure neutrality has no extra factor `exp y`. This file instead integrates
the actual energy difference, proves its parameter regularity, and uses the
constructed reset's small coefficients to bound that difference.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail
open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset
open NavierStokes.TailEnergyBounds

namespace NavierStokes.ResetEnergyBounds

theorem relative_abs_le_two_norm (c : Coeff) (y : ℝ) : |relative c y| ≤ 2 * ‖c‖ := by
  have hc0 : |c 0| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 0
  have hc1 : |c 1| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 1
  have hb0 : |bump 0 y| ≤ 1 := by
    rw [abs_of_nonneg (bump_nonneg 0 y)]
    exact bump_le_one 0 y
  have hb1 : |bump 1 y| ≤ 1 := by
    rw [abs_of_nonneg (bump_nonneg 1 y)]
    exact bump_le_one 1 y
  calc
    _ ≤ |c 0| * |bump 0 y| + |c 1| * |bump 1 y| := by
      simpa only [relative, abs_mul] using abs_add_le (c 0 * bump 0 y) (c 1 * bump 1 y)
    _ ≤ ‖c‖ * 1 + ‖c‖ * 1 := add_le_add
      (mul_le_mul hc0 hb0 (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul hc1 hb1 (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem relative_coeff_hasDerivAt {c : ℝ → Coeff} {c' : Coeff} {eta : ℝ}
    (hc : HasDerivAt c c' eta) (u : ℝ) :
    HasDerivAt (fun q => relative (c q) u) (relative c' u) eta := by
  exact ((hasDerivAt_pi.mp hc 0).mul_const (bump 0 u)).add
    ((hasDerivAt_pi.mp hc 1).mul_const (bump 1 u))

noncomputable def resetDensity (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) : ℝ :=
  Real.exp y * ((correctedAngular d c (y, eta)) ^ 2 - (finalAngular d (y, eta)) ^ 2)

theorem resetDensity_eq (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) :
    resetDensity d c eta y = energyDensity d eta y *
      ((1 + relative (c eta) (y - correctionCenter d)) ^ 2 - 1) := by
  dsimp [resetDensity, correctedAngular, energyDensity]
  ring

theorem resetDensity_reference (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) :
    resetDensity d c eta y = Real.exp y * (baseE d.core.lam (referenceAmplitude d) y) ^ 2 *
      ((1 + relative (c eta) (y - correctionCenter d)) ^ 2 - 1) := by
  unfold resetDensity
  rw [corrected_pressure_reference]
  dsimp [modifiedE]
  ring

theorem resetDensity_zero (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : y ∉ Ioo (d.releaseStart - 4) d.releaseStart) : resetDensity d c eta y = 0 := by
  simp [resetDensity, correctedAngular_unchanged d c eta hy]

theorem resetDensity_support (d : TailData) (c : ℝ → Coeff) (eta : ℝ) :
    support (resetDensity d c eta) ⊆ Icc (d.releaseStart - 4) d.releaseStart := by
  intro y hy
  have hm : y ∈ Ioo (d.releaseStart - 4) d.releaseStart := by
    by_contra hn
    exact hy (resetDensity_zero d c eta hn)
  exact ⟨hm.1.le, hm.2.le⟩

theorem resetDensity_contDiff (d : TailData) {c : ℝ → Coeff} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (Function.uncurry (resetDensity d c)) :=
  contDiff_snd.exp.mul
    ((((correctedAngular_contDiff d c hc).comp (contDiff_snd.prodMk contDiff_fst)).pow 2).sub
      (((finalAngular_contDiff d).comp (contDiff_snd.prodMk contDiff_fst)).pow 2))

theorem resetDensity_continuous (d : TailData) (c : ℝ → Coeff) (eta : ℝ) :
    Continuous (resetDensity d c eta) := by
  have he : resetDensity d c eta = fun y =>
      Real.exp y * (baseE d.core.lam (referenceAmplitude d) y) ^ 2 *
        ((1 + relative (c eta) (y - correctionCenter d)) ^ 2 - 1) :=
    funext (resetDensity_reference d c eta)
  rw [he]
  exact (Real.continuous_exp.mul ((baseE_contDiff _ _).continuous.pow 2)).mul
    (((continuous_const.add ((relative_contDiff _).continuous.comp
      (continuous_id.sub continuous_const))).pow 2).sub continuous_const)

theorem resetDensity_integrable (d : TailData) (c : ℝ → Coeff) (eta : ℝ) :
    Integrable (resetDensity d c eta) :=
  (resetDensity_continuous d c eta).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (resetDensity_support d c eta))

noncomputable def resetEnergy (d : TailData) (c : ℝ → Coeff) (eta : ℝ) : ℝ :=
  ∫ y, resetDensity d c eta y

theorem resetEnergy_eq_interval (d : TailData) (c : ℝ → Coeff) (eta : ℝ) :
    resetEnergy d c eta = ∫ y in (d.releaseStart - 4)..d.releaseStart, resetDensity d c eta y := by
  rw [intervalIntegral.integral_of_le (by linarith : d.releaseStart - 4 ≤ d.releaseStart)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  apply resetDensity_zero d c eta
  exact fun hm => hy ⟨hm.1, hm.2.le⟩

theorem resetEnergy_contDiff (d : TailData) {c : ℝ → Coeff} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (resetEnergy d c) := by
  have he : resetEnergy d c = (fun eta =>
      ∫ y in (d.releaseStart - 4)..d.releaseStart, resetDensity d c eta y) :=
    funext (resetEnergy_eq_interval d c)
  rw [he]
  exact compact_integral_contDiff (resetDensity d c) _ _ (by linarith) (resetDensity_contDiff d hc)

noncomputable def resetDensityEta (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) : ℝ :=
  Real.exp y * (baseE d.core.lam (referenceAmplitude d) y) ^ 2 *
    (2 * (1 + relative (c eta) (y - correctionCenter d)) *
      relative (deriv c eta) (y - correctionCenter d))

theorem resetDensity_hasDerivAt (d : TailData) {c : ℝ → Coeff}
    (hc : ContDiff ℝ ∞ c) (eta y : ℝ) :
    HasDerivAt (fun q => resetDensity d c q y) (resetDensityEta d c eta y) eta := by
  have hr := relative_coeff_hasDerivAt ((hc.differentiable (by simp) eta).hasDerivAt)
    (y - correctionCenter d)
  have hd := (((hr.const_add 1).pow 2).sub_const 1).const_mul
    (Real.exp y * (baseE d.core.lam (referenceAmplitude d) y) ^ 2)
  have he : (fun q => resetDensity d c q y) = (fun q =>
      Real.exp y * (baseE d.core.lam (referenceAmplitude d) y) ^ 2 *
        ((1 + relative (c q) (y - correctionCenter d)) ^ 2 - 1)) :=
    funext (fun q => resetDensity_reference d c q y)
  rw [he]
  convert! hd using 1
  simp [resetDensityEta]

theorem resetDensityEta_joint_continuous (d : TailData) {c : ℝ → Coeff}
    (hc : ContDiff ℝ ∞ c) : Continuous (Function.uncurry (resetDensityEta d c)) := by
  have hdc : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  exact ((Real.continuous_exp.comp continuous_snd).mul
    (((baseE_contDiff _ _).continuous.comp continuous_snd).pow 2)).mul
    ((continuous_const.mul (continuous_const.add
      (relative_joint_contDiff.continuous.comp
        ((hc.continuous.comp continuous_fst).prodMk (continuous_snd.sub continuous_const))))).mul
      (relative_joint_contDiff.continuous.comp
        ((hdc.continuous.comp continuous_fst).prodMk (continuous_snd.sub continuous_const))))

theorem resetEnergy_hasDerivAt (d : TailData) {c : ℝ → Coeff}
    (hc : ContDiff ℝ ∞ c) (eta : ℝ) :
    HasDerivAt (resetEnergy d c)
      (∫ y in (d.releaseStart - 4)..d.releaseStart, resetDensityEta d c eta y) eta := by
  have hD := resetDensityEta_joint_continuous d hc
  obtain ⟨C, hC⟩ := ((isCompact_closedBall eta 1).prod
    (isCompact_uIcc : IsCompact (uIcc (d.releaseStart - 4)
      d.releaseStart))).exists_bound_of_continuousOn
      hD.continuousOn
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := resetDensity d c) (F' := resetDensityEta d c)
    (bound := fun _ => C) (Metric.ball_mem_nhds eta (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun q => (resetDensity_continuous d c q).aestronglyMeasurable)
    ((resetDensity_continuous d c eta).intervalIntegrable _ _)
    (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun y hy q hq => hC (q, y)
      ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hq).le, uIoc_subset_uIcc hy⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun y _ q _ => resetDensity_hasDerivAt d hc q y)).2
  have he : resetEnergy d c = (fun q =>
      ∫ y in (d.releaseStart - 4)..d.releaseStart, resetDensity d c q y) :=
    funext (resetEnergy_eq_interval d c)
  rw [he]
  exact hd

section Bounds

variable {d : TailData} {K : ℝ} (w : ResetWitness d K)

include w in
theorem coefficient_scale_nonneg : 0 ≤ K * d.core.lam ^ (28 : ℕ) :=
  (norm_nonneg (w.coefficients 0)).trans (w.coefficient_bound 0)

theorem relative_bound (eta y : ℝ) :
    |relative (w.coefficients eta) y| ≤ 2 * (K * d.core.lam ^ (28 : ℕ)) :=
  (relative_abs_le_two_norm _ _).trans
    (mul_le_mul_of_nonneg_left (w.coefficient_bound eta) (by norm_num))

theorem relative_eta_bound (eta y : ℝ) :
    |relative (deriv w.coefficients eta) y| ≤ 2 * (K * d.core.lam ^ (28 : ℕ)) :=
  (relative_abs_le_two_norm _ _).trans
    (mul_le_mul_of_nonneg_left (w.eta_derivative_bound eta) (by norm_num))

theorem resetDensity_abs_le (eta : ℝ) (heta : eta ^ 2 ≤ 1) {y : ℝ}
    (hy : y ∈ Icc (d.releaseStart - 4) d.releaseStart) :
    |resetDensity d w.coefficients eta y| ≤
      6 * (K * d.core.lam ^ (28 : ℕ)) * energyDensity d eta d.core.endpoint := by
  let r := relative (w.coefficients eta) (y - correctionCenter d)
  have hr : |r| ≤ 1 / 2 := (w.small_jets eta _).1
  have hr' : |r| ≤ 2 * (K * d.core.lam ^ (28 : ℕ)) := relative_bound w eta _
  have h2 : |2 + r| ≤ 3 := by
    have := abs_add_le (2 : ℝ) r
    norm_num at this
    linarith
  have hq : |(1 + r) ^ 2 - 1| ≤ 6 * (K * d.core.lam ^ (28 : ℕ)) := by
    rw [show (1 + r) ^ 2 - 1 = r * (2 + r) by ring, abs_mul]
    have h := mul_le_mul_of_nonneg_left h2 (abs_nonneg r)
    nlinarith
  have hS : d.core.endpoint ≤ y :=
    (flattenEnd_gt_core d).le.trans ((last_four_after_flatten d).le.trans hy.1)
  have hE := energyDensity_prefix_le d eta heta hS hy.2
  rw [resetDensity_eq, abs_mul, abs_of_pos (energyDensity_pos d eta y)]
  change energyDensity d eta y * |(1 + r) ^ 2 - 1| ≤ _
  have h := mul_le_mul hE hq (abs_nonneg _) (energyDensity_pos d eta d.core.endpoint).le
  nlinarith

theorem resetDensityEta_abs_le (eta : ℝ) (heta : eta ^ 2 ≤ 1) {y : ℝ}
    (hy : y ∈ Icc (d.releaseStart - 4) d.releaseStart) :
    |resetDensityEta d w.coefficients eta y| ≤
      6 * (K * d.core.lam ^ (28 : ℕ)) * energyDensity d eta d.core.endpoint := by
  let r := relative (w.coefficients eta) (y - correctionCenter d)
  let r' := relative (deriv w.coefficients eta) (y - correctionCenter d)
  have hr : |r| ≤ 1 / 2 := (w.small_jets eta _).1
  have hr' : |r'| ≤ 2 * (K * d.core.lam ^ (28 : ℕ)) := relative_eta_bound w eta _
  have h1 : 2 * |1 + r| ≤ 3 := by
    have := abs_add_le (1 : ℝ) r
    norm_num at this
    linarith
  have hq : |2 * (1 + r) * r'| ≤ 6 * (K * d.core.lam ^ (28 : ℕ)) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := mul_le_mul_of_nonneg_right h1 (abs_nonneg r')
    nlinarith
  have hS : d.core.endpoint ≤ y :=
    (flattenEnd_gt_core d).le.trans ((last_four_after_flatten d).le.trans hy.1)
  have hE := energyDensity_prefix_le d eta heta hS hy.2
  have hid : resetDensityEta d w.coefficients eta y = energyDensity d eta y * (2 * (1 + r) * r') :=
    by
    dsimp [resetDensityEta, energyDensity, r, r']
    rw [original_matches_reference d eta hy]
  rw [hid, abs_mul, abs_of_pos (energyDensity_pos d eta y)]
  have h := mul_le_mul hE hq (abs_nonneg _) (energyDensity_pos d eta d.core.endpoint).le
  nlinarith

theorem resetEnergy_abs_le (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    |resetEnergy d w.coefficients eta| ≤
      24 * (K * d.core.lam ^ (28 : ℕ)) * energyDensity d eta d.core.endpoint := by
  rw [resetEnergy_eq_interval]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := resetDensity d w.coefficients eta)
    (C := 6 * (K * d.core.lam ^ (28 : ℕ)) * energyDensity d eta d.core.endpoint)
    (fun y (hy : y ∈ uIoc (d.releaseStart - 4) d.releaseStart) => by
      have hy' := uIoc_of_le (show d.releaseStart - 4 ≤ d.releaseStart by linarith) ▸ hy
      simpa only [Real.norm_eq_abs] using resetDensity_abs_le w eta heta ⟨hy'.1.le, hy'.2⟩)
  rw [Real.norm_eq_abs, show d.releaseStart - (d.releaseStart - 4) = 4 by ring] at h
  norm_num at h
  nlinarith

theorem resetEnergy_deriv_abs_le (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    |deriv (resetEnergy d w.coefficients) eta| ≤
      24 * (K * d.core.lam ^ (28 : ℕ)) * energyDensity d eta d.core.endpoint := by
  rw [(resetEnergy_hasDerivAt d w.smooth eta).deriv]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := resetDensityEta d w.coefficients eta)
    (C := 6 * (K * d.core.lam ^ (28 : ℕ)) * energyDensity d eta d.core.endpoint)
    (fun y (hy : y ∈ uIoc (d.releaseStart - 4) d.releaseStart) => by
      have hy' := uIoc_of_le (show d.releaseStart - 4 ≤ d.releaseStart by linarith) ▸ hy
      simpa only [Real.norm_eq_abs] using resetDensityEta_abs_le w eta heta ⟨hy'.1.le, hy'.2⟩)
  rw [Real.norm_eq_abs, show d.releaseStart - (d.releaseStart - 4) = 4 by ring] at h
  norm_num at h
  nlinarith

end Bounds

/-! ## Relation to the actual corrected post-pulse energy -/

theorem corrected_energy_eq (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) :
    Real.exp y * correctedAngular d c (y, eta) ^ 2 =
      energyDensity d eta y + resetDensity d c eta y := by
  dsimp [energyDensity, resetDensity]
  ring

theorem corrected_energy_integrable_postPulse (d : TailData) (c : ℝ → Coeff) (eta : ℝ) :
    IntegrableOn (fun y => Real.exp y * correctedAngular d c (y, eta) ^ 2) (Ioi d.core.endpoint) :=
      by
  have he : (fun y => Real.exp y * correctedAngular d c (y, eta) ^ 2) =
      (fun y => energyDensity d eta y + resetDensity d c eta y) :=
    funext (corrected_energy_eq d c eta)
  rw [he]
  exact (energyDensity_integrable_postPulse d eta).add (resetDensity_integrable d c
    eta).integrableOn

theorem integral_corrected_energy (d : TailData) (c : ℝ → Coeff) (eta : ℝ) :
    (∫ y in Ioi d.core.endpoint, Real.exp y * correctedAngular d c (y, eta) ^ 2) =
      postPulseEnergy d eta + resetEnergy d c eta := by
  have he : (fun y => Real.exp y * correctedAngular d c (y, eta) ^ 2) =
      (fun y => energyDensity d eta y + resetDensity d c eta y) :=
    funext (corrected_energy_eq d c eta)
  rw [he, integral_add (energyDensity_integrable_postPulse d eta)
    (resetDensity_integrable d c eta).integrableOn]
  change postPulseEnergy d eta + _ = _
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  apply resetDensity_zero d c eta
  intro hw
  apply hy
  exact ((flattenEnd_gt_core d).trans (last_four_after_flatten d)).trans hw.1

theorem corrected_energy_contDiff (d : TailData) {c : ℝ → Coeff} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun eta =>
      ∫ y in Ioi d.core.endpoint, Real.exp y * correctedAngular d c (y, eta) ^ 2) := by
  have he : (fun eta =>
      ∫ y in Ioi d.core.endpoint, Real.exp y * correctedAngular d c (y, eta) ^ 2) =
      (fun eta => postPulseEnergy d eta + resetEnergy d c eta) :=
    funext (integral_corrected_energy d c)
  rw [he]
  exact (postPulseEnergy_contDiff d).add (resetEnergy_contDiff d hc)

/-! ## Full normalization, including its parameter derivative -/

noncomputable def pulseNormalization (d : TailData) : ℝ :=
  Real.exp d.core.pulseStart * pulseAmplitude d.core ^ 2

theorem pulseNormalization_pos (d : TailData) : 0 < pulseNormalization d :=
  mul_pos (Real.exp_pos _) (sq_pos_of_pos (pulseAmplitude_pos d.core))

noncomputable def normalizedResetEnergy (d : TailData) (c : ℝ → Coeff) (eta : ℝ) : ℝ :=
  d.core.lam * resetEnergy d c eta / (pulseNormalization d * shape eta ^ 2)

theorem normalizedResetEnergy_eq (d : TailData) (c : ℝ → Coeff) (eta : ℝ) :
    normalizedResetEnergy d c eta = (d.core.lam / pulseNormalization d) *
      resetEnergy d c eta * (1 + eta ^ 2) ^ 2 := by
  have hp : 1 + eta ^ 2 ≠ 0 := by positivity
  simp only [normalizedResetEnergy, shape]
  field_simp [hp]

theorem normalizedResetEnergy_contDiff (d : TailData) {c : ℝ → Coeff}
    (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (normalizedResetEnergy d c) := by
  have he : normalizedResetEnergy d c = (fun eta => (d.core.lam / pulseNormalization d) *
      resetEnergy d c eta * (1 + eta ^ 2) ^ 2) :=
    funext (normalizedResetEnergy_eq d c)
  rw [he]
  exact (contDiff_const.mul (resetEnergy_contDiff d hc)).mul
    ((contDiff_const.add (contDiff_id.pow 2)).pow 2)

theorem normalizedResetEnergy_hasDerivAt (d : TailData) {c : ℝ → Coeff}
    (hc : ContDiff ℝ ∞ c) (eta : ℝ) :
    HasDerivAt (normalizedResetEnergy d c)
      (d.core.lam * deriv (resetEnergy d c) eta / (pulseNormalization d * shape eta ^ 2) +
        (4 * eta / (1 + eta ^ 2)) * normalizedResetEnergy d c eta) eta := by
  have hE := ((resetEnergy_contDiff d hc).differentiable (by simp) eta).hasDerivAt
  have hp : HasDerivAt (fun q : ℝ => (1 + q ^ 2) ^ 2) (4 * eta * (1 + eta ^ 2)) eta := by
    convert! (((hasDerivAt_id eta).fun_pow 2).const_add 1).fun_pow 2 using 1
    simp only [id_eq]
    ring
  have hd := (hE.const_mul (d.core.lam / pulseNormalization d)).mul hp
  have he : normalizedResetEnergy d c = (fun eta => (d.core.lam / pulseNormalization d) *
      resetEnergy d c eta * (1 + eta ^ 2) ^ 2) := funext (normalizedResetEnergy_eq d c)
  rw [he]
  convert! hd using 1
  have hp0 : 1 + eta ^ 2 ≠ 0 := by positivity
  have hN := (pulseNormalization_pos d).ne'
  simp only [shape]
  field_simp [hp0, hN]

section NormalizedBounds

variable {d : TailData} {K : ℝ} (w : ResetWitness d K)

theorem normalizedResetEnergy_abs_le (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    |normalizedResetEnergy d w.coefficients eta| ≤ 24 * K * d.core.lam ^ (29 : ℕ) := by
  have hden : 0 < pulseNormalization d * shape eta ^ 2 :=
    mul_pos (pulseNormalization_pos d) (sq_pos_of_pos (shape_pos eta))
  rw [normalizedResetEnergy, abs_div, abs_mul, abs_of_pos d.core.lam_pos, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have hb := (resetEnergy_abs_le w eta heta).trans
    (mul_le_mul_of_nonneg_left (energyDensity_endpoint_le d eta)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (coefficient_scale_nonneg w)))
  have h := mul_le_mul_of_nonneg_left hb d.core.lam_pos.le
  dsimp [pulseNormalization]
  convert! h using 1
  ring

theorem normalized_resetEnergy_deriv_abs_le (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    d.core.lam * |deriv (resetEnergy d w.coefficients) eta| /
      (pulseNormalization d * shape eta ^ 2) ≤ 24 * K * d.core.lam ^ (29 : ℕ) := by
  have hden : 0 < pulseNormalization d * shape eta ^ 2 :=
    mul_pos (pulseNormalization_pos d) (sq_pos_of_pos (shape_pos eta))
  apply (div_le_iff₀ hden).mpr
  have hb := (resetEnergy_deriv_abs_le w eta heta).trans
    (mul_le_mul_of_nonneg_left (energyDensity_endpoint_le d eta)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (coefficient_scale_nonneg w)))
  have h := mul_le_mul_of_nonneg_left hb d.core.lam_pos.le
  dsimp [pulseNormalization]
  convert! h using 1
  ring

theorem normalizedResetEnergy_deriv_abs_le (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    |deriv (normalizedResetEnergy d w.coefficients) eta| ≤ 72 * K * d.core.lam ^ (29 : ℕ) := by
  have hden : 0 < pulseNormalization d * shape eta ^ 2 :=
    mul_pos (pulseNormalization_pos d) (sq_pos_of_pos (shape_pos eta))
  have hcoef : |4 * eta / (1 + eta ^ 2)| ≤ 2 := by
    rw [show 4 * eta / (1 + eta ^ 2) = 2 * (2 * eta / (1 + eta ^ 2)) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [logShape_deriv_bound eta]
  have hfirst : |d.core.lam * deriv (resetEnergy d w.coefficients) eta /
      (pulseNormalization d * shape eta ^ 2)| ≤ 24 * K * d.core.lam ^ (29 : ℕ) := by
    simpa only [abs_div, abs_mul, abs_of_pos d.core.lam_pos, abs_of_pos hden] using
      normalized_resetEnergy_deriv_abs_le w eta heta
  have hsecond : |(4 * eta / (1 + eta ^ 2)) * normalizedResetEnergy d w.coefficients eta| ≤
      2 * (24 * K * d.core.lam ^ (29 : ℕ)) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (normalizedResetEnergy_abs_le w eta heta) (by norm_num))
  rw [(normalizedResetEnergy_hasDerivAt d w.smooth eta).deriv]
  calc
    _ ≤ |d.core.lam * deriv (resetEnergy d w.coefficients) eta /
          (pulseNormalization d * shape eta ^ 2)| +
        |(4 * eta / (1 + eta ^ 2)) * normalizedResetEnergy d w.coefficients eta| := abs_add_le _ _
    _ ≤ (24 * K * d.core.lam ^ (29 : ℕ)) + 2 * (24 * K * d.core.lam ^ (29 : ℕ)) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

end NormalizedBounds

/-- The outgoing schedule supplies the actual correction and all bounds.
There is no separate smallness assumption on a chosen correction. -/
theorem exists_scheduled_reset_energy_bounds :
    ∃ lam0 K C : ℝ, 0 < lam0 ∧ 0 < K ∧ 0 < C ∧
      ∀ d : TailData, d.core.lam < lam0 → ∃ w : ResetWitness d K,
        ContDiff ℝ ∞ (normalizedResetEnergy d w.coefficients) ∧
        ∀ eta : ℝ, eta ^ 2 ≤ 1 →
          |normalizedResetEnergy d w.coefficients eta| ≤ C * d.core.lam ^ (29 : ℕ) ∧
          |deriv (normalizedResetEnergy d w.coefficients) eta| ≤ C * d.core.lam ^ (29 : ℕ) := by
  obtain ⟨lam0, K, hlam0, hK, hreset⟩ := exists_scheduled_reset
  refine ⟨lam0, K, 72 * K, hlam0, hK, mul_pos (by norm_num) hK, ?_⟩
  intro d hd
  obtain ⟨w⟩ := hreset d hd
  refine ⟨w, normalizedResetEnergy_contDiff d w.smooth, ?_⟩
  intro eta heta
  constructor
  · have h := normalizedResetEnergy_abs_le w eta heta
    have hp := pow_nonneg d.core.lam_pos.le (29 : ℕ)
    nlinarith [mul_nonneg hK.le hp]
  · exact normalizedResetEnergy_deriv_abs_le w eta heta

/-- The constructed reset has arbitrarily small normalized energy and first
parameter derivative when the common parameter `lam` is sufficiently small. -/
theorem exists_scheduled_reset_small_energy (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ lam0 K : ℝ, 0 < lam0 ∧ 0 < K ∧
      ∀ d : TailData, d.core.lam < lam0 → ∃ w : ResetWitness d K,
        ContDiff ℝ ∞ (normalizedResetEnergy d w.coefficients) ∧
        ∀ eta : ℝ, eta ^ 2 ≤ 1 →
          |normalizedResetEnergy d w.coefficients eta| < epsilon ∧
          |deriv (normalizedResetEnergy d w.coefficients) eta| < epsilon := by
  obtain ⟨lam0, K, C, hlam0, hK, hC, hreset⟩ := exists_scheduled_reset_energy_bounds
  refine ⟨min lam0 (epsilon / C), K, lt_min hlam0 (div_pos hepsilon hC), hK, ?_⟩
  intro d hd
  obtain ⟨w, hw, hbounds⟩ := hreset d (lt_of_lt_of_le hd (min_le_left _ _))
  have hpow : d.core.lam ^ (29 : ℕ) ≤ d.core.lam := by
    have hp : d.core.lam ^ (28 : ℕ) ≤ 1 :=
      pow_le_one₀ d.core.lam_pos.le (by linarith [d.core.lam_lt])
    have h := mul_le_mul_of_nonneg_left hp d.core.lam_pos.le
    calc
      _ = d.core.lam * d.core.lam ^ (28 : ℕ) := by ring
      _ ≤ _ := by simpa using h
  have hlim : C * d.core.lam ^ (29 : ℕ) < epsilon := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow hC.le)
    have hsmall := (lt_div_iff₀ hC).mp (lt_of_lt_of_le hd (min_le_right _ _))
    nlinarith
  exact ⟨w, hw, fun eta heta =>
    ⟨(hbounds eta heta).1.trans_lt hlim, (hbounds eta heta).2.trans_lt hlim⟩⟩

end NavierStokes.ResetEnergyBounds
