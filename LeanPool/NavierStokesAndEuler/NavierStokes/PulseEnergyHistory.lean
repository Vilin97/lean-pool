/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingHistories
public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseLag

@[expose] public section

/-!
# Actual outgoing energy histories during the pulse

The history and its parameter derivative retain the actual incoming prefix.
Bounds come from their source integrals and the explicit pulse energy weight.
-/

namespace NavierStokes.PulseEnergyHistory

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open OutgoingSchedule OutgoingTail UniformAngularReset OutgoingHistories

variable {d : TailData} {K : ℝ}

noncomputable def pulseNormalization (c : Parameters) (eta : ℝ) : ℝ :=
  PulseAmplitude.normalization c * shape eta ^ 2

theorem pulseNormalization_pos (c : Parameters) (eta : ℝ) :
    0 < pulseNormalization c eta :=
  mul_pos (PulseAmplitude.normalization_pos c) (sq_pos_of_pos (shape_pos eta))

theorem pulse_time_le_endpoint (c : Parameters) {y : ℝ} (hy : y ≤ c.pulseLength) :
    c.pulseStart + y ≤ c.endpoint := by
  change c.pulseStart + y ≤ c.pulseStart + c.pulseLength
  linarith

/-- The actual reset leaves the pulse angular field unchanged. -/
theorem pulse_weight (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    X (d.core.pulseStart + y, eta) * E w (d.core.pulseStart + y, eta) ^ 2 =
      pulseNormalization d.core eta * PulseAmplitude.pulseWeight d.core y := by
  rw [E_before w eta (pulse_time_le_endpoint d.core hy'),
    angular_pulse d.core eta (by linarith)]
  rw [show d.core.pulseStart + y - d.core.pulseStart = y by ring]
  have he : Real.exp (d.core.pulseStart + y) *
      Real.exp (-(1 / 2 + d.core.lam) * y) ^ 2 =
      Real.exp d.core.pulseStart * Real.exp (-2 * d.core.lam * y) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold X pulseNormalization PulseAmplitude.normalization PulseAmplitude.pulseWeight
  calc
    _ = pulseAmplitude d.core ^ 2 * shape eta ^ 2 *
      (Real.exp (d.core.pulseStart + y) * Real.exp (-(1 / 2 + d.core.lam) * y) ^ 2) := by ring
    _ = _ := by rw [he]; ring

theorem pulse_U_eq (w : ResetWitness d K) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    U d amp (d.core.pulseStart + y, eta) = E w (d.core.pulseStart + y, eta) *
      pulseRatio d.core amp (y, eta) := by
  unfold U
  rw [axial_pulse d.core amp eta (by linarith), radialPulse_exp,
    E_before w eta (pulse_time_le_endpoint d.core hy')]
  rw [show d.core.pulseStart + y - d.core.pulseStart = y by ring]

/-- Exact source of the actual energy history throughout the pulse. -/
theorem energyWeight_pulse (w : ResetWitness d K) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    energyWeight w amp (d.core.pulseStart + y, eta) =
      pulseNormalization d.core eta * PulseAmplitude.pulseWeight d.core y *
        (pulseRatio d.core amp (y, eta) ^ 2 - 1 / 2) := by
  unfold energyWeight energyDensity
  rw [pulse_U_eq w amp eta hy hy']
  calc
    _ = (X (d.core.pulseStart + y, eta) * E w (d.core.pulseStart + y, eta) ^ 2) *
      (pulseRatio d.core amp (y, eta) ^ 2 - 1 / 2) := by ring
    _ = _ := by rw [pulse_weight w eta hy hy']

/-- Exact parameter derivative of the pulse energy source. -/
theorem dEta_energyWeight_pulse (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    dEta (energyWeight w amp) (d.core.pulseStart + y, eta) =
      pulseNormalization d.core eta * PulseAmplitude.pulseWeight d.core y *
        (2 * pulseRatio d.core amp (y, eta) * deriv (fun t => pulseRatio d.core amp (y, t)) eta -
          2 * shapeRate eta * (pulseRatio d.core amp (y, eta) ^ 2 - 1 / 2)) := by
  have hr : HasDerivAt (fun t => pulseRatio d.core amp (y, t))
      (deriv (fun t => pulseRatio d.core amp (y, t)) eta) eta :=
    (((pulseRatio_contDiff d.core ha).comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by simp) eta).hasDerivAt
  have hprod := ((((UniformAngularReset.shape_hasDerivAt eta).fun_pow 2).const_mul
    (PulseAmplitude.normalization d.core)).mul_const (PulseAmplitude.pulseWeight d.core y)).fun_mul
      ((hr.fun_pow 2).sub_const (1 / 2))
  have hact := dEta_hasDerivAt (energyWeight_smooth w ha) (d.core.pulseStart + y, eta)
  have heq : (fun t => energyWeight w amp (d.core.pulseStart + y, t)) =
      (fun t => PulseAmplitude.normalization d.core * shape t ^ 2 *
        PulseAmplitude.pulseWeight d.core y * (pulseRatio d.core amp (y, t) ^ 2 - 1 / 2)) := by
    funext t
    exact energyWeight_pulse w amp t hy hy'
  rw [heq] at hact
  calc
    _ = _ := hact.unique hprod
    _ = _ := by unfold pulseNormalization shapeRate; ring

/-- The pulse starts with the actual incoming energy, including the ideal past. -/
theorem S_at_pulseStart (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) :
    S w amp (d.core.pulseStart, eta) = PulseAmplitude.prefixEnergy d.core eta := by
  rw [S_eq_integral w ha]
  calc
    _ = ∫ t in Iic d.core.pulseStart, PulseAmplitude.energyIntegrand d (amp eta) eta t := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro t ht
      have htend : t ≤ d.core.endpoint :=
        ht.trans (PulseAmplitude.pulseStart_le_endpoint d.core)
      unfold PulseAmplitude.energyIntegrand U
      dsimp only
      rw [E_before w eta htend, finalAngular_before d eta htend,
        PulseAmplitude.axial_eq_of_amplitude_eq d.core amp (fun _ => amp eta) eta t rfl]
    _ = _ := PulseAmplitude.energyIntegrand_integral_prefix d (amp eta) eta

theorem prefixEnergy_hasDerivAt (c : Parameters) (eta : ℝ) :
    HasDerivAt (PulseAmplitude.prefixEnergy c)
      (2 * PulseAmplitude.prefixAxialEnergy c * eta +
        2 * PulseAmplitude.prefixAngularEnergy c * shape eta ^ 2 * shapeRate eta) eta := by
  convert! (((hasDerivAt_id eta).pow 2).const_mul (PulseAmplitude.prefixAxialEnergy c)).sub
    (((UniformAngularReset.shape_hasDerivAt eta).fun_pow 2).const_mul
      (PulseAmplitude.prefixAngularEnergy c)) using 1
  unfold shapeRate
  simp only [id_eq]
  ring

theorem dEta_S_at_pulseStart (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) :
    dEta (S w amp) (d.core.pulseStart, eta) =
      2 * PulseAmplitude.prefixAxialEnergy d.core * eta +
        2 * PulseAmplitude.prefixAngularEnergy d.core * shape eta ^ 2 * shapeRate eta := by
  rw [dEta_eq_deriv (S_smooth w ha)]
  have heq : (fun t => S w amp (d.core.pulseStart, t)) = PulseAmplitude.prefixEnergy d.core :=
    funext (S_at_pulseStart w ha)
  rw [heq, (prefixEnergy_hasDerivAt d.core eta).deriv]

theorem logarithmicRate_le_one (c : Parameters) : PulseAmplitude.logarithmicRate c.lam ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr c.lam_pos)
  have hm := mul_le_mul_of_nonneg_left h c.lam_pos.le
  have he : c.lam * (1 / c.lam - 1) = 1 - c.lam := by field_simp [c.lam_pos.ne']
  rw [he] at hm
  unfold PulseAmplitude.logarithmicRate
  nlinarith

theorem prefix_sum_bound (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) :
    PulseAmplitude.prefixAxialEnergy c + PulseAmplitude.prefixAngularEnergy c ≤
      PulseAmplitude.normalization c * PulseAmplitude.prefixBoundConstant c.P c.m / c.lam := by
  have hb := (PulseAmplitude.normalizedPrefix_bound c hwait).trans
    (mul_le_of_le_one_right (PulseAmplitude.prefixBoundConstant_pos c.P c.m).le
      (logarithmicRate_le_one c))
  have he : PulseAmplitude.normalizedPrefixAxial c + PulseAmplitude.normalizedPrefixAngular c =
      c.lam * (PulseAmplitude.prefixAxialEnergy c + PulseAmplitude.prefixAngularEnergy c) /
        PulseAmplitude.normalization c := by
    unfold PulseAmplitude.normalizedPrefixAxial PulseAmplitude.normalizedPrefixAngular
    ring
  rw [he] at hb
  have h := (div_le_iff₀ (PulseAmplitude.normalization_pos c)).mp hb
  apply (le_div_iff₀ c.lam_pos).mpr
  nlinarith

theorem shape_bounds {eta : ℝ} (heta : |eta| ≤ 1) :
    (1 / 4 : ℝ) ≤ shape eta ^ 2 ∧ shape eta ^ 2 ≤ 1 ∧ |shapeRate eta| ≤ 2 := by
  have hs : eta ^ 2 ≤ 1 := by
    nlinarith [sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr heta, sq_abs eta]
  have hlo : (1 / 2 : ℝ) ≤ shape eta := by
    change 1 / 2 ≤ (1 + eta ^ 2)⁻¹
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hhi := UniformAngularReset.shape_le_one eta
  refine ⟨by nlinarith, by nlinarith [shape_pos eta], ?_⟩
  rw [shapeRate, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by positivity : 0 < 1 + eta ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < 1 + eta ^ 2)).mpr
  nlinarith [sq_nonneg eta]

/-- One bound covers both normalized source factors. -/
theorem source_factor_bounds {R Reta rate B : ℝ} (hB : 0 ≤ B)
    (hR : |R| ≤ B) (hReta : |Reta| ≤ B) (hrate : |rate| ≤ 2) :
    |R ^ 2 - 1 / 2| ≤ 6 * B ^ 2 + 2 ∧
      |2 * R * Reta - 2 * rate * (R ^ 2 - 1 / 2)| ≤ 6 * B ^ 2 + 2 := by
  have hRsq : R ^ 2 ≤ B ^ 2 := by
    nlinarith [sq_le_sq₀ (abs_nonneg R) hB |>.mpr hR, sq_abs R]
  have hbase : |R ^ 2 - 1 / 2| ≤ B ^ 2 + 1 / 2 := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (sq_nonneg R), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hproduct : |R * Reta| ≤ B ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hR hReta (abs_nonneg _) hB
  have hfirst : |2 * R * Reta| ≤ 2 * B ^ 2 := by
    rw [show 2 * R * Reta = 2 * (R * Reta) by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hsecond : |2 * rate * (R ^ 2 - 1 / 2)| ≤ 4 * (B ^ 2 + 1 / 2) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul hrate hbase (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  exact ⟨hbase.trans (by nlinarith [sq_nonneg B]),
    (abs_sub _ _).trans (by linarith)⟩

/-- The actual energy source and its actual parameter derivative have a common bound. -/
theorem energy_sources_bound (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) {eta y B : ℝ} (heta : |eta| ≤ 1) (hB : 0 ≤ B)
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength)
    (hR : |pulseRatio d.core amp (y, eta)| ≤ B)
    (hReta : |deriv (fun t => pulseRatio d.core amp (y, t)) eta| ≤ B) :
    |energyWeight w amp (d.core.pulseStart + y, eta)| ≤
        pulseNormalization d.core eta * (6 * B ^ 2 + 2) ∧
      |dEta (energyWeight w amp) (d.core.pulseStart + y, eta)| ≤
        pulseNormalization d.core eta * (6 * B ^ 2 + 2) := by
  have hfactor := source_factor_bounds hB hR hReta (shape_bounds heta).2.2
  have hN := pulseNormalization_pos d.core eta
  have hw : 0 < PulseAmplitude.pulseWeight d.core y := Real.exp_pos _
  have hweight : pulseNormalization d.core eta * PulseAmplitude.pulseWeight d.core y ≤
      pulseNormalization d.core eta :=
    mul_le_of_le_one_right hN.le (PulseAmplitude.pulseWeight_le_one d.core hy)
  rw [energyWeight_pulse w amp eta hy hy', dEta_energyWeight_pulse w ha eta hy hy']
  constructor
  · rw [abs_mul, abs_of_pos (mul_pos hN hw)]
    exact mul_le_mul hweight hfactor.1 (abs_nonneg _) hN.le
  · rw [abs_mul, abs_of_pos (mul_pos hN hw)]
    exact mul_le_mul hweight hfactor.2 (abs_nonneg _) hN.le

/-- Prefix bounds include the incoming ideal history and its parameter derivative. -/
theorem initial_history_bounds (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) {eta : ℝ} (heta : |eta| ≤ 1) :
    |S w amp (d.core.pulseStart, eta)| ≤
        pulseNormalization d.core eta * (16 * PulseAmplitude.prefixBoundConstant d.core.P d.core.m)
          /
          d.core.lam ∧
      |dEta (S w amp) (d.core.pulseStart, eta)| ≤
        pulseNormalization d.core eta * (16 * PulseAmplitude.prefixBoundConstant d.core.P d.core.m)
          /
          d.core.lam := by
  let A := PulseAmplitude.prefixAxialEnergy d.core
  let G := PulseAmplitude.prefixAngularEnergy d.core
  have hA : 0 ≤ A := PulseAmplitude.prefixAxialEnergy_nonneg d.core
  have hG : 0 ≤ G := PulseAmplitude.prefixAngularEnergy_nonneg d.core
  have hs := shape_bounds heta
  have heta2 : eta ^ 2 ≤ 1 := by
    nlinarith [sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr heta, sq_abs eta]
  have hval : |S w amp (d.core.pulseStart, eta)| ≤ 4 * (A + G) := by
    rw [S_at_pulseStart w ha]
    change |A * eta ^ 2 - G * shape eta ^ 2| ≤ _
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (mul_nonneg hA (sq_nonneg _)),
      abs_of_nonneg (mul_nonneg hG (sq_nonneg _))]
    nlinarith [mul_le_of_le_one_right hA heta2, mul_le_of_le_one_right hG hs.2.1]
  have hder : |dEta (S w amp) (d.core.pulseStart, eta)| ≤ 4 * (A + G) := by
    rw [dEta_S_at_pulseStart w ha]
    change |2 * A * eta + 2 * G * shape eta ^ 2 * shapeRate eta| ≤ _
    apply (abs_add_le _ _).trans
    have hfirst : |2 * A * eta| ≤ 2 * A := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hA)]
      nlinarith [mul_le_of_le_one_right (show 0 ≤ 2 * A by positivity) heta]
    have hsecond : |2 * G * shape eta ^ 2 * shapeRate eta| ≤ 4 * G := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * G * shape eta ^ 2)]
      have hh := mul_le_mul hs.2.1 hs.2.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * G by positivity)]
    linarith
  have hscale : 4 * (A + G) ≤
      pulseNormalization d.core eta * (16 * PulseAmplitude.prefixBoundConstant d.core.P d.core.m) /
        d.core.lam := by
    calc
      _ ≤ 4 * (PulseAmplitude.normalization d.core *
          PulseAmplitude.prefixBoundConstant d.core.P d.core.m / d.core.lam) :=
        mul_le_mul_of_nonneg_left (prefix_sum_bound d.core hwait) (by norm_num)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hs.1
          (show 0 ≤ 16 * PulseAmplitude.normalization d.core *
            PulseAmplitude.prefixBoundConstant d.core.P d.core.m / d.core.lam by
              have h1 := (PulseAmplitude.normalization_pos d.core).le
              have h2 := (PulseAmplitude.prefixBoundConstant_pos d.core.P d.core.m).le
              have h3 := d.core.lam_pos.le
              positivity)
        unfold pulseNormalization
        convert! hh using 1 <;> ring
  exact ⟨hval.trans hscale, hder.trans hscale⟩

/-- Integrating an actual history source over a pulse of length `13 / lam`.
The final denominator is its exponentially decaying pulse energy weight. -/
theorem normalized_history_bound {H g : ℝ → ℝ} {lam N C M y : ℝ}
    (hlam : 0 < lam) (hN : 0 < N) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hy : 0 ≤ y) (hy' : y ≤ 13 / lam)
    (hg : Continuous g) (hd : ∀ t ∈ Icc (0 : ℝ) y, HasDerivAt H (g t) t)
    (hsource : ∀ t ∈ Icc (0 : ℝ) y, |g t| ≤ N * M)
    (hinit : |H 0| ≤ N * C / lam) :
    |H y| / (N * Real.exp (-2 * lam * y)) ≤ (C + 13 * M) * Real.exp 26 / lam := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (uIcc_of_le hy ▸ ht)) (hg.intervalIntegrable 0 y)
  have hint : |∫ t in (0 : ℝ)..y, g t| ≤ N * M * y := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := y) (C := N * M) (f := g) (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hsource t (uIcc_of_le hy ▸ uIoc_subset_uIcc ht))
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hy] using h
  have heq : H y = H 0 + ∫ t in (0 : ℝ)..y, g t := by linarith
  have hvalue : |H y| ≤ N * (C + 13 * M) / lam := by
    calc
      _ ≤ |H 0| + |∫ t in (0 : ℝ)..y, g t| := by rw [heq]; exact abs_add_le _ _
      _ ≤ N * C / lam + N * M * y := add_le_add hinit hint
      _ ≤ N * C / lam + N * M * (13 / lam) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hy' (mul_nonneg hN.le hM)) _
      _ = _ := by ring
  have hfactor : 1 ≤ Real.exp 26 * Real.exp (-2 * lam * y) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    nlinarith [(le_div_iff₀ hlam).mp hy']
  apply (div_le_iff₀ (mul_pos hN (Real.exp_pos _))).mpr
  calc
    _ ≤ N * (C + 13 * M) / lam := hvalue
    _ ≤ (C + 13 * M) * Real.exp 26 / lam * (N * Real.exp (-2 * lam * y)) := by
      have h := mul_le_mul_of_nonneg_left hfactor
        (show 0 ≤ N * (C + 13 * M) / lam by positivity)
      convert! h using 1 <;> ring

/-- Genuine normalized energy-history bounds from explicit pulse-ratio data.
No energy-history estimate appears among the hypotheses. -/
theorem pulse_history_bounds_of_ratio_bounds (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) {eta B y : ℝ}
    (heta : |eta| ≤ 1) (hB : 0 ≤ B) (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength)
    (hR : ∀ t ∈ Icc (0 : ℝ) d.core.pulseLength, |pulseRatio d.core amp (t, eta)| ≤ B)
    (hReta : ∀ t ∈ Icc (0 : ℝ) d.core.pulseLength,
      |deriv (fun e => pulseRatio d.core amp (t, e)) eta| ≤ B) :
    |S w amp (d.core.pulseStart + y, eta)| /
        (X (d.core.pulseStart + y, eta) * E w (d.core.pulseStart + y, eta) ^ 2) ≤
      (16 * PulseAmplitude.prefixBoundConstant d.core.P d.core.m + 13 * (6 * B ^ 2 + 2)) *
        Real.exp 26 / d.core.lam ∧
    |dEta (S w amp) (d.core.pulseStart + y, eta)| /
        (X (d.core.pulseStart + y, eta) * E w (d.core.pulseStart + y, eta) ^ 2) ≤
      (16 * PulseAmplitude.prefixBoundConstant d.core.P d.core.m + 13 * (6 * B ^ 2 + 2)) *
        Real.exp 26 / d.core.lam := by
  have hinit := initial_history_bounds w ha hwait heta
  have harg : Continuous (fun t : ℝ => (d.core.pulseStart + t, eta)) :=
    (continuous_const.add continuous_id).prodMk continuous_const
  have hg := (energyWeight_smooth w ha).continuous.comp harg
  have hgp := (dEta_smooth (energyWeight_smooth w ha)).continuous.comp harg
  have hs t (ht : t ∈ Icc (0 : ℝ) y) := energy_sources_bound w ha heta hB ht.1
    (ht.2.trans hy') (hR t ⟨ht.1, ht.2.trans hy'⟩) (hReta t ⟨ht.1, ht.2.trans hy'⟩)
  have hd : ∀ t ∈ Icc (0 : ℝ) y,
      HasDerivAt (fun u => S w amp (d.core.pulseStart + u, eta))
        (energyWeight w amp (d.core.pulseStart + t, eta)) t := by
    intro t _
    have h := (S_hasDerivAt w ha (d.core.pulseStart + t, eta)).comp t
      ((hasDerivAt_id t).const_add d.core.pulseStart)
    simp only [Function.comp_def, mul_one] at h
    exact h
  have hdp : ∀ t ∈ Icc (0 : ℝ) y,
      HasDerivAt (fun u => dEta (S w amp) (d.core.pulseStart + u, eta))
        (dEta (energyWeight w amp) (d.core.pulseStart + t, eta)) t := by
    intro t _
    have h := (dEta_prefix_hasDerivAt (initialS_smooth d) (energyWeight_smooth w ha)
      (d.core.pulseStart + t, eta)).comp t ((hasDerivAt_id t).const_add d.core.pulseStart)
    simp only [Function.comp_def, mul_one] at h
    exact h
  rw [pulse_weight w eta hy hy']
  constructor
  · apply normalized_history_bound d.core.lam_pos (pulseNormalization_pos d.core eta)
      (by have h := (PulseAmplitude.prefixBoundConstant_pos d.core.P d.core.m).le; positivity)
      (by positivity) hy hy' hg hd (fun t ht => (hs t ht).1)
    simpa only [add_zero] using hinit.1
  · apply normalized_history_bound d.core.lam_pos (pulseNormalization_pos d.core eta)
      (by have h := (PulseAmplitude.prefixBoundConstant_pos d.core.P d.core.m).le; positivity)
      (by positivity) hy hy' hgp hdp (fun t ht => (hs t ht).2)
    simpa only [add_zero] using hinit.2

/-- A common bound for the main pulse and its actual affine moment repair. -/
noncomputable def forceConstant (P m : ℝ) : ℝ :=
  OutgoingPulseBounds.mainBound + OutgoingPulseBounds.correctionJetBound P m 0

theorem forceConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < forceConstant P m :=
  add_pos OutgoingPulseBounds.mainBound_pos (OutgoingPulseBounds.correctionJetBound_pos hP m 0)

theorem forcing_abs_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120) (q A y : ℝ) :
    |PulseLag.forcing c q A y| ≤ forceConstant c.P c.m * (|q| + |A|) := by
  have hc := OutgoingPulseBounds.affineProfile_jet_bound c hsmall q A 0 y
  simp only [iteratedDeriv_zero] at hc
  have he : Real.exp (-(1 / (4 * c.lam))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by have h := c.lam_pos; positivity))
  have hc' : |OutgoingPulseBounds.affineProfile c q A y| ≤
      OutgoingPulseBounds.correctionJetBound c.P c.m 0 * (|q| + |A|) := by
    refine hc.trans ?_
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (OutgoingPulseBounds.correctionJetBound_pos c.P_pos c.m 0).le)
      (show 0 ≤ |q| + |A| by positivity)
    simpa only [mul_one] using h
  have hm : |A * mainPulse (c.lam * y)| ≤ OutgoingPulseBounds.mainBound * |A| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left (OutgoingPulseBounds.mainPulse_abs_le (c.lam * y))
      (abs_nonneg A)]
  calc
    _ ≤ |A * mainPulse (c.lam * y)| + |OutgoingPulseBounds.affineProfile c q A y| := abs_add_le _ _
    _ ≤ OutgoingPulseBounds.mainBound * |A| +
        OutgoingPulseBounds.correctionJetBound c.P c.m 0 * (|q| + |A|) := add_le_add hm hc'
    _ ≤ _ := by
      unfold forceConstant
      nlinarith [mul_nonneg OutgoingPulseBounds.mainBound_pos.le (abs_nonneg q)]

/-- The parameter derivative includes the derivative of the actual moment repair. -/
theorem pulseRatio_eta_hasDerivAt (c : Parameters) {amp : ℝ → ℝ} {eta amp' : ℝ}
    (ha : HasDerivAt amp amp' eta) (y : ℝ) :
    HasDerivAt (fun t => pulseRatio c amp (y, t))
      (PulseLag.forcing c (1 + 3 * eta ^ 2) amp' y) eta := by
  have hlin (q A : ℝ) : PulseLag.forcing c q A y =
      q * PulseLag.forcing c 1 0 y + A * PulseLag.forcing c 0 1 y := by
    simpa only [iteratedDeriv_zero] using PulseLag.forcing_jet_decomposition c q A 0 y
  have heq : (fun t => pulseRatio c amp (y, t)) =
      (fun t => OutgoingPulseBounds.parameterPolynomial t * PulseLag.forcing c 1 0 y +
        amp t * PulseLag.forcing c 0 1 y) := by
    funext t
    rw [← PulseLag.forcing_eq_pulseRatio c amp t y, hlin]
  rw [heq, hlin (1 + 3 * eta ^ 2) amp']
  exact ((OutgoingPulseBounds.parameterPolynomial_hasDerivAt eta).mul_const _).add
    (ha.mul_const _)

theorem pulse_ratio_bounds (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta)
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |amp'| ≤ 1) (y : ℝ) :
    |pulseRatio c amp (y, eta)| ≤ 6 * forceConstant c.P c.m ∧
      |deriv (fun t => pulseRatio c amp (y, t)) eta| ≤ 6 * forceConstant c.P c.m := by
  have hq := OutgoingPulseBounds.parameterPolynomial_bound heta
  have hq' : |1 + 3 * eta ^ 2| ≤ 4 := by
    simpa only [(OutgoingPulseBounds.parameterPolynomial_hasDerivAt eta).deriv] using
      OutgoingPulseBounds.parameterPolynomial_derivative_bound heta
  have hF := (forceConstant_pos c.P_pos c.m).le
  constructor
  · rw [← PulseLag.forcing_eq_pulseRatio c amp eta y]
    apply (forcing_abs_bound c hsmall _ _ y).trans
    nlinarith [mul_le_mul_of_nonneg_left
      (show |OutgoingPulseBounds.parameterPolynomial eta| + |amp eta| ≤ 6 by linarith) hF]
  · rw [(pulseRatio_eta_hasDerivAt c ha y).deriv]
    apply (forcing_abs_bound c hsmall _ _ y).trans
    nlinarith [mul_le_mul_of_nonneg_left
      (show |1 + 3 * eta ^ 2| + |amp'| ≤ 6 by linarith) hF]

/-- This constant depends only on the fixed parameters `P,m`. -/
noncomputable def historyConstant (P m : ℝ) : ℝ :=
  16 * PulseAmplitude.prefixBoundConstant P m + 13 * (6 * (6 * forceConstant P m) ^ 2 + 2)

theorem historyConstant_pos (P m : ℝ) : 0 < historyConstant P m := by
  have h := PulseAmplitude.prefixBoundConstant_pos P m
  unfold historyConstant
  positivity

/-- Both requested actual history bounds, with the actual repaired pulse source. -/
theorem pulse_history_bounds (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120) {eta y : ℝ} (heta : |eta| ≤ 1)
    (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    |S w amp (d.core.pulseStart + y, eta)| /
        (X (d.core.pulseStart + y, eta) * E w (d.core.pulseStart + y, eta) ^ 2) ≤
      historyConstant d.core.P d.core.m * Real.exp 26 / d.core.lam ∧
    |dEta (S w amp) (d.core.pulseStart + y, eta)| /
        (X (d.core.pulseStart + y, eta) * E w (d.core.pulseStart + y, eta) ^ 2) ≤
      historyConstant d.core.P d.core.m * Real.exp 26 / d.core.lam := by
  have hdata := pulse_ratio_bounds d.core hsmall
    ((ha.differentiable (by simp) eta).hasDerivAt) heta hamp hamp'
  exact pulse_history_bounds_of_ratio_bounds w ha hwait heta
    (mul_nonneg (by norm_num) (forceConstant_pos d.core.P_pos d.core.m).le) hy hy'
    (fun t _ => (hdata t).1) (fun t _ => (hdata t).2)

/-- Specialization to the corrected amplitude supplied by the proved energy solve. -/
theorem corrected_pulse_history_bounds (w : ResetWitness d K) (hK : 0 < K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120)
    (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    |S w (CorrectedPulseAmplitude.amplitude d w.coefficients) (d.core.pulseStart + y, eta)| /
        (X (d.core.pulseStart + y, eta) * E w (d.core.pulseStart + y, eta) ^ 2) ≤
      historyConstant d.core.P d.core.m * Real.exp 26 / d.core.lam ∧
    |dEta (S w (CorrectedPulseAmplitude.amplitude d w.coefficients))
        (d.core.pulseStart + y, eta)| /
        (X (d.core.pulseStart + y, eta) * E w (d.core.pulseStart + y, eta) ^ 2) ≤
      historyConstant d.core.P d.core.m * Real.exp 26 / d.core.lam := by
  obtain ⟨ha, hspec⟩ := CorrectedPulseAmplitude.amplitude_spec w hK hsmall hwait hscale
  have heta2 : eta ^ 2 ≤ 1 := by
    nlinarith [sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr heta, sq_abs eta]
  obtain ⟨hlo, hhi, _, hd, _⟩ := hspec eta heta2
  apply pulse_history_bounds w ha hwait hsmall heta _ _ hy hy'
  · rw [abs_of_pos (by linarith : 0 < CorrectedPulseAmplitude.amplitude d w.coefficients eta)]
    exact hhi.le
  · exact hd.trans (by linarith)

end

end NavierStokes.PulseEnergyHistory
