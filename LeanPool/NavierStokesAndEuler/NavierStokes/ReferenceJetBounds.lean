/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalEntrance
public import LeanPool.NavierStokesAndEuler.NavierStokes.ReferencePath

@[expose] public section

/-!
# Ordered jet bounds for the actual reference path

Coefficient-space norm bounds first give constants independent of the
normalization C. Only afterwards is the short REF transition chosen.
-/

noncomputable section

namespace NavierStokes.ReferenceJetBounds

private local instance (ε : ℝ) : NormedAddCommGroup (NaturalEntrance.CoefficientPair ε) :=
  inferInstance

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ProfileHistories NaturalAxisCoefficients NaturalAxisBridge NaturalProfile NaturalEntrance


theorem parameter_deriv {F : ProfileHistories.Field} {p : Point} (hF : ContDiffAt ℝ ∞ F p) :
    HasDerivAt (fun η => F (p.1, η)) (parameterPartial F p) p.2 := by
  simpa only [parameterPartial, Function.comp_def, id_eq, Prod.eta] using
    (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))

theorem radial_deriv {F : ProfileHistories.Field} {p : Point} (hF : ContDiffAt ℝ ∞ F p) :
    HasDerivAt (fun X => F (X, p.2)) (radialPartial F p) p.1 := by
  simpa only [radialPartial, Function.comp_def, id_eq, Prod.eta] using
    (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

theorem parameterPartial_eq_partialEta {F : ProfileHistories.Field} {p : Point} (hF : ContDiffAt ℝ
  ∞ F p) :
    parameterPartial F p = NaturalAxisBridge.partialEta F p := (parameter_deriv hF).deriv.symm

theorem radialPartial_eq_partialY {F : ProfileHistories.Field} {p : Point} (hF : ContDiffAt ℝ ∞ F
  p) :
    radialPartial F p = NaturalAxisBridge.partialY F p := (radial_deriv hF).deriv.symm

def jetConstant {h j σ : ℝ} {P0 : ℝ → ℝ} (v : CoefficientFamily h j σ P0) (k m : ℕ) : ℝ :=
  AxisEvaluation.jetBound v.epsilon 5 k m * (‖referencePair v‖ + 1)

theorem jetConstant_nonneg {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (k m : ℕ) : 0 ≤ jetConstant v k m := by
  exact mul_nonneg (AxisEvaluation.jetBound_nonneg v.epsilon_pos (by norm_num) k m)
    (by positivity)

theorem norm_pair_le {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (x : CoefficientPair v.epsilon)
    (hx : ‖x - referencePair v‖ ≤ 1) : ‖x‖ ≤ ‖referencePair v‖ + 1 := by
  calc
    ‖x‖ = ‖(x - referencePair v) + referencePair v‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - referencePair v‖ + ‖referencePair v‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem coefficient_jet_bound {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (x : CoefficientPair v.epsilon)
    (hx : ‖x - referencePair v‖ ≤ 1) (k m : ℕ) {p : Point} (hp : |p.1| ≤ 5) :
    |AxisEvaluation.mixedSeries window v.epsilon x.1 k m p| ≤ jetConstant v k m ∧
      |AxisEvaluation.mixedSeries window v.epsilon x.2 k m p| ≤ jetConstant v k m := by
  have hb (A : AxisCoefficientSpace.AxisSpace window v.epsilon) (hA : ‖A‖ ≤ ‖x‖) :
      |AxisEvaluation.mixedSeries window v.epsilon A k m p| ≤ jetConstant v k m := by
    have h := AxisEvaluation.mixedSeries_bound window v.epsilon_pos (by norm_num) (by norm_num) A k
      m hp
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hA.trans (norm_pair_le v x hx))
      (AxisEvaluation.jetBound_nonneg v.epsilon_pos (by norm_num) k m))
  exact ⟨hb x.1 (norm_fst_le x), hb x.2 (norm_snd_le x)⟩

section Natural

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (F : CoefficientProfile d Λ C)

theorem natural_U_value (hΛ : Λ ≠ 0) (p : Point) :
    Λ * (F.family.U p - NaturalAxisData.U j p.2) =
      AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.2 (rescalePoint Λ p) := by
  rw [F.U_eq]
  dsimp [axialField, affineProfile, pullback]
  field_simp ; ring

theorem natural_U_parameter (hΛ : Λ ≠ 0) {p : Point} (hp : p ∈ domain Λ) :
    Λ * (parameterPartial F.family.U p - 4) =
      NaturalAxisBridge.partialEta (AxisEvaluation.profile window d.coefficients.epsilon
        F.coefficients.2)
        (rescalePoint Λ p) := by
  have hpart : parameterPartial F.family.U p = NaturalAxisBridge.partialEta F.family.U p :=
    parameterPartial_eq_partialEta (F.family.natural.U_smooth.contDiffAt ((domain_isOpen
      Λ).mem_nhds hp))
  rw [hpart, F.U_eq]
  rw [axialField, affineProfile_partialEta
    (AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos F.coefficients.2)
    (1 / Λ) Λ hp (uStar_hasDerivAt j p.2)]
  field_simp ; ring

theorem natural_U_radial (hΛ : Λ ≠ 0) {p : Point} (hp : p ∈ domain Λ) :
    Λ * p.1 * radialPartial F.family.U p = (rescalePoint Λ p).1 *
      NaturalAxisBridge.partialY (AxisEvaluation.profile window d.coefficients.epsilon
        F.coefficients.2)
        (rescalePoint Λ p) := by
  have hpart : radialPartial F.family.U p = NaturalAxisBridge.partialY F.family.U p :=
    radialPartial_eq_partialY (F.family.natural.U_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds hp))
  rw [hpart, F.U_eq, axialField_partialY d.coefficients.epsilon_pos hΛ F.coefficients hp]
  rfl

theorem natural_log_parameter (_ : 0 < Λ) (hC : 0 < C) {p : Point} (hp : p ∈ domain Λ)
    (hφ : AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1 (rescalePoint Λ p)
      ≠ 0) :
    parameterPartial F.family.f p / F.family.f p - Λ * realGradient h j σ p.2 =
      NaturalAxisBridge.partialEta (AxisEvaluation.profile window d.coefficients.epsilon
        F.coefficients.1)
        (rescalePoint Λ p) /
          AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1 (rescalePoint Λ p)
            := by
  have hpart : parameterPartial F.family.f p = NaturalAxisBridge.partialEta F.family.f p :=
    parameterPartial_eq_partialEta (F.family.natural.f_smooth.contDiffAt ((domain_isOpen
      Λ).mem_nhds hp))
  rw [hpart, F.f_eq]
  rw [angularField, angularProfile_parameter_log_derivative
    (AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos F.coefficients.1) hp
    (realAmplitude_pos h j σ Λ hC p.2).ne' hφ
    (d.realAmplitude_hasDerivAt Λ C ⟨hp.2.1.le, hp.2.2.le⟩)]
  ring

theorem natural_log_radial (hC : 0 < C) {p : Point} (hp : p ∈ domain Λ)
    (hφ : AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1 (rescalePoint Λ p)
      ≠ 0) :
    p.1 * radialPartial F.family.f p / F.family.f p =
      (rescalePoint Λ p).1 *
        NaturalAxisBridge.partialY (AxisEvaluation.profile window d.coefficients.epsilon
          F.coefficients.1)
          (rescalePoint Λ p) /
            AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1 (rescalePoint Λ
              p) := by
  have hpart : radialPartial F.family.f p = NaturalAxisBridge.partialY F.family.f p :=
    radialPartial_eq_partialY (F.family.natural.f_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds hp))
  rw [hpart, F.f_eq]
  exact angularProfile_radial_log_derivative
    (AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos F.coefficients.1) hp
      (realAmplitude_pos h j σ Λ hC p.2).ne' hφ

theorem natural_U_bounds (hΛ : 0 < Λ) {p : Point} (hp : rescalePoint Λ p ∈ entranceSet) :
    |Λ * (F.family.U p - NaturalAxisData.U j p.2)| ≤ jetConstant d.coefficients 0 0 ∧
      |Λ * (parameterPartial F.family.U p - 4)| ≤ jetConstant d.coefficients 0 1 ∧
        |Λ * p.1 * radialPartial F.family.U p| ≤ 5 * jetConstant d.coefficients 1 0 := by
  have hdom : p ∈ domain Λ := entrance_mem_strip hp
  have h0 := (coefficient_jet_bound d.coefficients F.coefficients F.norm_ball 0 0
    (entrance_abs_le_five hp)).2
  have hη := (coefficient_jet_bound d.coefficients F.coefficients F.norm_ball 0 1
    (entrance_abs_le_five hp)).2
  have hx := (coefficient_jet_bound d.coefficients F.coefficients F.norm_ball 1 0
    (entrance_abs_le_five hp)).2
  rw [AxisEvaluation.mixedSeries_zero] at h0
  rw [natural_U_value F hΛ.ne', natural_U_parameter F hΛ.ne' hdom,
    natural_U_radial F hΛ.ne' hdom]
  rw [partialEta_profile window d.coefficients.epsilon_pos _ (entrance_mem_strip hp),
    partialY_profile window d.coefficients.epsilon_pos _ (entrance_mem_strip hp)]
  refine ⟨h0, hη, ?_⟩
  rw [abs_mul]
  exact mul_le_mul (entrance_abs_le_five hp) hx (abs_nonneg _)
    (by norm_num)

theorem natural_log_bound (hσ : 0 < σ) (hΛ : 0 < Λ) (hC : 0 < C)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    {p : Point} (hp : rescalePoint Λ p ∈ entranceSet) :
    |parameterPartial F.family.f p / F.family.f p - Λ * realGradient h j σ p.2| ≤
      8 * jetConstant d.coefficients 0 1 := by
  have hφ := coefficient_phi_lower d.coefficients hσ (profileErrorConstant_nonneg d)
    hscale F.coefficients F.norm_error hp.1.1 hp.1.2 (original_interval_interior hp.2)
  have hφpos : 0 < AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1
    (rescalePoint Λ p) :=
    lt_trans (by norm_num) hφ
  rw [natural_log_parameter F hΛ hC (entrance_mem_strip hp) hφpos.ne', abs_div, abs_of_pos hφpos]
  have hη := (coefficient_jet_bound d.coefficients F.coefficients F.norm_ball 0 1
    (entrance_abs_le_five hp)).1
  rw [partialEta_profile window d.coefficients.epsilon_pos _ (entrance_mem_strip hp)]
  apply (div_le_iff₀ hφpos).2
  have hE := jetConstant_nonneg d.coefficients 0 1
  nlinarith

def amplitudeConstant (d : AnalyticInputs h j σ P0) (Λ G : ℝ) : ℝ :=
  d.normalizationThreshold Λ * jetConstant d.coefficients 0 0 *
    (1 + Λ * G + 8 * jetConstant d.coefficients 0 1)

theorem amplitudeConstant_nonneg (hΛ : 0 ≤ Λ) {G : ℝ} (hG : 0 ≤ G) :
    0 ≤ amplitudeConstant d Λ G := by
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (jetConstant_nonneg d.coefficients 0 0))
    (by have := jetConstant_nonneg d.coefficients 0 1; positivity)

theorem natural_amplitude_bounds (hσ : 0 < σ) (hΛ : 0 < Λ) (hC : 0 < C)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    {G : ℝ} (hG : 0 ≤ G) {p : Point} (hp : rescalePoint Λ p ∈ entranceSet)
    (hgrad : |realGradient h j σ p.2| ≤ G) :
    |F.family.f p| ≤ amplitudeConstant d Λ G / C ∧
      |parameterPartial F.family.f p| ≤ amplitudeConstant d Λ G / C := by
  have hE0 := jetConstant_nonneg d.coefficients 0 0
  have hE1 := jetConstant_nonneg d.coefficients 0 1
  have hT : 0 < d.normalizationThreshold Λ := Real.exp_pos _
  have hbase : 0 ≤ d.normalizationThreshold Λ * jetConstant d.coefficients 0 0 / C := by positivity
  have hφ := (coefficient_jet_bound d.coefficients F.coefficients F.norm_ball 0 0
    (entrance_abs_le_five hp)).1
  rw [AxisEvaluation.mixedSeries_zero] at hφ
  have ha := realAmplitude_le_threshold d hΛ.le hC
    (show p.2 ∈ window.interval from ⟨(original_interval_interior hp.2).1.le,
      (original_interval_interior hp.2).2.le⟩)
  have hf0 : |F.family.f p| ≤ d.normalizationThreshold Λ * jetConstant d.coefficients 0 0 / C := by
    rw [F.f_eq]
    change |realAmplitude h j σ Λ C p.2 *
      AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1 (rescalePoint Λ p)| ≤ _
    rw [abs_mul, abs_of_pos (realAmplitude_pos h j σ Λ hC p.2)]
    calc
      _ ≤ (d.normalizationThreshold Λ / C) * jetConstant d.coefficients 0 0 :=
        mul_le_mul ha hφ (abs_nonneg _) (div_nonneg hT.le hC.le)
      _ = _ := by ring
  have hfp : 0 < F.family.f p := F.family.positive p (entrance_mem_strip hp) hp.1.1 hp.1.2
  have hl := natural_log_bound F hσ hΛ hC hscale hp
  have hlg : |parameterPartial F.family.f p / F.family.f p| ≤ Λ * G + 8 * jetConstant
    d.coefficients 0 1 := by
    calc
      _ = |(parameterPartial F.family.f p / F.family.f p - Λ * realGradient h j σ p.2) +
          Λ * realGradient h j σ p.2| := by ring_nf
      _ ≤ |parameterPartial F.family.f p / F.family.f p - Λ * realGradient h j σ p.2| +
          |Λ * realGradient h j σ p.2| := abs_add_le _ _
      _ ≤ 8 * jetConstant d.coefficients 0 1 + Λ * G := by
        rw [abs_mul, abs_of_pos hΛ]
        exact add_le_add hl (mul_le_mul_of_nonneg_left hgrad hΛ.le)
      _ = _ := by ring
  have hfη : |parameterPartial F.family.f p| ≤
      (d.normalizationThreshold Λ * jetConstant d.coefficients 0 0 / C) *
        (Λ * G + 8 * jetConstant d.coefficients 0 1) := by
    calc
      _ = |F.family.f p| * |parameterPartial F.family.f p / F.family.f p| := by
        rw [← abs_mul, mul_div_cancel₀ _ hfp.ne']
      _ ≤ _ := mul_le_mul hf0 hlg (abs_nonneg _) hbase
  constructor
  · apply hf0.trans
    have hb := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 1 + Λ * G + 8 * jetConstant d.coefficients 0 1 by
        nlinarith [mul_nonneg hΛ.le hG]) hbase
    simpa only [mul_one, amplitudeConstant, mul_div_assoc, div_mul_eq_mul_div, mul_assoc] using hb
  · apply hfη.trans
    have hb := mul_le_mul_of_nonneg_left
      (show Λ * G + 8 * jetConstant d.coefficients 0 1 ≤
        1 + Λ * G + 8 * jetConstant d.coefficients 0 1 by linarith) hbase
    simpa only [amplitudeConstant, mul_div_assoc, div_mul_eq_mul_div, mul_assoc] using hb

end Natural

def holdSet : Set Point := Icc (0 : ℝ) 110 ×ˢ Icc (-1 : ℝ) 1

theorem reference_mem (N : ReferencePath.Input) {p : Point} (hX : 0 ≤ p.1)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1) : p ∈ N.radialDomain.carrier := by
  change -20 < N.scale * p.1 ∧ p.2 ∈ ReferencePath.parameterInterval
  exact ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg N.scale_pos.le hX), original_interval_interior hη⟩

theorem endpoint_mem (N : ReferencePath.Input) {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) :
    (N.endpoint, η) ∈ domain N.scale := by
  change (-20 < N.scale * N.endpoint ∧ N.scale * N.endpoint < 20) ∧
    η ∈ ReferencePath.parameterInterval
  rw [N.scale_endpoint]
  exact ⟨by norm_num, original_interval_interior hη⟩

theorem first_parameter_difference {F G : ProfileHistories.Field} {x y η : ℝ}
    (hF : ContDiffAt ℝ ∞ F (x, η)) (hG : ContDiffAt ℝ ∞ G (y, η)) :
    iteratedDeriv 1 (fun z => F (x, z) - G (y, z)) η =
      parameterPartial F (x, η) - parameterPartial G (y, η) := by
  rw [iteratedDeriv_one]
  have hdF : HasDerivAt (fun z => F (x, z)) (parameterPartial F (x, η)) η := parameter_deriv hF
  have hdG : HasDerivAt (fun z => G (y, z)) (parameterPartial G (y, η)) η := parameter_deriv hG
  exact (hdF.sub hdG).deriv

theorem first_log_difference {F G : ProfileHistories.Field} {x y η : ℝ}
    (hF : ContDiffAt ℝ ∞ F (x, η)) (hG : ContDiffAt ℝ ∞ G (y, η))
    (hFn : F (x, η) ≠ 0) (hGn : G (y, η) ≠ 0) :
    iteratedDeriv 1 (fun z => Real.log (F (x, z)) - Real.log (G (y, z))) η =
      parameterPartial F (x, η) / F (x, η) - parameterPartial G (y, η) / G (y, η) := by
  rw [iteratedDeriv_one]
  exact (((parameter_deriv hF).log hFn).sub ((parameter_deriv hG).log hGn)).deriv

structure TransitionControl (N : ReferencePath.Input) (δ εU εF : ℝ) : Prop where
  length_pos : 0 < δ
  length_bound : 2 * δ < ReferencePath.rampLimit
  U_value : ∀ p : Point, N.endpoint ≤ p.1 → p.2 ∈ Icc (-1 : ℝ) 1 →
    |N.refU δ p - N.U (N.endpoint, p.2)| < εU
  U_parameter : ∀ p : Point, N.endpoint ≤ p.1 → p.2 ∈ Icc (-1 : ℝ) 1 →
    |parameterPartial (N.refU δ) p - parameterPartial N.U (N.endpoint, p.2)| < εU
  log_parameter : ∀ p : Point, N.endpoint ≤ p.1 → p.2 ∈ Icc (-1 : ℝ) 1 →
    |parameterPartial (N.refF δ) p / N.refF δ p -
      parameterPartial N.f (N.endpoint, p.2) / N.f (N.endpoint, p.2)| < 1
  f_value : ∀ p : Point, N.endpoint ≤ p.1 → p.2 ∈ Icc (-1 : ℝ) 1 →
    |N.refF δ p - N.f (N.endpoint, p.2)| < εF
  f_parameter : ∀ p : Point, N.endpoint ≤ p.1 → p.2 ∈ Icc (-1 : ℝ) 1 →
    |parameterPartial (N.refF δ) p - parameterPartial N.f (N.endpoint, p.2)| < εF

/-- One actual cutoff length works for all required low-order reference jets.
The tolerances may be chosen only after the fixed input profile is known. -/
theorem exists_transition_control (N : ReferencePath.Input) {εU εF : ℝ}
    (hεU : 0 < εU) (hεF : 0 < εF) :
    ∃ r > 0, ∀ δ, 0 < δ → δ < r → TransitionControl N δ εU εF := by
  obtain ⟨u0, hu0, hU0⟩ := N.ref_U_error_jet_close isCompact_Icc original_interval_interior 0 hεU
  obtain ⟨u1, hu1, hU1⟩ := N.ref_U_error_jet_close isCompact_Icc original_interval_interior 1 hεU
  obtain ⟨l1, hl1, hL1⟩ := N.ref_log_error_jet_close isCompact_Icc original_interval_interior 1
    zero_lt_one
  obtain ⟨f0, hf0, hF0⟩ := N.ref_field_error_jet_close isCompact_Icc original_interval_interior 0
    hεF
  obtain ⟨f1, hf1, hF1⟩ := N.ref_field_error_jet_close isCompact_Icc original_interval_interior 1
    hεF
  let r := min (ReferencePath.rampLimit / 4) (min u0 (min u1 (min l1 (min f0 f1))))
  have hr : 0 < r := lt_min (div_pos ReferencePath.rampLimit_pos (by norm_num))
    (lt_min hu0 (lt_min hu1 (lt_min hl1 (lt_min hf0 hf1))))
  refine ⟨r, hr, ?_⟩
  intro δ hδ hδr
  have hlim : δ < ReferencePath.rampLimit / 4 := hδr.trans_le (min_le_left _ _)
  have htail := hδr.trans_le (min_le_right _ _)
  have hδu0 : δ < u0 := htail.trans_le (min_le_left _ _)
  have htail1 := htail.trans_le (min_le_right _ _)
  have hδu1 : δ < u1 := htail1.trans_le (min_le_left _ _)
  have htail2 := htail1.trans_le (min_le_right _ _)
  have hδl1 : δ < l1 := htail2.trans_le (min_le_left _ _)
  have htail3 := htail2.trans_le (min_le_right _ _)
  have hδf0 : δ < f0 := htail3.trans_le (min_le_left _ _)
  have hδf1 : δ < f1 := htail3.trans_le (min_le_right _ _)
  have hδT : 2 * δ < ReferencePath.rampLimit := by linarith
  refine ⟨hδ, hδT, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hX hη
    simpa only [iteratedDeriv_zero, Prod.eta] using hU0 δ hδ hδu0 p.1 hX p.2 hη
  · intro p hX hη
    have hmem := reference_mem N (N.endpoint_pos.le.trans hX) hη
    have hrU := (N.refU_smooth hδ hδT).contDiffAt (N.radialDomain.isOpen.mem_nhds hmem)
    have hnU := N.U_smooth.contDiffAt ((domain_isOpen N.scale).mem_nhds (endpoint_mem N hη))
    have hc := hU1 δ hδ hδu1 p.1 hX p.2 hη
    rw [first_parameter_difference hrU hnU] at hc
    exact hc
  · intro p hX hη
    have hXp := N.endpoint_pos.le.trans hX
    have hmem := reference_mem N hXp hη
    have hrF := (N.refF_smooth hδ hδT).contDiffAt (N.radialDomain.isOpen.mem_nhds hmem)
    have hnF := N.f_smooth.contDiffAt ((domain_isOpen N.scale).mem_nhds (endpoint_mem N hη))
    have hc := hL1 δ hδ hδl1 p.1 hX p.2 hη
    rw [first_log_difference hrF hnF (N.refF_pos δ hmem hXp).ne'
      (N.endpoint_f_pos (original_interval_interior hη)).ne'] at hc
    exact hc
  · intro p hX hη
    simpa only [iteratedDeriv_zero, Prod.eta] using hF0 δ hδ hδf0 p.1 hX p.2 hη
  · intro p hX hη
    have hmem := reference_mem N (N.endpoint_pos.le.trans hX) hη
    have hrF := (N.refF_smooth hδ hδT).contDiffAt (N.radialDomain.isOpen.mem_nhds hmem)
    have hnF := N.f_smooth.contDiffAt ((domain_isOpen N.scale).mem_nhds (endpoint_mem N hη))
    have hc := hF1 δ hδ hδf1 p.1 hX p.2 hη
    rw [first_parameter_difference hrF hnF] at hc
    exact hc

theorem reference_initial_eventually (N : ReferencePath.Input) {δ : ℝ}
    (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit) {p : Point}
    (hX : p.1 ≤ N.endpoint) (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    (N.refF δ =ᶠ[𝓝 p] N.f) ∧ (N.refU δ =ᶠ[𝓝 p] N.U) := by
  have he : 1 < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
  have hm : p.1 < N.endpoint * Real.exp δ := by nlinarith [N.endpoint_pos]
  have hn : ∀ᶠ q in 𝓝 p, q.1 < N.endpoint * Real.exp δ ∧ q.2 ∈ ReferencePath.parameterInterval :=
    (continuousAt_fst.eventually (Iio_mem_nhds hm)).and
      (continuousAt_snd.eventually (ReferencePath.parameterInterval_open.mem_nhds
        (original_interval_interior hη)))
  constructor
  · filter_upwards [hn] with q hq
    exact N.refF_eq_natural hδ hδT hq.2 hq.1.le
  · filter_upwards [hn] with q hq
    exact N.refU_eq_natural hδ hδT hq.2 hq.1.le

theorem reference_initial_partials (N : ReferencePath.Input) {δ : ℝ}
    (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit) {p : Point}
    (hX : p.1 ≤ N.endpoint) (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    parameterPartial (N.refF δ) p = parameterPartial N.f p ∧
      parameterPartial (N.refU δ) p = parameterPartial N.U p ∧
        radialPartial (N.refU δ) p = radialPartial N.U p := by
  obtain ⟨hF, hU⟩ := reference_initial_eventually N hδ hδT hX hη
  unfold parameterPartial radialPartial
  rw [hF.fderiv_eq, hU.fderiv_eq]
  exact ⟨rfl, rfl, rfl⟩

theorem initial_entrance {Λ : ℝ} (hΛ : 0 < Λ) {p : Point}
    (hX : 0 ≤ p.1) (hupper : p.1 ≤ 4 / Λ) (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    rescalePoint Λ p ∈ entranceSet := by
  change (0 ≤ Λ * p.1 ∧ Λ * p.1 ≤ 41 / 10) ∧ p.2 ∈ Icc (-1 : ℝ) 1
  have hh := mul_le_mul_of_nonneg_left hupper hΛ.le
  have he : Λ * (4 / Λ) = 4 := by field_simp
  rw [he] at hh
  exact ⟨⟨mul_nonneg hΛ.le hX, by linarith⟩, hη⟩

theorem logtime_entrance (N : ReferencePath.Input) {p : Point} (hX : 0 < p.1)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1) (ht : N.logTime p.1 < ReferencePath.rampLimit) :
    rescalePoint N.scale p ∈ entranceSet := by
  have he : Real.exp (N.logTime p.1) < 41 / 40 := by
    simpa only [ReferencePath.rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)]
      using Real.exp_lt_exp.mpr ht
  have hs := N.fromLog_scaled (N.logTime p.1, p.2)
  rw [N.fromLog_logTime hX] at hs
  change (0 ≤ N.scale * p.1 ∧ N.scale * p.1 ≤ 41 / 10) ∧ p.2 ∈ Icc (-1 : ℝ) 1
  refine ⟨⟨(mul_pos N.scale_pos hX).le, ?_⟩, hη⟩
  dsimp only at hs
  rw [hs]
  linarith

def uniformBound {h j σ : ℝ} {P0 : ℝ → ℝ} (v : CoefficientFamily h j σ P0) : ℝ :=
  2 + jetConstant v 0 0 + 9 * jetConstant v 0 1 + 5 * jetConstant v 1 0

theorem uniformBound_controls {h j σ : ℝ} {P0 : ℝ → ℝ} (v : CoefficientFamily h j σ P0) :
    1 < uniformBound v ∧ 1 + jetConstant v 0 0 ≤ uniformBound v ∧
      1 + jetConstant v 0 1 ≤ uniformBound v ∧ 5 * jetConstant v 1 0 ≤ uniformBound v ∧
        1 + 8 * jetConstant v 0 1 ≤ uniformBound v := by
  have h0 := jetConstant_nonneg v 0 0
  have h1 := jetConstant_nonneg v 0 1
  have hx := jetConstant_nonneg v 1 0
  dsimp [uniformBound]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

structure JetBounds (h j σ Λ C B K : ℝ) (f U : ProfileHistories.Field) : Prop where
  axial_value : ∀ p ∈ holdSet, |Λ * (U p - NaturalAxisData.U j p.2)| ≤ B
  axial_parameter : ∀ p ∈ holdSet, |Λ * (parameterPartial U p - 4)| ≤ B
  axial_radial : ∀ p ∈ holdSet, |Λ * p.1 * radialPartial U p| ≤ B
  log_parameter : ∀ p ∈ holdSet,
    |parameterPartial f p / f p - Λ * realGradient h j σ p.2| ≤ B
  angular_value : ∀ p ∈ holdSet, |f p| ≤ K / C
  angular_parameter : ∀ p ∈ holdSet, |parameterPartial f p| ≤ K / C

section ReferenceEstimates

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (F : CoefficientProfile d Λ C) (hΛ : 0 < Λ)

abbrev referenceInput : ReferencePath.Input := ReferencePath.Input.ofNatural hΛ F.family

theorem reference_U_radial_bound {δ : ℝ} (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) {p : Point} (hp : p ∈ holdSet) :
    |Λ * p.1 * radialPartial ((referenceInput F hΛ).refU δ) p| ≤
      5 * jetConstant d.coefficients 1 0 := by
  let N := referenceInput F hΛ
  have hE := jetConstant_nonneg d.coefficients 1 0
  by_cases hz : p.1 = 0
  · simp only [hz, mul_zero, zero_mul, abs_zero]
    positivity
  have hX : 0 < p.1 := lt_of_le_of_ne hp.1.1 (Ne.symm hz)
  have hm := reference_mem N hp.1.1 hp.2
  have hd : deriv (fun X => N.refU δ (X, p.2)) p.1 = radialPartial (N.refU δ) p :=
    (radial_deriv ((N.refU_smooth hδ hδT).contDiffAt (N.radialDomain.isOpen.mem_nhds hm))).deriv
  by_cases ht : N.logTime p.1 < ReferencePath.rampLimit
  · have hs := N.same_radius_U_slope hδ hδT (original_interval_interior hp.2) hX ht
    rw [hd] at hs
    have heq : Λ * p.1 * radialPartial (N.refU δ) p =
        ReferencePath.slopeCutoff δ (N.logTime p.1) * (Λ * p.1 * radialPartial F.family.U p) := by
      calc
        _ = Λ * (p.1 * radialPartial (N.refU δ) p) := by ring
        _ = _ := by
          rw [hs]
          change Λ * (ReferencePath.slopeCutoff δ (N.logTime p.1) * (p.1 * radialPartial F.family.U
            p)) = _
          ring
    rw [heq, abs_mul, abs_of_nonneg (ReferencePath.slopeCutoff_mem δ (N.logTime p.1)).1]
    have hb := (natural_U_bounds F hΛ (logtime_entrance N hX hp.2 ht)).2.2
    exact (mul_le_mul_of_nonneg_left hb (ReferencePath.slopeCutoff_mem δ (N.logTime p.1)).1).trans
      (mul_le_of_le_one_left (by positivity) (ReferencePath.slopeCutoff_mem δ (N.logTime p.1)).2)
  · have hzcut := ReferencePath.slopeCutoff_zero hδ (hδT.le.trans (le_of_not_gt ht))
    have hs := (N.refU_hasDerivAt hδ hδT (original_interval_interior hp.2) hX).deriv
    rw [hd, hzcut, zero_mul, zero_div] at hs
    change |Λ * p.1 * radialPartial (N.refU δ) p| ≤ _
    rw [hs, mul_zero, abs_zero]
    positivity

theorem scaled_transfer (hpos : 0 < Λ) {a b c s : ℝ} (hclose : |a - b| ≤ 1 / Λ)
    (hbase : |Λ * (b - c)| ≤ s) : |Λ * (a - c)| ≤ 1 + s := by
  calc
    _ = |Λ * (a - b) + Λ * (b - c)| := by congr 1; ring
    _ ≤ |Λ * (a - b)| + |Λ * (b - c)| := abs_add_le _ _
    _ ≤ Λ * (1 / Λ) + s := by
      rw [abs_mul, abs_of_pos hpos]
      exact add_le_add (mul_le_mul_of_nonneg_left hclose hpos.le) hbase
    _ = _ := by field_simp

theorem transfer_difference {a b c r s : ℝ} (hclose : |a - b| ≤ r) (hbase : |b - c| ≤ s) :
    |a - c| ≤ r + s := by
  calc
    _ = |(a - b) + (b - c)| := by ring_nf
    _ ≤ |a - b| + |b - c| := abs_add_le _ _
    _ ≤ _ := add_le_add hclose hbase

theorem transfer_absolute {a b r s : ℝ} (hclose : |a - b| ≤ r) (hbase : |b| ≤ s) :
    |a| ≤ r + s := by
  simpa only [sub_zero] using transfer_difference (c := (0 : ℝ)) hclose (by simpa only [sub_zero]
    using hbase)

/-- The qualitative REF convergence has now been used only after Λ and C
were fixed, with explicit tolerances 1/Λ, 1, and 1/C. -/
theorem bounds_of_control (hσ : 0 < σ) (hC : 0 < C)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    {G : ℝ} (hG : 0 ≤ G) (hgrad : ∀ η ∈ Icc (-1 : ℝ) 1, |realGradient h j σ η| ≤ G)
    {δ : ℝ} (hc : TransitionControl (referenceInput F hΛ) δ (1 / Λ) (1 / C)) :
    JetBounds h j σ Λ C (uniformBound d.coefficients) (1 + amplitudeConstant d Λ G)
      ((referenceInput F hΛ).refF δ) ((referenceInput F hΛ).refU δ) := by
  let N := referenceInput F hΛ
  have hB := uniformBound_controls d.coefficients
  have hE0 := jetConstant_nonneg d.coefficients 0 0
  have hE1 := jetConstant_nonneg d.coefficients 0 1
  have hE10 := jetConstant_nonneg d.coefficients 1 0
  have hinit (p : Point) (hp : p ∈ holdSet) (hx : p.1 ≤ N.endpoint) :
      rescalePoint Λ p ∈ entranceSet := initial_entrance hΛ hp.1.1 hx hp.2
  have hend (η : ℝ) (hη : η ∈ Icc (-1 : ℝ) 1) :
      rescalePoint Λ (N.endpoint, η) ∈ entranceSet :=
    initial_entrance hΛ N.endpoint_pos.le le_rfl hη
  have hKle : amplitudeConstant d Λ G / C ≤ (1 + amplitudeConstant d Λ G) / C :=
    div_le_div_of_nonneg_right (by linarith) hC.le
  change JetBounds h j σ Λ C (uniformBound d.coefficients) (1 + amplitudeConstant d Λ G)
    (N.refF δ) (N.refU δ)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    by_cases hx : p.1 ≤ N.endpoint
    · rw [N.refU_eq_natural_initial δ hx]
      exact (natural_U_bounds F hΛ (hinit p hp hx)).1.trans (by linarith [hB.2.1])
    · have hxe := (lt_of_not_ge hx).le
      have hb := (natural_U_bounds F hΛ (hend p.2 hp.2)).1
      exact (scaled_transfer hΛ (hc.U_value p hxe hp.2).le hb).trans hB.2.1
  · intro p hp
    by_cases hx : p.1 ≤ N.endpoint
    · rw [(reference_initial_partials N hc.length_pos hc.length_bound hx hp.2).2.1]
      exact (natural_U_bounds F hΛ (hinit p hp hx)).2.1.trans (by linarith [hB.2.2.1])
    · have hxe := (lt_of_not_ge hx).le
      have hb := (natural_U_bounds F hΛ (hend p.2 hp.2)).2.1
      exact (scaled_transfer hΛ (hc.U_parameter p hxe hp.2).le hb).trans hB.2.2.1
  · intro p hp
    exact (reference_U_radial_bound F hΛ hc.length_pos hc.length_bound hp).trans hB.2.2.2.1
  · intro p hp
    by_cases hx : p.1 ≤ N.endpoint
    · rw [N.refF_eq_natural_initial δ hx,
        (reference_initial_partials N hc.length_pos hc.length_bound hx hp.2).1]
      exact (natural_log_bound F hσ hΛ hC hscale (hinit p hp hx)).trans (by linarith [hB.2.2.2.2])
    · have hxe := (lt_of_not_ge hx).le
      have hb := natural_log_bound F hσ hΛ hC hscale (hend p.2 hp.2)
      exact (transfer_difference (hc.log_parameter p hxe hp.2).le hb).trans hB.2.2.2.2
  · intro p hp
    by_cases hx : p.1 ≤ N.endpoint
    · rw [N.refF_eq_natural_initial δ hx]
      exact (natural_amplitude_bounds F hσ hΛ hC hscale hG (hinit p hp hx) (hgrad p.2
        hp.2)).1.trans hKle
    · have hxe := (lt_of_not_ge hx).le
      have hb := (natural_amplitude_bounds F hσ hΛ hC hscale hG (hend p.2 hp.2) (hgrad p.2 hp.2)).1
      have hb' := transfer_absolute (hc.f_value p hxe hp.2).le hb
      convert! hb' using 1 ; ring
  · intro p hp
    by_cases hx : p.1 ≤ N.endpoint
    · rw [(reference_initial_partials N hc.length_pos hc.length_bound hx hp.2).1]
      exact (natural_amplitude_bounds F hσ hΛ hC hscale hG (hinit p hp hx) (hgrad p.2
        hp.2)).2.trans hKle
    · have hxe := (lt_of_not_ge hx).le
      have hb := (natural_amplitude_bounds F hσ hΛ hC hscale hG (hend p.2 hp.2) (hgrad p.2 hp.2)).2
      have hb' := transfer_absolute (hc.f_parameter p hxe hp.2).le hb
      convert! hb' using 1 ; ring

end ReferenceEstimates

def radialErrorConstant {h j σ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0) : ℝ :=
  AxisEvaluation.jetBound d.coefficients.epsilon 5 1 0 * profileErrorConstant d

theorem radialErrorConstant_nonneg {h j σ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0) :
    0 ≤ radialErrorConstant d :=
  mul_nonneg (AxisEvaluation.jetBound_nonneg d.coefficients.epsilon_pos (by norm_num) 1 0)
    (profileErrorConstant_nonneg d)

theorem natural_radial_jet_error {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : CoefficientProfile d Λ C) (hΛ : 0 < Λ) {p : Point} (hp : p ∈ entranceSet) :
    |NaturalAxisBridge.partialY (AxisEvaluation.profile window d.coefficients.epsilon
      F.coefficients.1) p -
      sourceJets d.coefficients.epsilon_pos (referencePair d.coefficients) p 1| ≤
        radialErrorConstant d / Λ := by
  rw [partialY_profile window d.coefficients.epsilon_pos _ (entrance_mem_strip hp)]
  change |AxisEvaluation.mixedSeries window d.coefficients.epsilon F.coefficients.1 1 0 p -
    AxisEvaluation.mixedSeries window d.coefficients.epsilon (referencePair d.coefficients).1 1 0
      p| ≤ _
  have hb := AxisEvaluation.mixedSeries_sub_bound window d.coefficients.epsilon_pos
    (by norm_num) (by norm_num) F.coefficients.1 (referencePair d.coefficients).1 1 0
      (entrance_abs_le_five hp)
  have hn := (norm_fst_le (F.coefficients - referencePair d.coefficients)).trans F.norm_error
  have hj := AxisEvaluation.jetBound_nonneg d.coefficients.epsilon_pos (by norm_num : (1 : ℝ) ≤ 5)
    1 0
  have hk := profileErrorConstant_nonneg d
  rw [Real.norm_eq_abs] at hb
  apply hb.trans
  apply (mul_le_mul_of_nonneg_left hn hj).trans
  have he : AxisEvaluation.jetBound d.coefficients.epsilon 5 1 0 *
      (profileErrorConstant d / (2 * Λ)) = radialErrorConstant d / Λ / 2 := by
    dsimp [radialErrorConstant]
    field_simp [hΛ.ne']
  rw [he]
  have hnn : 0 ≤ radialErrorConstant d / Λ := div_nonneg (radialErrorConstant_nonneg d) hΛ.le
  linarith

/-- A genuine finite-dimensional source sample, with the radial jet error
still controlled by the coefficient norm. -/
structure SlopeSample {h j σ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)
    (Λ B Kerr : ℝ) (f : ProfileHistories.Field) (p : Point) where
  Y : ℝ
  theta : ℝ
  phi : ℝ
  error : ℝ
  point_mem : (Y, p.2) ∈ entranceSet
  theta_mem : theta ∈ Icc (0 : ℝ) 1
  phi_lower : 1 / 8 ≤ phi
  phi_upper : phi ≤ B
  error_bound : |error| ≤ Kerr / Λ
  slope_eq : p.1 * radialPartial f p / f p = theta * Y *
    (sourceJets d.coefficients.epsilon_pos (referencePair d.coefficients) (Y, p.2) 1 + error) / phi

theorem reference_slope_sample {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : CoefficientProfile d Λ C) (hΛ : 0 < Λ) (hσ : 0 < σ) (hC : 0 < C)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    {p : Point} (hX : (referenceInput F hΛ).endpoint ≤ p.1) (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    Nonempty (SlopeSample d Λ (uniformBound d.coefficients) (radialErrorConstant d)
      ((referenceInput F hΛ).refF δ) p) := by
  let N := referenceInput F hΛ
  have hXp : 0 < p.1 := N.endpoint_pos.trans_le hX
  have hmem := reference_mem N hXp.le hη
  have hfpos := N.refF_pos δ hmem hXp.le
  have hd : deriv (fun X => Real.log (N.refF δ (X, p.2))) p.1 =
      radialPartial (N.refF δ) p / N.refF δ p :=
    ((radial_deriv ((N.refF_smooth hδ hδT).contDiffAt (N.radialDomain.isOpen.mem_nhds hmem))).log
      hfpos.ne').deriv
  by_cases ht : N.logTime p.1 < ReferencePath.rampLimit
  · have hp := logtime_entrance N hXp hη ht
    have hφ := coefficient_phi_lower d.coefficients hσ (profileErrorConstant_nonneg d)
      hscale F.coefficients F.norm_error hp.1.1 hp.1.2 (original_interval_interior hη)
    have hφpos : 0 < AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1
      (rescalePoint Λ p) :=
      lt_trans (by norm_num) hφ
    let φ := AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1 (rescalePoint Λ
      p)
    let e := NaturalAxisBridge.partialY (AxisEvaluation.profile window d.coefficients.epsilon
      F.coefficients.1)
      (rescalePoint Λ p) - sourceJets d.coefficients.epsilon_pos (referencePair d.coefficients)
        (rescalePoint Λ p) 1
    refine ⟨{
      Y := Λ * p.1
      theta := ReferencePath.slopeCutoff δ (N.logTime p.1)
      phi := φ
      error := e
      point_mem := hp
      theta_mem := ReferencePath.slopeCutoff_mem δ (N.logTime p.1)
      phi_lower := hφ.le
      phi_upper := ?_
      error_bound := natural_radial_jet_error F hΛ hp
      slope_eq := ?_ }⟩
    · have hb := (coefficient_jet_bound d.coefficients F.coefficients F.norm_ball 0 0
      (entrance_abs_le_five hp)).1
      rw [AxisEvaluation.mixedSeries_zero] at hb
      exact (le_abs_self φ).trans (hb.trans (by linarith [(uniformBound_controls
        d.coefficients).2.1]))
    · have hs := N.same_radius_log_slope hδ hδT (original_interval_interior hη) hXp ht
      rw [hd] at hs
      change p.1 * (radialPartial (N.refF δ) p / N.refF δ p) =
        ReferencePath.slopeCutoff δ (N.logTime p.1) * (p.1 * radialPartial F.family.f p /
          F.family.f p) at hs
      rw [natural_log_radial F hC (entrance_mem_strip hp) hφpos.ne'] at hs
      dsimp [e, φ]
      simpa only [add_sub_cancel, rescalePoint, mul_div_assoc, mul_assoc] using hs
  · have hcut := ReferencePath.slopeCutoff_zero hδ (hδT.le.trans (le_of_not_gt ht))
    have hz := (N.log_refF_hasDerivAt hδ hδT (original_interval_interior hη) hXp).deriv
    rw [hd, hcut, zero_mul, zero_div] at hz
    refine ⟨{
      Y := 0
      theta := 0
      phi := 1
      error := 0
      point_mem := ⟨by norm_num, hη⟩
      theta_mem := ⟨le_rfl, zero_le_one⟩
      phi_lower := by norm_num
      phi_upper := (uniformBound_controls d.coefficients).1.le
      error_bound := by simpa only [abs_zero] using div_nonneg (radialErrorConstant_nonneg d) hΛ.le
      slope_eq := ?_ }⟩
    rw [mul_div_assoc, hz]
    simp only [mul_zero, zero_mul, zero_div]

theorem exists_gradient_bound (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ G > 0, ∀ η ∈ Icc (-1 : ℝ) 1, |realGradient h j σ η| ≤ G := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (NaturalEntrance.realGradient_continuous h j hσ).continuousOn
  refine ⟨1 + |R|, by positivity, ?_⟩
  intro η hη
  have hb := hR η hη
  rw [Real.norm_eq_abs] at hb
  linarith [le_abs_self R]

/-- All constants used to choose C precede C. The actual short transition
is selected only after C and the actual natural coefficient profile. -/
theorem ordered_reference_bounds {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hσ : 0 < σ) :
    ∃ B M Kerr : ℝ, 1 < B ∧ 0 < M ∧ 0 ≤ Kerr ∧
      ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, M ≤ Λ → ∃ KΛ > 0,
        ∀ C : ℝ, d.normalizationThreshold Λ ≤ C → ∀ F : CoefficientProfile d Λ C,
          ∃ r > 0, ∀ δ : ℝ, 0 < δ → δ < r →
            TransitionControl (referenceInput F hΛ) δ (1 / Λ) (1 / C) ∧
            JetBounds h j σ Λ C B KΛ ((referenceInput F hΛ).refF δ) ((referenceInput F hΛ).refU δ) ∧
            ∀ p ∈ holdSet, (referenceInput F hΛ).endpoint ≤ p.1 →
              Nonempty (SlopeSample d Λ B Kerr ((referenceInput F hΛ).refF δ) p) := by
  obtain ⟨G, hG, hgrad⟩ := exists_gradient_bound h j hσ
  let M := max 1 (AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d))
  refine ⟨uniformBound d.coefficients, M, radialErrorConstant d,
    (uniformBound_controls d.coefficients).1, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
      radialErrorConstant_nonneg d, ?_⟩
  intro Λ hΛ hM
  have hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ :=
    (le_max_right _ _).trans hM
  refine ⟨1 + amplitudeConstant d Λ G, ?_, ?_⟩
  · have hb := amplitudeConstant_nonneg (d := d) hΛ.le hG.le
    linarith
  intro C hC F
  have hCp : 0 < C := (Real.exp_pos _).trans_le hC
  obtain ⟨r, hr, hc⟩ := exists_transition_control (referenceInput F hΛ)
    (one_div_pos.mpr hΛ) (one_div_pos.mpr hCp)
  refine ⟨r, hr, ?_⟩
  intro δ hδ hδr
  have hcon := hc δ hδ hδr
  refine ⟨hcon, bounds_of_control F hΛ hσ hCp hscale hG.le hgrad hcon, ?_⟩
  intro p hp hX
  exact reference_slope_sample F hΛ hσ hCp hscale hcon.length_pos hcon.length_bound hX hp.2

end NavierStokes.ReferenceJetBounds

end
