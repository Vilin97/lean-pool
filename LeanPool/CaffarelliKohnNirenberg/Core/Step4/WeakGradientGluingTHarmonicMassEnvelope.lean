/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPHarmonicCells
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTForceMassEnvelope

/-! # Harmonic pressure estimates on the fixed gap collars

The collar floor is `1/128`. The larger absolute moment coefficient is
chosen before the numerical data and the suitable solution.
-/

@[expose] public section

section

/-!
# Pressure Gradient Origin Gap Harmonic Moment

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

/-- The harmonic moment coefficient is uniform on the admissible fixed collars. -/
theorem origin_harmonic_moment_constant_le_gap_absolute
    (C ρ : ℝ) (x : Vec3) (hC : 0 ≤ C) (hρlo : 1 / 128 ≤ ρ) (hρhi : ρ ≤ 1) :
    originHarmonicMomentConstant C ρ x ≤ originHarmonicAbsoluteMomentConstant (65536*C) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by norm_num) hρlo
  have hpow : ρ^(-4 : ℝ) ≤ 268435456 := by
    have hh := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1/128) hρlo
      (by norm_num : (-4 : ℝ) ≤ 0)
    exact hh.trans_eq (by norm_num)
  have he : C*ρ^(-3 : ℝ)/ρ = C*ρ^(-4 : ℝ) := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
    field_simp
  have hfirst : C*ρ^(-3 : ℝ)/ρ ≤ 268435456*C := by
    rw [he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpow hC
  have hsecond : C*ρ^(-3 : ℝ)/((Real.pi*4/3)^(1/3 : ℝ)*ρ) ≤
      268435456*C/(Real.pi*4/3)^(1/3 : ℝ) := by
    have hh := div_le_div_of_nonneg_right hfirst
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi*4/3) (1/3 : ℝ))
    convert hh using 1
    ring
  have hv : volume (vec3Ball x ρ) ≤ ENNReal.ofReal (Real.pi*4/3) := by
    rw [volume_vec3Ball_eq]
    have hh : ENNReal.ofReal ρ ≤ 1 := by
      exact (ENNReal.ofReal_le_ofReal hρhi).trans_eq (by simp)
    exact (mul_le_mul' (pow_le_one₀ (by positivity) hh) le_rfl).trans_eq (one_mul _)
  unfold originHarmonicMomentConstant originHarmonicAbsoluteMomentConstant
  apply mul_le_mul'
  · exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hv (by norm_num))
  · apply add_le_add
    · apply ENNReal.rpow_le_rpow _ (by norm_num)
      change ENNReal.ofReal (C*ρ^(-3 : ℝ)/ρ) ≤ _
      simpa only [show (4096 : ℝ)*(65536*C) = 268435456*C by ring] using
        ENNReal.ofReal_le_ofReal hfirst
    · apply ENNReal.rpow_le_rpow _ (by norm_num)
      change ENNReal.ofReal (C*ρ^(-3 : ℝ)/((Real.pi*4/3)^(1/3 : ℝ)*ρ)) ≤ _
      simpa only [show (4096 : ℝ)*(65536*C) = 268435456*C by ring] using
        ENNReal.ofReal_le_ofReal hsecond


end CKN.Core.Step4
end

end

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

private theorem envelope_slice_norm_power_le
    {S : Set Vec3} {g : Vec3 → ℝ} {M : ℝ≥0∞}
    (hg : AEStronglyMeasurable g (volume.restrict S))
    (hb : ∀ᵐ y ∂volume.restrict S, ‖g y‖ₑ ≤ M) :
    eLpNorm g (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict S)^(6/5 : ℝ) ≤
      volume S * M^(6/5 : ℝ) := by
  have hh := eLpNorm_le_of_ae_enorm_bound (p := ENNReal.ofReal (6/5 : ℝ)) hg hb
  simp only [smul_eq_mul, Measure.restrict_apply_univ] at hh
  norm_num only [ENNReal.toReal_ofReal, show (0 : ℝ) ≤ 6/5 by norm_num] at hh
  have hp := ENNReal.rpow_le_rpow hh (by norm_num : (0 : ℝ) ≤ 6/5)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at hp
  norm_num at hp
  simpa only [mul_comm] using hp

/-- The actual harmonic gradient satisfies the affine A-slot estimate on
any clipped cell contained in a fixed source collar. All numerical parameters
and the absolute harmonic coefficient precede the suitable solution. -/
theorem exists_gap_harmonic_mass_envelope_coefficient :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ε κ ρ R₁ t r : ℝ, ∀ x : Vec3, ∀ z : ParabolicPoint,
      ∀ S : Set Vec3,
      0 < κ → κ ≤ 25/9 → ∀ hρlo : 1/128 ≤ ρ, ρ ≤ 1 → 0 < r → r ≤ 1 →
      MeasurableSet S → S ⊆ vec3Ball x r → S ⊆ vec3Ball z.1 (ρ/2) →
      Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0 ⊆ Ioc (z.2-ρ^2) z.2 →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ}, IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1 →
      ((∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
          ENNReal.ofReal |p w| ^ (3/2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε) →
      ∀ i : Fin 3,
      ∃ M : ℝ → ℝ≥0∞,
        AEMeasurable M (volume.restrict (Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0), eLpNorm (fun y =>
          classicalGradient
          (harmonicPressurePart (mollifiedBallCutoff z.1
            (show 0 < ρ from lt_of_lt_of_le (by norm_num) hρlo)) u
            (sourceSliceCentredMean z.1 ρ u) p s) y i)
          (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict S)^(6/5 : ℝ) ≤ M s) ∧
        (∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0, M s) ≤
        (ENNReal.ofReal (Real.pi*4/3) * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) *
          ENNReal.ofReal ε^(4/5 : ℝ)) *
          ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/κ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_origin_harmonic_gradient_majorant
  refine ⟨65536*C, mul_nonneg (by norm_num) hC, ?_⟩
  intro q ε κ ρ R₁ t r x z S hκ hκhi hρlo hρhi hr hrhi hS hSball hShalf hwin
    Ω I u f Du p hsol hdom hsub hQ hsmall i
  have hρ : 0 < ρ := lt_of_lt_of_le (by norm_num) hρlo
  let J := Ioc (z.2-ρ^2) z.2
  let M := originHarmonicSliceMajorant C ρ z.1 u p
  let F : Vec3 × ℝ → ℝ := fun w => classicalGradient
    (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
      (sourceSliceCentredMean z.1 ρ u) p w.2) w.1 i
  obtain ⟨hm,hMass⟩ := origin_harmonic_majorant_moment_of_sws C ε hsol hdom hsmall hQ
  have hMass' : (∫⁻ s in J, M s^(3/2 : ℝ)) ≤
      originHarmonicAbsoluteMomentConstant (65536*C) * ENNReal.ofReal ε :=
    hMass.trans (mul_le_mul' (origin_harmonic_moment_constant_le_gap_absolute C ρ z.1 hC hρlo
      hρhi) le_rfl)
  have hb : ∀ᵐ s ∂volume.restrict J, ∀ᵐ y ∂volume.restrict S, ‖F (y,s)‖ₑ ≤ M s := by
    filter_upwards [hbound hsol hρ hsub] with s hs
    filter_upwards [ae_restrict_mem hS] with y hy
    exact hs i y (hShalf hy)
  have hf : ∀ᵐ s ∂volume.restrict J,
      AEStronglyMeasurable (fun y => F (y,s)) (volume.restrict S) := by
    filter_upwards [slice_harmonic_part_contDiffOn_ae_of_sws hsol hρ hsub] with s hs
    rw [euclideanBall_eq_vec3Ball_display (by positivity : 0 < ρ/2)] at hs
    have hd : ContinuousOn (fun y => F (y,s)) (vec3Ball z.1 (ρ/2)) := by
      exact (hs.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball _ _) (by simp)).clm_apply
        continuousOn_const
    exact (hd.mono hShalf).aestronglyMeasurable hS
  have htime : Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0 ⊆ Ioc (t-r^2) t ∩ J :=
    fun s hs => ⟨hs.1,hwin hs⟩
  have hMm := hm.mono_measure (Measure.restrict_mono_set volume hwin)
  refine ⟨fun s => volume S * M s^(6/5 : ℝ), (hMm.pow_const _).const_mul _, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hwin hf,
      ae_restrict_of_ae_restrict_of_subset hwin hb] with s hs hsB
    exact envelope_slice_norm_power_le hs hsB
  · have htimeMass := origin_harmonic_majorant_clipped_time_of_sws C ε t r hr hsol hdom hsmall hQ
    have hconst := ENNReal.rpow_le_rpow
      (origin_harmonic_moment_constant_le_gap_absolute C ρ z.1 hC hρlo hρhi)
      (by norm_num : (0 : ℝ) ≤ 4/5)
    have htimeMass' := htimeMass.trans (mul_le_mul' (mul_le_mul' hconst le_rfl) le_rfl)
    calc
      _ = volume S * ∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0, M s^(6/5 : ℝ) :=
        lintegral_const_mul'' _ (hMm.pow_const _)
      _ ≤ volume S * (originHarmonicAbsoluteMomentConstant (65536*C)^(4/5 : ℝ) *
          ENNReal.ofReal ε^(4/5 : ℝ) * ENNReal.ofReal r^(2/5 : ℝ)) :=
        mul_le_mul' le_rfl ((lintegral_mono_set htime).trans htimeMass')
      _ ≤ _ := by
        simpa only [mul_assoc] using
          harmonic_volume_radius_bound (65536*C) ε κ r x S hr hrhi hκ hκhi hSball

/-- A fixed absolute coefficient for measurable harmonic mass envelopes. -/
def gapHarmonicEnvelopeCoefficient : ℝ :=
  Classical.choose exists_gap_harmonic_mass_envelope_coefficient

/-- The affine threshold of the fixed harmonic mass envelope. -/
def gapHarmonicEnvelopeThreshold : ℝ :=
  originHarmonicThresholdA gapHarmonicEnvelopeCoefficient

/-- A measurable envelope for the harmonic slice mass fits the affine slot. -/
theorem exists_gap_harmonic_affine_envelope_of_sws :
    ∀ q ε C_CZ κ ρ R₁ t r : ℝ, ∀ x : Vec3, ∀ z : ParabolicPoint,
      ∀ KU KD : ℝ≥0∞, ∀ S : Set Vec3,
      gapHarmonicEnvelopeThreshold ≤ C_CZ →
      0 < κ → κ ≤ 25/9 → ∀ hρlo : 1/128 ≤ ρ, ρ ≤ 1 → 0 < r → r ≤ 1 →
      MeasurableSet S → S ⊆ vec3Ball x r → S ⊆ vec3Ball z.1 (ρ/2) →
      Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0 ⊆ Ioc (z.2-ρ^2) z.2 →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ}, IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1 →
      ((∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
          ENNReal.ofReal |p w| ^ (3/2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε) →
      ∀ i : Fin 3,
      ∃ M : ℝ → ℝ≥0∞,
        AEMeasurable M (volume.restrict (Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0), eLpNorm (fun y =>
          classicalGradient
          (harmonicPressurePart (mollifiedBallCutoff z.1
            (show 0 < ρ from lt_of_lt_of_le (by norm_num) hρlo)) u
            (sourceSliceCentredMean z.1 ρ u) p s) y i)
          (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict S)^(6/5 : ℝ) ≤ M s) ∧
        (∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0, M s) ≤
        originKPAffineASlot q C_CZ ε KU KD *
          ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/κ))) := by
  intro q ε C_CZ κ ρ R₁ t r x z KU KD S hCZ hκ hκhi hρlo hρhi hr hrhi hS hSball hShalf hwin
    Ω I u f Du p hsol hdom hsub hQ hsmall i
  obtain ⟨M, hMm, hMp, hb⟩ := (Classical.choose_spec
    exists_gap_harmonic_mass_envelope_coefficient).2
    q ε κ ρ R₁ t r x z S hκ hκhi hρlo hρhi hr hrhi hS hSball hShalf hwin
    hsol hdom hsub hQ hsmall i
  exact ⟨M, hMm, hMp, hb.trans (mul_le_mul'
    (origin_harmonic_coefficient_le_affine_slot gapHarmonicEnvelopeCoefficient C_CZ q ε KU KD hCZ)
      le_rfl)⟩


end CKN.Core.Step4
