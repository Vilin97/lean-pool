/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPHarmonicMoment
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPAffineSlot
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareRescale

/-!
# Pressure Gradient Origin KPHarmonic Cells

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4
/-- An explicit absolute threshold for the harmonic contribution, as a
function of the fixed absolute harmonic derivative coefficient. -/
def originHarmonicThresholdA (C : ℝ) : ℝ :=
  (ENNReal.ofReal (Real.pi*4/3) * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ)).toReal
/-- The harmonic coefficient is finite. -/
theorem originHarmonicAbsoluteMomentConstant_lt_top (C : ℝ) :
    originHarmonicAbsoluteMomentConstant C < ⊤ := by
  unfold originHarmonicAbsoluteMomentConstant
  finiteness
/-- The absolute threshold pays for the harmonic cell coefficient. -/
theorem origin_harmonic_coefficient_le_affine_slot
    (C C_CZ q ε : ℝ) (KU KD : ℝ≥0∞) (hC : originHarmonicThresholdA C ≤ C_CZ) :
    ENNReal.ofReal (Real.pi*4/3) * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) *
      ENNReal.ofReal ε^(4/5 : ℝ) ≤ originKPAffineASlot q C_CZ ε KU KD := by
  have hfin : ENNReal.ofReal (Real.pi*4/3) * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (originHarmonicAbsoluteMomentConstant_lt_top
        C).ne)
  have hc : ENNReal.ofReal (Real.pi*4/3) * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) ≤
      ENNReal.ofReal (|C_CZ|+1) := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (hC.trans (by linarith only [le_abs_self C_CZ]))
  have hh := mul_le_mul' hc (le_refl (ENNReal.ofReal ε^(4/5 : ℝ)))
  apply hh.trans
  unfold originKPAffineASlot
  apply le_trans ?_ le_add_self
  exact mul_le_mul' le_rfl (le_mul_of_one_le_left' (by norm_num))

theorem harmonic_volume_radius_bound
    (C ε κ r : ℝ) (x : Vec3) (S : Set Vec3)
    (hr : 0 < r) (hrhi : r ≤ 1) (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    (hS : S ⊆ vec3Ball x r) :
    volume S * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) *
      ENNReal.ofReal ε^(4/5 : ℝ) * ENNReal.ofReal r^(2/5 : ℝ) ≤
      (ENNReal.ofReal (Real.pi*4/3) * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) *
        ENNReal.ofReal ε^(4/5 : ℝ)) *
      ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/κ))) := by
  have hθ : 5*(1-(6/5 : ℝ)/κ) ≤ 17/5 := by
    have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6/5) hκ hκhi
    norm_num at hd
    linarith only [hd]
  have hrE : ENNReal.ofReal r ≤ 1 := by
    exact (ENNReal.ofReal_le_ofReal hrhi).trans_eq (by simp)
  calc
    _ ≤ volume (vec3Ball x r) * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) *
      ENNReal.ofReal ε^(4/5 : ℝ) * ENNReal.ofReal r^(2/5 : ℝ) :=
        mul_le_mul' (mul_le_mul' (mul_le_mul' (measure_mono hS) le_rfl) le_rfl) le_rfl
    _ = (ENNReal.ofReal (Real.pi*4/3) * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) *
        ENNReal.ofReal ε^(4/5 : ℝ)) * ENNReal.ofReal r^(17/5 : ℝ) := by
      rw [volume_vec3Ball_eq]
      rw [show (17/5 : ℝ) = 3+2/5 by norm_num,
        ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ENNReal.rpow_ofNat]
      ring
    _ ≤ _ := by
      rw [← ENNReal.ofReal_rpow_of_pos hr]
      exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow_of_exponent_ge hrE hθ)

/-- The actual harmonic gradient satisfies the affine A-slot estimate on
any clipped cell contained in a fixed source collar. All numerical parameters
and the absolute harmonic coefficient precede the suitable solution. -/
theorem exists_origin_harmonic_clipped_coefficient_bound_of_sws :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ε κ ρ R₁ t r : ℝ, ∀ x : Vec3, ∀ z : ParabolicPoint,
      ∀ S : Set Vec3,
      0 < κ → κ ≤ 25/9 → ∀ hρlo : 1/8 ≤ ρ, ρ ≤ 1 → 0 < r → r ≤ 1 →
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
      (∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0,
        eLpNorm (fun y => classicalGradient
          (harmonicPressurePart (mollifiedBallCutoff z.1
            (show 0 < ρ from lt_of_lt_of_le (by norm_num) hρlo)) u
            (sourceSliceCentredMean z.1 ρ u) p s) y i)
          (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict S)^(6/5 : ℝ)) ≤
        (ENNReal.ofReal (Real.pi*4/3) * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) *
          ENNReal.ofReal ε^(4/5 : ℝ)) *
          ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/κ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_origin_harmonic_gradient_majorant
  refine ⟨C, hC, ?_⟩
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
      originHarmonicAbsoluteMomentConstant C * ENNReal.ofReal ε :=
    hMass.trans (mul_le_mul' (origin_harmonic_moment_constant_le_absolute C ρ z.1 hC hρlo hρhi)
      le_rfl)
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
  have hh := origin_harmonic_clipped_slice_norm_bound C ε S J t r hr measurableSet_Ioc hm hMass'
    hf hb
  have htime : Ioc (t-r^2) t ∩ Ioc (-(R₁^2)) 0 ⊆ Ioc (t-r^2) t ∩ J :=
    fun s hs => ⟨hs.1,hwin hs⟩
  have hh' := (lintegral_mono_set htime).trans hh
  exact hh'.trans (harmonic_volume_radius_bound C ε κ r x S hr hrhi hκ hκhi hSball)
/-- The harmonic coefficient is selected once from the absolute derivative
estimate, before every numerical parameter, carrier and suitable solution. -/
def originHarmonicAbsoluteCoefficient : ℝ :=
  Classical.choose exists_origin_harmonic_clipped_coefficient_bound_of_sws

/-- A fixed real threshold for the harmonic A slot, independent of all
solution data, exponents, radii and cells. -/
def originHarmonicASlotThreshold : ℝ := originHarmonicThresholdA originHarmonicAbsoluteCoefficient


end CKN.Core.Step4
