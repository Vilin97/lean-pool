/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTGapForceAffine
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFourTermMass

/-! # Homogeneous time mass of the annular force increment

Spatial boundedness on the half-collar and Holder's inequality in space
and time retain the force data power without an additive constant.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

private theorem force_slice_norm_power_le
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

/-- The clipped mass of the actual force increment has the homogeneous
force power and the spatial cell volume, on every interior half-collar. -/
theorem exists_gap_force_mass_envelope_of_sws
    (ε R₁ r : ℝ) {z : ParabolicPoint} {ρ : ℝ}
    (hρ : 0 < ρ) (hlo : 1/128 ≤ ρ) (hhi : ρ ≤ 1/2)
    (hr : 0 < r) (hrρ : r ≤ ρ/2)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hQ : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1)
    (hforce : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (f w))^q) ≤ ENNReal.ofReal ε)
    (i : Fin 3) :
    ∃ M : ℝ → ℝ≥0∞,
      AEMeasurable M (volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0)) ∧
      (∀ᵐ s ∂volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0),
        eLpNorm (fun y => gapForceIncrement z hρ u p f i (y,s))
        (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁))^(6/5 : ℝ) ≤ M s) ∧
      (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0, M s) ≤
      volume (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁) *
        ENNReal.ofReal gapForceIncrementCoefficient^(6/5 : ℝ) *
        (ENNReal.ofReal (r^2))^(1-6/(5*q)) * ENNReal.ofReal ε^(6/(5*q)) := by
  let B := vec3Ball z.1 ρ
  let W := Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0
  let S := vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁
  let F : ℝ → ℝ≥0∞ := fun s => ∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (f (y,s)))
  have hsub := (closure_mono hQ).trans hdom
  have hwin : W ⊆ Ioc (z.2-ρ^2) z.2 := by
    intro s hs
    have hr' : r ≤ ρ := by linarith only [hrρ,hρ]
    exact ⟨lt_of_le_of_lt (sub_le_sub_left (pow_le_pow_left₀ hr.le hr' 2) _) hs.1.1,hs.1.2⟩
  have hspace : S ⊆ vec3Ball z.1 (ρ/2) :=
    fun x hx => lt_of_lt_of_le hx.1 hrρ
  have hS : MeasurableSet S := (vec3Ball_measurable _ _).inter (vec3Ball_measurable _ _)
  have hbox : B ×ˢ W ⊆ parabolicCylinder (0 : Vec3) 0 1 :=
    (Set.prod_mono (subset_refl _) hwin).trans hQ
  obtain ⟨Ω',J',hlocal,hunit⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1
    (by norm_num : (0 : ℝ) < 1) hdom
  have hdata := hsol.2.2.2.2.2.1 Ω' J' hlocal
  have hG : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (f w)))
      ((volume.restrict B).prod (volume.restrict W)) := by
    rw [Measure.prod_restrict]
    exact ((continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hdata.2.2.2.1).aemeasurable.ennreal_ofReal).mono_measure
      (Measure.restrict_mono_set volume (hbox.trans hunit))
  have hFm : AEMeasurable F (volume.restrict W) := hG.lintegral_prod_left'
  have hmass : (∫⁻ s in W, F s^(6/5 : ℝ)) ≤
      ENNReal.ofReal (r^2)^(1-6/(5*q)) * ENNReal.ofReal ε^(6/(5*q)) := by
    have h := harmonicRemainder_time_moment_le (a := 1) (c := q) (m := 6/(5*q))
      hG (by norm_num) (by linarith only [hsol.2.2.2.1]) (by ring)
      (harmonicRemainder_volume_ball_le_one hhi) (D := ENNReal.ofReal (r^2))
      (show volume W ≤ ENNReal.ofReal (r^2) from (measure_mono inter_subset_left).trans_eq (by
        rw [Real.volume_Ioc]; congr 1; ring))
      ((lintegral_mono_set hbox).trans hforce)
    simpa only [ENNReal.rpow_one] using h
  have hb := gap_force_increment_majorant_of_sws (z := z) hsol hρ hlo hsub
  have he := gap_force_increment_eq_pressureP8_ae_of_sws (z := z) hsol hρ hsub
  have hf := slice_force_source_data_ae_of_sws (z := z) hsol hρ hsub
  have hpoint : ∀ᵐ s ∂volume.restrict W,
      eLpNorm (fun y => gapForceIncrement z hρ u p f i (y,s))
        (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict S)^(6/5 : ℝ) ≤
        volume S * (ENNReal.ofReal gapForceIncrementCoefficient * F s)^(6/5 : ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hwin hb,
      ae_restrict_of_ae_restrict_of_subset hwin he,
      ae_restrict_of_ae_restrict_of_subset hwin hf] with s hbs hes hfs
    have hcont : ContinuousOn (fun y => classicalGradient
        (pressureP8 (mollifiedBallCutoff z.1 hρ) f s) y i) (vec3Ball z.1 (ρ/2)) :=
      ((contDiffOn_pressureP8_halfBall hρ hfs.2.2.1).continuousOn_fderiv_of_isOpen
        (isOpen_vec3Ball _ _) (by simp)).clm_apply continuousOn_const
    have hm : AEStronglyMeasurable (fun y => gapForceIncrement z hρ u p f i (y,s))
        (volume.restrict S) := (hcont.mono hspace).aestronglyMeasurable hS |>.congr (by
          filter_upwards [ae_restrict_mem hS] with y hy
          exact (hes i y (hspace hy)).symm)
    apply force_slice_norm_power_le hm
    filter_upwards [ae_restrict_mem hS] with y hy
    exact hbs i y (hspace hy)
  refine ⟨fun s => volume S * (ENNReal.ofReal gapForceIncrementCoefficient * F s)^(6/5 : ℝ),
    ((hFm.const_mul _).pow_const _).const_mul _, hpoint, ?_⟩
  calc
    _ = volume S * ENNReal.ofReal gapForceIncrementCoefficient^(6/5 : ℝ) *
        ∫⁻ s in W, F s^(6/5 : ℝ) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6/5), ← mul_assoc]
      exact lintegral_const_mul'' _ (hFm.pow_const _)
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul'
        (le_refl (volume S * ENNReal.ofReal gapForceIncrementCoefficient^(6/5 : ℝ))) hmass


private theorem force_increment_coefficient_le {C_CZ : ℝ}
    (hC : gapForceIncrementThreshold ≤ C_CZ) :
    ENNReal.ofReal (Real.pi*4/3) * ENNReal.ofReal gapForceIncrementCoefficient^(6/5 : ℝ) ≤
      (3 * ENNReal.ofReal (|C_CZ|+1))^(6/5 : ℝ) := by
  have hπ : ENNReal.ofReal (Real.pi*4/3) ≤ 5 := by
    have h : Real.pi*4/3 ≤ (5 : ℝ) := by linarith only [Real.pi_lt_d2]
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h
  have h5 : (5 : ℝ≥0∞) ≤ 5^(6/5 : ℝ) := by
    simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 5) (by norm_num : (1 : ℝ) ≤ 6/5)
  have hreal : 5 * gapForceIncrementCoefficient ≤ 3*(|C_CZ|+1) := by
    change 5 * gapForceIncrementCoefficient ≤ C_CZ at hC
    have ha := le_abs_self C_CZ
    have hn := abs_nonneg C_CZ
    linarith only [hC,ha,hn]
  have hbase : 5 * ENNReal.ofReal gapForceIncrementCoefficient ≤
      3 * ENNReal.ofReal (|C_CZ|+1) := by
    have h := ENNReal.ofReal_le_ofReal hreal
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat] using h
  calc
    _ ≤ 5^(6/5 : ℝ) * ENNReal.ofReal gapForceIncrementCoefficient^(6/5 : ℝ) :=
      mul_le_mul' (hπ.trans h5) le_rfl
    _ = (5 * ENNReal.ofReal gapForceIncrementCoefficient)^(6/5 : ℝ) :=
      (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)).symm
    _ ≤ _ := ENNReal.rpow_le_rpow hbase (by norm_num)

/-- The force increment has a measurable mass envelope within the affine slot. -/
theorem exists_gap_force_affine_envelope_of_sws
    (ε C_CZ τ R₁ r : ℝ) (KU KD : ℝ≥0∞)
    (hC : gapForceIncrementThreshold ≤ C_CZ) (hτ : 25/3 ≤ τ)
    {z : ParabolicPoint} {ρ : ℝ}
    (hρ : 0 < ρ) (hlo : 1/128 ≤ ρ) (hhi : ρ ≤ 1/2)
    (hr : 0 < r) (hrρ : r ≤ ρ/2)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hQ : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1)
    (hforce : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (f w))^q) ≤ ENNReal.ofReal ε)
    (i : Fin 3) :
    ∃ M : ℝ → ℝ≥0∞,
      AEMeasurable M (volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0)) ∧
      (∀ᵐ s ∂volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0),
        eLpNorm (fun y => gapForceIncrement z hρ u p f i (y,s))
        (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁))^(6/5 : ℝ) ≤ M s) ∧
      (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0, M s) ≤
      originKPAffineASlot q C_CZ ε KU KD *
        ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  let θ := 5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q)
  have hq := hsol.2.2.2.1
  have hr1 : r ≤ 1 := by linarith only [hrρ,hhi]
  have hθ : θ ≤ 3+2*(1-6/(5*q)) := by
    have hh := harmonicRemainder_theta_le_force hq hτ
    dsimp [θ]
    convert hh using 1
    ring
  have hrad := harmonicRemainder_radius_power_le hr
    (show ENNReal.ofReal r ≤ 1 by simpa using ENNReal.ofReal_le_ofReal hr1) hθ
  obtain ⟨M, hMm, hMp, hmass⟩ := exists_gap_force_mass_envelope_of_sws ε R₁ r hρ hlo hhi hr hrρ hsol hdom hQ hforce i
  have hslot := (le_add_right (le_refl
    ((3 * ENNReal.ofReal (|C_CZ|+1))^(6/5 : ℝ) * ENNReal.ofReal ε^(6/(5*q))))).trans
      (harmonicRemainder_two_terms_le_originKPAffineASlot q C_CZ ε KU KD hq)
  refine ⟨M, hMm, hMp, hmass.trans ?_⟩
  calc
    _ ≤ volume (vec3Ball z.1 r) * ENNReal.ofReal gapForceIncrementCoefficient^(6/5 : ℝ) *
        ENNReal.ofReal (r^2)^(1-6/(5*q)) * ENNReal.ofReal ε^(6/(5*q)) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' (measure_mono inter_subset_left) le_rfl) le_rfl) le_rfl
    _ = (ENNReal.ofReal (Real.pi*4/3) * ENNReal.ofReal gapForceIncrementCoefficient^(6/5 : ℝ)) *
        ENNReal.ofReal ε^(6/(5*q)) *
        (ENNReal.ofReal r^(3 : ℝ) * (ENNReal.ofReal r^(2 : ℝ))^(1-6/(5*q))) := by
      rw [volume_vec3Ball_eq, ENNReal.ofReal_pow hr.le]
      norm_num only [ENNReal.rpow_ofNat]
      ring
    _ ≤ (3 * ENNReal.ofReal (|C_CZ|+1))^(6/5 : ℝ) * ENNReal.ofReal ε^(6/(5*q)) *
        ENNReal.ofReal r^θ := mul_le_mul' (mul_le_mul' (force_increment_coefficient_le hC) le_rfl) hrad
    _ ≤ originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal r^θ := mul_le_mul' hslot le_rfl
    _ = _ := by rw [ENNReal.ofReal_rpow_of_pos hr]


end CKN.Core.Step4
