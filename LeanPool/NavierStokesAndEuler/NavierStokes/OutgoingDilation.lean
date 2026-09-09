/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalCompensation
import LeanPool.NavierStokesAndEuler.NavierStokes.ReleaseMoments

/-!
# Actual radial dilation of the constructed outgoing profile

The entrance radius rescales the radial variable. All moment laws below are
proved by change of variables in the actual integrals. The final section
locates the clean terminal switch and the second reserved compensation patch.
No heat edit is applied in this module.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology
open NavierStokes.OutgoingProfile NavierStokes.OutgoingTail

namespace NavierStokes.OutgoingDilation

theorem image_mul_Ioc (R X : ℝ) (hR : 0 < R) :
    (fun x : ℝ => R * x) '' Ioc 0 (X / R) = Ioc 0 X := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨mul_pos hR hu.1, by simpa only [mul_comm] using (le_div_iff₀ hR).mp hu.2⟩
  · intro hx
    refine ⟨x / R, ⟨div_pos hx.1 hR, (div_le_div_iff_of_pos_right hR).mpr hx.2⟩, ?_⟩
    exact mul_div_cancel₀ x hR.ne'

theorem integral_dilate_Ioc (f : ℝ → ℝ) (R X : ℝ) (hR : 0 < R) :
    (∫ x in Ioc 0 X, f (x / R)) = R * ∫ x in Ioc 0 (X / R), f x := by
  rw [← image_mul_Ioc R X hR]
  have hd : ∀ x ∈ Ioc 0 (X / R), HasDerivWithinAt (fun x : ℝ => R * x) R (Ioc 0 (X / R)) x := by
    intro x _
    simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul R).hasDerivWithinAt
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hd
    (fun _ _ _ _ h => mul_left_cancel₀ hR.ne' h)]
  simp only [abs_of_pos hR, smul_eq_mul, mul_div_cancel_left₀ _ hR.ne', integral_const_mul]

theorem integrable_dilate_Ioc (f : ℝ → ℝ) (R X : ℝ) (hR : 0 < R)
    (hf : IntegrableOn f (Ioc 0 (X / R))) :
    IntegrableOn (fun x => f (x / R)) (Ioc 0 X) := by
  rw [← image_mul_Ioc R X hR]
  have hd : ∀ x ∈ Ioc 0 (X / R), HasDerivWithinAt (fun x : ℝ => R * x) R (Ioc 0 (X / R)) x := by
    intro x _
    simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul R).hasDerivWithinAt
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc hd
    (fun _ _ _ _ h => mul_left_cancel₀ hR.ne' h) _).mpr
  simpa only [IntegrableOn, abs_of_pos hR, smul_eq_mul, mul_div_cancel_left₀ _ hR.ne'] using
      hf.const_mul R

theorem integral_dilate_Ioi (f : ℝ → ℝ) (R X : ℝ) (hR : 0 < R) :
    (∫ x in Ioi X, f (x / R)) = R * ∫ x in Ioi (X / R), f x := by
  simpa only [div_eq_mul_inv, inv_inv, smul_eq_mul] using
    integral_comp_mul_right_Ioi f X (inv_pos.mpr hR)

theorem integrable_dilate_Ioi_iff (f : ℝ → ℝ) (R X : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x => f (x / R)) (Ioi X) ↔ IntegrableOn f (Ioi (X / R)) := by
  simpa only [div_eq_mul_inv] using integrableOn_Ioi_comp_mul_right_iff f X (inv_pos.mpr hR)

/-- E, given by `F.E (p.1 / XR, p.2)`. -/
def E (F : Profile) (XR : ℝ) (p : ℝ × ℝ) : ℝ := F.E (p.1 / XR, p.2)
/-- U, given by `F.U (p.1 / XR, p.2)`. -/
def U (F : Profile) (XR : ℝ) (p : ℝ × ℝ) : ℝ := F.U (p.1 / XR, p.2)
/-- H, given by `Real.sqrt (2 * p.1) * E F XR p`. -/
def H (F : Profile) (XR : ℝ) (p : ℝ × ℝ) : ℝ := Real.sqrt (2 * p.1) * E F XR p
/-- Pi, given by `F.Pi (p.1 / XR, p.2)`. -/
def Pi (F : Profile) (XR : ℝ) (p : ℝ × ℝ) : ℝ := F.Pi (p.1 / XR, p.2)

/-- Power E, given by `F.powerE (X / XR)`. -/
def powerE (F : Profile) (XR X : ℝ) : ℝ := F.powerE (X / XR)
/-- Power H, given by `Real.sqrt (2 * X) * powerE F XR X`. -/
def powerH (F : Profile) (XR X : ℝ) : ℝ := Real.sqrt (2 * X) * powerE F XR X

/-- Energy density, given by `U F XR (X, eta) ^ 2 - E F XR (X, eta) ^ 2 / 2`. -/
def energyDensity (F : Profile) (XR eta X : ℝ) : ℝ := U F XR (X, eta) ^ 2 - E F XR (X, eta) ^ 2 / 2
/-- Canonical kernel, given by `E F XR (X, eta) ^ 2 / X`. -/
def canonicalKernel (F : Profile) (XR eta X : ℝ) : ℝ := E F XR (X, eta) ^ 2 / X

/-- M, given by `∫ u in Ioc 0 X, U F XR (u, eta)`. -/
def M (F : Profile) (XR eta X : ℝ) : ℝ := ∫ u in Ioc 0 X, U F XR (u, eta)
/-- I, given by `∫ u in Ioc 0 X, H F XR (u, eta)`. -/
def I (F : Profile) (XR eta X : ℝ) : ℝ := ∫ u in Ioc 0 X, H F XR (u, eta)
/-- J, given by `∫ u in Ioc 0 X, H F XR (u, eta) * U F XR (u, eta)`. -/
def J (F : Profile) (XR eta X : ℝ) : ℝ := ∫ u in Ioc 0 X, H F XR (u, eta) * U F XR (u, eta)
/-- S, given by `∫ u in Ioc 0 X, energyDensity F XR eta u`. -/
def S (F : Profile) (XR eta X : ℝ) : ℝ := ∫ u in Ioc 0 X, energyDensity F XR eta u
/-- Total S, given by `∫ u in Ioi 0, energyDensity F XR eta u`. -/
def totalS (F : Profile) (XR eta : ℝ) : ℝ := ∫ u in Ioi 0, energyDensity F XR eta u
/-- Renormalized I, given by `∫ u in Ioi 0, H F XR (u, eta) - powerH F XR u`. -/
def renormalizedI (F : Profile) (XR eta : ℝ) : ℝ := ∫ u in Ioi 0, H F XR (u, eta) - powerH F XR u
/-- Axis datum, given by `-(1 / 2 : ℝ) * ∫ u in Ioi 0, canonicalKernel F XR eta u`. -/
def axisDatum (F : Profile) (XR eta : ℝ) : ℝ := -(1 / 2 : ℝ) * ∫ u in Ioi 0, canonicalKernel F XR
    eta u

theorem H_scaling (F : Profile) (XR : ℝ) (hXR : 0 < XR) (p : ℝ × ℝ) :
    H F XR p = Real.sqrt XR * F.H (p.1 / XR, p.2) := by
  unfold H E Profile.H
  rw [← mul_assoc, ← Real.sqrt_mul hXR.le]
  congr 2
  field_simp

theorem powerH_scaling (F : Profile) (XR X : ℝ) (hXR : 0 < XR) :
    powerH F XR X = Real.sqrt XR * F.powerH (X / XR) := by
  unfold powerH powerE Profile.powerH
  rw [← mul_assoc, ← Real.sqrt_mul hXR.le]
  congr 2
  field_simp

theorem energyDensity_scaling (F : Profile) (XR eta X : ℝ) :
    energyDensity F XR eta X = F.energyDensity eta (X / XR) := rfl

theorem canonicalKernel_scaling (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) :
    canonicalKernel F XR eta X = XR⁻¹ * F.canonicalKernel eta (X / XR) := by
  unfold canonicalKernel E Profile.canonicalKernel
  by_cases hX : X = 0
  · simp [hX]
  · field_simp

theorem M_scaling (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) :
    M F XR eta X = XR * F.M eta (X / XR) :=
  integral_dilate_Ioc (fun u => F.U (u, eta)) XR X hXR

theorem I_scaling (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) :
    I F XR eta X = (XR * Real.sqrt XR) * ∫ u in Ioc 0 (X / XR), F.H (u, eta) := by
  unfold I
  simp_rw [H_scaling F XR hXR]
  rw [integral_const_mul, integral_dilate_Ioc (fun u => F.H (u, eta)) XR X hXR]
  ring

theorem J_scaling (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) :
    J F XR eta X = (XR * Real.sqrt XR) * F.J eta (X / XR) := by
  unfold J Profile.J
  simp_rw [H_scaling F XR hXR, U, mul_assoc]
  rw [integral_const_mul, integral_dilate_Ioc (fun u => F.H (u, eta) * F.U (u, eta)) XR X hXR]
  ring

theorem S_scaling (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) :
    S F XR eta X = XR * ∫ u in Ioc 0 (X / XR), F.energyDensity eta u :=
  integral_dilate_Ioc (F.energyDensity eta) XR X hXR

theorem totalS_scaling (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    totalS F XR eta = XR * F.totalS eta := by
  simpa only [totalS, energyDensity_scaling, zero_div, Profile.totalS] using
    integral_dilate_Ioi (F.energyDensity eta) XR 0 hXR

theorem renormalizedI_scaling (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    renormalizedI F XR eta = (XR * Real.sqrt XR) *
      ∫ u in Ioi 0, F.H (u, eta) - F.powerH u := by
  unfold renormalizedI
  simp_rw [H_scaling F XR hXR, powerH_scaling F XR _ hXR, ← mul_sub]
  rw [integral_const_mul, integral_dilate_Ioi (fun u => F.H (u, eta) - F.powerH u) XR 0 hXR,
      zero_div]
  ring

theorem positive (F : Profile) (XR : ℝ) (p : ℝ × ℝ) : 0 < E F XR p := F.E_pos _

theorem dilation_contDiffOn (XR : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.1 / XR, p.2)) domain :=
  (contDiff_fst.div_const XR).contDiffOn.prodMk contDiffOn_snd

theorem dilation_mapsTo (XR : ℝ) (hXR : 0 < XR) :
    MapsTo (fun p : ℝ × ℝ => (p.1 / XR, p.2)) domain domain :=
  fun _ hp => ⟨div_pos hp.1 hXR, mem_univ _⟩

theorem E_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) : ContDiffOn ℝ ∞ (E F XR) domain :=
  F.E_contDiffOn.comp (dilation_contDiffOn XR) (dilation_mapsTo XR hXR)

theorem U_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) : ContDiffOn ℝ ∞ (U F XR) domain :=
  F.U_contDiffOn.comp (dilation_contDiffOn XR) (dilation_mapsTo XR hXR)

theorem H_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) : ContDiffOn ℝ ∞ (H F XR) domain :=
  ((contDiffOn_const.mul contDiffOn_fst).sqrt
    (fun _ hp => ne_of_gt (mul_pos (by norm_num) hp.1))).mul (E_contDiffOn F XR hXR)

theorem Pi_contDiffOn (F : Profile) (XR : ℝ) (hXR : 0 < XR) : ContDiffOn ℝ ∞ (Pi F XR) domain :=
  F.Pi_contDiffOn.comp (dilation_contDiffOn XR) (dilation_mapsTo XR hXR)

/-- Family domain, given by `Ioi 0 ×ˢ domain`. -/
def familyDomain : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ domain

theorem dilation_family_contDiffOn :
    ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => (z.2.1 / z.1, z.2.2)) familyDomain :=
  (contDiff_snd.fst.contDiffOn.div contDiff_fst.contDiffOn
    (fun _ hz => ne_of_gt hz.1)).prodMk contDiff_snd.snd.contDiffOn

theorem dilation_family_mapsTo :
    MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.2.1 / z.1, z.2.2)) familyDomain domain := by
  intro z hz
  change 0 < z.2.1 / z.1 ∧ z.2.2 ∈ (univ : Set ℝ)
  exact ⟨div_pos hz.2.1 hz.1, mem_univ _⟩

theorem E_family_contDiffOn (F : Profile) :
    ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => E F z.1 z.2) familyDomain :=
  F.E_contDiffOn.comp dilation_family_contDiffOn dilation_family_mapsTo

theorem U_family_contDiffOn (F : Profile) :
    ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => U F z.1 z.2) familyDomain :=
  F.U_contDiffOn.comp dilation_family_contDiffOn dilation_family_mapsTo

theorem H_family_contDiffOn (F : Profile) :
    ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => H F z.1 z.2) familyDomain :=
  ((contDiffOn_const.mul contDiff_snd.fst.contDiffOn).sqrt
    (fun _ hz => ne_of_gt (mul_pos (by norm_num) hz.2.1))).mul (E_family_contDiffOn F)

theorem Pi_family_contDiffOn (F : Profile) :
    ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => Pi F z.1 z.2) familyDomain :=
  F.Pi_contDiffOn.comp dilation_family_contDiffOn dilation_family_mapsTo

theorem mass_integrable (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    IntegrableOn (fun X => U F XR (X, eta)) (Ioi 0) := by
  apply (integrable_dilate_Ioi_iff (fun X => F.U (X, eta)) XR 0 hXR).mpr
  simpa only [zero_div] using F.mass_integrable eta

theorem angular_integrable (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    IntegrableOn (fun X => H F XR (X, eta) * U F XR (X, eta)) (Ioi 0) := by
  have hi := (integrable_dilate_Ioi_iff (fun X => F.H (X, eta) * F.U (X, eta)) XR 0 hXR).mpr
    (by simpa only [zero_div] using F.angular_integrable eta)
  simpa only [IntegrableOn, H_scaling F XR hXR, U, mul_assoc] using hi.const_mul (Real.sqrt XR)

theorem energy_integrable (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    IntegrableOn (energyDensity F XR eta) (Ioi 0) := by
  apply (integrable_dilate_Ioi_iff (F.energyDensity eta) XR 0 hXR).mpr
  simpa only [zero_div] using F.energy_integrable eta

theorem renormalized_integrable (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    IntegrableOn (fun X => H F XR (X, eta) - powerH F XR X) (Ioi 0) := by
  have hi := (integrable_dilate_Ioi_iff (fun X => F.H (X, eta) - F.powerH X) XR 0 hXR).mpr
    (by simpa only [zero_div] using F.renormalized_integrable eta)
  simpa only [IntegrableOn, H_scaling F XR hXR, powerH_scaling F XR _ hXR, mul_sub] using
      hi.const_mul (Real.sqrt XR)

theorem normalized_I_integrable (F : Profile) (eta X : ℝ) (hX : 0 < X) :
    IntegrableOn (fun u => F.H (u, eta)) (Ioc 0 X) := by
  have hi := ReleaseMoments.ResetWitness.radial_history_integrable F.reset eta
    (le_max_left (0 : ℝ) (Real.log X))
  apply hi.mono_set
  intro u hu
  refine ⟨hu.1, hu.2.trans ?_⟩
  conv_lhs => rw [← Real.exp_log hX]
  exact Real.exp_le_exp.mpr (le_max_right _ _)

theorem I_integrable (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    IntegrableOn (fun u => H F XR (u, eta)) (Ioc 0 X) := by
  have hi := integrable_dilate_Ioc (fun u => F.H (u, eta)) XR X hXR
    (normalized_I_integrable F eta (X / XR) (div_pos hX hXR))
  simpa only [IntegrableOn, H_scaling F XR hXR] using hi.const_mul (Real.sqrt XR)

theorem mass_total_zero (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    (∫ X in Ioi 0, U F XR (X, eta)) = 0 := by
  change (∫ X in Ioi 0, F.U (X / XR, eta)) = 0
  rw [integral_dilate_Ioi (fun X => F.U (X, eta)) XR 0 hXR, zero_div, F.mass_integral_zero,
      mul_zero]

theorem angular_total_zero (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    (∫ X in Ioi 0, H F XR (X, eta) * U F XR (X, eta)) = 0 := by
  simp_rw [H_scaling F XR hXR, U, mul_assoc]
  rw [integral_const_mul, integral_dilate_Ioi (fun X => F.H (X, eta) * F.U (X, eta)) XR 0 hXR,
    zero_div, F.angular_integral_zero, mul_zero, mul_zero]

theorem renormalized_zero (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) : renormalizedI F XR eta = 0 :=
    by
  rw [renormalizedI_scaling F XR eta hXR, F.renormalized_angular_moment, mul_zero]

theorem energy_zero {F : Profile} {C : ℝ} (hF : Specification F C)
    (XR eta : ℝ) (hXR : 0 < XR) (heta : eta ^ 2 ≤ 1) : totalS F XR eta = 0 := by
  rw [totalS_scaling F XR eta hXR, hF.energy_zero eta heta, mul_zero]

theorem canonicalKernel_integral (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) :
    (∫ u in Ioi X, canonicalKernel F XR eta u) = ∫ u in Ioi (X / XR), F.canonicalKernel eta u := by
  simp_rw [canonicalKernel_scaling F XR eta _ hXR]
  rw [integral_const_mul, integral_dilate_Ioi (F.canonicalKernel eta) XR X hXR]
  field_simp

theorem canonicalKernel_integrable (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    IntegrableOn (canonicalKernel F XR eta) (Ioi 0) := by
  have hi := (integrable_dilate_Ioi_iff (F.canonicalKernel eta) XR 0 hXR).mpr
    (by simpa only [zero_div] using F.canonicalKernel_integrable eta)
  have he : canonicalKernel F XR eta = fun X => XR⁻¹ * F.canonicalKernel eta (X / XR) :=
    funext (fun X => canonicalKernel_scaling F XR eta X hXR)
  rw [he]
  exact hi.const_mul XR⁻¹

theorem Pi_canonical (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    Pi F XR (X, eta) = -(1 / 2 : ℝ) * ∫ u in Ioi X, E F XR (u, eta) ^ 2 / u := by
  change F.Pi (X / XR, eta) = -(1 / 2 : ℝ) * ∫ u in Ioi X, canonicalKernel F XR eta u
  rw [canonicalKernel_integral F XR eta X hXR, F.Pi_canonical eta (div_pos hX hXR)]
  rfl

theorem normalized_axisDatum_integral (F : Profile) (eta : ℝ) :
    F.axisDatum eta = -(1 / 2 : ℝ) * ∫ u in Ioi 0, F.canonicalKernel eta u := by
  rw [← Real.range_exp, ← image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn]
  simp_rw [F.canonicalKernel_comp_exp]
  rw [setIntegral_univ]
  rfl

theorem axisDatum_unchanged (F : Profile) (XR : ℝ) (hXR : 0 < XR) : axisDatum F XR = F.axisDatum :=
    by
  funext eta
  rw [axisDatum, canonicalKernel_integral F XR eta 0 hXR, zero_div, ← normalized_axisDatum_integral]

theorem Pi_tendsto_axis (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    Tendsto (fun X => Pi F XR (X, eta)) (𝓝[>] (0 : ℝ)) (𝓝 (axisDatum F XR eta)) := by
  rw [axisDatum_unchanged F XR hXR]
  apply (F.Pi_tendsto_axis eta).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have ht : Tendsto (fun X : ℝ => X / XR) (𝓝 (0 : ℝ)) (𝓝 (0 / XR)) :=
      (continuous_id.div_const XR).tendsto 0
    simpa only [zero_div] using ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with X hX
    exact div_pos hX hXR

/-- Clock, given by `Real.log (X / XR)`. -/
def clock (XR X : ℝ) : ℝ := Real.log (X / XR)
/-- Radius, given by `XR * Real.exp y`. -/
def radius (XR y : ℝ) : ℝ := XR * Real.exp y

theorem radius_pos (XR y : ℝ) (hXR : 0 < XR) : 0 < radius XR y := mul_pos hXR (Real.exp_pos y)

theorem clock_radius (XR y : ℝ) (hXR : 0 < XR) : clock XR (radius XR y) = y := by
  simp only [clock, radius, mul_div_cancel_left₀ _ hXR.ne', Real.log_exp]

theorem clock_center (XR X y : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    y + Real.log (X / radius XR y) = clock XR X := by
  rw [clock, radius, Real.log_div hX.ne' (mul_pos hXR (Real.exp_pos y)).ne',
    Real.log_mul hXR.ne' (Real.exp_pos y).ne', Real.log_exp, Real.log_div hX.ne' hXR.ne']
  ring

theorem clock_radius_mul (XR y x : ℝ) (hXR : 0 < XR) (hx : 0 < x) :
    clock XR (radius XR y * x) = y + Real.log x := by
  have h := clock_center XR (radius XR y * x) y hXR (mul_pos (radius_pos XR y hXR) hx)
  rw [mul_div_cancel_left₀ _ (radius_pos XR y hXR).ne'] at h
  exact h.symm

theorem radius_le_iff (XR X y : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    radius XR y ≤ X ↔ y ≤ clock XR X := by
  rw [clock, Real.le_log_iff_exp_le (div_pos hX hXR), le_div_iff₀ hXR]
  simp only [radius, mul_comm]

theorem radius_lt_iff (XR X y : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    radius XR y < X ↔ y < clock XR X := by
  rw [clock, Real.lt_log_iff_exp_lt (div_pos hX hXR), lt_div_iff₀ hXR]
  simp only [radius, mul_comm]

/-- Pulse end radius, given by `radius XR F.data.core.endpoint`. -/
def pulseEndRadius (F : Profile) (XR : ℝ) : ℝ := radius XR F.data.core.endpoint
/-- Tail radius, given by `radius XR (tailEnd F.data)`. -/
def tailRadius (F : Profile) (XR : ℝ) : ℝ := radius XR (tailEnd F.data)
/-- Switch radius, given by `radius XR (HeatTailEdit.switchStart F.data)`. -/
def switchRadius (F : Profile) (XR : ℝ) : ℝ := radius XR (HeatTailEdit.switchStart F.data)
/-- Carrier amplitude, given by `HeatTailEdit.outgoingAmplitude F.data`. -/
def carrierAmplitude (F : Profile) : ℝ := HeatTailEdit.outgoingAmplitude F.data

theorem switchRadius_eq (F : Profile) (XR : ℝ) :
    switchRadius F XR = XR * Real.exp (tailStart F.data + 1 / 5) := rfl

theorem switchRadius_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) : 0 < switchRadius F XR :=
  radius_pos XR _ hXR

theorem carrierAmplitude_pos (F : Profile) : 0 < carrierAmplitude F :=
  HeatTailEdit.outgoingAmplitude_pos F.data

theorem ideal_prefix (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X) (hX' : X ≤ XR) :
    E F XR (X, eta) = F.data.core.P * OutgoingSchedule.shape eta * (X / XR) ^ (1 / 10 : ℝ) ∧
    U F XR (X, eta) = 4 * eta ∧
    Pi F XR (X, eta) = axisDatum F XR eta +
      (5 / 2) * F.data.core.P ^ 2 * OutgoingSchedule.shape eta ^ 2 * (X / XR) ^ (1 / 5 : ℝ) := by
  have hx := div_pos hX hXR
  have hx' := (div_le_one hXR).mpr hX'
  rw [axisDatum_unchanged F XR hXR]
  exact ⟨F.E_ideal eta hx hx', F.U_ideal eta hx hx', F.Pi_ideal eta hx hx'⟩

theorem after_pulse (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X)
    (hfar : pulseEndRadius F XR ≤ X) :
    U F XR (X, eta) = 0 ∧ M F XR eta X = 0 ∧ J F XR eta X = 0 := by
  have hy := (radius_le_iff XR X F.data.core.endpoint hXR hX).mp hfar
  obtain ⟨hm, hj⟩ := F.moments_after eta (div_pos hX hXR) hy
  exact ⟨F.U_after eta hy, by rw [M_scaling F XR eta X hXR, hm, mul_zero],
    by rw [J_scaling F XR eta X hXR, hj, mul_zero]⟩

theorem powerE_coefficient (F : Profile) (XR X : ℝ) (hXR : 0 < XR) (hX : 0 < X) :
    powerE F XR X = (powerConstant F.data * XR ^ (1 / 2 + F.data.h)) * X ^ (-(1 / 2 + F.data.h)) :=
        by
  rw [powerE, Profile.powerE, Real.div_rpow hX.le hXR.le, Real.rpow_neg hXR.le, div_inv_eq_mul]
  ring

theorem eventual_power (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X)
    (hfar : tailRadius F XR ≤ X) :
    U F XR (X, eta) = 0 ∧ E F XR (X, eta) = powerE F XR X ∧
      I F XR eta X = X * H F XR (X, eta) / (1 - F.data.h) := by
  have hy := (radius_le_iff XR X (tailEnd F.data) hXR hX).mp hfar
  refine ⟨F.U_after eta (F.tailEnd_after_endpoint.trans hy), F.E_eventual eta (div_pos hX hXR) hy,
      ?_⟩
  rw [I_scaling F XR eta X hXR, F.angular_history_eventual eta (div_pos hX hXR) hy,
    H_scaling F XR hXR]
  field_simp [hXR.ne', F.data.one_sub_h_pos.ne']

theorem E_eq_clean_switch_profile (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR)
    (hX : switchRadius F XR ≤ X) :
    E F XR (X, eta) = HeatTailEdit.outgoingProfile F.data (switchRadius F XR) eta X := by
  have hp : 0 < X := (switchRadius_pos F XR hXR).trans_le hX
  have hy := (radius_le_iff XR X (HeatTailEdit.switchStart F.data) hXR hp).mp hX
  have hrel : F.data.releaseStart ≤ clock XR X := by
    have ht := tailStart_gt_release F.data
    dsimp only [HeatTailEdit.switchStart] at hy
    linarith
  have hout : clock XR X ∉ Ioo (F.data.releaseStart - 4) F.data.releaseStart := by
    intro h
    exact (not_lt_of_ge hrel) h.2
  change UniformAngularReset.correctedAngular F.data F.reset.coefficients (clock XR X, eta) =
    finalAngular F.data (HeatTailEdit.switchStart F.data + Real.log (X / switchRadius F XR), eta)
  rw [UniformAngularReset.correctedAngular_unchanged F.data F.reset.coefficients eta hout]
  rw [switchRadius, clock_center XR X (HeatTailEdit.switchStart F.data) hXR hp]

theorem E_tail_factorization (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR)
    (hX : switchRadius F XR ≤ X) :
    E F XR (X, eta) = HeatTailEdit.powerTail F.data.h (carrierAmplitude F)
      (switchRadius F XR) (HeatTailEdit.outgoingShape F.data) X := by
  rw [E_eq_clean_switch_profile F XR eta X hXR hX,
    HeatTailEdit.outgoingProfile_eq_powerTail F.data (switchRadius_pos F XR hXR) hX]
  rfl

theorem E_at_switch (F : Profile) (XR eta : ℝ) (hXR : 0 < XR) :
    E F XR (switchRadius F XR, eta) = carrierAmplitude F * (1 - F.data.rho) := by
  rw [E_eq_clean_switch_profile F XR eta (switchRadius F XR) hXR le_rfl,
    HeatTailEdit.outgoingProfile_at_switch F.data (switchRadius_pos F XR hXR)]
  rfl

theorem switchRadius_tendsto (F : Profile) : Tendsto (switchRadius F) atTop atTop := by
  exact tendsto_id.atTop_mul_const (Real.exp_pos (HeatTailEdit.switchStart F.data))

/-! ## The actual second reserved shaped-wait patch -/

/-- Patch clock, given by `F.data.core.pulseStart - 20`. -/
def patchClock (F : Profile) : ℝ := F.data.core.pulseStart - 20
/-- Patch radius, given by `radius XR (patchClock F)`. -/
def patchRadius (F : Profile) (XR : ℝ) : ℝ := radius XR (patchClock F)
/-- Patch ratio, given by `Real.exp (patchClock F - HeatTailEdit.switchStart F.data)`. -/
def patchRatio (F : Profile) : ℝ := Real.exp (patchClock F - HeatTailEdit.switchStart F.data)
/-- Patch amplitude, given by `OutgoingSchedule.radialAmplitude F.data.core.P
F.data.core.dropLength F.data.core.lam (patchClock F)`. -/
def patchAmplitude (F : Profile) : ℝ :=
  OutgoingSchedule.radialAmplitude F.data.core.P F.data.core.dropLength F.data.core.lam (patchClock
      F)
/-- Shaped patch amplitude, given by `patchAmplitude F * OutgoingSchedule.shape eta`. -/
def shapedPatchAmplitude (F : Profile) (eta : ℝ) : ℝ := patchAmplitude F * OutgoingSchedule.shape
    eta

/-- In the coordinate `x = X / patchRadius`, the second reserved patch is
the fixed interval `(1, exp 5)`. -/
def compensationPatch : TerminalCompensation.Patch where
  left := 1
  right := Real.exp 5
  left_pos := by norm_num
  ordered := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show (0 : ℝ) < 5 by norm_num)

theorem patchClock_after_hold (F : Profile) : F.data.core.holdStart < patchClock F := by
  dsimp only [patchClock, OutgoingSchedule.Parameters.pulseStart]
  linarith [F.data.core.wait_gt]

theorem patchClock_end_before_pulse (F : Profile) : patchClock F + 5 < F.data.core.pulseStart := by
  dsimp only [patchClock]
  linarith

theorem patchClock_end_before_switch (F : Profile) :
    patchClock F + 5 < HeatTailEdit.switchStart F.data := by
  have hp : F.data.core.pulseStart < F.data.core.endpoint := by
    dsimp only [OutgoingSchedule.Parameters.endpoint]
    linarith [F.data.core.pulseLength_pos]
  have hf := flattenEnd_gt_core F.data
  have hr := releaseStart_gt_flattenEnd F.data
  have ht := tailStart_gt_release F.data
  have hh := patchClock_end_before_pulse F
  dsimp only [HeatTailEdit.switchStart]
  linarith

theorem patchRadius_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) : 0 < patchRadius F XR :=
  radius_pos XR _ hXR

theorem patchAmplitude_pos (F : Profile) : 0 < patchAmplitude F :=
  mul_pos F.data.core.P_pos (Real.exp_pos _)

theorem shapedPatchAmplitude_pos (F : Profile) (eta : ℝ) : 0 < shapedPatchAmplitude F eta :=
  mul_pos (patchAmplitude_pos F) (OutgoingSchedule.shape_pos eta)

theorem shapedPatchAmplitude_contDiff (F : Profile) : ContDiff ℝ ∞ (shapedPatchAmplitude F) :=
  contDiff_const.mul OutgoingSchedule.shape_contDiff

theorem patchRatio_pos (F : Profile) : 0 < patchRatio F := Real.exp_pos _

theorem patchRadius_eq_ratio (F : Profile) (XR : ℝ) :
    patchRadius F XR = patchRatio F * switchRadius F XR := by
  dsimp only [patchRadius, patchRatio, switchRadius, radius]
  calc
    _ = XR * (Real.exp (patchClock F - HeatTailEdit.switchStart F.data) *
        Real.exp (HeatTailEdit.switchStart F.data)) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = _ := by ring

theorem patchRatio_right_lt_one (F : Profile) : patchRatio F * compensationPatch.right < 1 := by
  change Real.exp (patchClock F - HeatTailEdit.switchStart F.data) * Real.exp 5 < 1
  rw [← Real.exp_add, Real.exp_lt_one_iff]
  linarith [patchClock_end_before_switch F]

theorem patch_before_switch (F : Profile) (XR : ℝ) (hXR : 0 < XR) :
    patchRadius F XR * compensationPatch.right < switchRadius F XR := by
  calc
    _ = (patchRatio F * compensationPatch.right) * switchRadius F XR := by
      rw [patchRadius_eq_ratio]
      ring
    _ < _ := by simpa only [one_mul] using
      mul_lt_mul_of_pos_right (patchRatio_right_lt_one F) (switchRadius_pos F XR hXR)

theorem patch_switch_disjoint (F : Profile) (XR : ℝ) (hXR : 0 < XR) :
    Disjoint (Icc (patchRadius F XR) (patchRadius F XR * compensationPatch.right))
      (Ici (switchRadius F XR)) := by
  apply Set.disjoint_left.mpr
  intro X hX hK
  have h := patch_before_switch F XR hXR
  exact (not_lt_of_ge hK) (hX.2.trans_lt h)

theorem patch_log_bounds {x : ℝ} (hx : x ∈ Icc compensationPatch.left compensationPatch.right) :
    0 < x ∧ 0 ≤ Real.log x ∧ Real.log x ≤ 5 := by
  have hp : 0 < x := compensationPatch.left_pos.trans_le hx.1
  exact ⟨hp, Real.log_nonneg hx.1, (Real.log_le_iff_le_exp hp).mpr hx.2⟩

theorem U_on_patch (F : Profile) (XR eta x : ℝ) (hXR : 0 < XR)
    (hx : x ∈ Icc compensationPatch.left compensationPatch.right) :
    U F XR (patchRadius F XR * x, eta) = 0 := by
  obtain ⟨hp, hlo, hhi⟩ := patch_log_bounds hx
  change OutgoingSchedule.axial F.data.core F.amp (clock XR (patchRadius F XR * x), eta) = 0
  rw [patchRadius, clock_radius_mul XR (patchClock F) x hXR hp]
  apply OutgoingSchedule.axial_shaped_wait
  · linarith [patchClock_after_hold F]
  · linarith [patchClock_end_before_pulse F]

theorem E_on_patch (F : Profile) (XR eta x : ℝ) (hXR : 0 < XR)
    (hx : x ∈ Icc compensationPatch.left compensationPatch.right) :
    E F XR (patchRadius F XR * x, eta) =
      shapedPatchAmplitude F eta * x ^ (-(1 / 2 + F.data.core.lam)) := by
  obtain ⟨hp, hlo, hhi⟩ := patch_log_bounds hx
  have hcore : patchClock F + Real.log x ≤ F.data.core.endpoint := by
    have hb := patchClock_end_before_pulse F
    dsimp only [OutgoingSchedule.Parameters.endpoint]
    linarith [F.data.core.pulseLength_pos]
  change F.logE (clock XR (patchRadius F XR * x), eta) = _
  rw [patchRadius, clock_radius_mul XR (patchClock F) x hXR hp, F.logE_before eta hcore,
    OutgoingSchedule.angular]
  rw [OutgoingSchedule.radialAmplitude_hold (P := F.data.core.P) F.data.core.dropLength_pos.le
    (show F.data.core.dropLength + 2 ≤ patchClock F from (patchClock_after_hold F).le)
    (show patchClock F ≤ patchClock F + Real.log x by linarith)]
  have he : patchClock F + Real.log x - patchClock F = Real.log x := by ring
  rw [he, Real.rpow_def_of_pos hp]
  have hex : Real.exp (-(1 / 2 + F.data.core.lam) * Real.log x) =
      Real.exp (Real.log x * -(1 / 2 + F.data.core.lam)) := by congr 1; ring
  rw [hex]
  unfold shapedPatchAmplitude patchAmplitude
  ring

/-- The actual second reserved patch has the exact shaped power used by
the terminal compensation solver, and the axial field is zero there. -/
theorem patch_fields (F : Profile) (XR eta x : ℝ) (hXR : 0 < XR)
    (hx : x ∈ Icc compensationPatch.left compensationPatch.right) :
    U F XR (patchRadius F XR * x, eta) = 0 ∧
      E F XR (patchRadius F XR * x, eta) =
        shapedPatchAmplitude F eta * x ^ (-(1 / 2 + F.data.core.lam)) :=
  ⟨U_on_patch F XR eta x hXR hx, E_on_patch F XR eta x hXR hx⟩

theorem patch_model (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR)
    (hX : X / patchRadius F XR ∈ Icc compensationPatch.left compensationPatch.right) :
    E F XR (X, eta) = TerminalCompensation.cleanProfile F.data.core.lam
      (patchRadius F XR) (shapedPatchAmplitude F eta) X := by
  have he := E_on_patch F XR eta (X / patchRadius F XR) hXR hX
  rw [mul_div_cancel₀ X (patchRadius_pos F XR hXR).ne'] at he
  rw [he]
  unfold TerminalCompensation.cleanProfile TerminalCompensation.baseProfile
      TerminalCompensation.slope
  congr 2
  ring

theorem correction_zero_after_switch (F : Profile) (XR X : ℝ) (hXR : 0 < XR)
    (c : TerminalCompensation.Coeff) (hX : switchRadius F XR ≤ X) :
    TerminalCompensation.correction compensationPatch c (X / patchRadius F XR) = 0 := by
  by_contra hn
  have hs := TerminalCompensation.correction_support compensationPatch c hn
  have he : X ≤ patchRadius F XR * compensationPatch.right := by
    simpa only [mul_comm] using (div_le_iff₀ (patchRadius_pos F XR hXR)).mp hs.2
  exact (not_lt_of_ge hX) (he.trans_lt (patch_before_switch F XR hXR))

/-- Any additive correction on this actual patch leaves `E*U` pointwise
unchanged, before solving its three compensation moments. -/
theorem correction_times_U_zero (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR)
    (c : TerminalCompensation.Coeff) :
    TerminalCompensation.correction compensationPatch c (X / patchRadius F XR) * U F XR (X, eta) =
        0 := by
  by_cases hn : TerminalCompensation.correction compensationPatch c (X / patchRadius F XR) = 0
  · rw [hn, zero_mul]
  · have hs := TerminalCompensation.correction_support compensationPatch c hn
    have hu := U_on_patch F XR eta (X / patchRadius F XR) hXR hs
    rw [mul_div_cancel₀ X (patchRadius_pos F XR hXR).ne'] at hu
    rw [hu, mul_zero]

/-- A specification for actual fields in the unnormalized radial variable. -/
structure DilatedSpecification (F : Profile) (XR : ℝ) : Prop where
  angular_smooth : ContDiffOn ℝ ∞ (E F XR) domain
  axial_smooth : ContDiffOn ℝ ∞ (U F XR) domain
  momentum_smooth : ContDiffOn ℝ ∞ (H F XR) domain
  pressure_smooth : ContDiffOn ℝ ∞ (Pi F XR) domain
  angular_positive : ∀ p ∈ domain, 0 < E F XR p
  mass_integrable : ∀ eta : ℝ, IntegrableOn (fun X => U F XR (X, eta)) (Ioi 0)
  angular_integrable : ∀ eta : ℝ, IntegrableOn (fun X => H F XR (X, eta) * U F XR (X, eta)) (Ioi 0)
  mass_zero : ∀ eta : ℝ, (∫ X in Ioi 0, U F XR (X, eta)) = 0
  angular_zero : ∀ eta : ℝ, (∫ X in Ioi 0, H F XR (X, eta) * U F XR (X, eta)) = 0
  after_pulse : ∀ eta X : ℝ, 0 < X → pulseEndRadius F XR ≤ X →
    U F XR (X, eta) = 0 ∧ M F XR eta X = 0 ∧ J F XR eta X = 0
  energy_integrable : ∀ eta : ℝ, IntegrableOn (energyDensity F XR eta) (Ioi 0)
  energy_zero : ∀ eta : ℝ, eta ^ 2 ≤ 1 → totalS F XR eta = 0
  renormalized_integrable : ∀ eta : ℝ,
    IntegrableOn (fun X => H F XR (X, eta) - powerH F XR X) (Ioi 0)
  renormalized_zero : ∀ eta : ℝ, renormalizedI F XR eta = 0
  eventual_power : ∀ eta X : ℝ, 0 < X → tailRadius F XR ≤ X →
    U F XR (X, eta) = 0 ∧ E F XR (X, eta) = powerE F XR X ∧
      I F XR eta X = X * H F XR (X, eta) / (1 - F.data.h)
  ideal_prefix : ∀ eta X : ℝ, 0 < X → X ≤ XR →
    E F XR (X, eta) = F.data.core.P * OutgoingSchedule.shape eta * (X / XR) ^ (1 / 10 : ℝ) ∧
    U F XR (X, eta) = 4 * eta ∧
    Pi F XR (X, eta) = axisDatum F XR eta +
      (5 / 2) * F.data.core.P ^ 2 * OutgoingSchedule.shape eta ^ 2 * (X / XR) ^ (1 / 5 : ℝ)
  pressure_integrable : ∀ eta : ℝ, IntegrableOn (canonicalKernel F XR eta) (Ioi 0)
  pressure_canonical : ∀ eta X : ℝ, 0 < X →
    Pi F XR (X, eta) = -(1 / 2 : ℝ) * ∫ u in Ioi X, E F XR (u, eta) ^ 2 / u
  axis_unchanged : axisDatum F XR = F.axisDatum
  axis_limit : ∀ eta : ℝ,
    Tendsto (fun X => Pi F XR (X, eta)) (𝓝[>] (0 : ℝ)) (𝓝 (axisDatum F XR eta))
  fixed_switch_amplitude : ∀ eta : ℝ,
    E F XR (switchRadius F XR, eta) = carrierAmplitude F * (1 - F.data.rho)
  shaped_patch : ∀ eta x : ℝ, x ∈ Icc compensationPatch.left compensationPatch.right →
    U F XR (patchRadius F XR * x, eta) = 0 ∧
    E F XR (patchRadius F XR * x, eta) =
      shapedPatchAmplitude F eta * x ^ (-(1 / 2 + F.data.core.lam))
  patch_disjoint : Disjoint (Icc (patchRadius F XR) (patchRadius F XR * compensationPatch.right))
    (Ici (switchRadius F XR))

theorem preserves_specification {F : Profile} {C : ℝ} (hF : Specification F C)
    (XR : ℝ) (hXR : 0 < XR) : DilatedSpecification F XR where
  angular_smooth := E_contDiffOn F XR hXR
  axial_smooth := U_contDiffOn F XR hXR
  momentum_smooth := H_contDiffOn F XR hXR
  pressure_smooth := Pi_contDiffOn F XR hXR
  angular_positive := fun p _ => positive F XR p
  mass_integrable := fun eta => mass_integrable F XR eta hXR
  angular_integrable := fun eta => angular_integrable F XR eta hXR
  mass_zero := fun eta => mass_total_zero F XR eta hXR
  angular_zero := fun eta => angular_total_zero F XR eta hXR
  after_pulse := fun eta X hX hfar => after_pulse F XR eta X hXR hX hfar
  energy_integrable := fun eta => energy_integrable F XR eta hXR
  energy_zero := fun eta heta => energy_zero hF XR eta hXR heta
  renormalized_integrable := fun eta => renormalized_integrable F XR eta hXR
  renormalized_zero := fun eta => renormalized_zero F XR eta hXR
  eventual_power := fun eta X hX hfar => eventual_power F XR eta X hXR hX hfar
  ideal_prefix := fun eta X hX hX' => ideal_prefix F XR eta X hXR hX hX'
  pressure_integrable := fun eta => canonicalKernel_integrable F XR eta hXR
  pressure_canonical := fun eta X hX => Pi_canonical F XR eta X hXR hX
  axis_unchanged := axisDatum_unchanged F XR hXR
  axis_limit := fun eta => Pi_tendsto_axis F XR eta hXR
  fixed_switch_amplitude := fun eta => E_at_switch F XR eta hXR
  shaped_patch := fun eta x hx => patch_fields F XR eta x hXR hx
  patch_disjoint := patch_switch_disjoint F XR hXR

/-- The same reset and amplitude work simultaneously for every entrance radius.
The schedule is chosen once, before the radius is selected. -/
theorem exists_dilated_outgoing_profiles (P m : ℝ) (hP : 0 < P) (hm : 0 < m) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ lam : ℝ,
      0 < lam → lam < lam₀ → ∀ h : ℝ, 0 < h → 2 * h < lam →
      ∃ F : Profile, F.data.core.P = P ∧ F.data.core.m = m ∧
        F.data.core.lam = lam ∧ F.data.h = h ∧ Specification F C ∧
        ∀ XR : ℝ, 0 < XR → DilatedSpecification F XR := by
  obtain ⟨lam₀, C, hlam₀, hC, hc⟩ := OutgoingProfile.exists_outgoing_profile P m hP hm
  refine ⟨lam₀, C, hlam₀, hC, ?_⟩
  intro lam hlam hlam' h hh hsmall
  obtain ⟨F, hP', hm', hl', hh', _, hs⟩ := hc lam hlam hlam' h hh hsmall
  exact ⟨F, hP', hm', hl', hh', hs, fun XR hXR => preserves_specification hs XR hXR⟩

theorem exists_fixed_schedule (P m : ℝ) (hP : 0 < P) (hm : 0 < m) :
    ∃ lam C : ℝ, 0 < lam ∧ 0 < C ∧ ∀ h : ℝ, 0 < h → 2 * h < lam →
      ∃ F : Profile, F.data.core.P = P ∧ F.data.core.m = m ∧
        F.data.core.lam = lam ∧ F.data.h = h ∧ Specification F C ∧
        ∀ XR : ℝ, 0 < XR → DilatedSpecification F XR := by
  obtain ⟨lam, C, hlam, hC, hc⟩ := OutgoingProfile.exists_fixed_lambda P m hP hm
  refine ⟨lam, C, hlam, hC, ?_⟩
  intro h hh hsmall
  obtain ⟨F, hP', hm', hl', hh', hs⟩ := hc h hh hsmall
  exact ⟨F, hP', hm', hl', hh', hs, fun XR hXR => preserves_specification hs XR hXR⟩

end NavierStokes.OutgoingDilation
