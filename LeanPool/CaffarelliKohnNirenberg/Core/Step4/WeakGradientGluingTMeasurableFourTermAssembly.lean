/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTEnvelopeInstances
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSourceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotM1Instances

/-! # The actual pressure mass from measurable envelopes

Harmonic and force slice masses are dominated by measurable envelopes.
Only the final centred-source correction needs a mass bound without any
joint measurability assumption.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

/-- The exact four-term decomposition gives the affine bound on every common
thin cell. The first three time masses have measurable representatives or
envelopes supplied by suitability; the correction needs only its mass bound. -/
theorem actual_pressure_four_term_affine_instances
    (q ε C_CZ τ R₀ R₁ r : ℝ) (Cbase : ℝ → ℝ) (KU KD : ℝ≥0∞)
    (hthreshold : fourTermAffineThreshold (Cbase q) ≤ C_CZ)
    (hforce : originASlotForceIncrementThreshold ≤ Cbase q)
    (hharmonic : gapHarmonicEnvelopeThreshold ≤ Cbase q)
    (hinstances : (τ = 25/3 ∧ R₀ = 11/16 ∧ R₁ = 43/64) ∨
      (τ = 25 ∧ R₀ = 5/8 ∧ R₁ = 19/32))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w))^(3 : ℝ) +
        ENNReal.ofReal |p w|^(3/2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w))^q) ≤ ENNReal.ofReal ε)
    (hDp : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
        (fun y => p (y,s)) (fun y => Dp (y,s) i))
    (T : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (hTm : ∀ j i, Measurable (T j i))
    (hT : ∀ j i, ∀ᵐ s ∂volume, (fun y => T j i (y,s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        (fun y => (parabolicCylinder (0 : Vec3) 0 R₀).indicator
          (fun w => (∑ k, Du w j k * u w k) - f w j) (y,s)))
    (z : ParabolicPoint) (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁))
    (hr : 0 < r) (hcell : r ≤ 1/256) (i : Fin 3)
    (hraw : (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0,
      eLpNorm (fun y => ∑ j, T j i (y,s)) (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁))^(6/5 : ℝ)) ≤
      originKPAffineASlot q (Cbase q) ε KU KD *
        ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))))
    (hcorrection :
      let hρ : 0 < (R₀-R₁)/2 := by
        rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
      let η := mollifiedBallCutoff z.1 hρ
      let c := sourceSliceCentredMean z.1 ((R₀-R₁)/2) u
      (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0,
        eLpNorm (fun x => ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
          (rieszSecondL2_weak_type j i)
          (centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η (spatialDeriv η)
            (fun y => u (y,s)) (fun y => f (y,s)) (fun y => Du (y,s)) (c s) j) x)
          (ENNReal.ofReal (6/5 : ℝ))
          (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁))^(6/5 : ℝ)) ≤
        originKPAffineASlot q (Cbase q) ε KU KD *
          ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q)))) :
    (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0,
      eLpNorm (fun y => Dp (y,s) i) (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁))^(6/5 : ℝ)) ≤
      originKPAffineASlot q C_CZ ε KU KD *
        ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  have hnum : 0 < R₁ ∧ R₁ < R₀ ∧ R₀ ≤ 1 ∧ (1 : ℝ)/256 ≤ (R₀-R₁)/4 := by
    rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
  have hgapcell := hcell.trans hnum.2.2.2
  obtain ⟨MH, hMH, hHp, hHm⟩ := exists_gap_harmonic_affine_envelope_instances
    q ε (Cbase q) τ R₀ R₁ r KU KD hharmonic hinstances hsol hdom hsmall z hz hr hgapcell i
  have hf : gapForceIncrementThreshold ≤ Cbase q := hforce
  obtain ⟨MF, hMF, hFp, hFm⟩ := exists_gap_force_affine_envelope_instances
    q ε (Cbase q) τ R₀ R₁ r KU KD hf hinstances hsol hdom hsmall z hz hr hgapcell i
  have hid := ae_actual_pressure_eq_four_terms_half_gap_collar
    R₀ R₁ hnum.1 hnum.2.1 hnum.2.2.1 hsol hdom hDp T hT hr hgapcell hz
  have hrawMeas : Measurable (fun w : ParabolicPoint => ∑ j, T j i w) :=
    Finset.measurable_sum _ (fun j _ => hTm j i)
  have hAm := (origin_time_slice_norm_aemeasurable
    (by norm_num : (0 : ℝ) < 6/5) hrawMeas.aemeasurable.restrict
    (E := vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)
    (J := Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0)).pow_const (6/5 : ℝ)
  apply four_term_time_mass_affine hthreshold hAm hMH hMF _ hraw hHm hFm hcorrection
  filter_upwards [hid,hHp,hFp] with s hs hH hF
  have hb := four_term_slice_mass_le (hs i)
  exact hb.trans (mul_le_mul' le_rfl
    (add_le_add (add_le_add (add_le_add le_rfl hH) hF) le_rfl))

/-- Suitability supplies the selected raw Riesz field and both measurable
envelopes. Only the centred-source correction mass remains to be supplied. -/
theorem actual_pressure_four_term_affine_of_sws
    (q ε C_CZ τ R₀ R₁ r : ℝ) (Cbase : ℝ → ℝ) (KU KD : ℝ≥0∞)
    (hthreshold : fourTermAffineThreshold (Cbase q) ≤ C_CZ)
    (hriesz : rieszSourceThresholdA ≤ Cbase q)
    (hforce : originASlotForceIncrementThreshold ≤ Cbase q)
    (hharmonic : gapHarmonicEnvelopeThreshold ≤ Cbase q)
    (hinstances : (τ = 25/3 ∧ R₀ = 11/16 ∧ R₁ = 43/64) ∨
      (τ = 25 ∧ R₀ = 5/8 ∧ R₁ = 19/32))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hKU : KU < ⊤) (hKD : KD < ⊤)
    (hU : ∀ k, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => u w k)) ≤ KU)
    (hD : ∀ j k, morreyNorm 2 (25/8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => Du w j k)) ≤ KD)
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w))^(3 : ℝ) +
        ENNReal.ofReal |p w|^(3/2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w))^q) ≤ ENNReal.ofReal ε)
    (hDp : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
        (fun y => p (y,s)) (fun y => Dp (y,s) i))
    (z : ParabolicPoint) (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁))
    (hr : 0 < r) (hcell : r ≤ 1/256) (i : Fin 3)
    (hcorrection :
      let hρ : 0 < (R₀-R₁)/2 := by
        rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
      let η := mollifiedBallCutoff z.1 hρ
      let c := sourceSliceCentredMean z.1 ((R₀-R₁)/2) u
      (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0,
        eLpNorm (fun x => ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
          (rieszSecondL2_weak_type j i)
          (centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η (spatialDeriv η)
            (fun y => u (y,s)) (fun y => f (y,s)) (fun y => Du (y,s)) (c s) j) x)
          (ENNReal.ofReal (6/5 : ℝ))
          (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁))^(6/5 : ℝ)) ≤
        originKPAffineASlot q (Cbase q) ε KU KD *
          ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q)))) :
    (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0,
      eLpNorm (fun y => Dp (y,s) i) (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁))^(6/5 : ℝ)) ≤
      originKPAffineASlot q C_CZ ε KU KD *
        ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  have hnum : 0 < R₁ ∧ R₁ ≤ R₀ ∧ R₀ ≤ 1 ∧ 25/3 ≤ τ ∧ τ ≤ 25 := by
    rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
  obtain ⟨T, hTm, hT, hraw⟩ := exists_origin_riesz_source_affine_bound_of_sws
    q τ (Cbase q) R₀ R₁ ε KU KD hsol.2.2.2.1 hnum.2.2.2.1 hnum.2.2.2.2 hriesz
    hnum.1 hnum.2.1 hnum.2.2.1 hKU hKD hsol hdom hU hD hsmall
  exact actual_pressure_four_term_affine_instances q ε C_CZ τ R₀ R₁ r Cbase KU KD
    hthreshold hforce hharmonic hinstances hsol hdom hsmall hDp T hTm hT
    z hz hr hcell i (hraw i z r hr) hcorrection

end CKN.Core.Step4
