/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotHarmonic
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceP8
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientRegularity
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceSlices
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputsCentred
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTHarmonicMassEnvelope
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFourTermIdentification
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSourceQuantitative

/-! # The actual pressure mass from measurable envelopes

Harmonic and force slice masses are dominated by measurable envelopes.
Only the final centred-source correction needs a mass bound without any
joint measurability assumption.
-/

public section

section

/-!
# The absolute coefficients of the far-force increment

On a clipped cell the prescribed spatial pressure gradient of `prop:bootstrap`
splits into a Riesz field driven by the localized divergence source, the
gradient of the harmonic pressure part, the gradient of the *second force
potential* `p₈` of `eq:pk`, and a Riesz field driven by the centred source
correction.  This file fixes the absolute coefficients that the third summand
costs.

Display (3.5) bounds the classical gradient of `p₈,η` on the inner ball of a
collar of radius `ρ` by the `L¹` size of the force on that collar, with the
coefficient `400·c·cutoffGradientConstant·ρ⁻³`, in which the numeral
`400 = (3/20)⁻²` is the separation of `lem:cutoff`.  At the collar radii
`(R₀ − R₁)/2` of the two parameter triples of `prop:bootstrap` the scale
factor `ρ⁻³` is at most `128³`, and the cell volume contributes one further
factor `4π/3 ≤ 5`.  The three constants recorded here are the scale-free part
of that coefficient, its collar-uniform value, and the Calderón–Zygmund
threshold at which the affine slot pays for the increment.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-! ### The absolute coefficients -/

/-- The scale-free part of the far-force gradient coefficient of display (3.5):
the numeral `400 = (3/20)⁻²` of the separation of `lem:cutoff`, the order-one
constant of `eq:har-Ck`, and the cutoff gradient constant. -/
@[expose] def originASlotForceIncrementConstant : ℝ :=
  400 * sliceForcePotentialConstant * cutoffGradientConstant

/-- The far-force gradient coefficient at collar radii at least `1/128`, where
the scale factor `ρ⁻³` of display (3.5) is at most `128³`. -/
@[expose] def originASlotForceIncrementCoefficient : ℝ :=
  originASlotForceIncrementConstant * (128 : ℝ) ^ 3

/-- The absolute Calderón–Zygmund threshold at which the affine slot pays for
the far-force increment: the coefficient of display (3.5) times the cell-volume
factor `4π/3 ≤ 5`. -/
@[expose] def originASlotForceIncrementThreshold : ℝ :=
  5 * originASlotForceIncrementCoefficient

end CKN.Core.Step4
end

end

section

/-! # Measurable harmonic and force envelopes at the prescribed collars -/

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4
/-- The prescribed half-gap collar admits a measurable mass envelope within the affine slot. -/
theorem exists_gap_force_affine_envelope_instances
    (q ε C_CZ τ R₀ R₁ r : ℝ) (KU KD : ℝ≥0∞)
    (hC : gapForceIncrementThreshold ≤ C_CZ)
    (hinstances : (τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
    (z : ParabolicPoint) (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁))
    (hr : 0 < r) (hcell : r ≤ (R₀ - R₁) / 4) (i : Fin 3) :
    let hρ : 0 < (R₀-R₁)/2 := by
      rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
    ∃ M : ℝ → ℝ≥0∞,
      AEMeasurable M (volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0)) ∧
      (∀ᵐ s ∂volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0), eLpNorm (fun y =>
        gapForceIncrement z hρ u p f i (y,s))
        (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁))^(6/5 : ℝ) ≤ M s) ∧
      (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0, M s) ≤
      originKPAffineASlot q C_CZ ε KU KD *
        ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  have hnum : 0 < R₁ ∧ R₁ < R₀ ∧ R₀ ≤ 1 ∧ 25/3 ≤ τ ∧
      1/128 ≤ (R₀-R₁)/2 ∧ (R₀-R₁)/2 ≤ 1/2 := by
    rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
  have hρ : 0 < (R₀-R₁)/2 := by linarith only [hnum.2.1]
  have hQ : parabolicCylinder z.1 z.2 ((R₀-R₁)/2) ⊆
      parabolicCylinder (0 : Vec3) 0 1 :=
    (subset_closure.trans (half_gap_collar_closure_subset_outer hnum.1 hnum.2.1 hz)).trans
      (parabolicCylinder_mono (hnum.1.trans hnum.2.1).le hnum.2.2.1)
  exact exists_gap_force_affine_envelope_of_sws ε C_CZ τ R₁ r KU KD hC hnum.2.2.2.1
    hρ hnum.2.2.2.2.1 hnum.2.2.2.2.2 hr (by linarith only [hcell])
    hsol hdom hQ ((lintegral_mono (fun _ => le_add_left le_rfl)).trans hsmall) i


/-- The prescribed half-gap collar admits a measurable mass envelope within the affine slot. -/
theorem exists_gap_harmonic_affine_envelope_instances
    (q ε C_CZ τ R₀ R₁ r : ℝ) (KU KD : ℝ≥0∞)
    (hC : gapHarmonicEnvelopeThreshold ≤ C_CZ)
    (hinstances : (τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
    (z : ParabolicPoint) (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁))
    (hr : 0 < r) (hcell : r ≤ (R₀ - R₁) / 4) (i : Fin 3) :
    let hρ : 0 < (R₀-R₁)/2 := by
      rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
    ∃ M : ℝ → ℝ≥0∞,
      AEMeasurable M (volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0)) ∧
      (∀ᵐ s ∂volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0), eLpNorm (fun y =>
        classicalGradient
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (sourceSliceCentredMean z.1 ((R₀-R₁)/2) u) p s) y i)
        (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁))^(6/5 : ℝ) ≤ M s) ∧
      (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0, M s) ≤
      originKPAffineASlot q C_CZ ε KU KD *
        ENNReal.ofReal (r^(5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  have hnum : 0 < R₁ ∧ R₁ < R₀ ∧ R₀ ≤ 1 ∧ 25/3 ≤ τ ∧ τ ≤ 25 ∧
      1/128 ≤ (R₀-R₁)/2 ∧ (R₀-R₁)/2 ≤ 1/2 := by
    rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
  have hρ : 0 < (R₀-R₁)/2 := by linarith only [hnum.2.1]
  have hQ : parabolicCylinder z.1 z.2 ((R₀-R₁)/2) ⊆
      parabolicCylinder (0 : Vec3) 0 1 :=
    (subset_closure.trans (half_gap_collar_closure_subset_outer hnum.1 hnum.2.1 hz)).trans
      (parabolicCylinder_mono (hnum.1.trans hnum.2.1).le hnum.2.2.1)
  have hτ := hnum.2.2.2.1
  have hτhi := hnum.2.2.2.2.1
  have hlo := hnum.2.2.2.2.2.1
  have hhi := hnum.2.2.2.2.2.2
  have hrρ : r ≤ (R₀-R₁)/2 := by linarith only [hcell,hρ]
  have hspace : vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁ ⊆
      vec3Ball z.1 (((R₀-R₁)/2)/2) := by
    intro y hy
    change vec3EuclideanNorm (y-z.1) < ((R₀-R₁)/2)/2
    exact lt_of_lt_of_le (show vec3EuclideanNorm (y-z.1) < r from hy.1)
      (by linarith only [hcell])
  have hwin : Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0 ⊆
      Ioc (z.2-((R₀-R₁)/2)^2) z.2 := by
    intro s hs
    exact ⟨lt_of_le_of_lt (sub_le_sub_left (pow_le_pow_left₀ hr.le hrρ 2) _) hs.1.1,hs.1.2⟩
  exact exists_gap_harmonic_affine_envelope_of_sws q ε C_CZ
    (min ((1/τ+8/25)⁻¹) q) ((R₀-R₁)/2) R₁ z.2 r z.1 z KU KD
    (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁) hC
    (lt_of_lt_of_le (by norm_num) (endgame_kappa_ge hτ hsol.2.2.2.1))
    (endgame_kappa_le (by linarith only [hτ]) hτhi) hlo
    (by linarith only [hhi]) hr (by linarith only [hrρ,hhi])
    ((vec3Ball_measurable _ _).inter (vec3Ball_measurable _ _)) inter_subset_left hspace hwin
    hsol hdom ((closure_mono hQ).trans hdom) hQ hsmall i


end CKN.Core.Step4
end

end

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean
  CKN.Foundation.Heat
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
    (hinstances : (τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
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
    (hinstances : (τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hKU : KU < ⊤) (hKD : KD < ⊤)
    (hU : ∀ k, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => u w k)) ≤ KU)
    (hD : ∀ j k, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => Du w j k)) ≤ KD)
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
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
