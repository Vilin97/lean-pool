/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTHarmonicMassEnvelope
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFourTermIdentification

/-! # Measurable harmonic and force envelopes at the prescribed collars -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4
/-- The prescribed half-gap collar admits a measurable mass envelope within the affine slot. -/
theorem exists_gap_force_affine_envelope_instances
    (q ε C_CZ τ R₀ R₁ r : ℝ) (KU KD : ℝ≥0∞)
    (hC : gapForceIncrementThreshold ≤ C_CZ)
    (hinstances : (τ = 25/3 ∧ R₀ = 11/16 ∧ R₁ = 43/64) ∨
      (τ = 25 ∧ R₀ = 5/8 ∧ R₁ = 19/32))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w))^(3 : ℝ) +
        ENNReal.ofReal |p w|^(3/2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w))^q) ≤ ENNReal.ofReal ε)
    (z : ParabolicPoint) (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁))
    (hr : 0 < r) (hcell : r ≤ (R₀-R₁)/4) (i : Fin 3) :
    let hρ : 0 < (R₀-R₁)/2 := by
      rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
    ∃ M : ℝ → ℝ≥0∞,
      AEMeasurable M (volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0)) ∧
      (∀ᵐ s ∂volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0), eLpNorm (fun y => gapForceIncrement z hρ u p f i (y,s))
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
    (hinstances : (τ = 25/3 ∧ R₀ = 11/16 ∧ R₁ = 43/64) ∨
      (τ = 25 ∧ R₀ = 5/8 ∧ R₁ = 19/32))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w))^(3 : ℝ) +
        ENNReal.ofReal |p w|^(3/2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w))^q) ≤ ENNReal.ofReal ε)
    (z : ParabolicPoint) (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁))
    (hr : 0 < r) (hcell : r ≤ (R₀-R₁)/4) (i : Fin 3) :
    let hρ : 0 < (R₀-R₁)/2 := by
      rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
    ∃ M : ℝ → ℝ≥0∞,
      AEMeasurable M (volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0)) ∧
      (∀ᵐ s ∂volume.restrict (Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0), eLpNorm (fun y => classicalGradient
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
