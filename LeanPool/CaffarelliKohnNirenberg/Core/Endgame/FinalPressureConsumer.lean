/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.FinalCutoffConsumer
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.LocalBoxRestriction

/-! # `thm:endgame` on the one-sided cylinder

The final step of the proof of `thm:A`. The velocity is taken in both
`𝓜^{3,25}` and `𝓜^{3,25/3}` on the cylinder of radius `5/8`, and the
pressure gradient in `𝓜^{6/5,min {q, 25/9}}` on radius `19/32`, the exponent
of `eq:pressure-gradient-morrey` at `τ = 25` since `1/25 + 8/25 = 9/25`. The
localized sources are those of `lem:local-equation`, split at `t = 0`, and
the heat-potential estimate of `prop:heat-morrey-hoelder` produces the
Hölder representative on the closed half cylinder with exponent
`γ₀ = min {2 - 5/q, 1/5}` of `eq:gamma-value`. Only local integrability of
the pressure gradient, not a uniform bound at later times, is used to
justify that representation.
-/

public section

open Set MeasureTheory
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- The final local pressure-gradient estimate and the literal local heat
representation yield a uniform closed-half-cylinder estimate, with the
constant chosen before the domain and solution. -/
theorem exists_uniform_halfCylinder_of_final_pressure
    (q ε₀ : ℝ) (KU KUinitial KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hε₀ : 0 ≤ ε₀)
    (hKU : KU < ⊤) (hKUinitial : KUinitial < ⊤) (hKD : KD < ⊤)
    (hGA : ∃ KP : ℝ≥0∞, KP < ⊤ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ),
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
      (∀ i, morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
        (fun z => u z i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8) ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
        (fun z => Du z i j)) ≤ KD) →
      ∃ Dp : ParabolicPoint → Vec3,
        (∀ i, AEMeasurable (fun z => Dp z i)
          (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) (19 / 32)) I))) ∧
        (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
          U ⊆ vec3Ball (0 : Vec3) (19 / 32) →
          ∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) ∧
        (∀ (i : Fin 3) (ψ : Vec3 × ℝ → ℝ),
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ vec3Ball (0 : Vec3) (19 / 32) ×ˢ I →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
        ∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
          ((parabolicCylinder (0 : Vec3) 0 (19 / 32)).indicator (fun z => Dp z i)) ≤ KP)
    (hL : ∀ (Ω : Set Vec3) (I : Set ℝ)
      (u f Dp : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ), IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ (φ : Vec3 × ℝ → ℝ) (U : Set Vec3) (J : Set ℝ),
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      localBox Ω I U J → tsupport φ ⊆ U ×ˢ J →
      (∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) →
      (∀ (i : Fin 3) (ψ : Vec3 × ℝ → ℝ),
        ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ → tsupport ψ ⊆ U ×ˢ J →
        (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
          -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
      localizedVelocity φ u =ᵐ[volume] (fun z i => heatPotential
        (fun w => localizedGradientSourceG φ u Du f Dp w i)
        (fun j w => localizedGradientSourceH φ u j w i) z)) :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧
    ∀ (Ω : Set Vec3) (I : Set ℝ)
      (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ),
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
    closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
    (∀ i, morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ KU) →
    (∀ i, morreyNorm 3 (25 / 3) ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ KUinitial) →
    (∀ i j, morreyNorm 2 (25 / 8) ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => Du z i j)) ≤ KD) →
    (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
      ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2))) w (stepGamma₀ q) C₄ ∧
      ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
        IsRegularPoint Ω I u z := by
  obtain ⟨KP, hKP, hpressure⟩ := hGA
  obtain ⟨C, _, hfinal⟩ := exists_uniform_final_cutoff_consumer
  refine ⟨uniformHalfCylinderHolderBound q ε₀ (causalGradientMorreyBound q ε₀ C KU KD KP)
    (causalDerivativeMorreyBound C KUinitial),
    uniformHalfCylinderHolderBound_nonneg _ _ _ _ hε₀, ?_⟩
  intro Ω I u f Du p hsol hdom hU hUinitial hD hsmall
  obtain ⟨Dp, hDpAE, hDpInt, hDpWeak, hDpNorm⟩ :=
    hpressure Ω I u f Du p hsol hdom hsmall hU hD
  have hsub : parabolicCylinder (0 : Vec3) 0 (19 / 32) ⊆
      spaceTimeSet (vec3Ball (0 : Vec3) (19 / 32)) I := by
    intro z hz
    exact ⟨hz.1, (hdom (subset_closure
      (parabolicCylinder_mono (by norm_num) (by norm_num) hz))).2⟩
  have hAE (i : Fin 3) : AEMeasurable
      ((parabolicCylinder (0 : Vec3) 0 (19 / 32)).indicator (fun z => Dp z i)) volume :=
    (aemeasurable_indicator_iff ((vec3Ball_measurable _ _).prod measurableSet_Ioc)).mpr
      ((hDpAE i).mono_measure (Measure.restrict_mono (μ := volume) hsub le_rfl))
  apply hfinal q ε₀ KU KUinitial KD KP hq hε₀ hKU hKUinitial hKD hKP
    Ω I u f Dp Du p hsol hdom hU hUinitial hD hAE hDpNorm hsmall
  intro φ U J hφ hbox hφbox hspace _
  have hbox' := localBox_inter_spatial_open hbox
    (isOpen_vec3Ball (0 : Vec3) (19 / 32))
  have hspace' : ∀ z ∈ tsupport φ, z.1 ∈ vec3Ball (0 : Vec3) (19 / 32) := by
    intro z hz
    have hm : vec3EuclideanNorm (z.1 - 0) < 9 / 16 := hspace z hz
    exact hm.trans_le (by norm_num)
  apply hL Ω I u f Dp Du p hsol φ (U ∩ vec3Ball (0 : Vec3) (19 / 32)) J
    hφ hbox' (support_subset_inter_spatial_box hφbox hspace')
    (hDpInt _ J hbox' inter_subset_right)
  intro i ψ hψ hψbox
  apply hDpWeak i ψ hψ
  intro z hz
  have hm := hψbox hz
  exact ⟨hm.1.2, hbox.2.2.2.2.2 (subset_closure hm.2)⟩

end CKN.Core.Endgame
