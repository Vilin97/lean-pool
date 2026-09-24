/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.NestedCutoffs
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalSourceEndpoint
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalPressureExtension

/-! # The fixed final cutoff and the quantitative half-cylinder conclusion

The derivative constant is chosen before the domain. Pressure estimates on
the radius-19/32 cylinder suffice, by a past-time extension which leaves the
literal localized source unchanged. The remaining input is exactly the
global heat representation of the localized velocity.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- A domain-independent final cutoff constant gives the quantitative
half-cylinder conclusion from component bounds and literal localized heat
representations. No global pressure-gradient estimate is needed. -/
theorem exists_uniform_final_cutoff_consumer :
    ∃ C : ℝ, 0 < C ∧
    ∀ (q ε₀ : ℝ) (KU KUinitial KD KP : ℝ≥0∞),
    5 / 2 < q → 0 ≤ ε₀ → KU < ⊤ → KUinitial < ⊤ → KD < ⊤ → KP < ⊤ →
    ∀ (Ω : Set Vec3) (I : Set ℝ)
      (u f Dp : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ),
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
    closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
    (∀ i, morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ KU) →
    (∀ i, morreyNorm 3 (25 / 3) ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ KUinitial) →
    (∀ i j, morreyNorm 2 (25 / 8) ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => Du z i j)) ≤ KD) →
    (∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (19 / 32)).indicator
      (fun z => Dp z i)) volume) →
    (∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      ((parabolicCylinder (0 : Vec3) 0 (19 / 32)).indicator (fun z => Dp z i)) ≤ KP) →
    (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
    (∀ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      localBox Ω I Ω' J → tsupport φ ⊆ Ω' ×ˢ J →
      (∀ z ∈ tsupport φ, z.1 ∈ vec3Ball (0 : Vec3) (9 / 16)) →
      (∀ z ∈ tsupport φ, z.2 ≤ 0 →
        parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (9 / 16)) →
      localizedVelocity φ u =ᵐ[volume]
        (fun z i => heatPotential
          (fun w => localizedGradientSourceG φ u Du f Dp w i)
          (fun j w => localizedGradientSourceH φ u j w i) z)) →
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
      ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2))) w (stepGamma₀ q)
        (uniformHalfCylinderHolderBound q ε₀ (causalGradientMorreyBound q ε₀ C KU KD KP)
          (causalDerivativeMorreyBound C KUinitial)) ∧
      ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
        IsRegularPoint Ω I u z := by
  obtain ⟨ψ, C, hC, _, _, hcut⟩ := exists_uniform_nested_cutoff_derivative_bound
    (1 / 2) (9 / 16) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro q ε₀ KU KUinitial KD KP hq hε₀ hKU hKUinitial hKD hKP
    Ω I u f Dp Du p hsol hdom hU hUinitial hD hDp hP hsmall hL
  obtain ⟨φ, Ω', J, hφ, hbox, hφbox, hrange, hone, hsupp, hspace, _, hder⟩ :=
    hcut Ω I hsol.1 hsol.2.1 hdom
  have hPs := causalPressureExtension_component_bounds
    (R₁ := (19 / 32 : ℝ)) (R₀ := (5 / 8 : ℝ))
    (by norm_num) (by norm_num) Dp hDp hP
  have hsuppP : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (19 / 32) :=
    fun z hz ht => parabolicCylinder_mono (by norm_num) (by norm_num) (hsupp z hz ht)
  have hsource := localizedGradientSourceG_causalPressureExtension
    (19 / 32) φ u Du f Dp hsuppP
  have hrep := hL φ Ω' J hφ hbox hφbox hspace hsupp
  apply uniform_halfCylinder_of_literal_causal_sources q ε₀ C KU KUinitial KD KP
    hq hε₀ hC.le hKU hKUinitial hKD hKP hsol hdom hφ hrange
    (fun z hz ht => parabolicCylinder_mono (by norm_num) (by norm_num) (hsupp z hz ht))
    (fun z hz => (hder z hz).2) hU hUinitial hD
    (fun i => (hPs i).1) (fun i => (hPs i).2) hsmall
  rw [hsource]
  filter_upwards [ae_restrict_of_ae hrep,
    ae_restrict_mem ((vec3Ball_measurable (0 : Vec3) (1 / 2)).prod
      measurableSet_Ioc)] with z hz hzin
  have honez : φ (z.1, z.2) = 1 :=
    (hone (z.1, z.2) (subset_closure hzin)).self_of_nhds
  rw [← hz]
  funext i
  change u z i = φ (z.1, z.2) * u z i
  rw [honez, one_mul]

end CKN.Core.Endgame
