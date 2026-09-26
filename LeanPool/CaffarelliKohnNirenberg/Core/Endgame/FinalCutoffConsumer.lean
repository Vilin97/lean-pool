/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalGradientMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalDerivativeSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalHalfCylinder
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.NestedCutoffs
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalPressureExtension

/-! # The fixed final cutoff and the quantitative half-cylinder conclusion

The derivative constant is chosen before the domain. Pressure estimates on
the radius-19/32 cylinder suffice, by a past-time extension which leaves the
literal localized source unchanged. The remaining input is exactly the
global heat representation of the localized velocity.
-/

public section

section

/-! # Quantitative consumption of the literal localized sources

The actual gradient-slot and derivative-slot source estimates imply the
closed-half-cylinder Hölder conclusion once their literal heat representation
is supplied. This consumer does not construct that representation or the
pressure gradient. All norm estimates concern only nonpositive times.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- The numerical derivative-source coefficient from the initial velocity
Morrey bound and the cutoff derivative bound. -/
def causalDerivativeMorreyBound (C : ℝ) (KUinitial : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * C) *
    (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KUinitial)

/-- Finite initial velocity bounds give a finite derivative-source bound. -/
theorem causalDerivativeMorreyBound_lt_top (C : ℝ) {KUinitial : ℝ≥0∞}
    (hKUinitial : KUinitial < ⊤) : causalDerivativeMorreyBound C KUinitial < ⊤ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      Integration.volume_parabolicCylinder_lt_top.ne) hKUinitial)

/-- Actual source estimates consume a literal localized heat representation
to give a uniform closed-half-cylinder representative and interior regularity.
The source and pressure-gradient bounds remain explicit hypotheses. -/
theorem uniform_halfCylinder_of_literal_causal_sources
    (q ε₀ C : ℝ) (KU KUinitial KD KP : ℝ≥0∞)
    (hq : 5 / 2 < q) (hε₀ : 0 ≤ ε₀) (hC : 0 ≤ C)
    (hKU : KU < ⊤) (hKUinitial : KUinitial < ⊤) (hKD : KD < ⊤) (hKP : KP < ⊤)
    {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ}
    {u f Dp : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hφrange : ∀ z : Vec3 × ℝ, 0 ≤ φ z ∧ φ z ≤ 1)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (hder : ∀ z : Vec3 × ℝ, z.2 ≤ 0 →
      |timePartial φ z| ≤ C ∧ (∀ j, |spatialPartial φ j z| ≤ C) ∧
        |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C)
    (hU : ∀ i, morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ KU)
    (hUinitial : ∀ i, morreyNorm 3 (25 / 3)
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun z => u z i)) ≤ KUinitial)
    (hD : ∀ i j, morreyNorm 2 (25 / 8)
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun z => Du z i j)) ≤ KD)
    (hDp : ∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => Dp z i)) volume)
    (hP : ∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun z => Dp z i)) ≤ KP)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hrep : u =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))]
      (fun z i => heatPotential
        (fun w => localizedGradientSourceG φ u Du f Dp w i)
        (fun j w => localizedGradientSourceH φ u j w i) z)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
      ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2))) w (stepGamma₀ q)
        (uniformHalfCylinderHolderBound q ε₀ (causalGradientMorreyBound q ε₀ C KU KD KP)
          (causalDerivativeMorreyBound C KUinitial)) ∧
      ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
        IsRegularPoint Ω I u z := by
  have hF := causal_gradient_source_of_suitableWeakSolution q ε₀ C KU KD KP hq hC
    hsol hdom hφ hφrange hsupp (fun z hz => ⟨(hder z hz).1, (hder z hz).2.2⟩)
    hU hD hDp hP hsmall
  have hG := causal_derivative_source_of_suitableWeakSolution C KUinitial hC
    hsol hdom hφ hsupp (fun z hz => (hder z hz).2.1) hUinitial
  refine uniform_halfCylinder_representative_of_past_source_bounds q ε₀
    (causalGradientMorreyBound q ε₀ C KU KD KP) (causalDerivativeMorreyBound C KUinitial)
    hq hε₀ (causalGradientMorreyBound_lt_top q ε₀ C hq hKU hKD hKP)
    (causalDerivativeMorreyBound_lt_top C hKUinitial) hsol hdom hsmall
    (fun i => (hF i).1) (fun j i => (hG j i).1)
    (fun i => (hF i).2) (fun j i => (hG j i).2) ?_ ?_ hrep
  · intro z ht hz
    have hzS : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) := fun hm =>
      hz (parabolicCylinder_mono (by norm_num) (by norm_num) hm)
    funext i
    change localizedGradientSourceG φ u Du f Dp z i = 0
    have hzero := causalGradientSourceComponent_zero_outside_intermediate
      hφ.1 hsupp u Du f Dp i hzS
    simpa only [causalGradientSourceComponent,
      indicator_of_mem (show z ∈ {z : ParabolicPoint | z.2 ≤ 0} from ht)] using hzero
  · intro j z ht hz
    have hzS : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) := fun hm =>
      hz (parabolicCylinder_mono (by norm_num) (by norm_num) hm)
    funext i
    change localizedGradientSourceH φ u j z i = 0
    have hzero := causalDerivativeComponent_zero_outside_intermediate
      (u := u) hφ.1 hsupp j i hzS
    simpa only [causalDerivativeComponent,
      indicator_of_mem (show z ∈ {z : ParabolicPoint | z.2 ≤ 0} from ht)] using hzero

end CKN.Core.Endgame
end

end

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
