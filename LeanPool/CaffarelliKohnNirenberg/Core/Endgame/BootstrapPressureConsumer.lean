/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapDerivativeSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalBootstrap
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalPressureExtension
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.NestedCutoffs
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.LocalBoxRestriction

/-! # The bootstrap round of `prop:bootstrap`

The single round of `cor:one-round`, run with the cut-offs of Step 3 of the
proof of `thm:A`. From the velocity in `𝓜^{3,25/3}` and its gradient in
`𝓜^{2,25/8}` on the cylinder of radius `11/16`, together with the pressure
gradient in `𝓜^{6/5,25/11}` on radius `43/64` supplied by
`lem:pressure-gradient-morrey`, it returns the velocity in `𝓜^{3,25}` on
radius `5/8`. The exponents are those of `eq:bootstrap-gain`:
`1/ς = 1/τ - 2/25` with `τ = 25/3`; the undifferentiated source lies in
`𝓜^{6/5,25/11}` and the differentiated source in `𝓜^{3,25/6}`.

Every source is split at `t = 0` and only the past part is estimated, so no
bound at times after `0` is used; the pressure values there enter only the
local representation of the localized velocity.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- The initial one-sided pressure-gradient estimate and literal localized
equation give a solution-uniform improved velocity bound on the intermediate
cylinder. Future-time pressure values enter only the local representation. -/
theorem exists_uniform_bootstrap_of_initial_pressure
    (q ε₀ : ℝ) (KUinitial KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hKUinitial : KUinitial < ⊤) (hKD : KD < ⊤)
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
      (∀ i, morreyNorm 3 (25 / 3) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
        (fun z => u z i)) ≤ KUinitial) →
      (∀ i j, morreyNorm 2 (25 / 8) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
        (fun z => Du z i j)) ≤ KD) →
      ∃ Dp : ParabolicPoint → Vec3,
        (∀ i, AEMeasurable (fun z => Dp z i)
          (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) (43 / 64)) I))) ∧
        (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
          U ⊆ vec3Ball (0 : Vec3) (43 / 64) →
          ∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) ∧
        (∀ (i : Fin 3) (ψ : Vec3 × ℝ → ℝ),
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ vec3Ball (0 : Vec3) (43 / 64) ×ˢ I →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
        ∀ i, morreyNorm (6 / 5) (25 / 11 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 (43 / 64)).indicator (fun z => Dp z i)) ≤ KP)
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
    ∃ KU : ℝ≥0∞, KU < ⊤ ∧
    ∀ (Ω : Set Vec3) (I : Set ℝ)
      (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ),
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
    closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
    (∀ i, morreyNorm 3 (25 / 3) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => u z i)) ≤ KUinitial) →
    (∀ i j, morreyNorm 2 (25 / 8) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => Du z i j)) ≤ KD) →
    (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
    ∀ i, morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ KU := by
  obtain ⟨KP, hKP, hpressure⟩ := hGA
  obtain ⟨ψ, C, hC, _, _, hcut⟩ := exists_uniform_nested_cutoff_derivative_bound
    (5 / 8) (21 / 32) (by norm_num) (by norm_num) (by norm_num)
  let KF := bootstrapGradientMorreyBound q ε₀ C KUinitial KD KP
  let KH := ENNReal.ofReal (2 * C) * KUinitial
  have hKF : KF < ⊤ := bootstrapGradientMorreyBound_lt_top q ε₀ C hq hKUinitial hKD hKP
  have hKH : KH < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKUinitial
  refine ⟨bootstrapSourceMorreyBound (3 * KF) (3 * KH),
    bootstrapSourceMorreyBound_lt_top
      (ENNReal.mul_lt_top (by norm_num) hKF)
      (ENNReal.mul_lt_top (by norm_num) hKH), ?_⟩
  intro Ω I u f Du p hsol hdom hU hD hsmall
  obtain ⟨Dp, hDpAE, hDpInt, hDpWeak, hDpNorm⟩ :=
    hpressure Ω I u f Du p hsol hdom hsmall hU hD
  obtain ⟨φ, U, J, hφ, hbox, hφbox, hrange, hone, hsupp, hspace, _, hder⟩ :=
    hcut Ω I hsol.1 hsol.2.1 hdom
  have hsub : parabolicCylinder (0 : Vec3) 0 (43 / 64) ⊆
      spaceTimeSet (vec3Ball (0 : Vec3) (43 / 64)) I := by
    intro z hz
    exact ⟨hz.1, (hdom (subset_closure
      (parabolicCylinder_mono (by norm_num) (by norm_num) hz))).2⟩
  have hAE (i : Fin 3) : AEMeasurable
      ((parabolicCylinder (0 : Vec3) 0 (43 / 64)).indicator (fun z => Dp z i)) volume :=
    (aemeasurable_indicator_iff ((vec3Ball_measurable _ _).prod measurableSet_Ioc)).mpr
      ((hDpAE i).mono_measure (Measure.restrict_mono (μ := volume) hsub le_rfl))
  have hbox' := localBox_inter_spatial_open hbox
    (isOpen_vec3Ball (0 : Vec3) (43 / 64))
  have hspace' : ∀ z ∈ tsupport φ, z.1 ∈ vec3Ball (0 : Vec3) (43 / 64) := by
    intro z hz
    have hm : vec3EuclideanNorm (z.1 - 0) < 21 / 32 := hspace z hz
    exact hm.trans_le (by norm_num)
  have hrep := hL Ω I u f Dp Du p hsol φ (U ∩ vec3Ball (0 : Vec3) (43 / 64)) J
    hφ hbox' (support_subset_inter_spatial_box hφbox hspace')
    (hDpInt _ J hbox' inter_subset_right) (fun i ψ hψ hψbox =>
      hDpWeak i ψ hψ (fun z hz =>
        ⟨(hψbox hz).1.2, hbox.2.2.2.2.2 (subset_closure (hψbox hz).2)⟩))
  have hPs := causalPressureExtension_component_bounds
    (R₁ := (43 / 64 : ℝ)) (R₀ := (11 / 16 : ℝ))
    (by norm_num) (by norm_num) Dp hAE hDpNorm
  have hsuppP : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (43 / 64) :=
    fun z hz ht => parabolicCylinder_mono (by norm_num) (by norm_num) (hsupp z hz ht)
  have hsuppWide : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (11 / 16) :=
    fun z hz ht => parabolicCylinder_mono (by norm_num) (by norm_num) (hsupp z hz ht)
  have hsource := localizedGradientSourceG_causalPressureExtension
    (43 / 64) φ u Du f Dp hsuppP
  have hF := bootstrap_gradient_source_of_suitableWeakSolution q ε₀ C KUinitial KD KP
    hq hC.le hsol hdom hφ hrange hsuppWide
    (fun z hz => ⟨(hder z hz).2.1, (hder z hz).2.2.2⟩) hU hD
    (fun i => (hPs i).1) (fun i => (hPs i).2) hsmall
  simp only [causalGradientSourceComponent, hsource] at hF
  have hH := bootstrap_derivative_source_of_suitableWeakSolution C KUinitial hC.le
    hsol hdom hφ hsuppWide (fun z hz => (hder z hz).2.2.1) hU
  apply causal_bootstrap_morrey_le_of_localized_representation KF KH hKF hKH
    (fun i => (hF i).1) (fun j i => (hH j i).1)
    (fun i => (hF i).2) (fun j i => (hH j i).2)
    (fun z ht hz => (bootstrap_literal_sources_zero_on_past hφ.1 hsupp u Du f Dp ht hz).1)
    (fun j z ht hz => (bootstrap_literal_sources_zero_on_past hφ.1 hsupp u Du f Dp ht hz).2 j)
    ?_ hrep
  intro z hz
  exact (hone (z.1, z.2) (subset_closure hz)).self_of_nhds

end CKN.Core.Endgame
