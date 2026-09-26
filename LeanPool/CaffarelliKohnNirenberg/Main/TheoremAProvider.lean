/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremAUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.ThetaDecayTShape
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.InitialUniform
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapPressureConsumer
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.FinalPressureConsumer
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CarrierRestriction
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.StartCaccioppoli

/-! # Quantitative small-data regularity from the displayed analytic estimates

The start and iteration produce uniform initial norms. Two pressure-gradient
estimates and the literal localized equation supply the velocity improvement
and the final closed-cylinder estimate. Every remaining analytic input is
displayed explicitly; no regularity conclusion is assumed.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential
noncomputable section
namespace CKN

/-- The quantitative small-data conclusion follows from the displayed
start and theta inequalities, uniform one-sided pressure-gradient estimates,
and the literal localized heat representation. -/
theorem epsilonRegularityL3_provider_of_producers
    (q C₁₂_p1 C₃₂ C_CZ : ℝ)
    (hq : 5 / 2 < q)
    (hC₃₂ : 0 ≤ C₃₂)
    (hC : 0 ≤ C_CZ)
    (hLin34 : ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      pressureD p z r ≤ C₃₂ *
        ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
          (r / ρ) * pressureD p z ρ +
          (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)))
    (hCZ_p1 :
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ r : ℝ}, (hρ : 0 < ρ) → 0 < r → r ≤ ρ / 2 →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          eLpNorm' (fun w : ParabolicPoint => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
          ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ *
            alpha u z ρ * beta u Du z ρ))
    (hGA : ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
  5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
  0 ≤ C_CZ →
  0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
  KU < ∞ → KD < ∞ →
  ∃ KP : ℝ≥0∞, KP < ∞ ∧
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
      (∀ i, morreyNorm 3 τ
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
      ((∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
      ∃ Dp : ParabolicPoint → Vec3,
        (∀ i, AEMeasurable (fun z => Dp z i)
          (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
        (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
          U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
          Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) ∧
        (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
        (∀ i, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
          ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i)) ≤ KP))
    (hL : ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {φ : Vec3 × ℝ → ℝ}, φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
        ∀ {Ω' : Set Vec3} {J : Set ℝ}, localBox Ω I Ω' J →
        tsupport φ ⊆ Ω' ×ˢ J →
        ∀ {Dp : ParabolicPoint → Vec3},
        (∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet Ω' J))) →
        (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ Ω' ×ˢ J →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
        localizedVelocity φ u =ᵐ[volume]
          (fun z i => heatPotential
            (fun w => localizedGradientSourceG φ u Du f Dp w i)
            (fun j w => localizedGradientSourceH φ u j w i) z)) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  obtain ⟨C₂₇, C₂₈, hC₂₇, hC₂₈, hThetaDecay⟩ :=
    thetaDecay_T_of_inputs q C₁₂_p1 hCZ_p1
  obtain ⟨ε₀, KUinitial, KD, hε₀, hKUinitial, hKD, hinitial⟩ :=
    theoremA_initial_uniform_of_displays q startGammaConstant (caccioppoliC₂₆ q)
      C₂₇ C₂₈ C₃₂ hq hC₂₇ hC₂₈ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hC₃₂
      (fun hsol => caccioppoli_gamma_display_fixed hsol) hLin34
      (fun {Ω I u Du p f} hsol => hThetaDecay Ω I u Du p f hsol)
  obtain ⟨KU, hKU, hbootstrap⟩ := exists_uniform_bootstrap_of_initial_pressure
    q ε₀ KUinitial KD hq hKUinitial hKD
    (by
      obtain ⟨KP, hKP, hpressure⟩ := hGA q (25 / 3) C_CZ (11 / 16) (43 / 64)
        ε₀ KUinitial KD hq (by norm_num) (by norm_num) hC
        (by norm_num) (by norm_num) (by norm_num) hε₀.le hKUinitial hKD
      refine ⟨KP, hKP, ?_⟩
      intro Ω I u f Du p hsol hdom hsmall hU hD
      obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hpressure hsol hdom hU hD hsmall
      refine ⟨Dp, hAE, hInt, hweak, ?_⟩
      intro i
      have hmin : min (((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹) q = 25 / 11 := by
        rw [show ((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹ = 25 / 11 by norm_num]
        exact min_eq_left (by linarith only [hq])
      simpa only [hmin] using hN i)
    (fun _ _ _ _ _ _ _ hsol _ _ _ hφ hbox hsupp hInt hweak =>
      hL hsol hφ hbox hsupp hInt hweak)
  obtain ⟨C₄, hC₄, hfinal⟩ := exists_uniform_halfCylinder_of_final_pressure
    q ε₀ KU KUinitial KD hq hε₀.le hKU hKUinitial hKD
    (by
      obtain ⟨KP, hKP, hpressure⟩ := hGA q 25 C_CZ (5 / 8) (19 / 32)
        ε₀ KU KD hq (by norm_num) (by norm_num) hC
        (by norm_num) (by norm_num) (by norm_num) hε₀.le hKU hKD
      refine ⟨KP, hKP, ?_⟩
      intro Ω I u f Du p hsol hdom hsmall hU hD
      obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hpressure hsol hdom hU hD hsmall
      refine ⟨Dp, hAE, hInt, hweak, ?_⟩
      intro i
      have hexp : ((1 / (25 : ℝ)) + 8 / 25)⁻¹ = 25 / 9 := by norm_num
      simpa only [hexp, min_comm] using hN i)
    (fun _ _ _ _ _ _ _ hsol _ _ _ hφ hbox hsupp hInt hweak =>
      hL hsol hφ hbox hsupp hInt hweak)
  refine ⟨ε₀, stepGamma₀ q, C₄, hε₀, stepGamma₀_pos hq,
    (stepGamma₀_le_fifth q).trans (by norm_num), hC₄, ?_⟩
  intro Ω I u Du p f hsol hdom hsmall
  obtain ⟨hUinitial, hD⟩ := hinitial hsol hdom hsmall
  have hU := hbootstrap Ω I u f Du p hsol hdom hUinitial hD hsmall
  have hsub : parabolicCylinder (0 : Vec3) 0 (5 / 8) ⊆
      parabolicCylinder (0 : Vec3) 0 (11 / 16) :=
    parabolicCylinder_mono (by norm_num) (by norm_num)
  apply hfinal Ω I u f Du p hsol hdom hU
  · intro i
    exact (morreyNorm_indicator_mono_set (by norm_num : (0 : ℝ) ≤ 3)
      hsub (fun z => u z i)).trans (hUinitial i)
  · intro i j
    exact (morreyNorm_indicator_mono_set (by norm_num : (0 : ℝ) ≤ 2)
      hsub (fun z => Du z i j)).trans (hD i j)
  · exact hsmall

end CKN
