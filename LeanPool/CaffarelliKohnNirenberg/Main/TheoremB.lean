/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremBUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.ThetaDecayTShape
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Neighborhood
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ProducerRegularity
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradientInstances
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAOneRoundFinal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAFirstRoundConsumer
public import LeanPool.CaffarelliKohnNirenberg.Core.Parameters
public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecOn
public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable

/-!
# Theorem B

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

section

/-!
# Theorem BProvider

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential


noncomputable section

namespace CKN

/-! # The gradient criterion from neighborhood regularity

The lower-level conditional reduction consumes a local Hölder conclusion;
it is not a proof of the gradient criterion. The producer theorem instead
derives local regularity from the explicit pressure-gradient,
velocity-improvement, localized-equation, and source estimates. Both use
the extended-real neighborhood decay theorem.
-/


/-- The extended-real gradient criterion follows from the explicit theta,
pressure-gradient, velocity-improvement, localized-equation, and source
estimates. No local regularity conclusion is assumed. -/
theorem epsilonRegularityGradient_provider_of_producers
    (q C₁₂_p1 : ℝ) (hq : 5 / 2 < q)
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
    (hG : ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
        Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
        morreyVecMem 3 τ (Metric.ball z₀ R) u →
        (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
          (Metric.ball z₀ R) (fun z => Du z i)) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
            (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
          (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          morreyVecMem (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
            (Metric.ball z₀ (R / 2)) Dp)
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
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          IsRegularPoint Ω I u z₀ := by
  obtain ⟨C₂₇, C₂₈, hC₂₇, hC₂₈, hThetaDecay⟩ :=
    thetaDecay_T_of_inputs q C₁₂_p1 hCZ_p1
  refine ⟨iterationEpsilonStar C₂₇, iterationEpsilonStar_pos hC₂₇, ?_⟩
  intro Ω I u Du p f hsol z₀ hz₀ hgradient
  obtain ⟨r₂, M, hr₂, _hM, hcarrier, _hdecay, hu, hDu, _hp⟩ :=
    Core.Endgame.morrey_sources_of_gradient_limsup hsol hq hz₀ hC₂₇ hC₂₈
      (hThetaDecay Ω I u Du p f hsol) hgradient
  exact Core.Endgame.regular_point_of_local_producers q hq hG
    (routeA_one_round_velocity_improvement_of_gradient_inputs
      (by
        intro q' hq'
        exact hG q' (25 / 3) hq' (by norm_num) (by norm_num)) hL) hL
    (fun {_ _ _ _ _ _ _} hsol {_} hφ {_ _} hbox hφbox z₀ R hR hq _ =>
      localized_gradient_source_package_of_sws hsol hφ hbox hφbox z₀ R hR hq)
    hsol z₀ (r₂ / 4) (by positivity)
    ((Metric.ball_subset_ball (by linarith only [hr₂])).trans hcarrier) hu hDu


end CKN
end

end

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Main

/-- The gradient regularity criterion for suitable weak solutions. -/
theorem epsilonRegularityGradient (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          IsRegularPoint Ω I u z₀ := by
  exact CKN.Core.Endgame.epsilonRegularityGradient_unconditional q hq

end CKN.Main
