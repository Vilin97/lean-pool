/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyDecay
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyFormUniform

/-! # Neighborhood Morrey data from the gradient criterion

The smallness premise stays in the extended nonnegative reals. The only
additional estimate is the pair of one-step inequalities in `lem:theta-decay`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

/-- Neighborhood decay and the three initial Morrey memberships, obtained
from the gradient limsup and the one-step theta inequalities. -/
theorem morrey_sources_of_gradient_limsup
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hq : 5 / 2 < q)
    {z₀ : ParabolicPoint}
    (hz₀ : z₀ ∈ spaceTimeSet Ω I)
    {C₂₇ C₂₈ : ℝ}
    (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (h_theta_decay : ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
        C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
            theta (iterationKappa C₂₇) u Du p z ρ +
          C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
            (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
              theta (iterationKappa C₂₇) u Du p z ρ +
          C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
              theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                lambda q f z ρ ^ (1 / 2 : ℝ) +
          C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ ∧
      (theta (iterationKappa C₂₇) u Du p z ρ ≤ 1 →
        theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
              theta (iterationKappa C₂₇) u Du p z ρ +
            2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                  lambda q f z ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ))
    (h_beta_decay : Filter.limsup (fun r : ℝ =>
        (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
            ENNReal.ofReal (spatialGradientSq u Du w))
      (𝓝[>] (0 : ℝ)) <
        ENNReal.ofReal ((iterationEpsilonStar C₂₇) ^ (2 : ℕ)))
 :
    ∃ r₂ M : ℝ, 0 < r₂ ∧ 1 ≤ M ∧
      Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I ∧
      (∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
        max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
          M * r ^ (2 / 5 : ℝ)) ∧
      morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ (r₂ / 4)) u ∧
      (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
        (Metric.ball z₀ (r₂ / 4)) (fun z => Du z i)) ∧
      morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
        ((Metric.ball z₀ (r₂ / 4)).indicator p) < ⊤ := by
  obtain ⟨r₂, M, hr₂, hM, hcarrier, hdecay⟩ :=
    morreyDecay_of_thetaDecay hsol hq hz₀ hC₂₇ hC₂₈ h_theta_decay h_beta_decay
  obtain ⟨KU, KD, KP, hKU, hKD, hKP, hbounds⟩ :=
    step2_morrey_form_uniform M r₂ hM hr₂
  obtain ⟨huN, hDuN, hpN⟩ := hbounds hsol z₀ hcarrier hdecay
  obtain ⟨hu, hDu, hp⟩ :=
    step2_morrey_form_uniform_membership hKU hKD hKP huN hDuN hpN
  exact ⟨r₂, M, hr₂, hM, hcarrier, hdecay, hu, hDu, hp⟩

end CKN.Core.Endgame
