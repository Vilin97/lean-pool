/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.TheoremA.Route

/-! # Uniform initial bounds from the three displayed inequalities

The positive smallness threshold and all numerical norm bounds precede the
domain and the solution. The proof consumes the actual start and iteration
route on the wider cylinder needed for the first localization.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
noncomputable section
namespace CKN.Core.Endgame

/-- Uniform displayed estimates supply uniform initial velocity and gradient
Morrey bounds on the cylinder of radius eleven sixteenths. -/
theorem theoremA_initial_uniform_of_displays
    (q C₂₅ C₂₆ C₂₇ C₂₈ C₃₂ : ℝ)
    (hq : 5 / 2 < q) (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆) (hC₃₂ : 0 ≤ C₃₂)
    (hCaccGamma : ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      alpha u z r + beta u Du z r ≤
        C₂₅ * ((r / ρ) * gamma u z ρ +
          (r / ρ) ^ (-1 : ℝ) * gamma u z ρ ^ (3 / 2 : ℝ) +
          (r / ρ) ^ (-1 : ℝ) * delta p z ρ * gamma u z ρ ^ (1 / 2 : ℝ)) +
        C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u z ρ ^ (1 / 2 : ℝ) *
          lambda q f z ρ ^ (1 / 2 : ℝ))
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
    (hThetaDecay : ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {w : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder w.1 w.2 ρ) ⊆ spaceTimeSet Ω I →
      theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
        C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p w ρ +
          C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
            (beta u Du w ρ ^ (1 / 2 : ℝ) + beta u Du w ρ) *
              theta (iterationKappa C₂₇) u Du p w ρ +
          C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
            theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
              lambda q f w ρ ^ (1 / 2 : ℝ) +
          C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ ∧
      (theta (iterationKappa C₂₇) u Du p w ρ ≤ 1 →
        theta (iterationKappa C₂₇) u Du p w (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ +
            2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p w ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
              theta (iterationKappa C₂₇) u Du p w ρ ^ (1 / 2 : ℝ) *
                lambda q f w ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f w ρ)) :
    ∃ ε₀ : ℝ, ∃ KU KD : ℝ≥0∞, 0 < ε₀ ∧ KU < ⊤ ∧ KD < ⊤ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        (∀ i, morreyNorm 3 (25 / 3 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => u z i)) ≤ KU) ∧
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => Du z i j)) ≤ KD) := by
  obtain ⟨ε₀, hε₀, N, hroute⟩ := CKN.theoremA_initial_morrey_wide_of_inputs
    q C₂₅ C₂₆ C₂₇ C₂₈ C₃₂ hq hC₂₇ hC₂₈ hC₂₅ hC₂₆ hC₃₂
  let M := iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) *
    iterationEta C₂₇ * (iterationKappa C₂₇ / 4) ^ (-iterationEpsilon)
  refine ⟨ε₀, oneSidedVelocityMorreyBound M (iterationKappa C₂₇ / 4) ε₀,
    oneSidedGradientMorreyBound M (iterationKappa C₂₇ / 4) N, hε₀,
    oneSidedVelocityMorreyBound_lt_top M (iterationKappa C₂₇ / 4) ε₀,
    oneSidedGradientMorreyBound_lt_top M (iterationKappa C₂₇ / 4) N, ?_⟩
  intro Ω I u Du p f hsol hdom hsmall
  have h := hroute hsol hdom hsmall (hCaccGamma hsol) (hLin34 hsol) (hThetaDecay hsol)
  exact ⟨h.1, h.2.1⟩

end CKN.Core.Endgame
