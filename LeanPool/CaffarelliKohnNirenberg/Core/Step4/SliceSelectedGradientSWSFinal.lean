/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSliceCZ
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSWSUnconditional

/-!
# Display (3.5) with the explicit Calderón–Zygmund endpoint constant

The preceding slice theorem takes the weak-gradient construction as an explicit
`hP1` input.  The concrete extension theorem supplies exactly that input at
`czGradientOperatorConstant`, so this module exposes the resulting
solution-level statement without an analytic Calderón–Zygmund premise.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-- Display (3.5) on a slice of a suitable weak solution with the explicit
`czGradientOperatorConstant` in the first-potential gradient bound. -/
theorem slice_selected_gradient_ae_of_sws_of_source_data_unconditional
    (C₁₇ C₁₁ C₈ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    (hC₈ : sliceForceGradientConstant ≤ C₈)
    {E F : ℝ → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {V : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hC₁₁ : 0 ≤ C₁₁) (hE : ∀ s, 0 ≤ E s) (hF : ∀ s, 0 ≤ F s)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ C₁₁ * (E s) ^ (2 / 3 : ℝ))
    (hP78 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤ F s)
    (hV : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, MemLp (fun x => V (x, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x => V (x, s) i)))
    (hVpair : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∑ i : Fin 3, ∫ x, V (x, s) i * spatialDeriv ψ i x) =
          pressureSecondPairing
            (fun i j x => mollifiedBallCutoff z.1 hρ x *
              pressureUTensor u (fun t j => average
                (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) (x, s) i j) ψ) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k)
          (euclideanBall z.1 (ρ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (fun x => p (x, s)) (fun x => D x k)) ∧
        (∀ k : Fin 3, eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
          ENNReal.ofReal czGradientOperatorConstant *
              (∑ i : Fin 3, eLpNorm (fun x => V (x, s) i)
                (ENNReal.ofReal (6 / 5 : ℝ)) volume) +
            ENNReal.ofReal (C₁₇ *
              (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
                  (volume.restrict (euclideanBall z.1 ρ)) +
                C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s) * ρ ^ (-1 / 2 : ℝ)) +
            ENNReal.ofReal (sliceForceGradientBound czGradientOperatorConstant C₈
              z.1 hρ f s)) := by
  have hC_CZ : 0 ≤ czGradientOperatorConstant := by
    simp only [czGradientOperatorConstant, czGradientComponentConstant]
    positivity
  have hP1 : ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal czGradientOperatorConstant *
            eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    intro i G hG hGc
    exact exists_weak_pressure_gradient_unconditional i G hG hGc
  exact slice_selected_gradient_ae_of_sws_of_source_data_unconditional_with_hP1
    czGradientOperatorConstant C₁₇ C₁₁ C₈ hC_CZ hC₁₇ hC₈ hsol hρ hsub hC₁₁ hE hF
    hP1 hCZ_p1 hP78 hV hVpair

end CKN.Core.Step4
