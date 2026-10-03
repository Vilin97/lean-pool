/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseDerivative

/-! # Origin growth from the common temporal remainder input

A majorant on each contained cylinder's time window extends by zero to the
whole time axis. The backward origin cover then applies with the same half
ball and the same cylinder scale. No symmetric enlargement of the time window
or additional pressure estimate is needed.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat
open CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- Extending each temporal majorant by zero gives the global-time remainder
input used by the origin derivative construction. -/
theorem originClause_global_remainder_of_temporal_majorant
    (hRemainderMajorant :
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}, 5 / 2 < q →
        ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
            closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
            ∃ M : ℝ → ℝ≥0∞,
              AEMeasurable M (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) ∧
              (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
              ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
                ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
                  ‖classicalGradient
                    (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                      (sourceSliceCentredMean z.1 ρ u) p s +
                      pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s) :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      ∃ M : ℝ → ℝ≥0∞, AEMeasurable M volume ∧
        (∫⁻ s, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
            ‖classicalGradient
              (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                (sourceSliceCentredMean z.1 ρ u) p s +
                pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s := by
  intro Ω I q u Du p f hsol z ρ hρ hsub
  obtain ⟨M, hm, hn, hb⟩ := hRemainderMajorant hsol.2.2.2.1 hsol hρ hsub
  obtain ⟨hm', hn'⟩ := glued_time_indicator_power measurableSet_Ioc hm hn
  refine ⟨(Ioc (z.2 - ρ ^ 2) z.2).indicator M, hm', hn', ?_⟩
  filter_upwards [hb, ae_restrict_mem measurableSet_Ioc] with s hs hsJ
  simpa only [indicator_of_mem hsJ] using hs

/-- The common temporal remainder input yields one measurable weak pressure gradient
with finite Morrey norms on the backward origin carrier. -/
theorem originClause_derivative_morrey_of_temporal_majorant
    (hRemainderMajorant :
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}, 5 / 2 < q →
        ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
            closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
            ∃ M : ℝ → ℝ≥0∞,
              AEMeasurable M (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) ∧
              (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
              ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
                ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
                  ‖classicalGradient
                    (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                      (sourceSliceCentredMean z.1 ρ u) p s +
                      pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s)
    {q τ R₀ R₁ : ℝ} {KU KD : ℝ≥0∞}
    (hq : 5/2 < q) (hτ : 25/3 ≤ τ) (hτhi : τ ≤ 25)
    (hR₁ : 0 < R₁) (hgap : R₁ < R₀) (hR₀ : R₀ < 1)
    (hKU : KU < ⊤) (hKD : KD < ⊤)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => u w i)) ≤ KU)
    (hDu : ∀ i j, morreyNorm 2 (25/8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => Du w i j)) ≤ KD) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y,s)) (fun y => Dp (y,s) i)) ∧
      ∀ i : Fin 3, morreyNorm (6/5 : ℝ) (min ((1/τ+8/25)⁻¹) q)
        ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun w => Dp w i)) < ⊤ := by
  exact originClause_derivative_morrey_of_shared_remainder
    (originClause_global_remainder_of_temporal_majorant hRemainderMajorant)
    hq hτ hτhi hR₁ hgap hR₀ hKU hKD hsol hdom hU hDu

/-- The common temporal remainder input yields the clipped growth bound for the
same selected gradient, uniformly over all centres and positive radii. -/
theorem originClause_clipped_growth_of_temporal_majorant
    (hRemainderMajorant :
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}, 5 / 2 < q →
        ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
            closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
            ∃ M : ℝ → ℝ≥0∞,
              AEMeasurable M (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) ∧
              (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
              ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
                ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
                  ‖classicalGradient
                    (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                      (sourceSliceCentredMean z.1 ρ u) p s +
                      pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s)
    {q τ R₀ R₁ : ℝ} {KU KD : ℝ≥0∞}
    (hq : 5/2 < q) (hτ : 25/3 ≤ τ) (hτhi : τ ≤ 25)
    (hR₁ : 0 < R₁) (hgap : R₁ < R₀) (hR₀ : R₀ < 1)
    (hKU : KU < ⊤) (hKD : KD < ⊤)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => u w i)) ≤ KU)
    (hDu : ∀ i j, morreyNorm 2 (25/8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => Du w i j)) ≤ KD) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y,s)) (fun y => Dp (y,s) i)) ∧
      ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ (i : Fin 3) (z : ParabolicPoint) (r : ℝ), 0 < r →
        (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-R₁^2) 0,
          eLpNorm (fun y => Dp (y,s) i) (ENNReal.ofReal (6/5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6/5 : ℝ)) ≤
          A * ENNReal.ofReal (r ^ (5 * (1 - (6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  exact originClause_clipped_growth_of_shared_remainder
    (originClause_global_remainder_of_temporal_majorant hRemainderMajorant)
    hq hτ hτhi hR₁ hgap hR₀ hKU hKD hsol hdom hU hDu

end CKN.Core.Step4
