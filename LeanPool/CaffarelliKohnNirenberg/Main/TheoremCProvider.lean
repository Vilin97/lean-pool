/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremCOfB

/-!
# Theorem CProvider

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-! This module assembles Theorem C from the gradient criterion of Theorem B
for `IsSuitableWeakSolutionIntegrable`.  It is imported by `CKN.Main.TheoremC`
and participates in the public theorem assembly. -/

/-- Conditional assembly of Theorem C from the reduction in
`TheoremCOfB.lean`. -/
theorem caffarelliKohnNirenberg_provider_of_epsilonRegularityGradient
    (hB : ∀ (q : ℝ), 5 / 2 < q →
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
            IsRegularPoint Ω I u z₀) :
    ∀ (q : ℝ), 5 / 2 < q →
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 := by
  exact caffarelliKohnNirenberg_of_epsilonRegularityGradient hB

end CKN
