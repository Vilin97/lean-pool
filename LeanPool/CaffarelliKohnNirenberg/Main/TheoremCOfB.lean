/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Covering.TheoremCReductionClosed
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.CaffarelliKohnNirenberg.Statements.SingularSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq

/-!
# Theorem C from the gradient criterion of Theorem B

This module derives the global nullity of the parabolic singular set (paper label
`thm:C`) from the ε-regularity criterion of paper label `thm:B`, stated with the
gradient limsup criterion.  The analytic content is entirely in `thm:B`; the
reduction from the criterion to vanishing one dimensional parabolic Hausdorff
measure is `CKN.singularSet_null_of_gradient_criterion_closed` from
`CKN/Covering/TheoremCReductionClosed.lean`.

The hypothesis `hB` below expresses the gradient criterion of `thm:B` for
`IsSuitableWeakSolutionIntegrable`.  The public theorem uses the equivalent
suitable-solution class; the class-equivalence bridge supplies this version
when assembling Theorem C.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Theorem C (paper label `thm:C`) follows from the gradient ε-regularity
criterion of Theorem B (paper label `thm:B`).  The criterion is taken as the
hypothesis `hB` for `IsSuitableWeakSolutionIntegrable`, with the same
gradient limsup condition and regular-point conclusion. -/
theorem caffarelliKohnNirenberg_of_epsilonRegularityGradient
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
  intro q hq Ω I u Du p f hsol
  obtain ⟨ε₁, hε, hcrit⟩ := hB q hq
  exact singularSet_null_of_gradient_criterion_closed hq ε₁ hε hsol
    (hcrit Ω I u Du p f hsol)

end CKN
