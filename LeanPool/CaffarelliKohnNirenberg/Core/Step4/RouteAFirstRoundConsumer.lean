/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAOneRoundFinal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyFirstRound

/-!
# The first round of `prop:bootstrap` with its source data supplied

The one-round velocity improvement of `prop:bootstrap` takes three
inputs: the pressure-gradient producer, the gradient-slot heat
representation, and the localized source data of `eq:local-equation` at the
first-round exponents `(6/5, 25/11)` and `(3, 25/6)`.  The last of these is
`first_round_source_package_of_sws`, so the round below carries only the two
remaining inputs.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-- The localized first-round source data of `eq:local-equation` in the exact
shape consumed by the one-round velocity improvement. -/
theorem routeA_final_source_package_of_sws : routeAFinalSourcePackage :=
  first_round_source_package_of_sws

/-- One round of `prop:bootstrap` on an arbitrary parabolic ball:
from `u ∈ M^{3,25/3}` and `∇u ∈ M^{2,25/8}` on `𝔅_R(z₀)` the velocity
improves to `u ∈ M^{3,25}` on `𝔅_{R/4}(z₀)`, given the pressure-gradient
producer and the gradient-slot heat representation. -/
theorem routeA_one_round_velocity_improvement_of_gradient_inputs
    (hG : routeAGradientProducer)
    (hL : routeAGradientSlotRepresentation) :
    ∀ q : ℝ, 5 / 2 < q →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
        Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
        morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u →
        (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
          (Metric.ball z₀ R) (fun z => Du z i)) →
        morreyVecMem 3 25 (Metric.ball z₀ (R / 4)) u :=
  routeA_one_round_velocity_improvement_of_producers_final hG hL
    routeA_final_source_package_of_sws

end CKN.Core.Step4
