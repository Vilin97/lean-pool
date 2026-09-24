/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient

/-!
# Route AOne Round

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential
open CKN.Core.Step3
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

/- This is the exact representation binder consumed by the local producer
   theorem.  Its test functions are supported in the same local product box
   as the cutoff. -/
def routeA_gradient_slot_representation : Prop :=
  ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
    ∀ {φ : Vec3 × ℝ → ℝ}, φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
    ∀ {Ω' : Set Vec3} {J : Set ℝ}, localBox Ω I Ω' J →
    tsupport φ ⊆ Ω' ×ˢ J →
    ∀ {Dp : ParabolicPoint → Vec3},
    (∀ i, Integrable (fun z => Dp z i)
      (volume.restrict (spaceTimeSet Ω' J))) →
    (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport ψ ⊆ Ω' ×ˢ J →
      (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
        -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
    localizedVelocity φ u =ᵐ[volume]
      (fun z i => heatPotential
        (fun w => localizedGradientSourceG φ u Du f Dp w i)
        (fun j w => localizedGradientSourceH φ u j w i) z)

end CKN.Core.Step4
