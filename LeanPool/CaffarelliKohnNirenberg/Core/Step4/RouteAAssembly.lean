/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PointwisePotential
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Bootstrap
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CarrierLocalAE
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsM4
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-!
# Route AAssembly

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential
open CKN.Core.Step3

noncomputable section

namespace CKN.Core.Step4

/-! The Route A one-round interfaces: the producer propositions consumed by
    the bootstrap round, together with the round's exponent arithmetic. -/

/-! This producer is the explicit global-to-local seam for a heat-potential
core.  It records both the a.e. carrier identification and the conversion
from scalar component norms to the vector Morrey membership used by Route A. -/
def routeA_carrier_restriction_producer : Prop :=
  ∀ {Q₃ : Set ParabolicPoint} {u v : ParabolicPoint → Vec3},
    MeasurableSet Q₃ →
    morreyNorm 3 25 (fun z => vec3EuclideanNorm (v z)) < ∞ →
    u =ᵐ[volume.restrict Q₃] v →
    morreyVecMem 3 25 Q₃ u

theorem routeA_carrier_restriction_producer_of_core :
    routeA_carrier_restriction_producer := by
  intro Q₃ u v hQ hcore hcut
  exact CKN.Core.Endgame.morreyVecMem_three_twentyFive_of_ae_eq_restrict
    hQ hcut hcore


theorem routeA_round_exponents :
    2 * (25 / 11 : ℝ) < 5 ∧
      1 / (25 / 11 : ℝ) - 2 / 5 = 1 / 25 ∧
      (6 / 5 : ℝ) / (1 - 2 * (25 / 11 : ℝ) / 5) = 66 / 5 ∧
      (25 / 11 : ℝ) / (1 - 2 * (25 / 11 : ℝ) / 5) = 25 := by
  norm_num

/-! The following producer types are the exact boundaries consumed by the
one-round argument.  They keep the pressure-gradient construction, the local
heat representation, and the quarter-radius conclusion separate until their
analytic implementations are available.  The gradient boundary states a
Morrey membership, so it carries no Calderón--Zygmund constant: the
`L^{6/5}` control needed to build the selected field belongs to the
construction that discharges this interface, not to its statement. -/

def routeA_gradient_producer : Prop :=
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
      ∃ Dp : ParabolicPoint → Vec3,
        (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
          (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
        (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
        morreyVecMem (6 / 5 : ℝ)
          (min ((1 / (25 / 3 : ℝ) + 8 / 25)⁻¹) q)
          (Metric.ball z₀ (R / 2)) Dp

def routeA_representation_producer : Prop :=
  ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
    ∀ {φ : Vec3 × ℝ → ℝ},
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
    ∀ {U : Set Vec3} {J : Set ℝ},
      localBox Ω I U J → tsupport φ ⊆ U ×ˢ J →
    ∀ {Dp : ParabolicPoint → Vec3},
      (∀ i : Fin 3, Integrable (fun z => Dp z i)
        (volume.restrict (spaceTimeSet U J))) →
      (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
        tsupport ψ ⊆ U ×ˢ J →
        (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
          -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
      localizedVelocity φ u =ᵐ[volume] (fun z i => heatPotential
        (fun w => localizedGradientSourceG φ u Du f Dp w i)
        (fun j w => localizedGradientSourceH φ u j w i) z)

end CKN.Core.Step4
