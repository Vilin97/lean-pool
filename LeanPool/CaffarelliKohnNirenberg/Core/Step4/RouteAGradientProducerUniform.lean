/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSymmetricCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAGradientProducerUniformExponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.RouteAGradientProducerUniformMorrey
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Route AGradient Producer Uniform

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-! # The pressure-gradient producer at a free velocity exponent

The bootstrap of `prop:bootstrap` runs the velocity through the whole range
`τ ∈ [25/3, 25]` of Morrey exponents, and each round needs the pressure
gradient in `M^{6/5, κ(τ)}` with `1/κ(τ) = 1/τ + 1/τ₃` and `τ₃ = 25/8`, that
is `κ(τ) = (1/τ + 8/25)⁻¹`.  The symmetric-ball producer interfaces are
stated here with `τ` free, and the established `τ = 25/3` producers are identified
as the base point of that family.
-/

/-- The slicewise `L^{6/5}` pressure-gradient production on the symmetric
ball, with the incoming velocity Morrey exponent `τ` free.  The conclusion
does not mention `τ`: only the hypothesis on `u` does. -/
def symmetricPressureGradientSliceProducerUniform : Prop :=
  ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
      Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
      morreyVecMem 3 τ (Metric.ball z₀ R) u →
      (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
        (Metric.ball z₀ R) (fun z => Du z i)) →
      ∃ K : Fin 3 → ℝ → ℝ≥0∞,
        ∀ᵐ t ∂(volume.restrict (Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2))),
          ∀ i : Fin 3, ∃ g : Vec3 → ℝ,
            LocallyIntegrableOn g (vec3Ball z₀.1 R) volume ∧
            HasWeakPartialDerivOn (vec3Ball z₀.1 R) i
              (fun x => p (x, t)) g ∧
            eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
              (volume.restrict (vec3Ball z₀.1 (R / 2))) ≤ K i t

/-- The Route A pressure-gradient producer at a free velocity exponent.  This
is the statement consumed by the regularity provider for every `τ` that the
bootstrap of `prop:bootstrap` visits. -/
def routeAGradientProducerUniform : Prop :=
  ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
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
          (Metric.ball z₀ (R / 2)) Dp

/-! The exponent `τ = 25/3` instance.  It identifies the established
single-exponent slice interface as the base point of the uniform family. -/

/-- At `τ = 25/3` the uniform slice producer is the established slice producer. -/
theorem symmetricPressureGradientSliceProducer_of_uniform
    (h : symmetricPressureGradientSliceProducerUniform) :
    symmetricPressureGradientSliceProducer := by
  intro q hq Ω I u Du p f hsol z₀ R hR hdom hu hDu
  exact h q (25 / 3) hq le_rfl (by norm_num) hsol z₀ R hR hdom hu hDu

/-! The slice production is exponent-generic for free: on a ball of finite
radius the Morrey exponent can be lowered, so the established `τ = 25/3` slice
producer already yields the whole uniform family.  The cell transfer is the
only interface of the symmetric route that carries the exponent into its
conclusion, so it is the one remaining `τ`-dependent analytic input. -/

/-- The established slice producer gives the `τ`-uniform slice producer. -/
theorem symmetricPressureGradientSliceProducerUniform_of_base
    (h : symmetricPressureGradientSliceProducer) :
    symmetricPressureGradientSliceProducerUniform := by
  intro q τ hq hτ _hτ' Ω I u Du p f hsol z₀ R hR hdom hu hDu
  exact h q hq hsol z₀ R hR hdom
    (morreyVecMem_ball_three_base_of_le hτ hR hu) hDu

end CKN.Core.Step4
