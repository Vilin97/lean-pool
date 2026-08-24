/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 16002-16173,
16860-16867, 16880-16893, and 18025-18036.
Modifications: extracted the generic measure-to-invariant-vector spine and
made the Zhou detector and spectral construction explicit inputs; moved the
dual-action and energy guards to their first consumers. See the upstream PORT_MAP.md.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.ContinuousMap.CompactlySupported
import LeanPool.ConnesRigidity.Foundation.GroupTheory.SplitAbelianExtension

/-!
The spectral criterion component of the Connes rigidity formalization.
-/

namespace Connes

noncomputable section

universe u

open MeasureTheory
open scoped ENNReal NNReal CompactlySupported

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (PontryaginDual (Multiplicative A))]
  [BorelSpace (PontryaginDual (Multiplicative A))]

/-- Pontryagin dual of a discrete additive kernel. Paper: §3--4. -/
abbrev DiscreteCharacterSpace (A : Type u)
    [AddCommGroup A] [TopologicalSpace A] :=
  PontryaginDual (Multiplicative A)

/-- Inverse-dual action of a group on the character space. Paper: §4. -/
def dualCharacterAction
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (χ : DiscreteCharacterSpace A) : DiscreteCharacterSpace A where
  toFun a := χ (Multiplicative.ofAdd
    ((Multiplicative.toAdd (action h⁻¹)) (Multiplicative.toAdd a)))
  map_one' := by simp only [map_inv, toAdd_inv, toAdd_one, map_zero, ofAdd_zero, map_one]
  map_mul' a b := by
    change χ (Multiplicative.ofAdd
      ((Multiplicative.toAdd (action h⁻¹))
        (Multiplicative.toAdd a + Multiplicative.toAdd b))) = _
    rw [map_add]
    exact map_mul χ _ _
  continuous_toFun := continuous_of_discreteTopology

omit [MeasurableSpace (PontryaginDual (Multiplicative A))]
  [BorelSpace (PontryaginDual (Multiplicative A))] in
@[simp] theorem dualCharacterAction_trivial
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    dualCharacterAction action h (1 : DiscreteCharacterSpace A) = 1 := by
  ext a
  rfl

omit [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- The continuous monoid homomorphism underlying the dual action. -/
private def dualActionBaseContinuous
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    Multiplicative A →ₜ* Multiplicative A where
  toMonoidHom := ((MulAutMultiplicative A).symm (action h)).toMonoidHom
  continuous_toFun := continuous_of_discreteTopology

omit [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- The inverse-dual action is continuous. Paper: §4. -/
theorem continuous_dualCharacterAction
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    Continuous (dualCharacterAction action h) := by
  -- `PontryaginDual.map` is the continuous-map model underlying the pointwise action.
  change Continuous (fun χ : DiscreteCharacterSpace A ↦
    PontryaginDual.map (dualActionBaseContinuous action h⁻¹) χ)
  exact (PontryaginDual.map (dualActionBaseContinuous action h⁻¹)).continuous_toFun

/-- The inverse-dual action is measurable. Paper: §4. -/
theorem measurable_dualCharacterAction
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    Measurable (dualCharacterAction action h) :=
  (continuous_dualCharacterAction action h).measurable

/-- Invariant probability measure for the dual action, whose measurability is
recorded by `measurable_dualCharacterAction`. Paper: §4. -/
def IsInvariantSpectralMeasure
    (action : H →* Multiplicative (AddAut A))
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) : Prop :=
  ∀ h : H,
    (μ : Measure (DiscreteCharacterSpace A)).map
      (dualCharacterAction action h) = μ

/-- Mass of the trivial character. Paper: §4. -/
def spectralTrivialAtom
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) : ℝ :=
  (μ : Measure (DiscreteCharacterSpace A)).real {1}

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Character evaluation is continuous on the compact dual. Paper: §4. -/
theorem continuous_character_evaluation (a : A) :
    Continuous (fun χ : DiscreteCharacterSpace A ↦
      ((χ (Multiplicative.ofAdd a) : Circle) : ℂ)) := by
  -- Expose the continuous homomorphism carrier used by `continuous_eval_const`.
  change Continuous (fun χ : Multiplicative A →ₜ* Circle ↦
    ((χ (Multiplicative.ofAdd a) : Circle) : ℂ))
  exact continuous_subtype_val.comp
    (continuous_eval_const (Multiplicative.ofAdd a))

omit [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Compactly supported continuous test for spectral displacement. Paper: §4. -/
def spectralEnergyTest (a : A) :
    C_c(DiscreteCharacterSpace A, ℝ) where
  toFun χ := ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
  continuous_toFun :=
    ((continuous_character_evaluation a).sub continuous_const).norm.pow 2
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

omit [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
@[simp] theorem spectralEnergyTest_apply
    (a : A) (χ : DiscreteCharacterSpace A) :
    spectralEnergyTest a χ =
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2 := rfl

omit [DiscreteTopology A] in
/-- The spectral displacement integrand is integrable against every probability measure. -/
theorem integrable_spectralEnergyTest
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a : A) :
    Integrable (fun χ : DiscreteCharacterSpace A ↦
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2)
      (μ : Measure (DiscreteCharacterSpace A)) := by
  refine Integrable.of_bound ?_ 4 ?_
  · exact
      (((continuous_character_evaluation a).sub continuous_const).norm.pow 2).aestronglyMeasurable
  · filter_upwards with χ
    have hnorm : ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [Circle.norm_coe]; norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsquare := mul_self_le_mul_self (norm_nonneg _) hnorm
    nlinarith

/-- Spectral displacement energy of a kernel element. Its integrand is
integrable by `integrable_spectralEnergyTest`. Paper: §4. -/
def spectralDetectionEnergy
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a : A) : ℝ :=
  ∫ χ : DiscreteCharacterSpace A,
    ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
      ∂(μ : Measure (DiscreteCharacterSpace A))

/-- A normalized vector fixed by the quotient section. Paper: §4. -/
structure QuotientFixedUnitVector
    (E : SplitAbelianExtension A G H)
    (K : Type u) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K) where
  /--
  The `vector` component of `QuotientFixedUnitVector`.
  -/
  vector : K
  norm_one : ‖vector‖ = 1
  quotient_fixed : ∀ h : H,
    (π (E.splitting h) : K →L[ℂ] K) vector = vector

/-- Representation-specific spectral input used by the generic criterion.
Paper: §4. -/
structure SpectralMeasureInterface
    (E : SplitAbelianExtension A G H)
    (K : Type u) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K) where
  quotient_fixed_approximation :
    HasKazhdanPropertyT H →
      π.HasAlmostInvariantUnitVectors →
        ∀ (J : Finset A) (ε : ℝ), 0 < ε →
          ∃ ξ : QuotientFixedUnitVector E K π,
            (∑ a ∈ J,
              ‖(π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K)
                  ξ.vector - ξ.vector‖ ^ 2) < ε
  /--
  The `measure` component of `SpectralMeasureInterface`.
  -/
  measure : QuotientFixedUnitVector E K π →
    ProbabilityMeasure (DiscreteCharacterSpace A)
  measure_invariant : ∀ ξ,
    IsInvariantSpectralMeasure E.action (measure ξ)
  energy_eq : ∀ (ξ : QuotientFixedUnitVector E K π) (a : A),
    spectralDetectionEnergy (measure ξ) a =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K)
          ξ.vector - ξ.vector‖ ^ 2
  positive_atom_invariant :
    ∀ ξ : QuotientFixedUnitVector E K π,
      0 < spectralTrivialAtom (measure ξ) →
        ∃ η : K, η ≠ 0 ∧
          (∀ a : A,
            (π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K) η = η) ∧
          (∀ h : H, (π (E.splitting h) : K →L[ℂ] K) η = η)

/-- Finite spectral detection inequality. Paper: §4. -/
def HasFiniteSpectralDetection
    (E : SplitAbelianExtension A G H) (J : Finset A) (c : ℝ) : Prop :=
  ∀ μ : ProbabilityMeasure (DiscreteCharacterSpace A),
    IsInvariantSpectralMeasure E.action μ →
      c * (1 - spectralTrivialAtom μ) ≤
        ∑ a ∈ J, spectralDetectionEnergy μ a

omit [BorelSpace (DiscreteCharacterSpace A)] in
theorem exists_positive_spectral_atom
    (E : SplitAbelianExtension A G H)
    {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K)
    (spectral : SpectralMeasureInterface E K π)
    (hH : HasKazhdanPropertyT H)
    (hπ : π.HasAlmostInvariantUnitVectors)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c) :
    ∃ ξ : QuotientFixedUnitVector E K π,
      0 < spectralTrivialAtom (spectral.measure ξ) := by
  obtain ⟨ξ, hsmall⟩ :=
    spectral.quotient_fixed_approximation hH hπ J c hc
  refine ⟨ξ, ?_⟩
  have hdet := hdetection (spectral.measure ξ)
    (spectral.measure_invariant ξ)
  simp_rw [spectral.energy_eq] at hdet
  nlinarith

omit [BorelSpace (DiscreteCharacterSpace A)] in
theorem spectral_criterion_representation
    (E : SplitAbelianExtension A G H)
    {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K)
    (spectral : SpectralMeasureInterface E K π)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    ∃ ξ : K, ξ ≠ 0 ∧ π.IsInvariant ξ := by
  obtain ⟨ξ, hatom⟩ :=
    exists_positive_spectral_atom E π spectral hH hπ J hc hdetection
  obtain ⟨η, hη, hkernel, hquotient⟩ :=
    spectral.positive_atom_invariant ξ hatom
  exact ⟨η, hη,
    E.invariant_of_kernel_and_quotient π η hkernel hquotient⟩

omit [BorelSpace (DiscreteCharacterSpace A)] in
theorem spectral_criterion
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (spectral : ∀ (K : Type u)
      (_ : NormedAddCommGroup K)
      (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K)
      (π : UnitaryRepresentation G K),
        SpectralMeasureInterface E K π) :
    HasKazhdanPropertyT G := by
  intro K _ _ _ π hπ
  exact spectral_criterion_representation E π
    (spectral K inferInstance inferInstance inferInstance π)
    hH J hc hdetection hπ

end
end Connes
