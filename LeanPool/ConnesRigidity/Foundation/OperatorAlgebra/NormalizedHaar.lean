/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 12472-12581.
Modifications: generalized the compact additive Haar lemmas from the paper
carriers to arbitrary compact groups and updated simplification proofs. Paper:
§3. See the upstream PORT_MAP.md.
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
The normalized haar component of the Connes rigidity formalization.
-/

namespace Connes
namespace NormalizedHaar

open MeasureTheory TopologicalSpace

noncomputable section

universe u v

/-- The probability normalization of additive Haar measure on a compact group. Paper: §3. -/
def normalizedAddHaar
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] : Measure A :=
  Measure.addHaarMeasure
    (⟨⟨Set.univ, isCompact_univ⟩, by
      simp only [interior_univ, Set.univ_nonempty]⟩ : PositiveCompacts A)

instance normalizedAddHaar_isProbabilityMeasure
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] :
    IsProbabilityMeasure (normalizedAddHaar A) where
  measure_univ := by
    simpa only [normalizedAddHaar, interior_univ, Set.univ_nonempty,
      PositiveCompacts.coe_mk, Compacts.coe_mk] using
      (Measure.addHaarMeasure_self
        (K₀ := (⟨⟨Set.univ, isCompact_univ⟩, by
          simp only [interior_univ, Set.univ_nonempty]⟩ : PositiveCompacts A)))

instance normalizedAddHaar_isAddHaarMeasure
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] :
    Measure.IsAddHaarMeasure (normalizedAddHaar A) := by
  unfold normalizedAddHaar
  infer_instance

/-- Probability-normalized additive Haar measure is unique. Paper: §3. -/
theorem normalizedAddHaar_unique
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    [Measure.IsAddLeftInvariant μ] :
    μ = normalizedAddHaar A := by
  let U : PositiveCompacts A :=
    ⟨⟨Set.univ, isCompact_univ⟩, by
      simp only [interior_univ, Set.univ_nonempty]⟩
  have h := Measure.addHaarMeasure_unique μ U
  change μ = μ Set.univ • normalizedAddHaar A at h
  simpa only [measure_univ, one_smul] using h

/-- Continuous additive automorphisms preserve normalized Haar measure. Paper: §3. -/
theorem normalizedAddHaar_preserving_addEquiv
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (e : A ≃+ A) (he : Continuous e) (heinv : Continuous e.symm) :
    MeasurePreserving e (normalizedAddHaar A) (normalizedAddHaar A) := by
  let μ := normalizedAddHaar A
  have mappedHaar : Measure.IsAddHaarMeasure (μ.map e) :=
    e.isAddHaarMeasure_map μ he heinv
  have mappedProbability : IsProbabilityMeasure (μ.map e) :=
    μ.isProbabilityMeasure_map he.measurable.aemeasurable
  refine ⟨he.measurable, ?_⟩
  exact normalizedAddHaar_unique A (μ.map e)

/-- A continuous fiber shear by an additive term preserves product Haar measure. Paper: §3. -/
theorem skew_add_translation_measurePreserving
    {P : Type u} {Q : Type v} [AddCommGroup P] [AddCommGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [SecondCountableTopology Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure P) (ν : Measure Q) [SFinite μ] [SFinite ν]
    [Measure.IsAddLeftInvariant μ] [Measure.IsAddLeftInvariant ν]
    (a : P) (b : Q) (c : P → Q) (hc : Continuous c) :
    MeasurePreserving
      (fun z : P × Q ↦ (a + z.1, b + z.2 + c z.1))
      (μ.prod ν) (μ.prod ν) := by
  refine MeasurePreserving.skew_product (μc := ν) (μd := ν)
    (g := fun x : P ↦ fun y : Q ↦ b + y + c x)
    (measurePreserving_add_left μ a) ?_ ?_
  · exact (measurable_const.add measurable_snd).add
      (hc.measurable.comp measurable_fst)
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    convert map_add_left_eq_self ν (b + c x) using 1
    congr 1
    funext y
    abel

/-- Product probability Haar measure for two compact additive groups. Paper: §3. -/
def productHaar
    (P : Type u) (Q : Type v)
    [AddGroup P] [AddGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q] : Measure (P × Q) :=
  (normalizedAddHaar P).prod (normalizedAddHaar Q)

instance productHaar_isProbabilityMeasure
    (P : Type u) (Q : Type v)
    [AddGroup P] [AddGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q] :
    IsProbabilityMeasure (productHaar P Q) := by
  unfold productHaar
  infer_instance

instance productHaar_isAddLeftInvariant
    (P : Type u) (Q : Type v)
    [AddCommGroup P] [AddCommGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q] :
    Measure.IsAddLeftInvariant (productHaar P Q) where
  map_add_left_eq_self z := by
    have hp := measurePreserving_add_left (normalizedAddHaar P) z.1
    have hq := measurePreserving_add_left (normalizedAddHaar Q) z.2
    change
      Measure.map
          (fun p : P × Q ↦ (z.1 + p.1, z.2 + p.2))
          ((normalizedAddHaar P).prod (normalizedAddHaar Q)) =
        (normalizedAddHaar P).prod (normalizedAddHaar Q)
    exact (hp.prod hq).map_eq

/-- The product measure agrees with normalized Haar measure on the product group. Paper: §3. -/
theorem productHaar_eq_normalizedAddHaar
    (P : Type u) (Q : Type v)
    [AddCommGroup P] [AddCommGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [SecondCountableTopology P] [SecondCountableTopology Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q] :
    productHaar P Q = normalizedAddHaar (P × Q) :=
  normalizedAddHaar_unique (P × Q) (productHaar P Q)

/-- Continuous additive automorphisms of a product preserve product Haar. Paper: §3. -/
theorem productHaar_preserving_addEquiv
    (P : Type u) (Q : Type v)
    [AddCommGroup P] [AddCommGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [SecondCountableTopology P] [SecondCountableTopology Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q]
    (e : (P × Q) ≃+ (P × Q)) (he : Continuous e) (heinv : Continuous e.symm) :
    MeasurePreserving e (productHaar P Q) (productHaar P Q) := by
  rw [productHaar_eq_normalizedAddHaar P Q]
  exact normalizedAddHaar_preserving_addEquiv (P × Q) e he heinv

end
end NormalizedHaar
end Connes
