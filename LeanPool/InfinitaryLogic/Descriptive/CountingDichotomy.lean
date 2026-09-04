/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.ModelClassStandardBorel
import LeanPool.InfinitaryLogic.Descriptive.IsomorphismBorel
import LeanPool.InfinitaryLogic.Descriptive.StructureIsoSetoid
import Mathlib.SetTheory.Cardinal.Continuum
/-!
# Conditional Counting Dichotomy for Models

This file states the Silver–Burgess dichotomy as an explicit hypothesis, defines the
isomorphism equivalence relation on coded ℕ-models, and derives a conditional
counting theorem: for Lω₁ω sentences whose ℕ-models have bounded Scott height,
the number of isomorphism classes is either ≤ ℵ₀ or exactly 2^ℵ₀.

## Main Definitions

- `SilverBurgessDichotomy`: The Silver–Burgess dichotomy for Borel equivalence
  relations on standard Borel spaces.

The isomorphism relation `isoSetoid` this file counts is defined in
`Descriptive/StructureIsoSetoid.lean`, as the restriction of the ambient relation on
`StructureSpace L`.

## Main Results

- `counting_coded_models_dichotomy`: Conditional on `SilverBurgessDichotomy`, for
  any Lω₁ω sentence with bounded Scott height, the number of isomorphism classes
  among coded ℕ-models is either ≤ ℵ₀ or exactly 2^ℵ₀.
-/

universe u v w

namespace FirstOrder

namespace Language

open Cardinal Ordinal

/-- The Silver–Burgess dichotomy for Borel equivalence relations:
on a standard Borel space, a Borel equivalence relation has either
at most countably many classes or exactly continuum-many. -/
def SilverBurgessDichotomy : Prop :=
  ∀ {X : Type w} [MeasurableSpace X] [StandardBorelSpace X]
    (r : Setoid X),
    MeasurableSet {p : X × X | r.r p.1 p.2} →
    (#(Quotient r) ≤ ℵ₀) ∨ (#(Quotient r) = Cardinal.continuum)

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

omit [Countable (Σ l, L.Relations l)] in
/-- The subtype inclusion `↥(ModelsOf φ) × ↥(ModelsOf φ) → StructureSpace L × StructureSpace L`
is measurable. -/
private theorem measurable_subtypeVal_prod (φ : L.Sentenceω) :
    Measurable (fun p : ↥(ModelsOf φ) × ↥(ModelsOf φ) => (p.1.1, p.2.1)) :=
  (measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd)

/-- The isomorphism relation on coded ℕ-models is measurable when Scott height is bounded.
This lifts `iso_borel_of_bounded_scottHeight` to the subtype `↥(ModelsOf φ)`. -/
private theorem isoSetoid_measurableSet
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α) :
    MeasurableSet {p : ↥(ModelsOf φ) × ↥(ModelsOf φ) | (isoSetoid φ).r p.1 p.2} := by
  have hborel := iso_borel_of_bounded_scottHeight hα hbound
  have hset : {p : ↥(ModelsOf φ) × ↥(ModelsOf φ) | (isoSetoid φ).r p.1 p.2} =
      (fun p : ↥(ModelsOf φ) × ↥(ModelsOf φ) => (p.1.1, p.2.1)) ⁻¹'
        (IsoSet L ∩ (ModelsOf φ ×ˢ ModelsOf φ)) := by
    ext ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_prod, IsoSet]
    exact ⟨fun h => ⟨h, hc₁, hc₂⟩, fun ⟨h, _, _⟩ => h⟩
  rw [hset]
  exact (measurable_subtypeVal_prod φ) hborel

/-- Conditional counting theorem for ℕ-models with bounded Scott height:
if the Silver–Burgess dichotomy holds, then for any Lω₁ω sentence whose
ℕ-models all have Scott height ≤ α < ω₁, the number of isomorphism classes
among ℕ-models of φ is either ≤ ℵ₀ or exactly 2^ℵ₀. -/
theorem counting_coded_models_dichotomy
    (silver : SilverBurgessDichotomy.{v})
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α) :
    (#(Quotient (isoSetoid φ)) ≤ ℵ₀) ∨
    (#(Quotient (isoSetoid φ)) = Cardinal.continuum) :=
  silver (isoSetoid φ) (isoSetoid_measurableSet hα hbound)

end Language

end FirstOrder
