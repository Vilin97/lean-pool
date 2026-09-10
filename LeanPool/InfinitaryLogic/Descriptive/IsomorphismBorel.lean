/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.BFEquivBorel
import LeanPool.InfinitaryLogic.ModelTheory.CountingModels
/-!
# Isomorphism is Borel under Bounded Scott Height

This file proves that isomorphism restricted to models of a sentence is Borel
(measurable) when the Scott height is bounded by a countable ordinal.

## Main Results

- `iso_borel_of_bounded_scottHeight`: If all countable models of φ have Scott
  height ≤ α < ω₁, then the set of isomorphic pairs within ModelsOf(φ) × ModelsOf(φ)
  is measurable.
-/

universe u v

namespace FirstOrder

namespace Language

open Structure MeasureTheory Ordinal

variable {L : Language.{u, v}} [L.IsRelational]

/-- The set of code pairs whose decoded structures are isomorphic. -/
def IsoSet (L : Language.{u, v}) [L.IsRelational] : Set (StructurePairSpace L) :=
  {p | Nonempty (@Language.Equiv L ℕ ℕ p.1.toStructure p.2.toStructure)}

/-- Isomorphism on coded structures is Borel when Scott height is bounded.
If all countable models of φ have Scott height ≤ α < ω₁, then the set
of isomorphic pairs within ModelsOf(φ) × ModelsOf(φ) is measurable. -/
theorem iso_borel_of_bounded_scottHeight
    [Countable (Σ l, L.Relations l)]
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α) :
    MeasurableSet (IsoSet L ∩ (ModelsOf φ ×ˢ ModelsOf φ)) := by
  -- On ModelsOf φ × ModelsOf φ, IsoSet = BFEquivSet by bounded_scottHeight_iso_eq_BFEquiv
  suffices h : IsoSet L ∩ (ModelsOf φ ×ˢ ModelsOf φ) =
    BFEquivSet α 0 Fin.elim0 Fin.elim0 ∩ (ModelsOf φ ×ˢ ModelsOf φ) by
    rw [h]
    exact (bfEquivSet_measurableSet α hα 0 Fin.elim0 Fin.elim0).inter
      ((modelsOf_measurableSet φ).prod (modelsOf_measurableSet φ))
  ext ⟨c₁, c₂⟩
  simp only [Set.mem_inter_iff, Set.mem_prod]
  unfold IsoSet BFEquivSet ModelsOf ModelsOfBounded
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hiso, hc₁, hc₂⟩
    exact ⟨(@bounded_scottHeight_iso_eq_BFEquiv _ _ _ _ _ hα hbound
      ℕ ℕ c₁.toStructure c₂.toStructure _ _ hc₁ hc₂).mp hiso, hc₁, hc₂⟩
  · rintro ⟨hbf, hc₁, hc₂⟩
    exact ⟨(@bounded_scottHeight_iso_eq_BFEquiv _ _ _ _ _ hα hbound
      ℕ ℕ c₁.toStructure c₂.toStructure _ _ hc₁ hc₂).mpr hbf, hc₁, hc₂⟩

end Language

end FirstOrder
