/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Statement
public import Mathlib.Data.Nat.Pairing

/-!
# Basic facts about one-dimensional rectifiability

Countable one-rectifiability is inherited by subsets and countable unions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped MeasureTheory NNReal

namespace LeanPool.Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A set is purely one-unrectifiable if it meets every rectifiable set in a null set. -/
def IsPurelyOneUnrectifiable (s : Set X) : Prop :=
  ∀ t, IsCountablyOneRectifiable t → μH[1] (s ∩ t) = 0

/-- A subset of a countably one-rectifiable set is countably one-rectifiable. -/
theorem IsCountablyOneRectifiable.mono {s t : Set X} (hs : IsCountablyOneRectifiable s)
    (ht : t ⊆ s) : IsCountablyOneRectifiable t := by
  obtain ⟨f, hf, hnull⟩ := hs
  refine ⟨f, hf, measure_mono_null ?_ hnull⟩
  intro x hx
  exact ⟨ht hx.1, hx.2⟩

/-- A set of zero Hausdorff one-measure is countably one-rectifiable. -/
theorem isCountablyOneRectifiable_of_measure_zero [Nonempty X] {s : Set X}
    (hs : μH[1] s = 0) : IsCountablyOneRectifiable s := by
  let ⟨x⟩ := ‹Nonempty X›
  let f : ℕ → ℝ → X := fun _ _ ↦ x
  refine ⟨f, fun _ ↦ ⟨0, LipschitzWith.const _⟩, ?_⟩
  exact measure_mono_null sdiff_subset hs

/-- The empty set is countably one-rectifiable in a nonempty metric space. -/
@[simp]
theorem isCountablyOneRectifiable_empty [Nonempty X] :
    IsCountablyOneRectifiable (∅ : Set X) := by
  exact isCountablyOneRectifiable_of_measure_zero (measure_empty : μH[1] (∅ : Set X) = 0)

/-- A countable union of countably one-rectifiable sets is countably one-rectifiable. -/
theorem isCountablyOneRectifiable_iUnion {s : ℕ → Set X}
    (hs : ∀ i, IsCountablyOneRectifiable (s i)) :
    IsCountablyOneRectifiable (⋃ i, s i) := by
  classical
  choose f hf hnull using hs
  let g : ℕ → ℝ → X := fun n ↦ f n.unpair.1 n.unpair.2
  refine ⟨g, fun n ↦ hf n.unpair.1 n.unpair.2, ?_⟩
  apply measure_mono_null ?_ (measure_iUnion_null hnull)
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx.1
  refine mem_iUnion.mpr ⟨i, hxi, ?_⟩
  intro hxrange
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hxrange
  apply hx.2
  refine mem_iUnion.mpr ⟨Nat.pair i j, ?_⟩
  simpa [g] using hxj

/-- The union of two countably one-rectifiable sets is countably one-rectifiable. -/
theorem IsCountablyOneRectifiable.union {s t : Set X} (hs : IsCountablyOneRectifiable s)
    (ht : IsCountablyOneRectifiable t) : IsCountablyOneRectifiable (s ∪ t) := by
  rw [show s ∪ t = (⋃ n : ℕ, if n = 0 then s else t) by
    ext x
    constructor
    · rintro (hxs | hxt)
      · exact mem_iUnion_of_mem 0 (by simpa using hxs)
      · exact mem_iUnion_of_mem 1 (by simpa using hxt)
    · intro hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      by_cases hn : n = 0
      · exact Or.inl (by simpa [hn] using hxn)
      · exact Or.inr (by simpa [hn] using hxn)]
  apply isCountablyOneRectifiable_iUnion
  intro n
  split_ifs <;> assumption

/-- Pure one-unrectifiability is inherited by subsets. -/
theorem IsPurelyOneUnrectifiable.mono {s t : Set X} (hs : IsPurelyOneUnrectifiable s)
    (ht : t ⊆ s) : IsPurelyOneUnrectifiable t := by
  intro u hu
  exact measure_mono_null (inter_subset_inter_left u ht) (hs u hu)

/-- A rectifiable subset of a purely unrectifiable set has zero Hausdorff one-measure. -/
theorem IsPurelyOneUnrectifiable.measure_zero_of_rectifiable_subset {s t : Set X}
    (hs : IsPurelyOneUnrectifiable s) (ht : IsCountablyOneRectifiable t) (hts : t ⊆ s) :
    μH[1] t = 0 := by
  simpa [inter_eq_right.mpr hts] using hs t ht

end LeanPool.Besicovitch
