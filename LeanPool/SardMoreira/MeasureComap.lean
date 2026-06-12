/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# LeanPool.SardMoreira.MeasureComap
-/

open scoped ENNReal NNReal Set.Notation Pointwise
open MeasureTheory Filter Set Function Metric Topology

namespace MeasureTheory.Measure

theorem _root_.MeasureTheory.nullMeasurableSet_sum {ι α : Type*} {_ : MeasurableSpace α}
    [Countable ι] {μ : ι → Measure α} {s : Set α} :
    NullMeasurableSet s (.sum μ) ↔ ∀ i, NullMeasurableSet s (μ i) := by
  refine ⟨fun hs i ↦ hs.mono <| Measure.le_sum _ _, fun h ↦ ?_⟩
  use ⋂ i, toMeasurable (μ i) s, by measurability
  rw [EventuallyEq, Measure.ae_sum_iff]
  intro i
  refine (subset_iInter fun i ↦ subset_toMeasurable (μ i) s).eventuallyLE.antisymm ?_
  exact (iInter_subset _ i).eventuallyLE.trans (h i).toMeasurable_ae_eq.le

instance {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} (μ : Measure β) (f : α → β)
    [IsFiniteMeasure μ] : IsFiniteMeasure (μ.comap f) where
  measure_univ_lt_top :=
    (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans_lt (measure_lt_top _ _)

theorem comap_sum_countable {ι α β : Type*} {_ : MeasurableSpace α}
    {_ : MeasurableSpace β} [Countable ι] {f : α → β} {μ : ι → Measure β}
    (hf : ∀ i t, MeasurableSet t → NullMeasurableSet (f '' t) (μ i)) :
    (Measure.sum μ).comap f = .sum fun i ↦ (μ i).comap f := by
  by_cases hfi : Injective f
  · ext1 s hs
    simp +contextual [Measure.sum_apply_of_countable, comap_apply₀, hs.nullMeasurableSet,
      nullMeasurableSet_sum, hfi, hf]
  · simp [comap_undef, hfi]

namespace FiniteSpanningSetsIn

/-- The `FiniteSpanningSetsIn` of `μ.comap f` obtained by pulling back a
`FiniteSpanningSetsIn` of `μ` through a measurable preimage map. -/
protected def comap {α β : Type*}
    {_ : MeasurableSpace α} {_ : MeasurableSpace β} {μ : Measure β} {T : Set (Set β)}
    (sets : μ.FiniteSpanningSetsIn T) {S : Set (Set α)} {f : α → β} (hf : MapsTo (f ⁻¹' ·) T S)
    (hmeas : ∀ n, MeasurableSet (f ⁻¹' (sets.set n))) :
    (μ.comap f).FiniteSpanningSetsIn S where
  set n := f ⁻¹' (sets.set n)
  set_mem n := hf <| sets.set_mem n
  finite n := (Measure.comap_apply_le _ _ (hmeas n).nullMeasurableSet).trans_lt <|
    (measure_mono (image_preimage_subset _ _)).trans_lt <| sets.finite n
  spanning := by simp [← preimage_iUnion, sets.spanning]

end FiniteSpanningSetsIn

protected theorem _root_.MeasureTheory.SigmaFinite.comap
    {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} (μ : Measure β) {f : α → β}
    (hf : Measurable f) [SigmaFinite μ] : SigmaFinite (μ.comap f) :=
  ⟨⟨μ.toFiniteSpanningSetsIn.comap (mapsTo_univ _ _) fun n ↦
    hf <| μ.toFiniteSpanningSetsIn.set_mem n⟩⟩

instance {α : Type*} {_ : MeasurableSpace α} {p : α → Prop} {μ : Measure α} [SigmaFinite μ] :
    SigmaFinite (μ.comap (↑) : Measure (Subtype p)) :=
  .comap μ measurable_subtype_coe

instance {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} (μ : Measure β) [SFinite μ]
    (f : α → β) : SFinite (μ.comap f) := by
  by_cases hf : ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ
  · rw [← sum_sfiniteSeq μ, Measure.comap_sum_countable]
    · infer_instance
    · exact fun n t ht ↦ (hf t ht).mono (sfiniteSeq_le _ _)
  · rw [Measure.comap_undef]
    · infer_instance
    · exact mt And.right hf

end MeasureTheory.Measure
