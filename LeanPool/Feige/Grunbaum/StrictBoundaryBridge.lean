/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Grunbaum.ProbabilityCore

/-!
# Passing from closed to strict halfspaces
-/

open MeasureTheory Set

noncomputable section

namespace Grunbaum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- A nonzero linear functional has no boundary mass, so closed and strict
halfspaces cut the same volume from every measurable set. -/
theorem volume_inter_le_eq_volume_inter_lt
    (K : Set E) (hK : MeasurableSet K)
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0) (t : ℝ) :
    volume (K ∩ {x | t ≤ L x}) =
      volume (K ∩ {x | t < L x}) := by
  have hlevel : volume {x : E | L x = t} = 0 := by
    simpa only [Set.preimage, Set.mem_singleton_iff, ofPred_mem_eq] using
      volume_preimage_singleton_eq_zero L hL t
  have hdecomp :
      K ∩ {x | t ≤ L x} =
        (K ∩ {x | t < L x}) ∪ (K ∩ {x | L x = t}) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_union]
    constructor
    · intro hx
      rcases hx with ⟨hxK, hxle⟩
      rcases hxle.lt_or_eq with hlt | heq
      · exact Or.inl ⟨hxK, hlt⟩
      · exact Or.inr ⟨hxK, heq.symm⟩
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.le⟩
      · exact ⟨hx.1, hx.2 ▸ le_rfl⟩
  have hboundary : volume (K ∩ {x : E | L x = t}) = 0 :=
    measure_mono_null inter_subset_right hlevel
  have hdisjoint :
      Disjoint (K ∩ {x : E | t < L x}) (K ∩ {x : E | L x = t}) := by
    refine Set.disjoint_left.2 ?_
    intro x hxlt hxeq
    exact (ne_of_gt hxlt.2) hxeq.2
  have hboundaryMeas : MeasurableSet (K ∩ {x : E | L x = t}) :=
    hK.inter ((measurableSet_singleton t).preimage L.measurable)
  rw [hdecomp]
  rw [measure_union hdisjoint hboundaryMeas, hboundary, add_zero]

end Grunbaum
