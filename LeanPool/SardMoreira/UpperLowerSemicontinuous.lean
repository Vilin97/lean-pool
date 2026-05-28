/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.Semicontinuity.Basic

open Set Filter Function TopologicalSpace

namespace Topology

variable {X Y : Type*} [TopologicalSpace X] [LinearOrder Y] {f : X → Y} {s : Set X} {x : X}

theorem continuousWithinAt_toLower_comp_iff :
    ContinuousWithinAt (WithLower.toLower ∘ f) s x ↔ UpperSemicontinuousWithinAt f s x :=
  IsLower.tendsto_nhds_iff_lt

theorem continuousWithinAt_toUpper_comp_iff :
    ContinuousWithinAt (WithUpper.toUpper ∘ f) s x ↔ LowerSemicontinuousWithinAt f s x :=
  IsUpper.tendsto_nhds_iff_lt

theorem continuousAt_toLower_comp_iff :
    ContinuousAt (WithLower.toLower ∘ f) x ↔ UpperSemicontinuousAt f x :=
  IsLower.tendsto_nhds_iff_lt

theorem continuousAt_toUpper_comp_iff :
    ContinuousAt (WithUpper.toUpper ∘ f) x ↔ LowerSemicontinuousAt f x :=
  IsUpper.tendsto_nhds_iff_lt

theorem continuousOn_toLower_comp_iff :
    ContinuousOn (WithLower.toLower ∘ f) s ↔ UpperSemicontinuousOn f s :=
  forall₂_congr fun _ _ ↦ continuousWithinAt_toLower_comp_iff

theorem continuousOn_toUpper_comp_iff :
    ContinuousOn (WithUpper.toUpper ∘ f) s ↔ LowerSemicontinuousOn f s :=
  forall₂_congr fun _ _ ↦ continuousWithinAt_toUpper_comp_iff

theorem continuous_toLower_comp_iff : Continuous (WithLower.toLower ∘ f) ↔ UpperSemicontinuous f :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ continuousAt_toLower_comp_iff

theorem continuous_toUpper_comp_iff : Continuous (WithUpper.toUpper ∘ f) ↔ LowerSemicontinuous f :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ continuousAt_toUpper_comp_iff

end Topology

-- Mathlib has this lemma, but the proof is less elegant there. TODO: upstream the proof
theorem LowerSemicontinuousOn.exists_isMinOn' {X α : Type*} [TopologicalSpace X] [LinearOrder α]
    {f : X → α} {s : Set X} (hf : LowerSemicontinuousOn f s) (hs : IsCompact s) (hne : s.Nonempty) :
    ∃ x ∈ s, IsMinOn f s x := by
  rw [← Topology.continuousOn_toUpper_comp_iff] at hf
  exact hs.exists_isMinOn (f := Topology.WithUpper.toUpper ∘ f) hne hf
