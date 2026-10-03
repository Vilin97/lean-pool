/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws

/-! The fixed-time maps of a smooth flow are C¹ inverses. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Flow

/-- For each pair of times, the two spatial flow maps are continuously
differentiable inverses of one another. -/
theorem flow_fixed_time_maps_are_C1_inverses
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) :
    ContDiff ℝ 1 (fun x => X t x s) ∧
      ContDiff ℝ 1 (fun x => X s x t) ∧
      (∀ x, X s (X t x s) t = x) ∧
      (∀ x, X t (X s x t) s = x) := by
  obtain ⟨L, _, hL⟩ := exists_global_spatial_lipschitz hb
  have hLip : ∃ L : ℝ, ∀ u x y, ‖b u x - b u y‖ ≤ L * ‖x - y‖ :=
    ⟨L, hL⟩
  refine ⟨flow_spatial_contDiff_one hb hX s t,
    flow_spatial_contDiff_one hb hX t s, ?_, ?_⟩
  · intro x
    calc
      X s (X t x s) t = X s x s := flow_group_law b hLip hX x s t s
      _ = x := hX.1 x s
  · intro x
    calc
      X t (X s x t) s = X t x t := flow_group_law b hLip hX x t s t
      _ = x := hX.1 x t

end AVenhance.Infra.Flow
