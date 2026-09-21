/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Closure

/-!
# Frontier points of open sets

## Main results

* `IsOpen.notMem_of_mem_frontier`: A frontier point of an open set does not belong to the set.
-/

public section

/-- A frontier point of an open set does not belong to the set. -/
theorem IsOpen.notMem_of_mem_frontier {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsOpen s) {x : X} (hx : x ∈ frontier s) : x ∉ s := by
  rw [hs.frontier_eq] at hx
  exact hx.2

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
