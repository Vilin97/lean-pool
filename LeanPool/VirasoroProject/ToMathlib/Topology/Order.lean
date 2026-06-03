/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.Order

/-!
# LeanPool.VirasoroProject.ToMathlib.Topology.Order
-/

section

open Filter
open scoped Topology

lemma DiscreteTopology.tendsto_nhds_iff_eventually_eq
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {ι : Type*} {F : Filter ι}
    (f : ι → X) (x : X) :
    F.Tendsto f (𝓝 x) ↔ F.Eventually (fun i ↦ f i = x) := by
  constructor <;>
  · intro h; simp_all

end
