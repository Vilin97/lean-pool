/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Order
import Mathlib.Topology.WithTopology
/-!
# Topological API for `WithTopology`

This file adds only the two topology lemmas used by valuation theory. The
underlying type, topology, and basic API come directly from Mathlib. Algebraic
structures needed on a particular topology-indexed copy are installed at that
copy's owner rather than globally in the root `WithTopology` namespace.
-/

universe u v

namespace WithTopology

variable {X : Type u} {t : TopologicalSpace X}

/-- The canonical homeomorphism from Mathlib's topology-indexed copy to its
underlying carrier equipped with the indexed topology. -/
def homeomorph {α : Type u} {topology : TopologicalSpace α} :
    @Homeomorph (WithTopology α topology) α
      (inferInstance : TopologicalSpace (WithTopology α topology)) topology where
  toEquiv := WithTopology.equiv α topology
  continuous_toFun := continuous_ofTopology topology
  continuous_invFun := continuous_toTopology topology

/-- Convergence in a topology-indexed copy is convergence of the underlying
points for the indexed topology. -/
theorem tendsto_nhds_iff {ι : Type v} {l : Filter ι}
    {f : ι → WithTopology X t} {x : WithTopology X t} :
    Filter.Tendsto f l (nhds x) ↔
      Filter.Tendsto (fun i => (f i).ofTopology) l
        (@nhds X t x.ofTopology) := by
  have h :=
    (homeomorph (α := X) (topology := t)).isEmbedding.tendsto_nhds_iff
    (f := f) (l := l) (y := x)
  exact h

end WithTopology
