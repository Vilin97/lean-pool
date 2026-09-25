/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeGenusOne
import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso

/-!
# Transport of pointed genus-one rigidity

The rigid pointed-cycle predicate is invariant under graph isomorphism.  This
small transport lemma is useful when nested induced-subgraph cuts introduce
extra subtype layers around an already-certified marker cycle.
-/

namespace Utilities

universe u v

namespace PointedGenusOneRigid

/-- Transport a pointed rigid genus-one graph along a graph isomorphism. -/
theorem map {G : CFGraph.{u}} {H : CFGraph.{v}} {root : G.V}
    (hRigid : PointedGenusOneRigid G root) (equivalence : CFGraphIso G H) :
    PointedGenusOneRigid H (equivalence.vertexEquiv root) where
  connected := equivalence.graph_connected_map hRigid.connected
  genus_one := equivalence.genus_eq.trans hRigid.genus_one
  exists_ne := by
    obtain ⟨p, hp⟩ := hRigid.exists_ne
    exact ⟨equivalence.vertexEquiv p, fun h =>
      hp (equivalence.vertexEquiv.injective h)⟩
  nontrivial := by
    intro q hq hLinear
    let p := equivalence.vertexEquiv.symm q
    have hp : p ≠ root := by
      intro h
      apply hq
      exact (equivalence.vertexEquiv.apply_symm_apply q).symm.trans
        (congrArg equivalence.vertexEquiv h)
    apply hRigid.nontrivial p hp
    apply (equivalence.linear_equiv_mapDiv_iff
      (oneChip root - oneChip p) 0).mp
    simpa [p] using hLinear

end PointedGenusOneRigid

end Utilities
