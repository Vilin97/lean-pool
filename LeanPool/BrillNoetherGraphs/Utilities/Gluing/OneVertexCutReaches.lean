/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.InteriorScriptTransport
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexCutWedge

/-!
# A one-vertex cut is the free case of the transport lemma

`Utilities.Gluing.reaches_of_induced_script` localizes a picture to an induced
subgraph at the price of freezing the script on the boundary.  This file
records that a `OneVertexCut` is exactly the case where that price is zero:
the cut's `no_cross` field says the glue vertex is the *only* vertex of `left`
with an edge leaving `left`, and a script may always be normalised to vanish at
one prescribed vertex.

So the transport lemma subsumes the vertex-wedge delivery statement, and this
file is the machine-checked form of that claim.  What the transport lemma adds
beyond it is the case of a larger boundary, which a `OneVertexCut` cannot
express and which is what a chip-free component of a two-edge-connected core
actually presents.
-/

namespace Utilities.Gluing

open Utilities.Certificate.StrongSeparator

universe u

variable {K : CFGraph.{u}}

/-- Away from the glue vertex, every vertex of the left half of a one-vertex
cut is interior to it. -/
theorem interior_left_of_oneVertexCut (cut : OneVertexCut K) {u : K.V}
    (hu : u ∈ cut.left) (hne : u ≠ cut.glue) : Interior K cut.left u := by
  intro w hw
  have hright : w ∈ cut.right := (cut.vertex_cover w).resolve_left hw
  have hwne : w ≠ cut.glue := by
    intro hwg
    exact hw (hwg ▸ cut.glue_mem_left)
  exact cut.no_cross u hu hne w hright hwne

/-- **A picture proved on the left factor of a one-vertex cut is a picture on
the ambient graph.**  No condition on the script: a one-vertex cut is the free
case of `reaches_of_induced_script`. -/
theorem reaches_of_oneVertexCut_left (cut : OneVertexCut K)
    {D : CFDiv K} (hOff : ∀ v : K.V, v ∉ cut.left → 0 ≤ D v)
    {p : K.V} (hp : p ∈ cut.left)
    (t : firing_script cut.leftGraph)
    (hEff : effective ((fun x : cut.leftGraph.V => D x.val)
      - one_chip (⟨p, hp⟩ : cut.leftGraph.V) + prin cut.leftGraph t)) :
    Reaches K D p :=
  reaches_of_induced_script_of_unique_boundary cut.left_nonempty
    cut.glue_mem_left
    (fun _ hu hne => interior_left_of_oneVertexCut cut hu hne)
    hOff hp t hEff

end Utilities.Gluing
