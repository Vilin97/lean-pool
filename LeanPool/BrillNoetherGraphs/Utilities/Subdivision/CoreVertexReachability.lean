/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator

/-!
# Rank-one existence from reaching the core of a subdivision

The embedded core vertices are a strong separator in every positive
subdivision.  Consequently, on a connected subdivision, it is enough for a
divisor to reach every core vertex in order to have rank at least one.  This
is the common final step shared by explicit-potential, loop-split, and local
configuration certificates.
-/

namespace Utilities.Certificate.CoreVertexReachability

open Finset

/-- On a connected positive subdivision, a divisor which reaches every
embedded core vertex has rank at least one. -/
theorem bnExists_of_reaches_coreVertices
    {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (hConnected : graph_connected spec.graph)
    (D : CFDiv spec.graph) (degree : ℤ)
    (hDegree : deg D = degree)
    (hReaches : ∀ vertex : Fin n,
      StrongSeparator.Reaches spec.graph D (spec.coreVertex vertex)) :
    BNExists spec.graph 1 degree := by
  refine ⟨D, hDegree, ?_⟩
  apply StrongSeparator.rank_ge_one_of_strongSeparatorCertificate
    hConnected
    (ExplicitPotential.Certificate.coreVertices_nonempty spec)
    spec.coreVertices_strongSeparatorCertificate
  intro vertex hVertex
  obtain ⟨anchor, _hAnchor, rfl⟩ := Finset.mem_image.mp hVertex
  exact hReaches anchor

end Utilities.Certificate.CoreVertexReachability
