/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageBranches

/-!
# Exhaustive normalized-incidence classification

The 35 possible first rows reduce to seven symmetry orbits.  A kernel-audited
finite search excludes every completion of those canonical rows using checked
geometric obstruction witnesses.
-/

namespace Erdos97Octagon

open RawIncidence

/-- No normalized octagon incidence table has a convex planar realisation. -/
theorem normalized_convex_realisation_impossible
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q) (hN : Q.Normalized) :
    False := by
  obtain ⟨rowOneIndex, hrowOne⟩ := exists_rowOneIndex Q
  obtain ⟨orbit, p', Q', hC', hR', hN', hSparse', hBalanced', hcanonical⟩ :=
    canonicalize_rowOne hC hR hN rowOneIndex hrowOne
  exact canonicalBranch_impossible hC' hR' hN' hSparse' hBalanced'
    orbit hcanonical

/-- A convex-independent labelled octagon has a vertex that does not have
four other labelled vertices at one common distance. -/
theorem erdos97_convex_octagon
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p) :
    ∃ vertex, ¬HasFourEquidistant p vertex := by
  by_contra hall
  push Not at hall
  obtain ⟨p', Q, hC', hR', hN, _hSparse, _hBalanced⟩ :=
    normalized_reduction_of_all_hasFour hC hall
  exact normalized_convex_realisation_impossible hC' hR' hN

end Erdos97Octagon
