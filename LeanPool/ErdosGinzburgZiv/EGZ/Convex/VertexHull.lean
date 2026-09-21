/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.AffineLattice
import Mathlib.Analysis.Convex.KreinMilman

/-!
# A polytope is the convex hull of its vertices

This finite-dimensional consequence of Krein--Milman is used when a hollow
rational polytope is converted into a finite `p`-hollow family.
-/

namespace EGZ.RationalPolytope

/-- The convex hull of the actual extreme points of a rational polytope is
the whole polytope, even when its stored generating finset is redundant. -/
theorem carrier_eq_convexHull_vertexSet {d : ℕ} (P : RationalPolytope d) :
    P.carrier = convexHull ℝ P.vertexSet := by
  have hKM : closure (convexHull ℝ P.vertexSet) = P.carrier := by
    simpa only [vertexSet] using
      (closure_convexHull_extremePoints P.isCompact P.convex)
  have hcompact : IsCompact (convexHull ℝ P.vertexSet) :=
    P.finite_vertexSet.isCompact_convexHull ℝ
  rw [hcompact.isClosed.closure_eq] at hKM
  exact hKM.symm

/-- Every point of a polytope is a convex combination of its vertices. -/
theorem mem_convexHull_vertexSet {d : ℕ} (P : RationalPolytope d)
    {q : RealCoord d} (hq : q ∈ P.carrier) :
    q ∈ convexHull ℝ P.vertexSet := by
  rwa [← P.carrier_eq_convexHull_vertexSet]

end EGZ.RationalPolytope
