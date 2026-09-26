/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Tactic
public import LeanPool.NandakumarRamanaRao.NRR.BodySpace.Basic

/-!
# Boundary nullity for compact convex subbodies

The frontier of a convex set in a finite-dimensional real normed space is Lebesgue-null. On the
plane this applies uniformly to every `NRR.ConvexSubbody`, including lower-dimensional
(degenerate) ones, since the underlying Mathlib convex body is convex.

The a.e. complement statement `ConvexSubbody.ae_not_mem_frontier` is the exact exceptional-set
lemma required by membership stability and area continuity: almost every point of the plane avoids
the frontier of a given subbody.
-/

@[expose] public section

open MeasureTheory

open NRR.Geometry

namespace NRR

namespace ConvexSubbody

variable {K : Geometry.ConvexBody Plane}

/-- The frontier of a convex subbody carrier is Lebesgue-null. This holds for arbitrary subbodies,
including lower-dimensional ones, via `Convex.addHaar_frontier`. -/
theorem frontier_null (C : ConvexSubbody K) :
    volume (frontier (C.body : Set Plane)) = 0 :=
  C.convex.addHaar_frontier volume

/-- Almost every point of the plane lies outside the frontier of a convex subbody. This is the
exceptional-set lemma consumed by dominated-convergence arguments for membership and area
continuity. -/
theorem ae_not_mem_frontier (C : ConvexSubbody K) :
    ∀ᵐ x ∂volume, x ∉ frontier (C.body : Set Plane) := by
  rw [ae_iff]
  simpa using C.frontier_null

end ConvexSubbody

/-- Root-body form: the frontier of any Mathlib `ConvexBody Plane` is Lebesgue-null. -/
theorem mathlibConvexBody_frontier_null (C : _root_.ConvexBody Plane) :
    volume (frontier (C : Set Plane)) = 0 :=
  C.convex'.addHaar_frontier volume

end NRR
