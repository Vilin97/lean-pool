/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.ConvexHull
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.SupportingBall

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Compact Straszewicz theorem

This module assembles the compact finite-dimensional Straszewicz theorem from the source-shaped
pieces in `ConvexHull` and `SupportingBall`.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Finite-dimensional compact-convex Straszewicz theorem.

Every extreme point of a compact convex set is a limit of exposed points. The proof follows the
Rockafellar source route: assume an extreme point is not in the exposed-point closure, separate it
from `conv (closure exposedPoints)`, then use the supporting-ball construction to find an exposed
point on the wrong side of the separating halfspace. -/
theorem straszewiczCompactConvexStatement
    [FiniteDimensional ℝ E] :
    StraszewiczCompactConvexStatement E := by
  intro s hcompact hconv x hx
  by_contra hxnot
  obtain ⟨l, u, hsep, hxout⟩ :=
    exists_strict_separating_dual_convexHull_closure_mathlib_exposedPoints
      (E := E) hcompact hconv hx hxnot
  let normal : E := (InnerProductSpace.toDual ℝ E).symm l
  have hx_mem : x ∈ s := _root_.extremePoints_subset hx
  have hnormal_x : inner ℝ normal x = l x := by
    simp [normal]
  obtain ⟨p, hpexposed, hpout_inner⟩ :=
    exists_mathlib_exposedPoint_inner_lt_of_isCompact_of_inner_lt
      (s := s) hcompact (normal := normal) (x := x) (u := u) hx_mem
      (by simpa [hnormal_x] using hxout)
  have hnormal_p : inner ℝ normal p = l p := by
    simp [normal]
  have hp_hull : p ∈ convexHull ℝ (closure (Set.exposedPoints ℝ s)) :=
    subset_convexHull (𝕜 := ℝ) (s := closure (Set.exposedPoints ℝ s))
      (subset_closure hpexposed)
  have hp_lt : l p < u := hsep p hp_hull
  exact (not_lt_of_ge hpout_inner.le) (by simpa [hnormal_p] using hp_lt)

end AleksandrovDifferentiability
