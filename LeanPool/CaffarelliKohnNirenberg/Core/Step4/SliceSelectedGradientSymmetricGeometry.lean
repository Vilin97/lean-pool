/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradient
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-! # Geometry of the symmetric parabolic window

Display `eq:parabolic-ball` of `paper/ckn.tex` presents the parabolic ball of
radius `R` about `z₀ = (x₀, t₀)` as the product of the spatial Euclidean ball
`B_R(x₀)` with the symmetric time interval `(t₀ - R², t₀ + R²)`, written
`𝔅_R(z₀)`.

This file records the elementary spatial facts needed to rewrite membership
between the one-sided and symmetric carriers: the explicit round ball
`euclideanBall` is the norm ball `vec3Ball`, and the closure of a smaller norm
ball lies inside any larger one, so the boundary of an inner carrier is
absorbed by the slightly larger open window used in display (3.5).

The module contains no analytic content: it is pure parabolic geometry, and its
statements are used only to rewrite membership between the one-sided and
symmetric carriers. -/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-- The explicit round ball `euclideanBall x₀ r` of `CKN/Foundation/Sobolev` and
the norm ball `vec3Ball x₀ r` of `CKN/Foundation/Parabolic` describe the same
subset of `Vec3` whenever `r > 0`, because both are cut out by the strict
inequality `vecEuclideanNorm (x - x₀) < r`. -/
theorem euclideanBall_eq_vec3Ball_of_pos {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- The closed ball of radius `r` is contained in the open ball of any larger
radius `s`, so the closure of `vec3Ball x r` is a subset of `vec3Ball x s` when
`0 < r < s`.  This lets the boundary of an inner carrier be absorbed into the
slightly larger open window used in display (3.5). -/
theorem closure_vec3Ball_subset_vec3Ball {x : Vec3} {r s : ℝ} (hr : 0 < r)
    (hrs : r < s) :
    closure (vec3Ball x r) ⊆ vec3Ball x s := by
  rw [closure_vec3Ball hr]
  intro y hy
  change vec3EuclideanNorm (y - x) < s
  exact lt_of_le_of_lt hy hrs

end CKN.Core.Step4
