/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.SupportFunctionBasic
/-!
# `NRR.Geometry.ConvexBody` — continuity of the support function

This module proves that the support function `u ↦ h_K(u)` of a `ConvexBody` `K` is (globally
Lipschitz, hence) continuous in the direction variable. This is the analytic prerequisite for
width, Cauchy perimeter, and all later integration over the unit circle / sphere.

## Contents

* `exists_radius_bound` — existence of a radius `R ≥ 0` bounding the norms of points of `K`
 (from compactness / boundedness).
* `supportFunction_lipschitz_with_radius` — the quantitative estimate
 `|h_K(u) - h_K(v)| ≤ R · ‖u - v‖` whenever `K ⊆ closedBall 0 R`.
* `supportFunction_lipschitzWith` — the bundled `LipschitzWith` statement.
* `continuous_supportFunction`, `continuousAt_supportFunction`, `continuousOn_supportFunction`
 — full-space continuity.
* `uniformContinuousOn_supportFunction` — uniform continuity on any subset (in fact
 the global Lipschitz bound gives uniform continuity everywhere).
* `continuousOn_supportFunction_on_sphere` — continuity restricted to the unit sphere, an
 immediate corollary.

## Design notes

The proof follows the preferred Lipschitz route: subadditivity of the support function plus the
radius bound `h_K(u) ≤ R‖u‖` give `h_K(u) - h_K(v) ≤ h_K(u - v) ≤ R‖u - v‖`, and symmetrically,
so the map is `R`-Lipschitz. This is more robust than a compact-maximum-with-parameters argument
and yields the strongest downstream API.
-/

namespace NRR.Geometry

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Existence of a radius bound.** Every convex body is bounded, so there is `R ≥ 0` with
`‖x‖ ≤ R` for all `x ∈ K`. -/
theorem exists_radius_bound (K : ConvexBody E) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ (K : Set E), ‖x‖ ≤ R := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  have hR' : ∀ x ∈ (K : Set E), ‖x‖ ≤ R := by
    intro x hx
    have := hR hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hRnn : 0 ≤ R := by
    obtain ⟨x, hx⟩ := K.nonempty
    exact le_trans (norm_nonneg x) (hR' x hx)
  exact ⟨R, hRnn, hR'⟩

/-- **Lipschitz estimate.** If every point of `K` has norm at most `R`, the support function is
`R`-Lipschitz: `|h_K(u) - h_K(v)| ≤ R · ‖u - v‖`. -/
theorem supportFunction_lipschitz_with_radius
    (K : ConvexBody E) {R : ℝ}
    (hR : ∀ x ∈ (K : Set E), ‖x‖ ≤ R) :
    ∀ u v : E,
      |supportFunction K u - supportFunction K v| ≤ R * ‖u - v‖ := by
  intro u v
  have hle : ∀ a b : E, supportFunction K a - supportFunction K b ≤ R * ‖a - b‖ := by
    intro a b
    have h1 : supportFunction K a ≤ supportFunction K b + supportFunction K (a - b) := by
      have h := K.supportFunction_add_direction_le b (a - b)
      rwa [show b + (a - b) = a from by abel] at h
    have h2 : supportFunction K (a - b) ≤ R * ‖a - b‖ :=
      K.supportFunction_le_radius hR (a - b)
    linarith
  rw [abs_sub_le_iff]
  constructor
  · exact hle u v
  · have := hle v u
    rw [show ‖v - u‖ = ‖u - v‖ from by rw [norm_sub_rev]] at this
    exact this

/-- **Bundled Lipschitz.** The support function is `R.toNNReal`-Lipschitz when `K ⊆ closedBall 0 R`. -/
theorem supportFunction_lipschitzWith
    (K : ConvexBody E) {R : ℝ} (hRnn : 0 ≤ R)
    (hR : ∀ x ∈ (K : Set E), ‖x‖ ≤ R) :
    LipschitzWith R.toNNReal (fun u : E => supportFunction K u) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro u v
  rw [Real.dist_eq, Real.coe_toNNReal R hRnn, dist_eq_norm]
  exact K.supportFunction_lipschitz_with_radius hR u v

/-- **Full-space continuity** of the support function in the direction variable. -/
theorem continuous_supportFunction
    (K : ConvexBody E) :
    Continuous (fun u : E => supportFunction K u) := by
  obtain ⟨R, hRnn, hR⟩ := K.exists_radius_bound
  exact (K.supportFunction_lipschitzWith hRnn hR).continuous

/-- **Continuity at a point.** -/
theorem continuousAt_supportFunction
    (K : ConvexBody E) (u : E) :
    ContinuousAt (fun v : E => supportFunction K v) u :=
  K.continuous_supportFunction.continuousAt

/-- **Continuity on a set.** -/
theorem continuousOn_supportFunction
    (K : ConvexBody E) (s : Set E) :
    ContinuousOn (fun u : E => supportFunction K u) s :=
  K.continuous_supportFunction.continuousOn

/-- **Uniform continuity on a subset.** The global Lipschitz bound gives uniform continuity on
every subset of the ambient inner product space. -/
theorem uniformContinuousOn_supportFunction
    (K : ConvexBody E) {s : Set E} :
    UniformContinuousOn (fun u : E => supportFunction K u) s := by
  obtain ⟨R, hRnn, hR⟩ := K.exists_radius_bound
  exact ((K.supportFunction_lipschitzWith hRnn hR).uniformContinuous).uniformContinuousOn

/-- **Continuity on the unit sphere**, an immediate corollary of full-space continuity. -/
theorem continuousOn_supportFunction_on_sphere
    (K : ConvexBody E) :
    ContinuousOn (fun u : E => supportFunction K u) (Metric.sphere (0 : E) 1) :=
  K.continuous_supportFunction.continuousOn

end ConvexBody

end NRR.Geometry
