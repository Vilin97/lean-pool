/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeter

/-!
# `NRR.Geometry.ConvexBody` — basic scalar properties of the planar perimeter

This module records basic scalar properties of the planar Cauchy perimeter
`planarPerimeter` (defined in `PlanarPerimeter.lean`):

* **Nonnegativity** — already available as `planarPerimeter_nonneg` from `PlanarPerimeter.lean`
 (reused, not restated, to avoid a duplicate declaration in the same namespace).
* **Extensionality** (`planarPerimeter_ext`) — the perimeter depends only on the underlying
 set of the convex body, stated in the pointwise-membership form.
* **Upper bound from a width bound** (`planarPerimeter_le_of_width_bound`) — if the width along
 every direction `circleVec θ`, `θ ∈ [0, 2π]`, is bounded by `C`, then the perimeter is at
 most `π · C`. This is `(1/2) · ((2π − 0) · C) = π · C`.

## Import policy

Only `PlanarPerimeter.lean` is imported; it transitively provides all of Mathlib together with
the `planarPerimeter`, `widthFunction`, and `circleVec` APIs. No extra imports are required.
-/

namespace NRR.Geometry

open Real MeasureTheory ConvexBody

/-- **Extensionality.** The planar perimeter depends only on the underlying set of the convex
body, here in pointwise-membership form. -/
theorem planarPerimeter_ext
    {K L : ConvexBody Plane}
    (h : ∀ x, x ∈ (K : Set Plane) ↔ x ∈ (L : Set Plane)) :
    planarPerimeter K = planarPerimeter L := by
  apply planarPerimeter_congr
  exact Set.ext h

/-- **Upper bound from a width bound.** If the width along every direction `circleVec θ`,
`θ ∈ [0, 2π]`, is bounded by `C`, then the planar perimeter is at most `π · C`. -/
theorem planarPerimeter_le_of_width_bound
    (K : ConvexBody Plane) {C : ℝ}
    (hC : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      widthFunction K (circleVec θ) ≤ C) :
    planarPerimeter K ≤ (Real.pi) * C := by
  refine le_trans (mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on ?_ ?_ ?_ hC) (by positivity)) ?_ <;> norm_num
  · positivity
  · exact intervalIntegrable_planarPerimeter_integrand K
  · linarith

/-- **Positive width.** A convex body (which has nonempty interior) has strictly positive width
in every nonzero direction. -/
theorem ConvexBody.widthFunction_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : ConvexBody E) {u : E} (hu : u ≠ 0) :
    0 < widthFunction K u := by
  -- Since $u \neq 0$, we can choose $x_0 \in \text{interior}(K)$.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ interior (K : Set E), True := by
    exact ⟨ _, K.interior_nonempty.choose_spec, trivial ⟩;
  -- Since $x₀ \in \text{interior}(K)$, there exists $r > 0$ such that $B(x₀, r) \subseteq K$.
  obtain ⟨r, hr_pos, hr⟩ : ∃ r > 0, Metric.ball x₀ r ⊆ K.carrier := by
    exact Metric.mem_nhds_iff.1 ( mem_interior_iff_mem_nhds.1 hx₀.1 );
  -- Choose $t$ such that $0 < t < r$.
  obtain ⟨t, ht_pos, ht⟩ : ∃ t > 0, t < r ∧ t * ‖u‖ > 0 := by
    exact ⟨ r / 2, half_pos hr_pos, half_lt_self hr_pos, mul_pos ( half_pos hr_pos ) ( norm_pos_iff.mpr hu ) ⟩;
  -- Consider the points $x₀ + \frac{t}{‖u‖} u$ and $x₀ - \frac{t}{‖u‖} u$.
  set v := (t / ‖u‖) • u with hv_def
  have hv_mem : x₀ + v ∈ K.carrier ∧ x₀ - v ∈ K.carrier := by
    refine' ⟨ hr _, hr _ ⟩ <;> simp +decide [ *, norm_smul, abs_of_pos ];
  -- By definition of support function, we have:
  have h_support : K.supportFunction u ≥ inner ℝ (x₀ + v) u ∧ K.supportFunction (-u) ≥ inner ℝ (x₀ - v) (-u) := by
    exact ⟨ K.inner_le_supportFunction hv_mem.1, K.inner_le_supportFunction hv_mem.2 ⟩;
  simp_all +decide [ inner_add_left, inner_sub_left, inner_smul_left ];
  nlinarith [ show 0 < t / ‖u‖ * ‖u‖ ^ 2 by positivity, norm_pos_iff.mpr hu ]

/-- **Strict positivity.** The planar perimeter of a convex body is strictly positive. -/
theorem planarPerimeter_pos
    (K : ConvexBody Plane) :
    0 < planarPerimeter K := by
  refine' mul_pos ( by norm_num ) ( _ );
  apply intervalIntegral.integral_pos;
  · positivity;
  · exact Continuous.continuousOn ( by exact continuous_widthFunction K |> Continuous.comp <| continuous_circleVec );
  · exact fun x hx => ConvexBody.widthFunction_nonneg K _;
  · exact ⟨ 0, ⟨ le_rfl, Real.two_pi_pos.le ⟩, ConvexBody.widthFunction_pos _ <| by norm_num [ circleVec ] ⟩

end NRR.Geometry
