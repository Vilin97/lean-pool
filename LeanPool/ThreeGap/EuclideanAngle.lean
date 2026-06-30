/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The separation → angle crux for the Euclidean growth inequality

The Euclidean (`L²`) growth inequality behind the **Euclidean five-distance theorem** `g₂ ≤ 5`
(Haynes–Marklof) rests on a single geometric fact about the best-approximation **remainder vectors**
`r(qₙ), r(qₙ₊₁), …` in a doubling window: each has Euclidean norm `≤ δₙ`, and (separation lemma,
`SimApprox.window_separation`) any two are at distance `≥ δₙ`. This file proves the **crux** that
converts that metric separation into an **angular** separation:

  `‖u‖, ‖v‖ ≤ δ` and `‖u − v‖ ≥ δ`  ⟹  `angle u v ≥ π/3`,

and the **strict** form `angle u v > π/3` when one of the vectors is strictly shorter than `δ`
(which
holds for all but the first remainder vector, since the defects strictly decrease). The verified
algebraic heart is `a² + b² − ab ≤ δ²` for `a, b ≤ δ` (equality iff `a = b = δ`).

**Where this sits in the route to `g₂ ≤ 5`.** Pairwise angles `> π/3` cap the number of remainder
vectors in a window, hence the index gap `n − m`, hence the gap count:

* A `6`-sector pigeonhole gives `≤ 6` vectors (`K = 6`, `g₂ ≤ 7`) — the contact-number bound.
* The angular **gap-sum** (`6 × (>60°) > 360°`) with the *strict* bound gives `≤ 5` (`K = 5`,
  `g₂ ≤ 6`).
* The **sharp** `≤ 4` (`K = 4`, `g₂ ≤ 5`) is **Romanov's theorem** (M.V. Romanov, *Moscow Univ.
Math.
  Bull.* 61 (2006)): it needs the strict length-monotonicity *together with* the arithmetic
  difference-of-denominators structure, packaged as a convex-position argument plus a synthetic
  hexagon separation lemma — a strictly finer (and figure-dependent) input than the angle bound
  here.

This file isolates the fully-proven angular crux; the packing count on top of it is the remaining
geometric step (sharp form = Romanov). Axiom-clean; elementary.
-/

namespace ThreeGap.EuclideanAngle

open RealInnerProductSpace
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The algebraic heart.** For `0 ≤ a, b ≤ δ`, `a² + b² − ab ≤ δ²` (equality iff `a = b = δ`).
Proof: `a² ≤ aδ`, `b² ≤ bδ`, and `aδ + bδ − ab ≤ δ²` since `(δ − a)(δ − b) ≥ 0`. -/
theorem sq_add_sq_sub_mul_le {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haδ : a ≤ δ) (hbδ : b ≤ δ) :
    a ^ 2 + b ^ 2 - a * b ≤ δ ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 haδ) (sub_nonneg.2 hbδ), mul_nonneg ha (sub_nonneg.2 haδ),
    mul_nonneg hb (sub_nonneg.2 hbδ)]

/-- **Strict algebraic heart.** For *positive* `a, b ≤ δ`, if moreover `a < δ` or `b < δ`, the
inequality is strict. (Positivity is needed: `(a, b) = (0, δ)` gives equality `δ²`.) -/
theorem sq_add_sq_sub_mul_lt {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b) (haδ : a ≤ δ) (hbδ : b ≤ δ)
    (hstrict : a < δ ∨ b < δ) : a ^ 2 + b ^ 2 - a * b < δ ^ 2 := by
  rcases hstrict with h | h
  · nlinarith [mul_nonneg (sub_nonneg.2 haδ) (sub_nonneg.2 hbδ), mul_pos ha (sub_pos.2 h),
      mul_nonneg hb.le (sub_nonneg.2 hbδ)]
  · nlinarith [mul_nonneg (sub_nonneg.2 haδ) (sub_nonneg.2 hbδ), mul_pos hb (sub_pos.2 h),
      mul_nonneg ha.le (sub_nonneg.2 haδ)]

/-- **Separation ⟹ inner-product bound.** If `‖u‖, ‖v‖ ≤ δ` and the vectors are `δ`-separated
(`δ ≤ ‖u − v‖`), then `⟪u, v⟫ ≤ ‖u‖ ‖v‖ / 2`. (Law of cosines + the algebraic heart.) -/
theorem inner_le_half_mul_norm {u v : E} {δ : ℝ} (hu : ‖u‖ ≤ δ) (hv : ‖v‖ ≤ δ)
    (hsep : δ ≤ ‖u - v‖) : ⟪u, v⟫ ≤ ‖u‖ * ‖v‖ / 2 := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hu
  have hsq : δ ^ 2 ≤ ‖u - v‖ ^ 2 := by nlinarith [norm_nonneg (u - v)]
  rw [norm_sub_sq_real] at hsq
  have halg := sq_add_sq_sub_mul_le (norm_nonneg u) (norm_nonneg v) hu hv
  nlinarith [halg, hsq]

/-- **The angular crux (non-strict).** `δ`-separated vectors of norm `≤ δ` subtend an angle `≥ π/3`.
This is the contact-number input: pairwise `≥ 60°` ⟹ at most `6` such vectors in the plane. -/
theorem angle_ge_pi_div_three {u v : E} {δ : ℝ} (hu0 : 0 < ‖u‖) (hv0 : 0 < ‖v‖) (hu : ‖u‖ ≤ δ)
    (hv : ‖v‖ ≤ δ) (hsep : δ ≤ ‖u - v‖) : π / 3 ≤ InnerProductGeometry.angle u v := by
  have hbound := inner_le_half_mul_norm hu hv hsep
  have hc : ⟪u, v⟫ / (‖u‖ * ‖v‖) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith [hbound]
  have h13 : Real.arccos (1 / 2) = π / 3 := by
    rw [← Real.cos_pi_div_three]; exact Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])
  calc π / 3 = Real.arccos (1 / 2) := h13.symm
    _ ≤ Real.arccos (⟪u, v⟫ / (‖u‖ * ‖v‖)) := Real.arccos_le_arccos hc
    _ = InnerProductGeometry.angle u v := rfl

/-- **The angular crux (strict).** If in addition one vector is strictly shorter than `δ` — which
holds for every remainder vector after the first, since the defects strictly decrease — the angle is
strictly `> π/3`. This strictness is what upgrades the count from `≤ 6` to `≤ 5` (`6 × (>60°) >
360°`);
the sharp `≤ 4` is Romanov's finer argument. -/
theorem angle_gt_pi_div_three {u v : E} {δ : ℝ} (hu0 : 0 < ‖u‖) (hv0 : 0 < ‖v‖) (hu : ‖u‖ ≤ δ)
    (hv : ‖v‖ ≤ δ) (hsep : δ ≤ ‖u - v‖) (hstrict : ‖u‖ < δ ∨ ‖v‖ < δ) :
    π / 3 < InnerProductGeometry.angle u v := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hu
  have hsq : δ ^ 2 ≤ ‖u - v‖ ^ 2 := by nlinarith [norm_nonneg (u - v)]
  rw [norm_sub_sq_real] at hsq
  have halg := sq_add_sq_sub_mul_lt hu0 hv0 hu hv hstrict
  have hbound : ⟪u, v⟫ < ‖u‖ * ‖v‖ / 2 := by nlinarith [halg, hsq]
  have hc : ⟪u, v⟫ / (‖u‖ * ‖v‖) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]; linarith [hbound]
  have h13 : Real.arccos (1 / 2) = π / 3 := by
    rw [← Real.cos_pi_div_three]; exact Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])
  have hge : ⟪u, v⟫ / (‖u‖ * ‖v‖) ≥ -1 := by
    have := abs_real_inner_div_norm_mul_norm_le_one u v
    rw [abs_le] at this; exact this.1
  calc π / 3 = Real.arccos (1 / 2) := h13.symm
    _ < Real.arccos (⟪u, v⟫ / (‖u‖ * ‖v‖)) := Real.arccos_lt_arccos hge hc (by norm_num)
    _ = InnerProductGeometry.angle u v := rfl

/-- **Haynes–Marklof Proposition 2** (the cone-partition route to the *sharp* Euclidean
five-distance
bound `g₂ ≤ 5`, Haynes–Marklof, *IMRN* 2022, arXiv:2009.08444). If the angle between nonzero `u, v`
is `< π/3`, then `‖u − v‖ < max ‖u‖ ‖v‖`. This is the clean two-vector statement that *replaces*
Romanov's growth lemma and the angular↔magnitude coupling: within any `< π/3` cone of directions,
two
distinct nearest-neighbour distances cannot both occur. -/
theorem norm_sub_lt_max_of_angle_lt {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hang : InnerProductGeometry.angle u v < π / 3) : ‖u - v‖ < max ‖u‖ ‖v‖ := by
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hmem : InnerProductGeometry.angle u v ∈ Set.Icc 0 π :=
    ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  have hmem3 : π / 3 ∈ Set.Icc 0 π := ⟨by positivity, by linarith [Real.pi_pos]⟩
  -- `angle < π/3 ⟹ cos angle > cos(π/3) = 1/2`
  have hcos : (1 : ℝ) / 2 < Real.cos (InnerProductGeometry.angle u v) := by
    rw [← Real.cos_pi_div_three]; exact Real.strictAntiOn_cos hmem hmem3 hang
  rw [InnerProductGeometry.cos_angle] at hcos
  have hinner : ‖u‖ * ‖v‖ / 2 < ⟪u, v⟫ := by
    rw [lt_div_iff₀ (by positivity)] at hcos; linarith [hcos]
  -- `‖u−v‖² < ‖u‖²+‖v‖²−‖u‖‖v‖ ≤ (max ‖u‖ ‖v‖)²`
  have hsq : ‖u - v‖ ^ 2 < (max ‖u‖ ‖v‖) ^ 2 := by
    rw [norm_sub_sq_real]
    rcases le_total ‖u‖ ‖v‖ with h | h
    · rw [max_eq_right h]; nlinarith [hinner, hu0, hv0, h]
    · rw [max_eq_left h]; nlinarith [hinner, hu0, hv0, h]
  exact lt_of_pow_lt_pow_left₀ 2 (le_trans (norm_nonneg u) (le_max_left _ _)) hsq

/-- **The record-angle bound** (the contrapositive form Haynes–Marklof Theorem 8 consumes). If `u`
is
shorter than `w` but their difference is *longer* than `w` (`‖w‖ < ‖u − w‖`), then the angle between
them is `≥ π/3`. For the record vectors `v₁,…,v_{K-1}` (increasing norms, `‖vᵢ − vⱼ‖ > ‖vⱼ‖`), this
gives the pairwise `≥ π/3` separation feeding the `5`-on-a-circle count. -/
theorem angle_ge_pi_div_three_of_norm_sub_gt {u w : E} (hu : u ≠ 0) (hw : w ≠ 0)
    (hnorm : ‖u‖ ≤ ‖w‖) (hsub : ‖w‖ < ‖u - w‖) : π / 3 ≤ InnerProductGeometry.angle u w := by
  by_contra h
  rw [not_le] at h
  have hlt := norm_sub_lt_max_of_angle_lt hu hw h
  rw [max_eq_right hnorm] at hlt
  linarith

end ThreeGap.EuclideanAngle
