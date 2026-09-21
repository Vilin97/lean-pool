/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.WidthContinuity

/-!
# `NRR.Geometry.ConvexBody` — the angle parameterization of the unit circle

This module sets up a **deterministic angle-parameterization** of the planar unit circle,
to be used as the integration domain for Cauchy's perimeter formula. Instead of introducing
a measure on the unit circle (Haar measure, quotient-circle measure, or a measure on a
unit-sphere subtype), we parameterize directions by the interval `[0, 2π]` via the map

```text
θ ↦ (cos θ, sin θ).
```

## Design notes

* The plane is fixed as `Plane := EuclideanSpace ℝ (Fin 2)`. This is
 definitionally equal to the project's `NRR.E2` abbreviation. The local
 name keeps this module focused on width continuity and uses the standard
 Euclidean additive, normed, and inner-product instances.
* `circleVec θ` is built with the Euclidean vector notation `!₂[cos θ, sin θ]`, so its
 coordinates are `circleVec θ 0 = cos θ` and `circleVec θ 1 = sin θ`. Both coordinate
 projections are exposed as `@[simp]` lemmas, since later perimeter proofs rewrite through
 them.
* The width function `widthFunction K` (from `Width.lean`) is continuous in the direction
 (`continuous_widthFunction` from `WidthContinuity.lean`); composing with the continuous
 `circleVec` and restricting to the compact interval `[0, 2π]` gives interval integrability.

## Import policy

Only `WidthContinuity.lean` is imported; it transitively provides all of Mathlib (via
`Basic.lean`'s `import Mathlib`) together with the width-function continuity API. No extra
imports are required.
-/

namespace NRR.Geometry

open Real MeasureTheory

/-- The Euclidean plane `ℝ²`. Definitionally equal to `NRR.E2`; reintroduced here to
keep this module independent of the area API. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The angle parameterization of the unit circle: `circleVec θ = (cos θ, sin θ)` as a point
of the Euclidean plane. -/
noncomputable def circleVec (θ : ℝ) : Plane := !₂[Real.cos θ, Real.sin θ]

/-- First coordinate of `circleVec θ` is `cos θ`. -/
@[simp] theorem circleVec_zero_coord (θ : ℝ) :
    circleVec θ 0 = Real.cos θ := by
  simp [circleVec]

/-- Second coordinate of `circleVec θ` is `sin θ`. -/
@[simp] theorem circleVec_one_coord (θ : ℝ) :
    circleVec θ 1 = Real.sin θ := by
  simp [circleVec]

/-- `circleVec θ` is a unit vector: `‖circleVec θ‖ = 1`. -/
@[simp] theorem norm_circleVec (θ : ℝ) :
    ‖circleVec θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [circleVec_zero_coord, circleVec_one_coord, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_eq_one, ← Real.sin_sq_add_cos_sq θ]
  ring

/-- `circleVec θ` lies on the unit sphere centered at the origin. -/
theorem circleVec_mem_unitSphere (θ : ℝ) :
    circleVec θ ∈ Metric.sphere (0 : Plane) 1 := by
  simp

/-- The angle parameterization is continuous. -/
theorem continuous_circleVec : Continuous circleVec := by
  have h : circleVec
      = (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm
          ∘ (fun θ => ![Real.cos θ, Real.sin θ]) := by
    funext θ; ext i; fin_cases i <;> rfl
  rw [h]
  apply (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The angle parameterization is `2π`-periodic. -/
theorem circleVec_periodic : Function.Periodic circleVec (2 * Real.pi) := by
  intro θ
  ext i
  fin_cases i <;> simp [circleVec, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Antipodal shift: `circleVec (θ + π) = - circleVec θ`. Useful for width symmetry. -/
theorem circleVec_add_pi (θ : ℝ) :
    circleVec (θ + Real.pi) = - circleVec θ := by
  ext i
  fin_cases i <;> simp [circleVec, Real.cos_add_pi, Real.sin_add_pi]

/-- Any continuous scalar field on the plane, composed with `circleVec`, is interval-integrable
on `[0, 2π]`. -/
theorem intervalIntegrable_comp_circleVec
    {f : Plane → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun θ : ℝ => f (circleVec θ))
      volume 0 (2 * Real.pi) :=
  (hf.comp continuous_circleVec).intervalIntegrable 0 (2 * Real.pi)

/-- The width of a convex body along `circleVec` is interval-integrable on `[0, 2π]`; this is
the integrand of Cauchy's perimeter formula. -/
theorem intervalIntegrable_width_circleVec
    (K : ConvexBody Plane) :
    IntervalIntegrable
      (fun θ : ℝ => ConvexBody.widthFunction K (circleVec θ))
      volume 0 (2 * Real.pi) :=
  intervalIntegrable_comp_circleVec K.continuous_widthFunction

end NRR.Geometry
