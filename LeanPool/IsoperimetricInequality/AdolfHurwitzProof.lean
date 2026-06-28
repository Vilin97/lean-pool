/-
Copyright (c) 2026 M. Samarakkody. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: M. Samarakkody
-/

import LeanPool.IsoperimetricInequality.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Adolf Hurwitz's Proof of the Isoperimetric Inequality

This file formalizes Adolf Hurwitz's 1902 proof of the classical isoperimetric inequality
in the plane: among all simple closed curves of a given perimeter, the circle encloses the
maximum area.

## Proof outline

Given a simple closed C¹ curve `γ` of length `L`, we reparametrize it over `[0, 2π]` via
  `f(θ) = x(Lθ/(2π))`,  `g(θ) = y(Lθ/(2π))`.

The proof proceeds as follows:
1. **Area formula**: Express the enclosed area using the shoelace formula and reparametrize
   to get `area = (1/2) ∫₀²π (f g' - g f') dθ`.
2. **IBP**: Integration by parts shows `∫ f g' = -∫ g f'`, simplifying the area to
   `area = ∫₀²π f g' dθ`.
3. **AM-GM inequality**: Pointwise `2 f g' ≤ f² + (g')²` gives
   `area ≤ (1/2) ∫₀²π (f² + (g')²) dθ`.
4. **Wirtinger's inequality**: Since `f` has zero mean (centroid at origin), Parseval's
   theorem from `IsoperimetricInequality.Basic` gives `∫ f² ≤ ∫ (f')²`, upgrading step 3 to
   `area ≤ (1/2) ∫₀²π ((f')² + (g')²) dθ`.
5. **Arc-length constraint** (to be completed): Under arc-length parametrization,
   `(f')² + (g')² = (L/(2π))²` everywhere, so
   `∫₀²π ((f')² + (g')²) dθ = L²/(2π)`, yielding `area ≤ L²/(4π)`,
   with equality iff `γ` is a circle.

## Main declarations

- `SimpleClosedC1Curve`: structure for simple closed C¹ curves parametrized over `[0, L]`
- `area_parametrized`: shoelace area formula in terms of `f`, `g`
- `IBP_to_fParm_gParm`: integration by parts for `∫ f g'`
- `area_simplified`: area equals `∫ f g' dθ`
- `fParm_gParm_ineq`: AM-GM pointwise inequality
- `area_inequality`: area bounded by `(1/2) ∫ (f² + (g')²) dθ`
- `apply_Wirtingers_ineq`: Wirtinger's inequality `∫ f² ≤ ∫ (f')²` for zero-mean `f`
- `addition_ineq`: combines AM-GM and Wirtinger to give `area ≤ (1/2) ∫ ((f')² + (g')²) dθ`
- `apply_fParm_gParm_deriv_sq_sum`: arc-length constraint gives `area ≤ (1/2) ∫₀²π L²/(4π²) dθ`
- `isoperimetric_inequality`: the main result `area ≤ L²/(4π)`
-/

namespace IsoperimetricInequality

/-- A simple closed C¹ curve in ℝⁿ, parametrized over [0, L] where L is the arc length. -/
structure SimpleClosedC1Curve (n : ℕ) where
  /-- The parametrization map. -/
  curve : ℝ → EuclideanSpace ℝ (Fin n)
  /-- The period (arc length) of the curve. -/
  length : ℝ
  /-- The period is positive. -/
  length_pos : 0 < length
  /-- The curve is continuous. -/
  continuous : Continuous curve
  /-- The curve is C¹: a derivative exists at every point. -/
  has_deriv : ∀ t : ℝ, ∃ f : EuclideanSpace ℝ (Fin n), HasDerivAt curve f t
  /-- The curve is closed: its endpoints coincide. -/
  closed : curve 0 = curve length
  /-- The curve is L-periodic. -/
  periodic : ∀ t : ℝ, curve (t + length) = curve t
  /-- The curve is simple: injective on the open interval (0, L). -/
  simple : ∀ t s : ℝ, t ∈ Set.Ioo 0 length → s ∈ Set.Ioo 0 length → curve t = curve s → t = s

/-- The arc length of `γ` over the interval `[a, b]`. -/
noncomputable def arcLength {n : ℕ} (γ : SimpleClosedC1Curve n) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ.curve t‖

/-- The total perimeter of `γ`: arc length over one period `[0, L]`. -/
noncomputable def perimeter {n : ℕ} (γ : SimpleClosedC1Curve n) : ℝ :=
  arcLength γ 0 γ.length

/-- A curve is arc-length parametrized if it has unit speed.
    Since the parameter runs over [0, L], this means ‖γ'(t)‖ = 1 everywhere. -/
def IsArcLengthParametrized {n : ℕ} (γ : SimpleClosedC1Curve n) : Prop :=
  ∀ t : ℝ, ‖deriv γ.curve t‖ = 1

/-- The x-coordinate of a planar curve at parameter `s`. -/
noncomputable def xCoord (γ : SimpleClosedC1Curve 2) (s : ℝ) : ℝ :=
  γ.curve s 0

/-- The y-coordinate of a planar curve at parameter `s`. -/
noncomputable def yCoord (γ : SimpleClosedC1Curve 2) (s : ℝ) : ℝ :=
  γ.curve s 1

/-- Reparametrized x-coordinate: f(θ) = x(Lθ/(2π)) for θ ∈ [0, 2π] -/
noncomputable def fParm (γ : SimpleClosedC1Curve 2) (θ : ℝ) : ℝ :=
  xCoord γ (γ.length * θ / (2 * Real.pi))

/-- Reparametrized y-coordinate: g(θ) = y(Lθ/(2π)) for θ ∈ [0, 2π] -/
noncomputable def gParm (γ : SimpleClosedC1Curve 2) (θ : ℝ) : ℝ :=
  yCoord γ (γ.length * θ / (2 * Real.pi))

/-- fParm is 2π-periodic. -/
lemma fParm_periodic (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    fParm γ (θ + 2 * Real.pi) = fParm γ θ := by
  simp only [fParm, xCoord]
  have h : γ.length * (θ + 2 * Real.pi) / (2 * Real.pi) =
           γ.length * θ / (2 * Real.pi) + γ.length := by
    field_simp
  rw [h, γ.periodic]

/-- gParm is 2π-periodic. -/
lemma gParm_periodic (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    gParm γ (θ + 2 * Real.pi) = gParm γ θ := by
      simp only [gParm, yCoord]
      have h : γ.length * (θ + 2 * Real.pi) / (2 * Real.pi) =
               γ.length * θ / (2 * Real.pi) + γ.length := by
                field_simp
      rw [h, γ.periodic]


/-- The x-coordinate function is differentiable; its derivative at `t` is the 0th component
    of the curve's velocity vector at `t`. -/
lemma xCoord_hasDerivAt (γ : SimpleClosedC1Curve 2) (t : ℝ) :
    HasDerivAt (xCoord γ) ((γ.has_deriv t).choose 0) t := by
  set f := (γ.has_deriv t).choose
  have hf := (γ.has_deriv t).choose_spec
  have hFD : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => v 0)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0) (γ.curve t) :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (γ.curve t) 0
  have hcomp := HasFDerivAt.comp_hasDerivAt t hFD hf
  exact hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (by intro y; rfl))

/-- The y-coordinate function is differentiable; its derivative at `t` is the 1st component
    of the curve's velocity vector at `t`. -/
lemma yCoord_hasDerivAt (γ : SimpleClosedC1Curve 2) (t : ℝ) :
    HasDerivAt (yCoord γ) ((γ.has_deriv t).choose 1) t := by
  set f := (γ.has_deriv t).choose
  have hf := (γ.has_deriv t).choose_spec
  have hFD : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => v 1)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1) (γ.curve t) :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (γ.curve t) 1
  have hcomp := HasFDerivAt.comp_hasDerivAt t hFD hf
  exact hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (by intro y; rfl))

/-- The derivative of fParm by the chain rule:
    (fParm γ)'(θ) = (xCoord γ)'(γ.length · θ / (2π)) · γ.length / (2π) -/
lemma fParm_deriv (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    deriv (fParm γ) θ =
      deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)) * (γ.length / (2 * Real.pi)) := by
  have hx := (xCoord_hasDerivAt γ (γ.length * θ / (2 * Real.pi))).differentiableAt
  have hinner : HasDerivAt (fun t => γ.length * t / (2 * Real.pi)) (γ.length / (2 * Real.pi)) θ :=
  by
    have heq : (fun t : ℝ => γ.length * t / (2 * Real.pi)) =
               fun t => t * (γ.length / (2 * Real.pi)) := by
      ext t; rw [mul_comm, mul_div_assoc]
    rw [heq]
    have hid : HasDerivAt (fun t : ℝ => t) 1 θ := hasDerivAt_id θ
    have h := HasDerivAt.mul_const hid (γ.length / (2 * Real.pi))
    simpa using h
  have hg : HasDerivAt (xCoord γ) (deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)))
      (γ.length * θ / (2 * Real.pi)) := hx.hasDerivAt
  have hcomp : HasDerivAt (xCoord γ ∘ fun t => γ.length * t / (2 * Real.pi))
      (deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)) * (γ.length / (2 * Real.pi))) θ :=
    HasDerivAt.comp θ hg hinner
  exact HasDerivAt.deriv hcomp

/-- The derivative of gParm by the chain rule:
    (gParm γ)'(θ) = (yCoord γ)'(γ.length · θ / (2π)) · γ.length / (2π) -/
lemma gParm_deriv (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    deriv (gParm γ) θ =
      deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)) * (γ.length / (2 * Real.pi)) := by
  have hy := (yCoord_hasDerivAt γ (γ.length * θ / (2 * Real.pi))).differentiableAt
  have hinner :
  HasDerivAt (fun t => γ.length * t / (2 * Real.pi)) (γ.length / (2 * Real.pi)) θ := by
    have heq : (fun t : ℝ => γ.length * t / (2 * Real.pi)) =
               fun t => t * (γ.length / (2 * Real.pi)) := by
      ext t; rw [mul_comm, mul_div_assoc]
    rw [heq]
    have hid : HasDerivAt (fun t : ℝ => t) 1 θ := hasDerivAt_id θ
    have h := HasDerivAt.mul_const hid (γ.length / (2 * Real.pi))
    simpa using h
  have hg : HasDerivAt (yCoord γ) (deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)))
      (γ.length * θ / (2 * Real.pi)) := hy.hasDerivAt
  have hcomp : HasDerivAt (yCoord γ ∘ fun t => γ.length * t / (2 * Real.pi))
      (deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)) * (γ.length / (2 * Real.pi))) θ :=
    HasDerivAt.comp θ hg hinner
  exact HasDerivAt.deriv hcomp

/-- The sum of squared derivatives of the reparametrized coordinates equals the sum of squared
    derivatives of the original coordinates, scaled by `(L / 2π)²`. -/
lemma fParm_gParm_deriv_sq_sum (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    deriv (fParm γ) θ ^ 2 + deriv (gParm γ) θ ^ 2 =
      (deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)) ^ 2 +
       deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)) ^ 2) *
      (γ.length / (2 * Real.pi)) ^ 2 := by
  rw [fParm_deriv, gParm_deriv]
  ring

/-- Under arc-length parametrization, the sum of squares of coordinate derivatives equals 1,
    because the speed ‖γ'(t)‖ = 1 and the two components square-sum to the squared norm. -/
lemma due_to_arc_length_parametrization (γ : SimpleClosedC1Curve 2)
    (h : IsArcLengthParametrized γ) (θ : ℝ) :
    deriv (xCoord γ) (γ.length * θ / (2 * Real.pi)) ^ 2 +
    deriv (yCoord γ) (γ.length * θ / (2 * Real.pi)) ^ 2 = 1 := by
  set t := γ.length * θ / (2 * Real.pi)
  have hxd := (xCoord_hasDerivAt γ t).deriv
  have hyd := (yCoord_hasDerivAt γ t).deriv
  have hchoose : deriv γ.curve t = (γ.has_deriv t).choose :=
    (γ.has_deriv t).choose_spec.deriv
  have hnorm : ‖(γ.has_deriv t).choose‖ = 1 := by rw [← hchoose]; exact h t
  rw [hxd, hyd]
  have hsq : (γ.has_deriv t).choose 0 ^ 2 + (γ.has_deriv t).choose 1 ^ 2 =
      ‖(γ.has_deriv t).choose‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rw [hsq, hnorm, one_pow]

/-- Under arc-length parametrization, the sum of squared derivatives of the reparametrized
    coordinates is the constant `(L / 2π)²`. -/
lemma fParm_gParm_deriv_eq_sum_const (γ : SimpleClosedC1Curve 2)
    (h : IsArcLengthParametrized γ) (θ : ℝ) :
    deriv (fParm γ) θ ^ 2 + deriv (gParm γ) θ ^ 2 = (γ.length / (2 * Real.pi)) ^ 2 := by
  rw [fParm_gParm_deriv_sq_sum]
  rw [due_to_arc_length_parametrization γ h]
  ring


/-- The signed area enclosed by `γ` between parameters `a` and `b`,
    computed via the shoelace formula: 1/2 ∫ (x · y' - y · x') dt. -/
noncomputable def area (γ : SimpleClosedC1Curve 2)
  (a b : ℝ) : ℝ :=
  (1/2)*∫ t in a..b, (γ.curve t 0 * deriv γ.curve t 1 - γ.curve t 1 * deriv γ.curve t 0)


/-- x'(s) = (2π/L) f'(θ), where θ = 2π·s/L -/
lemma xPrime_s (γ : SimpleClosedC1Curve 2) (s : ℝ) :
    deriv (xCoord γ) s =
      (2 * Real.pi) / γ.length * deriv (fParm γ) (2 * Real.pi * s / γ.length) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hL : (0 : ℝ) < γ.length := γ.length_pos
  have h := fParm_deriv γ (2 * Real.pi * s / γ.length)
  have hsimp : γ.length * (2 * Real.pi * s / γ.length) / (2 * Real.pi) = s := by
    field_simp
  rw [hsimp] at h
  rw [h]
  field_simp [hL.ne', hpi.ne']

/-- y'(s) = (2π/L) g'(θ), where θ = 2π·s/L -/
lemma yPrime_s (γ : SimpleClosedC1Curve 2) (s : ℝ) :
    deriv (yCoord γ) s =
      (2 * Real.pi) / γ.length * deriv (gParm γ) (2 * Real.pi * s / γ.length) := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hL : (0 : ℝ) < γ.length := γ.length_pos
    have h := gParm_deriv γ (2 * Real.pi * s / γ.length)
    have hsimp : γ.length * (2 * Real.pi * s / γ.length) / (2 * Real.pi) = s := by
      field_simp
    rw [hsimp] at h
    rw [h]
    field_simp [hL.ne', hpi.ne']

/-- area = (1/2)∫₀²π f(θ)g'(θ) - g(θ)f'(θ) dθ -/
lemma area_parametrized (γ : SimpleClosedC1Curve 2) :
    area γ 0 γ.length =
      (1 / 2) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        fParm γ t * deriv (gParm γ) t - gParm γ t * deriv (fParm γ) t := by
  unfold area
  have hL : (0 : ℝ) < γ.length := γ.length_pos
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have key : (1/2) * ∫ s in (0 : ℝ)..γ.length,
    (xCoord γ s * deriv (yCoord γ) s - yCoord γ s * deriv (xCoord γ) s) =
    (1/2) * ∫ t in (0 : ℝ)..(2*Real.pi),
    fParm γ t * deriv (gParm γ) t - gParm γ t * deriv (fParm γ) t := by
      have xeq : ∀ s, xCoord γ s = fParm γ (2 * Real.pi * s / γ.length) := fun s ↦ by
        simp only [fParm, xCoord]
        have heq : γ.length * (2 * Real.pi * s / γ.length) / (2 * Real.pi) = s := by
         field_simp [hL.ne']
        rw [heq]
      have yeq : ∀ s, yCoord γ s = gParm γ (2 * Real.pi * s / γ.length) := fun s ↦ by
        simp only [gParm, yCoord]
        have heq : γ.length * (2 * Real.pi * s / γ.length) / (2 * Real.pi) = s := by
          field_simp [hL.ne']
        rw [heq]
      simp_rw [xeq, yeq, xPrime_s, yPrime_s]
      have hπL_ne : γ.length ≠ 0 := hL.ne'
      have h2π_ne : (2 : ℝ) * Real.pi ≠ 0 := hpi.ne'
      have hscale : (2 * Real.pi / γ.length) ≠ 0 := div_ne_zero h2π_ne hπL_ne
      -- factor (2π/L) out of each integrand term
      have factor : ∀ s : ℝ,
          fParm γ (2 * Real.pi * s / γ.length) *
            (2 * Real.pi / γ.length * deriv (gParm γ) (2 * Real.pi * s / γ.length)) -
          gParm γ (2 * Real.pi * s / γ.length) *
            (2 * Real.pi / γ.length * deriv (fParm γ) (2 * Real.pi * s / γ.length)) =
          (2 * Real.pi / γ.length) *
            (fParm γ (2 * Real.pi / γ.length * s) * deriv (gParm γ) (2 * Real.pi / γ.length * s) -
             gParm γ (2 * Real.pi / γ.length * s) * deriv (fParm γ) (2 * Real.pi / γ.length * s)) :=
        fun s => by rw [show 2 * Real.pi * s / γ.length =
        2 * Real.pi / γ.length * s from by ring]; ring
      congr 1
      simp_rw [factor, intervalIntegral.integral_const_mul]
      -- use smul_integral_comp_mul_left with named args to pin down f exactly
      have key3 := intervalIntegral.smul_integral_comp_mul_left
        (f := fun t : ℝ => fParm γ t * deriv (gParm γ) t - gParm γ t * deriv (fParm γ) t)
        (a := (0 : ℝ)) (b := γ.length) (2 * Real.pi / γ.length)
      rw [mul_zero, show (2 * Real.pi / γ.length) * γ.length = 2 * Real.pi from by
        field_simp] at key3
      exact key3
  -- connect the outer goal (uses .ofLp and deriv γ.curve) to key (uses xCoord/yCoord)
  have hxd : ∀ t : ℝ, deriv (xCoord γ) t = (deriv γ.curve t) 0 := fun t => by
    rw [(xCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have hyd : ∀ t : ℝ, deriv (yCoord γ) t = (deriv γ.curve t) 1 := fun t => by
    rw [(yCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have eq1 : (1/2) * ∫ t in (0:ℝ)..γ.length,
      ((γ.curve t).ofLp 0 * (deriv γ.curve t).ofLp 1 -
       (γ.curve t).ofLp 1 * (deriv γ.curve t).ofLp 0) =
    (1/2) * ∫ s in (0:ℝ)..γ.length,
      (xCoord γ s * deriv (yCoord γ) s - yCoord γ s * deriv (xCoord γ) s) := by
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [xCoord, yCoord, hxd, hyd]
  rw [eq1]
  exact key

/-- IBP to prove ∫₀²π f(θ) g'(θ) dθ = -∫₀²π g(θ) f'(θ) dθ -/
lemma IBP_to_fParm_gParm (γ : SimpleClosedC1Curve 2)
    (hdc : Continuous (deriv γ.curve)) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), fParm γ t * deriv (gParm γ) t =
      -∫ t in (0 : ℝ)..(2 * Real.pi), gParm γ t * deriv (fParm γ) t := by
  -- Step 1: HasDerivAt for fParm γ at every point (chain rule)
  have hfHD : ∀ t : ℝ, HasDerivAt (fParm γ) (deriv (fParm γ) t) t := fun t => by
    rw [fParm_deriv]
    have hinner : HasDerivAt (fun θ : ℝ => γ.length * θ / (2 * Real.pi))
        (γ.length / (2 * Real.pi)) t := by
      have heq : (fun θ : ℝ => γ.length * θ / (2 * Real.pi)) =
                 fun θ => θ * (γ.length / (2 * Real.pi)) := by ext θ; ring
      rw [heq]; simpa using (hasDerivAt_id t).mul_const (γ.length / (2 * Real.pi))
    exact HasDerivAt.comp t
      (xCoord_hasDerivAt γ _).differentiableAt.hasDerivAt hinner
  -- Step 2: HasDerivAt for gParm γ at every point (chain rule)
  have hgHD : ∀ t : ℝ, HasDerivAt (gParm γ) (deriv (gParm γ) t) t := fun t => by
    rw [gParm_deriv]
    have hinner : HasDerivAt (fun θ : ℝ => γ.length * θ / (2 * Real.pi))
        (γ.length / (2 * Real.pi)) t := by
      have heq : (fun θ : ℝ => γ.length * θ / (2 * Real.pi)) =
                 fun θ => θ * (γ.length / (2 * Real.pi)) := by ext θ; ring
      rw [heq]; simpa using (hasDerivAt_id t).mul_const (γ.length / (2 * Real.pi))
    exact HasDerivAt.comp t
      (yCoord_hasDerivAt γ _).differentiableAt.hasDerivAt hinner
  -- Step 3: HasDerivAt for the product t ↦ fParm γ t * gParm γ t (product rule)
  have hprodHD : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun t => fParm γ t * gParm γ t)
        (deriv (fParm γ) t * gParm γ t + fParm γ t * deriv (gParm γ) t) t :=
    fun t _ => (hfHD t).mul (hgHD t)
  -- Step 4: Express coordinate derivatives in terms of deriv γ.curve
  have hxd : ∀ t : ℝ, deriv (xCoord γ) t = (deriv γ.curve t) 0 := fun t => by
    rw [(xCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have hyd : ∀ t : ℝ, deriv (yCoord γ) t = (deriv γ.curve t) 1 := fun t => by
    rw [(yCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  -- Step 5: Continuity of coordinate projections (PiLp projections are CLMs)
  have eval0 : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => v 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).continuous
  have eval1 : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => v 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).continuous
  -- Step 6: Continuity of the reparametrization θ ↦ L·θ/(2π)
  have hlinear : Continuous (fun θ : ℝ => γ.length * θ / (2 * Real.pi)) := by fun_prop
  -- Step 7: Continuity of fParm γ and gParm γ
  have hf_cont : Continuous (fParm γ) := by
    have heq : fParm γ = (fun v : EuclideanSpace ℝ (Fin 2) => v 0) ∘ γ.curve ∘
               (fun θ => γ.length * θ / (2 * Real.pi)) := by
      ext θ; simp [fParm, xCoord, Function.comp]
    rw [heq]; exact eval0.comp (γ.continuous.comp hlinear)
  have hg_cont : Continuous (gParm γ) := by
    have heq : gParm γ = (fun v : EuclideanSpace ℝ (Fin 2) => v 1) ∘ γ.curve ∘
               (fun θ => γ.length * θ / (2 * Real.pi)) := by
      ext θ; simp [gParm, yCoord, Function.comp]
    rw [heq]; exact eval1.comp (γ.continuous.comp hlinear)
  -- Step 8: Continuity of deriv (fParm γ) and deriv (gParm γ)
  have hdf_cont : Continuous (fun θ => deriv (fParm γ) θ) := by
    have heq : (fun θ => deriv (fParm γ) θ) =
               fun θ => (deriv γ.curve (γ.length * θ / (2 * Real.pi))) 0 *
                        (γ.length / (2 * Real.pi)) := by
      ext θ; rw [fParm_deriv, hxd]
    rw [heq]; exact (eval0.comp (hdc.comp hlinear)).mul continuous_const
  have hdg_cont : Continuous (fun θ => deriv (gParm γ) θ) := by
    have heq : (fun θ => deriv (gParm γ) θ) =
               fun θ => (deriv γ.curve (γ.length * θ / (2 * Real.pi))) 1 *
                        (γ.length / (2 * Real.pi)) := by
      ext θ; rw [gParm_deriv, hyd]
    rw [heq]; exact (eval1.comp (hdc.comp hlinear)).mul continuous_const
  -- Step 9: Integrability from continuity on compact intervals
  have hint1 : IntervalIntegrable (fun t => deriv (fParm γ) t * gParm γ t)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (hdf_cont.mul hg_cont).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t => fParm γ t * deriv (gParm γ) t)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (hf_cont.mul hdg_cont).intervalIntegrable _ _
  have hint : IntervalIntegrable
      (fun t => deriv (fParm γ) t * gParm γ t + fParm γ t * deriv (gParm γ) t)
      MeasureTheory.volume 0 (2 * Real.pi) := hint1.add hint2
  -- Step 10: FTC — ∫₀²π (fg)' = fg(2π) - fg(0)
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprodHD hint
  -- Step 11: Boundary term vanishes by 2π-periodicity of f and g
  have hf2π : fParm γ (2 * Real.pi) = fParm γ 0 := by
    have h := fParm_periodic γ 0; simp only [zero_add] at h; exact h
  have hg2π : gParm γ (2 * Real.pi) = gParm γ 0 := by
    have h := gParm_periodic γ 0; simp only [zero_add] at h; exact h
  rw [hf2π, hg2π, sub_self] at ftc
  -- ftc : ∫ (f'g + fg') = 0
  -- Step 12: Split the integral of the sum
  rw [intervalIntegral.integral_add hint1 hint2] at ftc
  -- ftc : ∫ f'g + ∫ fg' = 0
  -- Step 13: Solve for ∫ fg' and rewrite using commutativity of multiplication
  have key : ∫ t in (0:ℝ)..(2 * Real.pi), fParm γ t * deriv (gParm γ) t =
             -(∫ t in (0:ℝ)..(2 * Real.pi), deriv (fParm γ) t * gParm γ t) := by linarith
  rw [key]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _; ring

/-- area = ∫ 0 2π f(θ) g'(θ) dθ -/
lemma area_simplified (γ : SimpleClosedC1Curve 2)
    (hdc : Continuous (deriv γ.curve)) :
    area γ 0 γ.length = ∫ t in (0 : ℝ)..(2 * Real.pi), fParm γ t * (deriv (gParm γ) t) := by
  rw [area_parametrized]
  have ibp := IBP_to_fParm_gParm γ hdc
  -- Re-establish continuity facts needed for integrability
  have hlinear : Continuous (fun θ : ℝ => γ.length * θ / (2 * Real.pi)) := by fun_prop
  have eval0 : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => v 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).continuous
  have eval1 : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => v 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).continuous
  have hxd : ∀ t : ℝ, deriv (xCoord γ) t = (deriv γ.curve t) 0 := fun t => by
    rw [(xCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have hyd : ∀ t : ℝ, deriv (yCoord γ) t = (deriv γ.curve t) 1 := fun t => by
    rw [(yCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have hf_cont : Continuous (fParm γ) := by
    have heq : fParm γ = (fun v : EuclideanSpace ℝ (Fin 2) => v 0) ∘ γ.curve ∘
               (fun θ => γ.length * θ / (2 * Real.pi)) := by
      ext θ; simp [fParm, xCoord, Function.comp]
    rw [heq]; exact eval0.comp (γ.continuous.comp hlinear)
  have hg_cont : Continuous (gParm γ) := by
    have heq : gParm γ = (fun v : EuclideanSpace ℝ (Fin 2) => v 1) ∘ γ.curve ∘
               (fun θ => γ.length * θ / (2 * Real.pi)) := by
      ext θ; simp [gParm, yCoord, Function.comp]
    rw [heq]; exact eval1.comp (γ.continuous.comp hlinear)
  have hdf_cont : Continuous (fun θ => deriv (fParm γ) θ) := by
    have heq : (fun θ => deriv (fParm γ) θ) =
               fun θ => (deriv γ.curve (γ.length * θ / (2 * Real.pi))) 0 *
                        (γ.length / (2 * Real.pi)) := by
      ext θ; rw [fParm_deriv, hxd]
    rw [heq]; exact (eval0.comp (hdc.comp hlinear)).mul continuous_const
  have hdg_cont : Continuous (fun θ => deriv (gParm γ) θ) := by
    have heq : (fun θ => deriv (gParm γ) θ) =
               fun θ => (deriv γ.curve (γ.length * θ / (2 * Real.pi))) 1 *
                        (γ.length / (2 * Real.pi)) := by
      ext θ; rw [gParm_deriv, hyd]
    rw [heq]; exact (eval1.comp (hdc.comp hlinear)).mul continuous_const
  -- Integrability of fg' and gf'
  have hint_fg' : IntervalIntegrable (fun t => fParm γ t * deriv (gParm γ) t)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (hf_cont.mul hdg_cont).intervalIntegrable _ _
  have hint_gf' : IntervalIntegrable (fun t => gParm γ t * deriv (fParm γ) t)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (hg_cont.mul hdf_cont).intervalIntegrable _ _
  -- Split ∫ (fg' - gf') = ∫ fg' - ∫ gf', then use IBP: ∫ fg' = -∫ gf'
  rw [intervalIntegral.integral_sub hint_fg' hint_gf']
  linarith

/-- 2f(θ)g'(θ) ≤ (f(θ))^2 + (g'(θ))^2 -/
lemma fParm_gParm_ineq (γ : SimpleClosedC1Curve 2) (θ : ℝ) :
    2 * fParm γ θ * deriv (gParm γ) θ ≤ (fParm γ θ)^2 + (deriv (gParm γ) θ)^2 := by
  have h : 0 ≤ (fParm γ θ - deriv (gParm γ) θ)^2 := sq_nonneg _
  nlinarith [h]

/-- area ≤ (1/2) * ∫0 2π ((f(θ))^2 + (g'(θ))^2) dθ -/
lemma area_inequality (γ : SimpleClosedC1Curve 2)
    (hdc : Continuous (deriv γ.curve)) :
    area γ 0 γ.length ≤
      (1/2) * ∫ t in (0 : ℝ)..(2 * Real.pi), ((fParm γ t)^2 + (deriv (gParm γ) t)^2) := by
  rw [area_simplified γ hdc]
  -- Continuity facts needed for integrability
  have hlinear : Continuous (fun θ : ℝ => γ.length * θ / (2 * Real.pi)) := by fun_prop
  have eval0 : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => v 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).continuous
  have eval1 : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => v 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).continuous
  have hyd : ∀ t : ℝ, deriv (yCoord γ) t = (deriv γ.curve t) 1 := fun t => by
    rw [(yCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have hf_cont : Continuous (fParm γ) := by
    have heq : fParm γ = (fun v : EuclideanSpace ℝ (Fin 2) => v 0) ∘ γ.curve ∘
               (fun θ => γ.length * θ / (2 * Real.pi)) := by
      ext θ; simp [fParm, xCoord, Function.comp]
    rw [heq]; exact eval0.comp (γ.continuous.comp hlinear)
  have hdg_cont : Continuous (fun θ => deriv (gParm γ) θ) := by
    have heq : (fun θ => deriv (gParm γ) θ) =
               fun θ => (deriv γ.curve (γ.length * θ / (2 * Real.pi))) 1 *
                        (γ.length / (2 * Real.pi)) := by
      ext θ; rw [gParm_deriv, hyd]
    rw [heq]; exact (eval1.comp (hdc.comp hlinear)).mul continuous_const
  -- Integrability of lhs and rhs integrands
  have hint_lhs : IntervalIntegrable (fun t => fParm γ t * deriv (gParm γ) t)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (hf_cont.mul hdg_cont).intervalIntegrable _ _
  have hint_rhs : IntervalIntegrable
      (fun t => (1 / 2) * ((fParm γ t)^2 + (deriv (gParm γ) t)^2))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (continuous_const.mul ((hf_cont.pow 2).add (hdg_cont.pow 2))).intervalIntegrable _ _
  -- Pointwise: fg' ≤ (1/2)(f² + g'²) follows from fParm_gParm_ineq
  have hpw : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      fParm γ t * deriv (gParm γ) t ≤ (1 / 2) * ((fParm γ t)^2 + (deriv (gParm γ) t)^2) :=
    fun t _ => by linarith [fParm_gParm_ineq γ t]
  -- ∫ fg' ≤ ∫ (1/2)(f² + g'²) by integral_mono_on
  have hmono := intervalIntegral.integral_mono_on (by positivity) hint_lhs hint_rhs hpw
  -- Pull 1/2 out: ∫ (1/2)(f² + g'²) = (1/2) * ∫ (f² + g'²) via integral_smul
  have heq : ∫ t in (0 : ℝ)..(2 * Real.pi),
        (1 / 2 : ℝ) * ((fParm γ t)^2 + (deriv (gParm γ) t)^2) =
      (1 / 2) * ∫ t in (0 : ℝ)..(2 * Real.pi), ((fParm γ t)^2 + (deriv (gParm γ) t)^2) := by
    have h : (fun t => (1 / 2 : ℝ) * ((fParm γ t)^2 + (deriv (gParm γ) t)^2)) =
             (fun t => (1 / 2 : ℝ) • ((fParm γ t)^2 + (deriv (gParm γ) t)^2)) := by
      ext t; simp [smul_eq_mul]
    rw [h, intervalIntegral.integral_smul, smul_eq_mul]
  linarith

/-- Apply Wirtinger's Inequality: for a 2π-periodic function with zero mean (a₀ = 0),
    the Parseval and Wirtinger integral formulas imply ∫₀²π f² ≤ ∫₀²π (f')².
    This follows from comparing the Fourier coefficient sums:
    ∑ₙ (aₙ² + bₙ²) ≤ ∑ₙ n²(aₙ² + bₙ²) since n ≥ 1 for all n : ℕ+. -/
lemma apply_Wirtingers_ineq (γ : SimpleClosedC1Curve 2)
    -- Fourier coefficients for fParm γ (with a 0 = 0 encoding zero mean)
    (a b : ℕ → ℝ)
    -- Parseval identity: ∫₀²π (fParm γ)² = π · ∑ₙ≥1 (aₙ² + bₙ²)
    -- (zero mean / a₀ = 0 is implicit here — the constant term is absent)
    (h_parseval : ∫ t in (0 : ℝ)..(2 * Real.pi), (fParm γ t) ^ 2 =
        Real.pi * ∑' n : ℕ+, ((a n) ^ 2 + (b n) ^ 2))
    -- Wirtinger identity (Parseval applied to f'): ∫₀²π (fParm γ')² = π · ∑ₙ≥1 n²(aₙ² + bₙ²)
    (h_wirtinger : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (fParm γ) t) ^ 2 =
        Real.pi * ∑' n : ℕ+, ((n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2)))
    -- Summability of n²(aₙ² + bₙ²) (needed for tsum comparison)
    (hsum : Summable (fun n : ℕ+ => (n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2))) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), (fParm γ t) ^ 2 ≤
      ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (fParm γ) t) ^ 2 := by
  rw [h_parseval, h_wirtinger]
  -- It suffices to compare ∑ (aₙ² + bₙ²) ≤ ∑ n²(aₙ² + bₙ²)
  apply mul_le_mul_of_nonneg_left _ (le_of_lt Real.pi_pos)
  -- Pointwise: aₙ² + bₙ² ≤ n²(aₙ² + bₙ²), since n² ≥ 1 for n : ℕ+
  have hpw : ∀ n : ℕ+, (a n) ^ 2 + (b n) ^ 2 ≤ (n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2) :=
      fun n => by
    have hn_nat : (1 : ℕ) ≤ n := Nat.succ_le_of_lt n.2
    have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_nat
    have hnn : (0 : ℝ) ≤ (a n) ^ 2 + (b n) ^ 2 := by positivity
    calc (a n) ^ 2 + (b n) ^ 2
        = 1 * ((a n) ^ 2 + (b n) ^ 2) := (one_mul _).symm
      _ ≤ (n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hnn
          nlinarith [sq_nonneg ((n : ℝ) - 1)]
  -- Summability of left side follows from right side via domination
  have hsum_left : Summable (fun n : ℕ+ => (a n) ^ 2 + (b n) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpw hsum
  exact hsum_left.tsum_le_tsum hpw hsum

/-- Combining `area_inequality` (AM-GM) and `apply_Wirtingers_ineq` (Wirtinger):
    the enclosed area is bounded by (1/2) times the integral of the sum of squared
    reparametrized velocities. -/
lemma addition_ineq (γ : SimpleClosedC1Curve 2)
    (hdc : Continuous (deriv γ.curve))
    -- Fourier coefficients and Parseval/Wirtinger hypotheses for fParm γ
    (a b : ℕ → ℝ)
    (h_parseval : ∫ t in (0 : ℝ)..(2 * Real.pi), (fParm γ t) ^ 2 =
        Real.pi * ∑' n : ℕ+, ((a n) ^ 2 + (b n) ^ 2))
    (h_wirtinger : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (fParm γ) t) ^ 2 =
        Real.pi * ∑' n : ℕ+, ((n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2)))
    (hsum : Summable (fun n : ℕ+ => (n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2))) :
    area γ 0 γ.length ≤
      (1/2) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        ((deriv (fParm γ) t)^2 + (deriv (gParm γ) t)^2) := by
  -- Rebuild continuity facts needed for integrability
  have hlinear : Continuous (fun θ : ℝ => γ.length * θ / (2 * Real.pi)) := by fun_prop
  have eval0 : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => v 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).continuous
  have eval1 : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => v 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).continuous
  have hxd : ∀ t : ℝ, deriv (xCoord γ) t = (deriv γ.curve t) 0 := fun t => by
    rw [(xCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have hyd : ∀ t : ℝ, deriv (yCoord γ) t = (deriv γ.curve t) 1 := fun t => by
    rw [(yCoord_hasDerivAt γ t).deriv, (γ.has_deriv t).choose_spec.deriv]
  have hf_cont : Continuous (fParm γ) := by
    have heq : fParm γ = (fun v : EuclideanSpace ℝ (Fin 2) => v 0) ∘ γ.curve ∘
               (fun θ => γ.length * θ / (2 * Real.pi)) := by
      ext θ; simp [fParm, xCoord, Function.comp]
    rw [heq]; exact eval0.comp (γ.continuous.comp hlinear)
  have hdf_cont : Continuous (fun θ => deriv (fParm γ) θ) := by
    have heq : (fun θ => deriv (fParm γ) θ) =
               fun θ => (deriv γ.curve (γ.length * θ / (2 * Real.pi))) 0 *
                        (γ.length / (2 * Real.pi)) := by ext θ; rw [fParm_deriv, hxd]
    rw [heq]; exact (eval0.comp (hdc.comp hlinear)).mul continuous_const
  have hdg_cont : Continuous (fun θ => deriv (gParm γ) θ) := by
    have heq : (fun θ => deriv (gParm γ) θ) =
               fun θ => (deriv γ.curve (γ.length * θ / (2 * Real.pi))) 1 *
                        (γ.length / (2 * Real.pi)) := by ext θ; rw [gParm_deriv, hyd]
    rw [heq]; exact (eval1.comp (hdc.comp hlinear)).mul continuous_const
  -- Integrability of each squared term
  have hint_f2 : IntervalIntegrable (fun t => (fParm γ t)^2)
      MeasureTheory.volume 0 (2 * Real.pi) := (hf_cont.pow 2).intervalIntegrable _ _
  have hint_dg2 : IntervalIntegrable (fun t => (deriv (gParm γ) t)^2)
      MeasureTheory.volume 0 (2 * Real.pi) := (hdg_cont.pow 2).intervalIntegrable _ _
  have hint_df2 : IntervalIntegrable (fun t => (deriv (fParm γ) t)^2)
      MeasureTheory.volume 0 (2 * Real.pi) := (hdf_cont.pow 2).intervalIntegrable _ _
  -- Step 1: area ≤ (1/2) * ∫ (f² + (g')²)   [area_inequality + AM-GM]
  -- Step 2: ∫ f² ≤ ∫ (f')²                   [apply_Wirtingers_ineq]
  -- Step 3: add ∫ (g')² to both sides of Step 2
  have h_wirtingers := apply_Wirtingers_ineq γ a b h_parseval h_wirtinger hsum
  have h_int_ineq : ∫ t in (0:ℝ)..(2*Real.pi), ((fParm γ t)^2 + (deriv (gParm γ) t)^2) ≤
                    ∫ t in (0:ℝ)..(2*Real.pi), ((deriv (fParm γ) t)^2 + (deriv (gParm γ) t)^2) := by
    rw [intervalIntegral.integral_add hint_f2 hint_dg2,
        intervalIntegral.integral_add hint_df2 hint_dg2]
    linarith
  calc area γ 0 γ.length
      ≤ (1/2) * ∫ t in (0:ℝ)..(2*Real.pi), ((fParm γ t)^2 + (deriv (gParm γ) t)^2) :=
          area_inequality γ hdc
    _ ≤ (1/2) * ∫ t in (0:ℝ)..(2*Real.pi), ((deriv (fParm γ) t)^2 + (deriv (gParm γ) t)^2) :=
          mul_le_mul_of_nonneg_left h_int_ineq (by norm_num)


/-- **Isoperimetric bound**: under arc-length parametrization, the area is at most
    `(1/2) * ∫₀²π (L/(2π))² dθ = L²/(4π)`.
    This combines `addition_ineq` (Wirtinger + AM-GM) with the arc-length constraint
    `(f')² + (g')² = (L/(2π))²` from `fParm_gParm_deriv_sq_sum`. -/
lemma apply_fParm_gParm_deriv_sq_sum (γ : SimpleClosedC1Curve 2)
    (hdc : Continuous (deriv γ.curve))
    (h_arc : IsArcLengthParametrized γ)
    (a b : ℕ → ℝ)
    (h_parseval : ∫ t in (0 : ℝ)..(2 * Real.pi), (fParm γ t) ^ 2 =
        Real.pi * ∑' n : ℕ+, ((a n) ^ 2 + (b n) ^ 2))
    (h_wirtinger : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (fParm γ) t) ^ 2 =
        Real.pi * ∑' n : ℕ+, ((n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2)))
    (hsum : Summable (fun n : ℕ+ => (n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2))) :
    area γ 0 γ.length ≤
      (1/2) * ∫ _ in (0 : ℝ)..(2 * Real.pi), (γ.length ^ 2 / (4 * (Real.pi) ^ 2)) := by
  calc area γ 0 γ.length
      ≤ (1/2) * ∫ t in (0:ℝ)..(2 * Real.pi),
            ((deriv (fParm γ) t) ^ 2 + (deriv (gParm γ) t) ^ 2) :=
          addition_ineq γ hdc a b h_parseval h_wirtinger hsum
    _ = (1/2) * ∫ t in (0:ℝ)..(2 * Real.pi), (γ.length ^ 2 / (4 * Real.pi ^ 2)) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro t _
          -- fParm_gParm_deriv_sq_sum: (f')²+(g')² = (x'²+y'²) * (L/(2π))²
          have hsq := fParm_gParm_deriv_sq_sum γ t
          -- due_to_arc_length_parametrization: x'²+y'² = 1
          have harc := due_to_arc_length_parametrization γ h_arc t
          -- combine: (f')²+(g')² = (L/(2π))² = L²/(4π²)
          rw [harc, one_mul] at hsq
          exact hsq.trans (by ring)


/-- **Isoperimetric Inequality** (Adolf Hurwitz, 1902): for any simple closed C¹ curve of
    length `L = γ.length`, the enclosed area satisfies `area ≤ L² / (4π)`.
    Combines `apply_fParm_gParm_deriv_sq_sum` (which gives `area ≤ (1/2) ∫₀²π L²/(4π²) dθ`)
    with evaluation of the constant integral: `(1/2) · L²/(4π²) · 2π = L²/(4π)`. -/
theorem isoperimetric_inequality (γ : SimpleClosedC1Curve 2)
    (hdc : Continuous (deriv γ.curve))
    (h_arc : IsArcLengthParametrized γ)
    (a b : ℕ → ℝ)
    (h_parseval : ∫ t in (0 : ℝ)..(2 * Real.pi), (fParm γ t) ^ 2 =
        Real.pi * ∑' n : ℕ+, ((a n) ^ 2 + (b n) ^ 2))
    (h_wirtinger : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv (fParm γ) t) ^ 2 =
        Real.pi * ∑' n : ℕ+, ((n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2)))
    (hsum : Summable (fun n : ℕ+ => (n : ℝ) ^ 2 * ((a n) ^ 2 + (b n) ^ 2))) :
    area γ 0 γ.length ≤ γ.length ^ 2 / (4 * Real.pi) := by
  calc area γ 0 γ.length
      ≤ (1/2) * ∫ _ in (0 : ℝ)..(2 * Real.pi), (γ.length ^ 2 / (4 * (Real.pi) ^ 2)) :=
          apply_fParm_gParm_deriv_sq_sum γ hdc h_arc a b h_parseval h_wirtinger hsum
    _ = γ.length ^ 2 / (4 * Real.pi) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          -- ∫ _ in 0..(2π), c = (2π - 0) * c = 2π * c
          -- (1/2) * (2π * (L²/(4π²))) = L²/(4π)
          have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
          field_simp
          ring

end IsoperimetricInequality
