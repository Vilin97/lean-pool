/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.Invariance
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.CircleParam

/-!
# Bridge to Mathlib Circle Integrals

Connects the project's `generalizedWindingNumber'` (defined via Cauchy principal value)
to mathlib's `circleIntegral` for the case of circular contours.

Mathlib does not define a general winding number, but it provides:
* `circleIntegral f c R` -- the integral `∮ z in C(c,R), f z`
* `circleIntegral.integral_sub_inv_of_mem_ball` -- `∮ z in C(c,R), (z-w)⁻¹ = 2πi`
  when `w ∈ ball c R`

This file shows that for `circleMap c R` over `[0, 2π]`, the project's
`generalizedWindingNumber'` agrees with the classical contour integral formula,
which in turn equals `(2πi)⁻¹ * circleIntegral (· - w)⁻¹ c R`.

## Main Results

* `contourIntegral_circleMap_eq_circleIntegral` -- the interval integral
    `∫ θ in 0..2π, f(circleMap c R θ) * deriv(circleMap c R) θ` equals
    mathlib's `∮ z in C(c,R), f z`
* `generalizedWindingNumber_circleMap_eq_inv_circleIntegral` -- when
    `circleMap c R` avoids `w`, the generalized winding number equals
    `(2πi)⁻¹ * ∮ z in C(c,R), (z - w)⁻¹`
* `generalizedWindingNumber_circleMap_eq_one_of_mem_ball` -- for `w ∈ ball c R`
    with `R > 0`, the generalized winding number of `circleMap c R` around `w`
    equals 1, via mathlib's `integral_sub_inv_of_mem_ball`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- The interval integral `∫ θ in 0..2π, f(circleMap c R θ) * deriv(circleMap c R) θ`
equals mathlib's circle integral `∮ z in C(c,R), f z`.

This is the key bridge: mathlib defines `circleIntegral` using `smul` (scalar
multiplication `deriv(circleMap c R) θ • f(circleMap c R θ)`), while the project
uses `mul` (pointwise multiplication `f(γ t) * deriv γ t`). For `ℂ`-valued
functions, `smul` and `mul` coincide. -/
theorem contourIntegral_circleMap_eq_circleIntegral (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      f (circleMap c R θ) * deriv (circleMap c R) θ =
    ∮ z in C(c, R), f z := by
  simp only [circleIntegral, smul_eq_mul, mul_comm]

/-- The generalized winding number of `circleMap c R` around `w` (for a point
not on the circle) equals `(2πi)⁻¹ * ∮ z in C(c,R), (z - w)⁻¹`.

This combines `generalizedWindingNumber_eq_classical_away` (which shows the PV
winding number equals the classical integral when the curve avoids `w`) with
`contourIntegral_circleMap_eq_circleIntegral` (which identifies the classical
integral with mathlib's `circleIntegral`). -/
theorem generalizedWindingNumber_circleMap_eq_inv_circleIntegral
    (c w : ℂ) (R : ℝ) (hR : 0 < R)
    (hw : ‖w - c‖ ≠ R) :
    generalizedWindingNumber' (circleMap c R) 0 (2 * Real.pi) w =
    (2 * Real.pi * I)⁻¹ * (∮ z in C(c, R), (z - w)⁻¹) := by
  -- The curve avoids w because ‖circleMap c R θ - c‖ = |R| = R (since R > 0)
  -- and ‖w - c‖ ≠ R by hypothesis.
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- Build a PiecewiseC1Curve for circleMap c R on [0, 2π]
  have hcont : ContinuousOn (circleMap c R) (Icc 0 (2 * Real.pi)) :=
    (continuous_circleMap c R).continuousOn
  have hdiff : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi), t ∉ ({0, 2 * Real.pi} : Finset ℝ) →
      DifferentiableAt ℝ (circleMap c R) t :=
    fun t _ _ => (differentiable_circleMap c R).differentiableAt
  have hderiv_cont : ∀ t ∈ Ioo (0 : ℝ) (2 * Real.pi),
      t ∉ ({0, 2 * Real.pi} : Finset ℝ) →
      ContinuousAt (deriv (circleMap c R)) t := by
    intro t _ _
    have : deriv (circleMap c R) = fun θ => circleMap 0 R θ * I := by
      ext θ; exact deriv_circleMap c R θ
    rw [this]
    exact (continuous_circleMap 0 R).continuousAt.mul continuousAt_const
  let γ : PiecewiseC1Curve := {
    toFun := circleMap c R
    a := 0
    b := 2 * Real.pi
    hab := h2pi
    partition := {0, 2 * Real.pi}
    partition_subset := by
      intro x hx
      simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨le_refl _, h2pi.le⟩
      · exact ⟨h2pi.le, le_refl _⟩
    endpoints_in_partition := by
      exact ⟨by simp, by simp⟩
    continuous_toFun := hcont
    smooth_off_partition := hdiff
    deriv_continuous_off_partition := hderiv_cont
  }
  -- circleMap avoids w
  have havoids : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi), circleMap c R t ≠ w := by
    intro t _
    have h_norm : ‖circleMap c R t - c‖ = R := by
      simp [circleMap, Complex.norm_real, abs_of_pos hR,
        Complex.norm_exp_ofReal_mul_I]
    intro heq
    rw [heq] at h_norm
    exact hw h_norm
  -- Apply the classical away theorem
  have hclass := generalizedWindingNumber_eq_classical_away γ w havoids
  simp only [γ] at hclass
  rw [hclass]
  congr 1
  exact contourIntegral_circleMap_eq_circleIntegral (fun z => (z - w)⁻¹) c R

/-- The generalized winding number of `circleMap c R` around a point `w` inside
the circle equals 1.

This is the definitive bridge between the project's `generalizedWindingNumber'`
and mathlib's circle integral theory. The proof factors through mathlib's
`circleIntegral.integral_sub_inv_of_mem_ball`, which computes
`∮ z in C(c,R), (z-w)⁻¹ = 2πi`. -/
theorem generalizedWindingNumber_circleMap_eq_one_of_mem_ball
    (c w : ℂ) (R : ℝ) (hR : 0 < R) (hw : w ∈ Metric.ball c R) :
    generalizedWindingNumber' (circleMap c R) 0 (2 * Real.pi) w = 1 := by
  -- w ∈ ball c R means dist w c < R, so ‖w - c‖ < R ≠ R
  have hw_ne : ‖w - c‖ ≠ R := by
    have h_lt : dist w c < R := hw
    rw [Complex.dist_eq] at h_lt
    exact ne_of_lt h_lt
  rw [generalizedWindingNumber_circleMap_eq_inv_circleIntegral c w R hR hw_ne]
  rw [circleIntegral.integral_sub_inv_of_mem_ball hw]
  have hpi_ne : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero]
  field_simp

/-- The classical contour integral of `(z - w)⁻¹` around a circle containing `w`
equals `2πi`, expressed in the project's interval integral format.

This is a convenience wrapper: it states the result purely in terms of interval
integrals (no `circleIntegral` notation), useful for downstream proofs that
work with `∫ t in a..b, ...` rather than `∮`. -/
theorem circleMap_contourIntegral_sub_inv_eq_two_pi_I
    (c w : ℂ) (R : ℝ) (_hR : 0 < R) (hw : w ∈ Metric.ball c R) :
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      (circleMap c R θ - w)⁻¹ * deriv (circleMap c R) θ =
    2 * Real.pi * I := by
  have h := contourIntegral_circleMap_eq_circleIntegral (fun z => (z - w)⁻¹) c R
  rw [h]
  exact circleIntegral.integral_sub_inv_of_mem_ball hw

end
