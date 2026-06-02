/-
Copyright (c) 2026 seb488, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: seb488, Aristotle
-/
import LeanPool.LeanComplexAnalysis.Harmonic.PoissonIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Poisson Integral Formula on Disc

## Main results

Theorems `poisson_integral_of_harmonicOn_disc_continuousOn_closedDisc` and
`poisson_integral_of_harmonicOn_disc_continuousOn_closedDisc_ker_re`:
Every function `u : ℂ → ℝ` harmonic on the disc with radius `R` and center `0`, and
continuous on the closed disc, can be represented as
```
u(z) = 1/(2π) ∫_0^{2π} (R² - |z|²) / |R * exp (it) - z|² * u(R * exp (it)) dt
     = 1/(2π) ∫_0^{2π} Re((R * exp (it) + z) / (R * exp (it) - z)) * u(R * exp (it)) dt,
```
for `z` in the disc.

Theorem `poisson_integral_of_diffContOnCl_disc` and `poisson_integral_of_diffContOnCl_disc_ker_re`:
Every function `f : ℂ → E` ℂ-differentiable on the disc with radius `R` and center `0`, and
continuous on the closed disc, with values in a complex Banach space `E`, can be represented as
```
f(z) = 1/(2π) ∫_0^{2π} (R² - |z|²) / |R * exp (it) - z|² • f(R * exp (it)) dt
     = 1/(2π) ∫_0^{2π} Re((R * exp (it) + z) / (R * exp (it) - z)) • f(R * exp (it)) dt,
```
for `z` in the disc.

## Implementation Notes

The proof follows from
- Cauchy Integral Formula,
- Cauchy-Goursat Theorem,
- a harmonic function is the real part of a holomorphic function on a disc,
- Lebesgue's Dominated Convergence Theorem.

## References

[Rudin, *Real and Complex Analysis* (Theorem 11.9)][rudin2006real]

## Tags

ℂ-differentiable function, harmonic function, Poisson integral.
-/

open Complex Metric Real Set

namespace LeanPool.LeanComplexAnalysis

/-- Scaling by `r ∈ (0,1)` a point in a closed disc centerd at `0` is in the open disc. -/
lemma mem_disc_of_scaled {z : ℂ} {r R : ℝ} (hR : 0 < R)
    (hz : ‖z‖ ≤ R) (hr : r ∈ Ioo 0 1) : r * z ∈ ball 0 R := by
  rw [mem_ball, dist_zero_right, norm_mul, norm_real, norm_eq_abs, abs_of_pos hr.1]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz (le_of_lt hr.1))
                       ((mul_lt_iff_lt_one_left hR).mpr hr.2)

/-- `r * R * exp (t * I)` is in the disc of radius `R` and center `0`, for `r ∈ (0,1)`. -/
lemma mem_disc_of_scaled_exp_ofReal_mul_I {r R : ℝ} (hR : 0 < R) (hr : r ∈ Ioo 0 1) (t : ℝ) :
    r * R * exp (t * I) ∈ ball 0 R := by
      rw [mul_assoc]
      apply mem_disc_of_scaled hR _ hr
      simp [norm_exp_ofReal_mul_I, abs_of_pos hR]


/-- `R * exp (t * I)` is not equal to any `z` in the disc of radius `R`, centered at `0`. -/
lemma neq_in_disc_of_mul_exp_ofReal_mul_I {z : ℂ} {R : ℝ}
    (hz : z ∈ ball 0 R) (t : ℝ) : R * exp (t * I) - z ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  simp [← h, mem_ball, dist_zero_right, norm_exp_ofReal_mul_I,
        norm_real, norm_eq_abs, abs_of_pos (pos_of_mem_ball hz)] at hz

/-- `R * star (exp (t * I))` is not equal to any `z` in the disc of radius `R`, centered at `0`. -/
lemma neq_in_disc_of_mul_star_exp_ofReal_mul_I {z : ℂ} {R : ℝ}
    (hz : z ∈ ball 0 R) (t : ℝ) : R * star (exp (t * I)) - star z ≠ 0 := by
  have : R * star (exp (t * I)) = star (R * exp (t * I)) := by simp [star_mul']
  rw [this, ← star_sub]
  exact star_ne_zero.mpr (neq_in_disc_of_mul_exp_ofReal_mul_I hz t)

/-- `R ^ 2 - star z * w ≠ 0`, for `z` in the disc with radius `R` and center `0`,
and for `w` in the closed disc. -/
lemma radius_sq_sub_star_mul_neq_zero {z : ℂ} {w : ℂ} {R : ℝ}
    (hz : z ∈ ball 0 R) (hw : w ∈ closedBall 0 R) : R ^ 2 - star z * w ≠ 0 := by
  intro h
  have hz_norm : ‖z‖ < R := by rw [mem_ball_zero_iff] at hz; exact hz
  have hw_norm : ‖w‖ ≤ R := mem_closedBall_zero_iff.mp hw
  have : ‖star z * w‖ < R ^ 2 := by
    calc ‖star z * w‖ ≤ ‖star z‖ * ‖w‖ := norm_mul_le _ _
      _ = ‖z‖ * ‖w‖ := by rw [norm_star]
      _ < R ^ 2 := by  nlinarith [norm_nonneg z, norm_nonneg w]
  rw [sub_eq_zero] at h
  rw [← h] at this
  simp [norm_real, norm_eq_abs, abs_of_pos (pos_of_mem_ball hz)] at this

/-- If `f` is `ℂ`-differentiable on a disc centered at zero,
then `ζ ↦ f (r * ζ)` is differentiable at `z` for `r` in `(0,1)` and `z` in the closed disc. -/
lemma differentiableAt_of_differentiableOn_disc_of_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} {r R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hz : z ∈ closedBall 0 R) (hr : r ∈ Ioo 0 1) :
    DifferentiableAt ℂ (fun ζ => f (r * ζ)) z := by
  rw [mem_closedBall, dist_zero_right] at hz
  exact DifferentiableAt.comp z (hf.differentiableAt
        (isOpen_ball.mem_nhds (mem_disc_of_scaled hR hz hr)))
        (differentiableAt_id.const_mul _)

/-- Cauchy's integral formula applied to `f` `ℂ`-differentiable on a disc centered at `0`,
at the point `r*z`, for `r` in `(0,1)` and `z` in the disc. -/
lemma cauchy_circleIntegral_formula_scaled_disc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ} {r R : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 R) :
    f (r * z) = (1 / (2 * π * I)) • ∮ (ζ : ℂ) in C(0, R), (1 / (ζ - z)) • f (r * ζ) := by
  have hfr_cont : ContinuousOn (fun ζ => f (r * ζ)) (closedBall 0 R) :=
    fun x hx => (DifferentiableAt.continuousAt (differentiableAt_of_differentiableOn_disc_of_mul
                  (pos_of_mem_ball hz) hf hx hr)).continuousWithinAt
  have := @circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    _ _ _ _ R 0 z (fun ζ => f (r * ζ)) ∅ countable_empty hz hfr_cont
  simp only [div_eq_inv_mul, mul_one]
  rw [this]
  · simp only [smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero]
    exact Eq.symm (MulAction.one_smul (f (r * z)))
  · intro x hx
    simp only [diff_empty] at hx
    exact differentiableAt_of_differentiableOn_disc_of_mul (pos_of_mem_ball hz) hf
            (ball_subset_closedBall hx) hr

/-- Cauchy's integral formula for `ℂ`-differentiable functions on a disc centred at 0,
evaluated at scaled points `r * z` with `r ∈ (0,1)`. -/
lemma cauchy_integral_formula_scaled_disc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ} {r R : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 R) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2 * π,
                (R * exp (t * I) / (R * exp (t * I) - z)) • f (r * R * exp (t * I)) := by
  have h_cauchy := cauchy_circleIntegral_formula_scaled_disc hf hr hz
  rw [← circleIntegral.integral_smul] at h_cauchy
  rw [← intervalIntegral.integral_smul, h_cauchy]
  simp only [circleIntegral]
  congr 1
  ext t
  have : f (r * circleMap 0 R t) = f (r * R * exp (t * I)) := by
    congr 1
    simp [circleMap, mul_assoc]
  rw [this]
  simp only [← smul_assoc]
  have : (deriv (circleMap 0 R) t • (1 / (2 * π * I))) • (1 / (circleMap 0 R t - z)) =
         ((1 / (2 * π)) • (R * exp (t * I) / (R * exp (t * I) - z))) := by
    simp only [deriv_circleMap, circleMap, zero_add, mul_inv_rev,
              div_eq_inv_mul, smul_eq_mul, real_smul, ofReal_mul,
              ofReal_inv, ofReal_ofNat, mul_one, mul_assoc]
    rw [← mul_assoc I I⁻¹, mul_inv_cancel₀ I_ne_zero, one_mul]
    ring_nf
  rw [this, Complex.real_smul, mul_smul]

/-- If `f` is `ℂ`-differentiable on a disc centered at zero, then
`ζ ↦ (star z / (I * (R ^ 2 - star z * ζ))) • f (r * ζ)` is differentiable at `w`
in the closed disc with radius `R` and center `0`, for `r` in `(0,1)`. -/
lemma differentiableAt_goursat_integrand_scaled_disc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {z w : ℂ} {r R : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : r ∈ Ioo 0 1)
    (hz : z ∈ ball 0 R) (hw : w ∈ closedBall 0 R) :
    DifferentiableAt ℂ (fun ζ => (star z / (I * (R ^ 2 - star z * ζ))) • f (r * ζ)) w := by
  refine DifferentiableAt.smul ?_ ?_
  · refine DifferentiableAt.div (differentiableAt_const _) ?_ ?_
    · apply DifferentiableAt.const_mul
      refine DifferentiableAt.sub (differentiableAt_const (R ^ 2 : ℂ)) ?_
      exact DifferentiableAt.mul (differentiableAt_const (star z)) differentiableAt_id
    · exact mul_ne_zero I_ne_zero (radius_sq_sub_star_mul_neq_zero hz hw)
  · exact differentiableAt_of_differentiableOn_disc_of_mul (pos_of_mem_ball hz) hf hw hr

/-- We apply the Cauchy-Goursat theorem to the function
`ζ ↦ (star z / (I * (R ^ 2 - star z * ζ))) • (f (r * ζ)))`
on the circle of radius `R`, centered at `0`. -/
lemma vanishing_goursat_circleIntegral_scaled_disc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} {r R : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 R) :
    (∮ w in C(0, R), (star z / (I * (R ^ 2 - star z * w))) • f (r * w)) = 0 := by
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable
          (pos_of_mem_ball hz).le countable_empty
  · exact fun ζ hζ => (DifferentiableAt.continuousAt
          (differentiableAt_goursat_integrand_scaled_disc hf hr hz hζ)).continuousWithinAt
  · rw [diff_empty]
    exact fun ζ hζ => differentiableAt_goursat_integrand_scaled_disc hf hr hz
                      (ball_subset_closedBall hζ)

/-- An auxiliary identity that will be used in the integrand of the Cauchy-Goursat theorem. -/
lemma goursat_integrand_eq_aux_disc (z : ℂ) (t R : ℝ) (hR : 0 < R) :
    star z / (R * star (exp (t * I)) - star z) =
    I * R * exp (t * I) * (star z / (I * (R ^ 2 - star z * R * exp (t * I)))) := by
  have : I * (R ^ 2 - star z * R * exp (t * I)) = I * R * (R - star z * exp (t * I)) := by
    ring_nf
  rw [this]
  have : I * R ≠ 0 := by simp [I_ne_zero, ne_of_gt hR]
  rw [star_exp_ofReal_mul_I_eq_inv, mul_comm (I * R), mul_assoc, ← mul_div_assoc,
      mul_div_mul_left (hc := this), ← mul_div_assoc, mul_comm (exp (t * I)),
      mul_div_assoc, div_eq_mul_inv (star z)]
  congr 1
  rw [inv_eq_one_div]
  nth_rewrite 2 [← inv_inv (exp (t * I)), inv_eq_one_div]
  rw [div_div, mul_sub, mul_comm (star z), ← mul_assoc,
      inv_mul_cancel₀ (Complex.exp_ne_zero (t * I)), one_mul]
  congr 1
  ring_nf

/-- The Cauchy-Goursat theorem for a disc centered at `0` implies the integral of a
`ℂ`-differentiable function against a conjugate Cauchy kernel vanishes. -/
lemma vanishing_goursat_integral_scaled_disc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} {r R : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 R) :
    ∫ t in 0..2 * π, (star z / (R * star (exp (t * I)) - star z)) •
      f (r * R * exp (t * I)) = 0 := by
  convert (vanishing_goursat_circleIntegral_scaled_disc hf hr hz) using 3
  rw [circleIntegral_def_Icc]
  rw [intervalIntegral.integral_of_le (mul_nonneg zero_le_two pi_pos.le)]
  congr 1
  · exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc
  · funext θ
    simp only [circleMap_zero, deriv_circleMap, smul_smul]
    nth_rewrite 1 [mul_comm (R * exp (θ * I)), ← mul_assoc I]
    rw [goursat_integrand_eq_aux_disc z θ R (pos_of_mem_ball hz)]
    congr 1 <;> simp [mul_assoc]

/-- We put together `cauchy_integral_formula_scaled_disc` and
`vanishing_goursat_integral_scaled_disc`. -/
lemma cauchy_goursat_integral_scaled_disc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ} {r R : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 R) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2 * π,
              (R * exp (t * I) / (R * exp (t * I) - z)) • f (r * R * exp (t * I)) +
              (star z / (R * star (exp (t * I)) - star z)) • f (r * R* exp (t * I)) := by
  rw [intervalIntegral.integral_add]
  · rw [cauchy_integral_formula_scaled_disc hf hr hz,
        vanishing_goursat_integral_scaled_disc hf hr hz, add_zero]
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.smul ?_ ?_
    · exact ContinuousOn.div (Continuous.continuousOn (by fun_prop))
                               (Continuous.continuousOn (by fun_prop))
                               (fun t _ => neq_in_disc_of_mul_exp_ofReal_mul_I hz t)
    · exact hf.continuousOn.comp (Continuous.continuousOn (by fun_prop))
              (fun t _ => mem_disc_of_scaled_exp_ofReal_mul_I (pos_of_mem_ball hz) hr t)
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.smul ?_ ?_
    · exact ContinuousOn.div (Continuous.continuousOn continuous_const)
       (Continuous.continuousOn (by fun_prop))
       (fun t _ => neq_in_disc_of_mul_star_exp_ofReal_mul_I hz t)
    · exact hf.continuousOn.comp (by fun_prop)
                (fun t _ => mem_disc_of_scaled_exp_ofReal_mul_I (pos_of_mem_ball hz) hr t)

/-- For a ℂ-differentiable function `f : ℂ → E` on a disc centered at `0`, `f(r*z)` equals the
integral of `f(r*R*e^{it})` against the Poisson kernel, where `r ∈ (0,1)` and `z` is in the disc. -/
theorem poisson_integral_of_differentiableOn_scaled_disc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ} {r R : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 R) :
    f (r * z) = (1 / (2 * π)) • ∫ t in 0..2 * π,
      ((R ^ 2 - ‖z‖ ^ 2) / ‖R * exp (t * I) - z‖ ^ 2) • f (r * R * exp (t * I)) := by
  convert cauchy_goursat_integral_scaled_disc hf hr hz using 3
  ext t
  rw [← add_smul]
  apply congrArg (fun (x : ℂ) => x • f (r * R * exp (t * I)))
  dsimp
  simp only [← star_def]
  rw [div_add_div _ _ (neq_in_disc_of_mul_exp_ofReal_mul_I hz t)
                      (neq_in_disc_of_mul_star_exp_ofReal_mul_I hz t)]
  symm
  have : (R * exp (t * I) * (R * star (exp (t * I)) - star z) + (R * cexp (t * I) - z) * star z) =
          R ^ 2 - ‖z‖ ^ 2 := by
    ring_nf
    rw [mul_assoc, mul_comm (star z), star_def]
    simp [mul_conj, normSq_eq_norm_sq]
  rw [this]
  simp only [ofReal_div, ofReal_sub, ofReal_pow]
  congr 1
  have : R * star (exp (t * I)) - star z = star (R * exp (t * I) - z) := by
    simp [star_sub, star_mul']
  rw [this, star_def, mul_conj, normSq_eq_norm_sq, ofReal_pow]


open InnerProductSpace

/-- For a harmonic function `u` on a disc with radius `R`, centered at `0`,
`u(r*z)` equals the integral of `u(r*R*e^{it})` against the Poisson kernel,
where `r ∈ (0,1)` and `z` is in the disc. -/
theorem poisson_integral_of_harmonicOn_scaled_disc {u : ℂ → ℝ} {z : ℂ} {r R : ℝ}
    (hu : HarmonicOnNhd u (ball 0 R)) (hr : r ∈ Ioo 0 1) (hz : z ∈ ball 0 R) :
    u (r * z) = (1 / (2 * π)) * ∫ t in (0)..(2 * π),
      ((R ^ 2 - ‖z‖ ^ 2) / ‖R * exp (t * I) - z‖ ^ 2) * u (r * R * exp (t * I)) := by
  have hfu : ∃ (f : ℂ → ℂ), DifferentiableOn ℂ f (ball 0 R) ∧
    EqOn (fun (z : ℂ) => (f z).re) u (ball 0 R) := by
    obtain ⟨f, hf⟩ := hu.exists_analyticOnNhd_ball_re_eq
    use f
    exact ⟨hf.1.differentiableOn, hf.2⟩
  obtain ⟨f, hf, hf_eq⟩ := hfu
  rw [← hf_eq (mem_disc_of_scaled (pos_of_mem_ball hz) (LT.lt.le (mem_ball_zero_iff.mp hz)) hr)]
  -- We replace `u(rz)` by `Re(f(rz))`.
  have hrt_eq : EqOn
    (fun t : ℝ => (R ^ 2 - ‖z‖^2) / ‖R * exp (t * I) - z‖^2 * (f (r * R * exp (t * I))).re)
    (fun t : ℝ => (R ^ 2 - ‖z‖^2) / ‖R * exp (t * I) - z‖^2 * u (r * R * exp (t * I)))
    (uIcc 0 (2 * π)) := fun t _ => by
      simp only [← hf_eq (mem_disc_of_scaled_exp_ofReal_mul_I (pos_of_mem_ball hz) hr t)]
  rw [← intervalIntegral.integral_congr hrt_eq]
  dsimp
  rw [congr_arg re (poisson_integral_of_differentiableOn_scaled_disc hf hr hz)]
  change ((((1 / (2 * π) : ℝ) : ℂ) *
    (∫ t in 0..2 * π, ((R ^ 2 - ‖z‖ ^ 2) / ‖R * exp (t * I) - z‖ ^ 2) •
      f (r * R * exp (t * I)))).re = _)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  simp only [intervalIntegral.integral_of_le two_pi_pos.le]
  symm
  rw [← RCLike.re_eq_complex_re]
  convert integral_re _ using 1
  · simp only [real_smul, RCLike.mul_re, RCLike.re_to_complex, ofReal_re, RCLike.im_to_complex,
               ofReal_im, zero_mul, sub_zero]
  · refine ContinuousOn.integrableOn_Icc ?_ |> fun h => h.mono_set <| Ioc_subset_Icc_self
    have h_eq :
        (fun t : ℝ =>
            ((R ^ 2 - ‖z‖ ^ 2) / ‖↑R * cexp (↑t * I) - z‖ ^ 2) •
              f (↑r * ↑R * cexp (↑t * I))) =
          fun t : ℝ =>
            (((R ^ 2 - ‖z‖ ^ 2) / ‖↑R * cexp (↑t * I) - z‖ ^ 2 : ℝ) : ℂ) *
              f (↑r * ↑R * cexp (↑t * I)) := by
      funext t
      rw [Complex.real_smul]
    rw [h_eq]
    refine ContinuousOn.mul ?_ ?_
    · refine Continuous.continuousOn ?_
      have hd : Continuous fun t : ℝ =>
          ((R ^ 2 - ‖z‖ ^ 2) / ‖↑R * cexp (↑t * I) - z‖ ^ 2 : ℝ) :=
        Continuous.div (by fun_prop) (by fun_prop)
          (fun t => by positivity [neq_in_disc_of_mul_exp_ofReal_mul_I hz t])
      exact Complex.continuous_ofReal.comp hd
    · exact hf.continuousOn.comp (Continuous.continuousOn (by fun_prop))
        (fun t _ => mem_disc_of_scaled_exp_ofReal_mul_I (pos_of_mem_ball hz) hr t)

open Filter Topology

/-- We bound  `t ↦ ‖k (R * exp (t * I)) • f (r * R * exp (t * I))‖`, for
`k` continuous on the circle of radius `R` and center `0`,
and `f` continuous on the closed disc of radius `R` and center `0`. -/
lemma bounds_of_continuousOn_circle_closedDisc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → E} {k : ℂ → ℝ} {r t R : ℝ} (hR : 0 < R) (hr : r ∈ Ioo 0 1)
    (hf : ContinuousOn f (closedBall 0 R)) (hk : ContinuousOn k (sphere 0 R)) :
    ‖k (R * exp (t * I)) • f (r * R * exp (t * I))‖ ≤
    sSup ((fun ζ ↦ |k ζ|) '' sphere 0 R) * sSup ((fun w ↦ ‖f w‖) '' closedBall 0 R) := by
  have h_bds :
      ‖f (r * R * exp (t * I))‖ ≤ sSup (image (fun w => ‖f w‖) (closedBall 0 R)) ∧
      ‖k (R * exp (t * I))‖ ≤ sSup (image (fun w => ‖k w‖) (sphere 0 R)) := by
    refine ⟨le_csSup ?_ ?_, le_csSup ?_ ?_⟩
    · exact IsCompact.bddAbove (isCompact_closedBall 0 R |>.image_of_continuousOn hf.norm)
    · exact ⟨_, ball_subset_closedBall (mem_disc_of_scaled_exp_ofReal_mul_I hR hr t), rfl⟩
    · exact IsCompact.bddAbove (IsCompact.image_of_continuousOn (isCompact_sphere 0 R) hk.norm)
    · exact ⟨R * exp (t * I), ⟨by simp [norm_exp_ofReal_mul_I, hR.le], rfl⟩⟩
  have hmul_bds : |k (R * exp (t * I))| * ‖f (r * R * exp (t * I))‖ ≤
    (sSup (image (fun ζ => |k ζ|) (sphere 0 R))) *
    (sSup (image (fun w => ‖f w‖) (closedBall 0 R))) := by
        apply mul_le_mul h_bds.2 h_bds.1 (norm_nonneg (f (r * R * exp (t * I))))
        apply sSup_nonneg
        rintro _ ⟨_, ⟨_, hx⟩⟩
        simp_rw [← hx, norm_nonneg]
  have hmul_norm : ‖k (R * exp (t * I)) • f (r * R * exp (t * I))‖ ≤
    ‖k (R * exp (t * I))‖ * ‖f (r * R * exp (t * I))‖ := by rw [norm_smul]
  exact le_trans hmul_norm hmul_bds

/-- For a sequence `rₙ → 1` with `rₙ ∈ (0,1)`, the integral of
`t ↦ k(R*e^{it}) • f(rₙ*R*e^{it})` on `[0 , 2π]` converges to the integral of
`t ↦ k(R*e^{it}) • f(R*e^{it})` on `[0 , 2π]`, when `f` is continuous on the
closed disc of radius `R` and center `0`, and `k` is continuous on the circle of radius `R`
and center `0`, by Lebesgue's Dominated Convergence Theorem. -/
lemma tendsto_integral_prod_of_continuousOn_circle_closedDisc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {k : ℂ → ℝ} {r : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (closedBall 0 R)) (hk : ContinuousOn k (sphere 0 R))
    (hr : ∀ n, r n ∈ Ioo 0 1) (hr_lim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => ∫ t in 0..2 * π, k (R * exp (t * I)) • f (r n * R * exp (t * I)))
      atTop (𝓝 (∫ t in 0..2 * π, k (R * exp (t * I)) • f (R * exp (t * I)))) := by
  have hrn (n : ℕ) (t : ℝ) : r n * R * exp (t * I) ∈ closedBall 0 R :=
      ball_subset_closedBall (mem_disc_of_scaled_exp_ofReal_mul_I hR (hr n) t)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
  rotate_right
  -- We define the bound to be the supremum of the integrand.
  · exact fun x => sSup ((fun ζ ↦ |k ζ|) '' sphere 0 R) * sSup ((fun w ↦ ‖f w‖) '' closedBall 0 R)
  -- We verify the measurability of the integrand.
  · apply Eventually.of_forall
    intro n
    apply Continuous.aestronglyMeasurable
    refine Continuous.smul ?_ ?_
    · refine ContinuousOn.comp_continuous (s:= sphere 0 R) hk (by fun_prop) ?_
      · intro x
        simp [norm_exp_ofReal_mul_I, norm_real, norm_eq_abs, abs_of_pos hR]
    · exact ContinuousOn.comp_continuous (s:= closedBall 0 R) hf (by fun_prop) (hrn n)
  -- We verify that the integrand is eventually bounded by the bound.
  · exact Eventually.of_forall fun n => Eventually.of_forall fun t ht =>
             bounds_of_continuousOn_circle_closedDisc hR (hr n) hf hk
  · simp only [ne_eq, enorm_ne_top, not_false_eq_true, intervalIntegrable_const]
  -- We verify the pointwise convergence of the integrand.
  · refine Eventually.of_forall fun x hx => Tendsto.smul tendsto_const_nhds ?_
    apply Tendsto.comp (hf.continuousWithinAt _)
    · rw [tendsto_nhdsWithin_iff]
      constructor
      · simpa [mul_assoc] using Tendsto.mul
          (continuous_ofReal.continuousAt.tendsto.comp hr_lim) tendsto_const_nhds
      · exact Eventually.of_forall (fun n => hrn n x)
    · simp [mem_closedBall, dist_zero_right, norm_exp_ofReal_mul_I, abs_of_pos hR]

/-- The Poisson kernel is continuous on the circle. -/
theorem poisson_ker_continousOn_circle {z : ℂ} {R : ℝ} (hz : z ∈ ball 0 R) :
     ContinuousOn (fun ζ => (R ^ 2 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2) (sphere 0 R) := by
  refine continuousOn_of_forall_continuousAt ?_
  intro ζ hζ
  refine ContinuousAt.div (continuousAt_const) (by fun_prop) ?_
  intro h
  rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h
  rw [h, mem_sphere, dist_zero_right] at hζ
  simp [mem_ball, dist_zero_right, hζ] at hz


/-- If `rₙ` tends to `1`, then `f (rₙ * z)` tends to `f z`, for `z` in a disc centered at `0`,
when `f` is continuous on the closed disc. -/
lemma tendsto_of_radius_tendsto_one_of_continuousOn_closedDisc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} {z : ℂ} {r : ℕ → ℝ} {R : ℝ}
    (hc : ContinuousOn f (closedBall 0 R)) (hr_lim : Tendsto r atTop (𝓝 1))
    (hz : z ∈ ball 0 R) : Tendsto (fun n => f (r n * z)) atTop (𝓝 (f z)) := by
  have h_seq : Tendsto (fun n => r n * z) atTop (𝓝 z) := by
    simpa using Tendsto.mul (continuous_ofReal.continuousAt.tendsto.comp hr_lim)
      (tendsto_const_nhds (x := z))
  specialize hc z (ball_subset_closedBall hz)
  have hc : ContinuousAt f z := ContinuousWithinAt.continuousAt hc (closedBall_mem_nhds_of_mem hz)
  exact (ContinuousAt.tendsto hc).comp h_seq

/-- **Poisson integral formula for harmonic functions on a disc**:
A function `u` harmonic on a disc with radius `R` and center `0`,
and continuous on the closed disc, satisfies
`u(z) = (1/2π) ∫_0^{2π} (R² - |z|²) / |R*e^{it} - z|² u(R*e^{it}) dt` for `z` in the disc. -/
theorem poisson_integral_of_harmonicOn_disc_continuousOn_closedDisc
    {u : ℂ → ℝ} {z : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (ball 0 R)) (hc : ContinuousOn u (closedBall 0 R)) (hz : z ∈ ball 0 R) :
    u z = (1 / (2 * π)) * ∫ t in 0..(2 * π),
      (R ^ 2 - ‖z‖ ^ 2) / ‖R * exp (t * I) - z‖ ^ 2 * u (R * exp (t * I)) := by
  let r : ℕ → ℝ := fun n => 1 - 1 / (n + 2)
  -- We approximate `1` by a sequence `rₙ` in `(0,1)`.
  obtain ⟨hr, hr_lim⟩ := seq_tendsto_to_oneIn_unit_interval_aux
  have h_poisson (n : ℕ) := poisson_integral_of_harmonicOn_scaled_disc hu (hr n) hz
  have hu_lim := tendsto_integral_prod_of_continuousOn_circle_closedDisc (pos_of_mem_ball hz) hc
                 (poisson_ker_continousOn_circle hz) hr hr_lim
  have hu_lim : Tendsto (fun n => (u (r n * z))) atTop (𝓝 ((1 / (2 * π)) * ∫ t in 0..2 * π,
      ((R ^ 2 - ‖z‖^2) / ‖R * exp (t * I) - z‖^2 * u (R * exp (t * I))))) := by
    simp only [r, h_poisson]
    dsimp only [smul_eq_mul] at hu_lim
    exact (Tendsto.const_mul (1 / (2 * π)) hu_lim)
  -- We conclude by uniqueness of limits.
  rw [← tendsto_nhds_unique hu_lim
        (tendsto_of_radius_tendsto_one_of_continuousOn_closedDisc hc hr_lim hz)]

/-- **Poisson integral formula for ℂ-differentiable functions on a disc**:
A function `f : ℂ → E` `ℂ`-differentiable on a disc with radius `R` and center `0`,
and continuous on the closed disc, satisfies
`f(z) = (1/2π) ∫_0^{2π} (R² - |z|²) / |R*e^{it} - z|² f(R*e^{it}) dt` for `z` in the disc. -/
theorem poisson_integral_of_diffContOnCl_disc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ}
    {R : ℝ} (hf : DiffContOnCl ℂ f (ball 0 R)) (hz : z ∈ ball 0 R) :
    f z = (1 / (2 * π)) • ∫ t in 0..(2 * π),
      ((R ^ 2 - ‖z‖ ^ 2) / ‖R * exp (t * I) - z‖ ^ 2) • f (R * exp (t * I)) := by
  let r : ℕ → ℝ := fun n => 1 - 1 / (n + 2)
  obtain ⟨hr, hr_lim⟩ := seq_tendsto_to_oneIn_unit_interval_aux
  have h_poisson (n : ℕ) :=
      poisson_integral_of_differentiableOn_scaled_disc hf.differentiableOn (hr n) hz
  have hc := DiffContOnCl.continuousOn_ball hf
  have hu_lim : Tendsto (fun n => (f (r n * z))) atTop (𝓝 ((1 / (2 * π)) • ∫ t in 0..2 * π,
      ((R ^ 2 - ‖z‖ ^ 2) / ‖R * exp (t * I) - z‖ ^ 2) • f (R * exp (t * I)))) := by
    simp only [r, h_poisson]
    exact (Tendsto.const_smul (tendsto_integral_prod_of_continuousOn_circle_closedDisc
      (pos_of_mem_ball hz) hc (poisson_ker_continousOn_circle hz) hr hr_lim) (1 / (2 * π)))
  rw [← tendsto_nhds_unique (hu_lim)
        (tendsto_of_radius_tendsto_one_of_continuousOn_closedDisc hc hr_lim hz)]

/-- The real part of the Herglotz–Riesz kernel is equal to the Poisson kernel. -/
theorem realPart_herglotz_ker_eq_poisson_ker {R : ℝ} (x w : ℂ) (hx : ‖x‖ = R) :
    ((x + w) / (x - w)).re = (R ^ 2 - ‖w‖ ^ 2) / ‖x - w‖ ^ 2 := by
  rw [div_re, normSq_eq_norm_sq (x - w)]
  calc (x + w).re * (x - w).re / ‖x - w‖ ^ 2 + (x + w).im * (x - w).im / ‖x - w‖ ^ 2
   _ = ((x.re + w.re) * (x.re - w.re) + (x.im + w.im) * (x.im - w.im)) / ‖x - w‖ ^ 2 := by
        simp only [add_re, sub_re, add_im, sub_im, add_div]
   _ = ((x.re * x.re + x.im * x.im) - (w.re * w.re + w.im * w.im)) / ‖x - w‖ ^ 2 := by ring_nf
   _ = ((normSq x) - (normSq w)) / ‖x - w‖ ^ 2 := by simp only [normSq_apply]
   _ = (‖x‖ ^ 2 - ‖w‖ ^ 2) / ‖x - w‖ ^ 2 := by simp only [normSq_eq_norm_sq]
   _ = (R ^ 2 - ‖w‖ ^ 2) / ‖x - w‖ ^ 2 := by rw [hx, pow_two]

/-- **Poisson integral formula for harmonic functions on a disc**:
A function `u : ℂ → ℝ` harmonic on a disc with radius `R` and center `0`, and
continuous on the closed disc, satisfies
`u(z) = (1/2π) ∫_0^{2π} Re((R*e^{it} + z) / (R*e^{it} - z)) * u(R*e^{it}) dt`
for `z` in the disc. -/
theorem poisson_integral_of_harmonicOn_disc_continuousOn_closedDisc_ker_re
    {u : ℂ → ℝ} {z : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (ball 0 R)) (hc : ContinuousOn u (closedBall 0 R)) (hz : z ∈ ball 0 R) :
    u z = (1 / (2 * π)) * ∫ t in 0..(2 * π),
      ((R * exp (t * I) + z) / (R * exp (t * I) - z)).re * u (R * exp (t * I)) := by
  rw [poisson_integral_of_harmonicOn_disc_continuousOn_closedDisc hu hc hz]
  congr 3
  ext t
  congr 1
  exact (realPart_herglotz_ker_eq_poisson_ker
         (R * exp (t * I)) z (by simp [norm_exp_ofReal_mul_I, (pos_of_mem_ball hz).le])).symm

/-- **Poisson integral formula for ℂ-differentiable functions on a disc**:
A function `f : ℂ → E` `ℂ`-differentiable on a disc with radius `R` and center `0`,
and continuous on the closed disc, satisfies
`f(z) = (1/2π) ∫_0^{2π} Re((R*e^{it} + z) / (R*e^{it} - z)) • f(R*e^{it}) dt`
for `z` in the disc. -/
theorem poisson_integral_of_diffContOnCl_disc_ker_re
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z : ℂ}
    {R : ℝ} (hf : DiffContOnCl ℂ f (ball 0 R)) (hz : z ∈ ball 0 R) :
    f z = (1 / (2 * π)) • ∫ t in 0..(2 * π),
      ((R * exp (t * I) + z) / (R * exp (t * I) - z)).re • f (R * exp (t * I)) := by
  rw [poisson_integral_of_diffContOnCl_disc hf hz]
  congr 3
  ext t
  congr 1
  exact (realPart_herglotz_ker_eq_poisson_ker
         (R * exp (t * I)) z (by simp [norm_exp_ofReal_mul_I, (pos_of_mem_ball hz).le])).symm

/-- **Poisson integral formula for harmonic functions on a disc**:
A function `u : ℂ → ℝ` harmonic on a disc with radius `R` and center `0`,
and continuous on the closed disc, satisfies
`u(z) = (1/2π) ∫_0^{2π} Re((R*e^{it} + z) / (R*e^{it} - z)) * u(R*e^{it}) dt`
for `z` in the disc. -/
theorem circleAverage_of_harmonicOn_disc_continuousOn_closedDisc
    {u : ℂ → ℝ} {z : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (ball 0 R)) (hc : ContinuousOn u (closedBall 0 R)) (hz : z ∈ ball 0 R) :
    u z = circleAverage (fun ζ => ((ζ + z) / (ζ - z)).re * u ζ) 0 R := by
  simp [circleAverage, circleMap,
        poisson_integral_of_harmonicOn_disc_continuousOn_closedDisc_ker_re hu hc hz]

/-- **Poisson integral formula for ℂ-differentiable functions on a disc**:
A function `f : ℂ → E` `ℂ`-differentiable on a disc with radius `R` and center `0`,
and continuous on the closed disc, satisfies
`f(z) = (1/2π) ∫_0^{2π} Re((R*e^{it} + z) / (R*e^{it} - z)) • f(R*e^{it}) dt`
for `z` in the disc. -/
theorem circleAverage_of_diffContOnCl_disc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {z : ℂ} {R : ℝ} (hf : DiffContOnCl ℂ f (ball 0 R)) (hz : z ∈ ball 0 R) :
    f z = circleAverage (fun ζ => ((ζ + z) / (ζ - z)).re • f ζ) 0 R := by
  simp [circleAverage, circleMap,
        poisson_integral_of_diffContOnCl_disc_ker_re hf hz]

end LeanPool.LeanComplexAnalysis
