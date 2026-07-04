import Mathlib
import JL.SquaredGaussian

/-!
# Gaussian tail analysis: the centered folded normal is 1-sub-Gaussian

This file builds, from scratch against mathlib, the one-dimensional analytic fact underlying the
unconditional exponential QJL distortion bound: if `Z ~ N(0,1)` then the centered folded normal
`|Z| − √(2/π)` is sub-Gaussian with variance proxy `1`, i.e.

`∀ t, ∫ exp (t · (|Z| − √(2/π))) ≤ exp (t² / 2)`.

The route is:
* `gaussian_foldedMGF`: the folded moment generating function in closed form
  `∫ exp (t·|x|) d(gaussianReal 0 1) = √(2/π) · exp(t²/2) · g t`,
  where `g t = ∫ x in Ioi 0, exp (−(x−t)²/2)`.
* `hasDerivAt_g`: `g` is differentiable with `g' t = exp(−t²/2)` (the parameter sits in the
  integration limit, so this is the fundamental theorem of calculus, no differentiation under the
  integral with respect to a fixed domain is needed for the sign analysis).
* `two_g_le`: the sharp inequality `√(2/π) · g t ≤ exp(t·√(2/π))` for all `t`, proven by a sign
  analysis of `f t = exp(t·√(2/π)) − √(2/π)·g t` (`f 0 = 0`, derivative sign split at `0` and
  `−2√(2/π)`, with the far-negative tail handled by the trivial bound `exp(t·|x|) ≤ 1`).
* `foldedNormal_subgaussian`: assembling the above into `HasSubgaussianMGF (|·| − √(2/π)) 1`.
-/

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal Topology

namespace JL

/-- The "completed-square half-line Gaussian" `g t = ∫ x in Ioi 0, exp(−(x−t)²/2)`. -/
noncomputable def gTail (t : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), rexp (-(x - t) ^ 2 / 2)

/-- `exp (t · |x|)` is integrable against the standard Gaussian (dominated by
`exp (t·x) + exp (−t·x)`). -/
theorem integrable_exp_mul_abs (t : ℝ) :
    Integrable (fun x : ℝ => rexp (t * |x|)) (gaussianReal 0 1) := by
  have hdom : Integrable (fun x : ℝ => rexp (t * x) + rexp (-t * x)) (gaussianReal 0 1) :=
    (integrable_exp_mul_gaussianReal t).add (integrable_exp_mul_gaussianReal (-t))
  refine hdom.mono' ?_ ?_
  · exact (measurable_exp.comp ((measurable_const.mul measurable_id.abs))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    have h1 : (0 : ℝ) ≤ rexp (t * x) := (Real.exp_pos _).le
    have h2 : (0 : ℝ) ≤ rexp (-t * x) := (Real.exp_pos _).le
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]; linarith
    · rw [abs_of_neg hx, show t * -x = -t * x by ring]; linarith

/-- The constant `2·(√(2π))⁻¹ = √(2/π)`. -/
theorem two_mul_inv_sqrt : 2 * (√(2 * π))⁻¹ = √(2 / π) := by
  have h2 : (0 : ℝ) ≤ 2 * (√(2 * π))⁻¹ := by positivity
  calc 2 * (√(2 * π))⁻¹
      = √((2 * (√(2 * π))⁻¹) ^ 2) := (Real.sqrt_sq h2).symm
    _ = √(2 / π) := by
        congr 1
        rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
        field_simp

/-- **Folded-normal moment generating function (closed form).** For `Z ~ N(0,1)`,
`∫ exp(t·|x|) = √(2/π) · exp(t²/2) · g t`, where `g t = ∫ x in Ioi 0, exp(−(x−t)²/2)`. -/
theorem gaussian_foldedMGF (t : ℝ) :
    ∫ x, rexp (t * |x|) ∂(gaussianReal 0 1) = √(2 / π) * rexp (t ^ 2 / 2) * gTail t := by
  have hseteq : ∫ x in Ioi (0 : ℝ), rexp (t * x - x ^ 2 / 2) = rexp (t ^ 2 / 2) * gTail t := by
    rw [gTail, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [← Real.exp_add]
    congr 1
    ring
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  calc ∫ x, gaussianPDFReal 0 1 x • rexp (t * |x|)
      = ∫ x, (fun y : ℝ => (√(2 * π))⁻¹ * rexp (t * y - y ^ 2 / 2)) |x| := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [stdGaussian_pdf, smul_eq_mul]
        have hexp : (-x ^ 2 / 2 : ℝ) + t * |x| = t * |x| - |x| ^ 2 / 2 := by rw [sq_abs]; ring
        rw [mul_assoc, ← Real.exp_add, hexp]
    _ = 2 * ∫ x in Ioi (0 : ℝ), (√(2 * π))⁻¹ * rexp (t * x - x ^ 2 / 2) := by
        rw [integral_comp_abs (f := fun y : ℝ => (√(2 * π))⁻¹ * rexp (t * y - y ^ 2 / 2))]
    _ = √(2 / π) * rexp (t ^ 2 / 2) * gTail t := by
        rw [integral_const_mul, hseteq, ← two_mul_inv_sqrt]
        ring

/-! ## The derivative of `gTail` -/

/-- The half-line Gaussian density `y ↦ exp(−y²/2)` is integrable on `ℝ`. -/
theorem integrable_exp_neg_half_sq : Integrable (fun y : ℝ => rexp (-y ^ 2 / 2)) := by
  have h := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 / 2 by norm_num)
  refine h.congr ?_
  filter_upwards with y
  congr 1; ring

/-- The total Gaussian integral `∫ exp(−y²/2) = √(2π)`. -/
theorem integral_exp_neg_half_sq : ∫ y : ℝ, rexp (-y ^ 2 / 2) = √(2 * π) := by
  have h := integral_gaussian (1 / 2)
  rw [show (π / (1 / 2) : ℝ) = 2 * π by ring] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with y
  congr 1; ring

/-- **Derivative of `gTail`.** `g' t = exp(−t²/2)`. The parameter sits inside the integrand, but a
translation `x ↦ x − t` moves it into the lower integration limit, after which the result follows
from the fundamental theorem of calculus for the lower-tail integral `s ↦ ∫_{Iic s} exp(−y²/2)`. -/
theorem hasDerivAt_gTail (t : ℝ) : HasDerivAt gTail (rexp (-t ^ 2 / 2)) t := by
  have hφcont : Continuous (fun y : ℝ => rexp (-y ^ 2 / 2)) := by fun_prop
  have hφint : Integrable (fun y : ℝ => rexp (-y ^ 2 / 2)) := integrable_exp_neg_half_sq
  -- FTC: `s ↦ ∫_{Iic s} exp(−y²/2)` has derivative `exp(−s²/2)`.
  have hH : ∀ s₀ : ℝ, HasDerivAt (fun s => ∫ y in Iic s, rexp (-y ^ 2 / 2)) (rexp (-s₀ ^ 2 / 2)) s₀ := by
    intro s₀
    have hFTC : HasDerivAt (fun s => ∫ y in (0 : ℝ)..s, rexp (-y ^ 2 / 2)) (rexp (-s₀ ^ 2 / 2)) s₀ :=
      intervalIntegral.integral_hasDerivAt_right (hφcont.intervalIntegrable 0 s₀)
        hφcont.aestronglyMeasurable.stronglyMeasurableAtFilter hφcont.continuousAt
    have heq : (fun s => ∫ y in Iic s, rexp (-y ^ 2 / 2))
        = fun s => (∫ y in Iic (0 : ℝ), rexp (-y ^ 2 / 2)) + ∫ y in (0 : ℝ)..s, rexp (-y ^ 2 / 2) := by
      funext s
      have hsub := intervalIntegral.integral_Iic_sub_Iic (f := fun y : ℝ => rexp (-y ^ 2 / 2))
        (a := (0 : ℝ)) (b := s) (μ := volume) hφint.integrableOn hφint.integrableOn
      linarith [hsub]
    rw [heq]
    exact hFTC.const_add (∫ y in Iic (0 : ℝ), rexp (-y ^ 2 / 2))
  -- `gTail t' = √(2π) − ∫_{Iic (−t')} exp(−y²/2)`.
  have hgEq : ∀ t' : ℝ, gTail t' = √(2 * π) - ∫ y in Iic (-t'), rexp (-y ^ 2 / 2) := by
    intro t'
    have hgsub : gTail t' = ∫ y in Ioi (-t'), rexp (-y ^ 2 / 2) := by
      rw [gTail]
      have hmp : MeasurePreserving (fun x : ℝ => x - t') volume volume :=
        measurePreserving_sub_right volume t'
      have hemb : MeasurableEmbedding (fun x : ℝ => x - t') :=
        (Homeomorph.subRight t').isClosedEmbedding.measurableEmbedding
      have hpre : (fun x : ℝ => x - t') ⁻¹' Ioi (-t') = Ioi (0 : ℝ) := by
        ext x; simp only [Set.mem_preimage, Set.mem_Ioi]; constructor <;> intro h <;> linarith
      have hcv := hmp.setIntegral_preimage_emb hemb (fun y : ℝ => rexp (-y ^ 2 / 2)) (Ioi (-t'))
      rw [hpre] at hcv
      exact hcv
    rw [hgsub]
    have hcompl : ∫ y in Ioi (-t'), rexp (-y ^ 2 / 2)
        = (∫ y, rexp (-y ^ 2 / 2)) - ∫ y in Iic (-t'), rexp (-y ^ 2 / 2) := by
      have h := setIntegral_compl (μ := volume) (s := Iic (-t'))
        (measurableSet_Iic) hφint
      rwa [compl_Iic] at h
    rw [hcompl, integral_exp_neg_half_sq]
  rw [show gTail = (fun t' => √(2 * π) - ∫ y in Iic (-t'), rexp (-y ^ 2 / 2)) from funext hgEq]
  have hinner : HasDerivAt (fun t' : ℝ => -t') (-1) t := (hasDerivAt_id t).neg
  have hcomp := (hH (-t)).comp t hinner
  have hfinal := hcomp.const_sub (√(2 * π))
  have hval : rexp (-t ^ 2 / 2) = -(rexp (-(-t) ^ 2 / 2) * -1) := by
    rw [mul_neg_one, neg_neg]; congr 1; ring
  rw [hval]
  exact hfinal

/-! ## The sharp inequality `√(2/π) · gTail t ≤ exp(t · √(2/π))` -/

/-- The normalising identity `√(2/π) · gTail 0 = 1`. -/
theorem sqrt_two_div_pi_mul_gTail_zero : √(2 / π) * gTail 0 = 1 := by
  have hgTail0 : gTail 0 = √(2 * π) / 2 := by
    have hcomp : ∫ x : ℝ, rexp (-(|x|) ^ 2 / 2) = 2 * ∫ x in Ioi (0 : ℝ), rexp (-x ^ 2 / 2) :=
      integral_comp_abs (f := fun x : ℝ => rexp (-x ^ 2 / 2))
    have habs : (fun x : ℝ => rexp (-(|x|) ^ 2 / 2)) = fun x : ℝ => rexp (-x ^ 2 / 2) := by
      funext x; rw [sq_abs]
    rw [habs, integral_exp_neg_half_sq] at hcomp
    have hcongr : gTail 0 = ∫ x in Ioi (0 : ℝ), rexp (-x ^ 2 / 2) := by
      rw [gTail]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _; simp only [sub_zero]
    rw [hcongr]; linarith [hcomp]
  rw [hgTail0]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [show √(2 / π) * (√(2 * π) / 2) = √(2 / π) * √(2 * π) / 2 by ring,
    ← Real.sqrt_mul (by positivity)]
  rw [show (2 / π) * (2 * π) = 4 by field_simp; ring,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **Sharp folded-normal inequality.** `√(2/π) · gTail t ≤ exp(t · √(2/π))` for all `t`.
This is equivalent to `2·Φ(t) ≤ exp(t·√(2/π))` for the standard normal CDF `Φ`.

The proof studies `f t = exp(t·√(2/π)) − √(2/π)·gTail t`, which has `f 0 = 0` and derivative
`f' t = √(2/π)·(exp(t·√(2/π)) − exp(−t²/2))`. On `[−2√(2/π), ∞)` the sign of `f'` shows `0` is a
minimum (`isMinOn_Ici_of_deriv`), giving `f ≥ 0`; on the far-negative tail `t < −2√(2/π)` the bound
`exp(t·|x|) ≤ 1` yields `√(2/π)·gTail t ≤ exp(−t²/2) ≤ exp(t·√(2/π))`. -/
theorem two_g_le (t : ℝ) : √(2 / π) * gTail t ≤ rexp (t * √(2 / π)) := by
  set c : ℝ := √(2 / π) with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by positivity)
  set f : ℝ → ℝ := fun s => rexp (c * s) - c * gTail s with hf
  have hf' : ∀ s, HasDerivAt f (c * (rexp (c * s) - rexp (-s ^ 2 / 2))) s := by
    intro s
    have h1 : HasDerivAt (fun s => rexp (c * s)) (rexp (c * s) * c) s := by
      simpa using ((hasDerivAt_id s).const_mul c).exp
    have h2 : HasDerivAt (fun s => c * gTail s) (c * rexp (-s ^ 2 / 2)) s :=
      (hasDerivAt_gTail s).const_mul c
    have h3 := h1.sub h2
    have hval : c * (rexp (c * s) - rexp (-s ^ 2 / 2)) = rexp (c * s) * c - c * rexp (-s ^ 2 / 2) := by
      ring
    rw [hval]
    exact h3
  have hderiv_eq : ∀ s, deriv f s = c * (rexp (c * s) - rexp (-s ^ 2 / 2)) :=
    fun s => (hf' s).deriv
  have hf0 : f 0 = 0 := by
    simp only [hf, mul_zero, Real.exp_zero]
    rw [sqrt_two_div_pi_mul_gTail_zero]; ring
  have hdiff : Differentiable ℝ f := fun s => (hf' s).differentiableAt
  -- The goal reduces to `c * gTail t ≤ rexp (t * c)`.
  rcases le_or_gt (-(2 * c)) t with htge | htlt
  · -- `t ≥ −2c`: minimum of `f` at `0`.
    have hmin : IsMinOn f (Ici (-(2 * c))) 0 := by
      refine isMinOn_Ici_of_deriv hdiff.continuous.continuousAt hdiff.continuous.continuousAt
        hdiff.differentiableOn hdiff.differentiableOn ?_ ?_
      · intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        rw [hderiv_eq]
        have hexp : rexp (c * x) ≤ rexp (-x ^ 2 / 2) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_neg_of_neg_of_pos hx2 (show (0 : ℝ) < 2 * c + x by linarith)]
        nlinarith [hcpos.le, hexp]
      · intro x hx
        rw [hderiv_eq]
        have hexp : rexp (-x ^ 2 / 2) ≤ rexp (c * x) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_pos hcpos hx, sq_nonneg x]
        nlinarith [hcpos.le, hexp]
    have hle : f 0 ≤ f t := hmin htge
    have h0 : f t = rexp (c * t) - c * gTail t := rfl
    rw [hf0, h0] at hle
    rw [mul_comm t c]
    linarith [hle]
  · -- `t < −2c`: far-negative tail via the trivial bound `exp(t·|x|) ≤ 1`.
    have htneg : t ≤ 0 := by linarith [hcpos]
    have htriv : ∫ x, rexp (t * |x|) ∂(gaussianReal 0 1) ≤ 1 := by
      have hle : ∀ x : ℝ, rexp (t * |x|) ≤ 1 := by
        intro x
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x, htneg])
      calc ∫ x, rexp (t * |x|) ∂(gaussianReal 0 1)
          ≤ ∫ _x, (1 : ℝ) ∂(gaussianReal 0 1) :=
            integral_mono (integrable_exp_mul_abs t) (integrable_const 1) hle
        _ = 1 := by simp
    rw [gaussian_foldedMGF t, ← hc] at htriv
    have hpos : (0 : ℝ) < rexp (t ^ 2 / 2) := Real.exp_pos _
    have hstep : c * gTail t ≤ rexp (-t ^ 2 / 2) := by
      have hneg : rexp (-t ^ 2 / 2) = (rexp (t ^ 2 / 2))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [hneg, ← one_div, le_div_iff₀ hpos]
      have heqp : c * gTail t * rexp (t ^ 2 / 2) = c * rexp (t ^ 2 / 2) * gTail t := by ring
      rw [heqp]; exact htriv
    have hfin : rexp (-t ^ 2 / 2) ≤ rexp (t * c) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_pos_of_neg_of_neg (show t < 0 by linarith) (show c + t / 2 < 0 by linarith)]
    exact le_trans hstep hfin

/-! ## The centered folded normal is `1`-sub-Gaussian -/

/-- **The centered folded normal is `1`-sub-Gaussian.** For `Z ~ N(0,1)`, the centered absolute
value `|Z| − √(2/π)` has a sub-Gaussian moment generating function with variance proxy `1`:
`∫ exp(t·(|Z| − √(2/π))) ≤ exp(t²/2)` for all `t`. -/
theorem foldedNormal_subgaussian :
    HasSubgaussianMGF (fun z : ℝ => |z| - √(2 / π)) ⟨1, by norm_num⟩ (gaussianReal 0 1) where
  integrable_exp_mul t := by
    have h := (integrable_exp_mul_abs t).const_mul (rexp (-(t * √(2 / π))))
    refine h.congr ?_
    filter_upwards with z
    rw [← Real.exp_add]; congr 1; ring
  mgf_le t := by
    rw [mgf]
    have hrw : ∫ z, rexp (t * (|z| - √(2 / π))) ∂(gaussianReal 0 1)
        = rexp (-(t * √(2 / π))) * (√(2 / π) * rexp (t ^ 2 / 2) * gTail t) := by
      rw [← gaussian_foldedMGF t, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      rw [← Real.exp_add]; congr 1; ring
    rw [hrw]
    show rexp (-(t * √(2 / π))) * (√(2 / π) * rexp (t ^ 2 / 2) * gTail t) ≤ rexp (1 * t ^ 2 / 2)
    rw [one_mul]
    have hg := two_g_le t
    calc rexp (-(t * √(2 / π))) * (√(2 / π) * rexp (t ^ 2 / 2) * gTail t)
        = rexp (t ^ 2 / 2) * (rexp (-(t * √(2 / π))) * (√(2 / π) * gTail t)) := by ring
      _ ≤ rexp (t ^ 2 / 2) * (rexp (-(t * √(2 / π))) * rexp (t * √(2 / π))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
      _ = rexp (t ^ 2 / 2) := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end JL
