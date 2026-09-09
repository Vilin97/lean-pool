/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# An actual holomorphic primitive on a convex open set

The primitive is the radial segment integral. Its derivative is proved by
differentiating under a uniformly dominated integral on a compact local product,
then applying the real fundamental theorem of calculus along the segment.
No disk containing the entire domain and no assumed primitive are required.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AnalyticPrimitive

open Set Filter MeasureTheory Metric
open scoped Topology Interval ContDiff

/-- Integration along the straight segment from zero to `z`. -/
def primitive (g : ℂ → ℂ) (z : ℂ) : ℂ := z * ∫ t in (0 : ℝ)..1, g ((t : ℂ) * z)

@[simp] theorem primitive_zero (g : ℂ → ℂ) : primitive g 0 = 0 := by
  simp [primitive]

theorem primitive_eq_integral (g : ℂ → ℂ) (z : ℂ) :
    primitive g z = ∫ t in (0 : ℝ)..1, z * g ((t : ℂ) * z) := by
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem segment_mem {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) * z ∈ U := by
  simpa only [Complex.real_smul] using hU.smul_mem_of_zero_mem h0 hz ht

theorem continuousOn_segment {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {g : ℂ → ℂ} (hg : ContinuousOn g U) {z : ℂ} (hz : z ∈ U) :
    ContinuousOn (fun t : ℝ => g ((t : ℂ) * z)) (Icc (0 : ℝ) 1) := by
  exact hg.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
    (fun _ ht => segment_mem hU h0 hz ht)

/-- The complex derivative of the parameter-dependent integrand. -/
def integrandDerivative (g : ℂ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  g ((t : ℂ) * z) + ((t : ℂ) * z) * deriv g ((t : ℂ) * z)

theorem integrand_hasDerivAt {U : Set ℂ} (ho : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} {t : ℝ} (htz : (t : ℂ) * z ∈ U) :
    HasDerivAt (fun w : ℂ => w * g ((t : ℂ) * w)) (integrandDerivative g z t) z := by
  have hgd := (hg _ htz).differentiableAt (ho.mem_nhds htz)
  convert! (hasDerivAt_id z).mul (hgd.hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul (t : ℂ))) using 1
  simp only [integrandDerivative, Function.comp_apply, id_eq, mul_one, one_mul]
  ring

theorem integrandDerivative_continuousOn_segment {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    ContinuousOn (integrandDerivative g z) (Icc (0 : ℝ) 1) := by
  exact (continuousOn_segment hU h0 hg.continuousOn hz).add
    ((Complex.continuous_ofReal.mul continuous_const).continuousOn.mul
      (continuousOn_segment hU h0 (hg.deriv ho).continuousOn hz))

/-- The same derivative integrand is the real derivative of `t*g(t*z)`. -/
theorem segment_product_hasDerivAt {U : Set ℂ} (ho : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} {t : ℝ} (htz : (t : ℂ) * z ∈ U) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * g ((s : ℂ) * z))
      (integrandDerivative g z t) t := by
  have ht : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    exact Complex.ofRealCLM.hasDerivAt (x := t)
  have hgd := (hg _ htz).differentiableAt (ho.mem_nhds htz)
  convert! ht.mul (hgd.hasDerivAt.comp t (ht.mul_const z)) using 1
  simp only [integrandDerivative, Function.comp_apply, one_mul]
  ring

theorem integral_integrandDerivative {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    (∫ t in (0 : ℝ)..1, integrandDerivative g z t) = g z := by
  have hint : IntervalIntegrable (integrandDerivative g z) volume 0 1 :=
    (integrandDerivative_continuousOn_segment ho hU h0 hg hz).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => (s : ℂ) * g ((s : ℂ) * z))
    (f' := integrandDerivative g z) (a := 0) (b := 1)
    (fun t ht => segment_product_hasDerivAt ho hg
      (segment_mem hU h0 hz (by simpa only [uIcc_of_le zero_le_one] using ht))) hint
  simpa using he

/-- An actual holomorphic primitive on any convex open neighborhood of zero. -/
theorem hasDerivAt_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (primitive g) (g z) z := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds hz)
  let K : Set (ℂ × ℝ) := closedBall z r ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall z r).prod isCompact_Icc
  have hm : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) :=
    (Complex.continuous_ofReal.comp continuous_snd).mul continuous_fst
  have hmU : MapsTo (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) K U := by
    intro p hp
    exact segment_mem hU h0 (hrU hp.1) hp.2
  have hcont : ContinuousOn (fun p : ℂ × ℝ => integrandDerivative g p.1 p.2) K := by
    exact (hg.continuousOn.comp hm.continuousOn hmU).add
      (hm.continuousOn.mul ((hg.deriv ho).continuousOn.comp hm.continuousOn hmU))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hFint : ∀ w ∈ U, IntervalIntegrable (fun t : ℝ => w * g ((t : ℂ) * w))
      volume 0 1 := by
    intro w hw
    exact (continuousOn_const.mul
      (continuousOn_segment hU h0 hg.continuousOn hw)).intervalIntegrable_of_Icc (by norm_num)
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => w * g ((t : ℂ) * w)) (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    simpa only [uIoc_of_le zero_le_one] using
      (hFint w (hrU (ball_subset_closedBall hw))).aestronglyMeasurable
  have hDint : IntervalIntegrable (integrandDerivative g z) volume 0 1 :=
    (integrandDerivative_continuousOn_segment ho hU h0 hg hz).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have hDmeas : AEStronglyMeasurable (integrandDerivative g z)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    simpa only [uIoc_of_le zero_le_one] using hDint.aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball z r,
      ‖integrandDerivative g w t‖ ≤ C := by
    filter_upwards [] with t
    intro ht w hw
    apply hC (w, t)
    exact ⟨ball_subset_closedBall hw,
      by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht⟩
  have hdiff : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball z r,
      HasDerivAt (fun v : ℂ => v * g ((t : ℂ) * v)) (integrandDerivative g w t) w := by
    filter_upwards [] with t
    intro ht w hw
    exact integrand_hasDerivAt ho hg (segment_mem hU h0
      (hrU (ball_subset_closedBall hw))
      (by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht))
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w t => w * g ((t : ℂ) * w)) (F' := integrandDerivative g)
    (bound := fun _ => C) (Metric.ball_mem_nhds _ hr) hFmeas (hFint z hz) hDmeas hbound
    intervalIntegrable_const hdiff).2
  rw [integral_integrandDerivative ho hU h0 hg hz] at hd
  simpa only [← primitive_eq_integral] using hd

theorem differentiableOn_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : DifferentiableOn ℂ (primitive g) U := by
  intro z hz
  exact (hasDerivAt_primitive ho hU h0 hg hz).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : AnalyticOnNhd ℂ (primitive g) U :=
  (differentiableOn_primitive ho hU h0 hg).analyticOnNhd ho

/-- Reality is local to the real points of the given convex domain. -/
theorem primitive_im_eq_zero {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {g : ℂ → ℂ} (hreal : ∀ x : ℝ, (x : ℂ) ∈ U → (g x).im = 0)
    {x : ℝ} (hx : (x : ℂ) ∈ U) : (primitive g x).im = 0 := by
  have heq : (∫ t in (0 : ℝ)..1, g ((t : ℂ) * (x : ℂ))) =
      ∫ t in (0 : ℝ)..1, ((g ((t : ℂ) * (x : ℂ))).re : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htx := segment_mem hU h0 hx
      (show t ∈ Icc (0 : ℝ) 1 by simpa only [uIcc_of_le zero_le_one] using ht)
    have him : (g ((t : ℂ) * (x : ℂ))).im = 0 := by
      simpa only [Complex.ofReal_mul] using hreal (t * x)
        (by simpa only [Complex.ofReal_mul] using htx)
    apply Complex.ext
    · simp
    · simpa using him
  rw [primitive, heq, intervalIntegral.integral_ofReal]
  simp

/-- If the integrand extends a real function, its segment primitive extends
the corresponding real segment integral exactly. -/
theorem primitive_ofReal (g : ℂ → ℂ) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (x : ℝ) :
    primitive g x = ((x * ∫ t in (0 : ℝ)..1, f (t * x) : ℝ) : ℂ) := by
  have heq : (fun t : ℝ => g ((t : ℂ) * (x : ℂ))) =
      fun t : ℝ => (f (t * x) : ℂ) := by
    funext t
    rw [← Complex.ofReal_mul, hreal]
  rw [primitive, heq, intervalIntegral.integral_ofReal, Complex.ofReal_mul]

theorem hasDerivAt_real_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    HasDerivAt (fun y : ℝ => (primitive g y).re) (g x).re x :=
  (hasDerivAt_primitive ho hU h0 hg hx).real_of_complex

/-- The normalized exponential built from the actual segment primitive. -/
def amplitude (g : ℂ → ℂ) (Λ C : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (Λ * primitive g z) / C

@[simp] theorem amplitude_zero (g : ℂ → ℂ) (Λ C : ℂ) : amplitude g Λ C 0 = 1 / C := by
  simp [amplitude]

theorem amplitude_ne_zero (g : ℂ → ℂ) (Λ : ℂ) {C : ℂ} (hC : C ≠ 0) (z : ℂ) :
    amplitude g Λ C z ≠ 0 :=
  div_ne_zero (Complex.exp_ne_zero _) hC

/-- Normalization is constant in the spatial variable, so the differential
equation is valid for any normalization scalar. -/
theorem hasDerivAt_amplitude {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (Λ C : ℂ) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (amplitude g Λ C) ((Λ * g z) * amplitude g Λ C z) z := by
  have hd := (((hasDerivAt_primitive ho hU h0 hg hz).const_mul Λ).cexp).div_const C
  convert! hd using 1
  unfold amplitude
  ring

theorem analyticOnNhd_amplitude {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (Λ C : ℂ) : AnalyticOnNhd ℂ (amplitude g Λ C) U := by
  apply DifferentiableOn.analyticOnNhd _ ho
  intro z hz
  exact (hasDerivAt_amplitude ho hU h0 hg Λ C hz).differentiableAt.differentiableWithinAt

/-- The actual logarithmic derivative of the nonvanishing normalized
exponential is the prescribed scaled holomorphic gradient. -/
theorem amplitude_log_derivative {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (Λ : ℂ) {C : ℂ} (hC : C ≠ 0)
    {z : ℂ} (hz : z ∈ U) :
    deriv (amplitude g Λ C) z / amplitude g Λ C z = Λ * g z := by
  rw [(hasDerivAt_amplitude ho hU h0 hg Λ C hz).deriv]
  exact mul_div_cancel_right₀ _ (amplitude_ne_zero g Λ hC z)

theorem amplitude_ofReal (g : ℂ → ℂ) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (Λ C x : ℝ) :
    amplitude g Λ C x =
      ((Real.exp (Λ * (x * ∫ t in (0 : ℝ)..1, f (t * x))) / C : ℝ) : ℂ) := by
  rw [amplitude, primitive_ofReal g f hreal x, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, ← Complex.ofReal_div]

theorem amplitude_real_pos (g : ℂ → ℂ) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (Λ : ℝ) {C : ℝ} (hC : 0 < C) (x : ℝ) :
    0 < (amplitude g Λ C x).re := by
  rw [amplitude_ofReal g f hreal Λ C x, Complex.ofReal_re]
  exact div_pos (Real.exp_pos _) hC

theorem hasDerivAt_real_amplitude {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (Λ C : ℝ) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    HasDerivAt (fun y : ℝ => (amplitude g Λ C y).re)
      ((Λ * f x) * (amplitude g Λ C x).re) x := by
  have hd := (hasDerivAt_amplitude ho hU h0 hg Λ C hx).real_of_complex
  simpa only [hreal, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero] using hd

theorem real_amplitude_log_derivative {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (Λ : ℝ) {C : ℝ} (hC : 0 < C)
    {x : ℝ} (hx : (x : ℂ) ∈ U) :
    deriv (fun y : ℝ => (amplitude g Λ C y).re) x / (amplitude g Λ C x).re = Λ * f x := by
  rw [(hasDerivAt_real_amplitude ho hU h0 hg f hreal Λ C hx).deriv]
  exact mul_div_cancel_right₀ _ (ne_of_gt (amplitude_real_pos g f hreal Λ hC x))

end NavierStokes.AnalyticPrimitive

end
