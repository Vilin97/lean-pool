/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.IntegrableExpMul

-- Import our basic definitions
import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.Euclidean
import LeanPool.OSforGFF.General.FunctionalAnalysis
import LeanPool.OSforGFF.General.BesselFunction

/-!
# Momentum Space Propagator for Gaussian Free Field

This file implements the momentum space free propagator 1/(‖k‖²+m²) and its properties.
This is the foundation for the free covariance function in position space, which is computed
via Fourier transform.

## Main Definitions

- `freePropagatorMomentum`: Momentum space propagator 1/(‖k‖²+m²)
- `freeCovariance`: Position space covariance via Fourier transform
- `freeCovarianceKernel`: Alternative name for compatibility
- `propagatorMultiplication`: Linear operator for multiplication by propagator

## Key Results

- `freePropagator_even`: Propagator is an even function
- `freeCovariance_symmetric`: Covariance is symmetric C(x,y) = C(y,x)
- `freePropagator_smooth`, `freePropagator_complex_smooth`: Smoothness results
- `freePropagator_pos`, `freePropagator_bounded`: Propagator is positive and bounded
-/

open MeasureTheory Complex Real Filter
open TopologicalSpace
open scoped Real InnerProductSpace BigOperators

/-! No axioms declared in this file. -/

noncomputable section
/-! ### Small helper lemmas for integration and complex algebra -/


/-- Helper theorem: integral of a real-valued function, coerced to ℂ, equals `ofReal`
of the real integral. -/
theorem integral_ofReal_eq {α} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ)
  (_hf : Integrable h μ) :
  ∫ x, (h x : ℂ) ∂μ = Complex.ofReal (∫ x, h x ∂μ) :=
  integral_complex_ofReal


/-- Helper lemma: Schwartz functions are L²-integrable. -/
lemma schwartz_L2_integrable (f : TestFunctionℂ) :
  Integrable (fun k => ‖f k‖^2) volume := by
  -- Using Mathlib's `SchwartzMap.memLp` we know any Schwartz function lies in every `L^p` space.
  have hf_memLp : MemLp f 2 volume :=
    f.memLp 2 volume
  have hf_meas : AEStronglyMeasurable f volume := hf_memLp.1
  -- Translate the `L^2` membership into integrability of the squared norm.
  simpa using (memLp_two_iff_integrable_sq_norm hf_meas).1 hf_memLp

/-- Helper theorem: Integrability is preserved by multiplying a real integrand with a real
constant. -/
theorem integral_const_mul {α} [MeasurableSpace α] (μ : Measure α) (c : ℝ)
  (f : α → ℝ) (hf : Integrable f μ) :
  Integrable (fun x => c * f x) μ :=
  MeasureTheory.Integrable.const_mul hf c

/-- Helper theorem: Integral of a real constant multiple pulls out of the integral. -/
theorem integral_const_mul_eq {α} [MeasurableSpace α] (μ : Measure α) (c : ℝ)
  (f : α → ℝ) (_hf : Integrable f μ) :
  ∫ x, c * f x ∂ μ = c * ∫ x, f x ∂ μ :=
  MeasureTheory.integral_const_mul c f

/-- Helper theorem: Monotonicity of the real integral for pointwise ≤ between nonnegative functions,
    assuming the larger one is integrable.
-/
theorem real_integral_mono_of_le
  {α} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
  (hg : Integrable g μ) (hf_nonneg : ∀ x, 0 ≤ f x) (hle : ∀ x, f x ≤ g x) :
  ∫ x, f x ∂ μ ≤ ∫ x, g x ∂ μ :=
  MeasureTheory.integral_mono_of_nonneg (ae_of_all _ hf_nonneg) hg (ae_of_all _ hle)

/-! ## Free Covariance in Euclidean QFT

The free covariance is the fundamental two-point correlation function for the Gaussian Free Field.
In Euclidean spacetime, it is given by the Fourier transform:

C(x,y) = ∫ (d^d k)/(2π)^d * 1/(k² + m²) * exp(-i k·(x-y))

where:
- m > 0 is the mass parameter
- k² = k·k is the Euclidean norm squared (using inner product ⟨k,k⟩)
- d is the spacetime dimension

This defines a positive definite bilinear form, which is essential for reflection positivity.

Key point: In Lean, we can use ⟨x, y⟩ for the inner product and ‖x‖ for the norm.
-/

variable {m : ℝ} [Fact (0 < m)]

/-- The free propagator in momentum space: 1/(k² + m²)
    This is the Fourier transform of the free covariance
-/
def freePropagatorMomentum (m : ℝ) (k : SpaceTime) : ℝ :=
  1 / (‖k‖^2 + m^2)

/-- The free propagator is an even function: it depends only on ‖k‖. -/
lemma freePropagator_even (m : ℝ) (k : SpaceTime) :
    freePropagatorMomentum m (-k) = freePropagatorMomentum m k := by
  simp [freePropagatorMomentum]

/-- The propagator in "Mathlib momentum coordinates".
    When using Mathlib's Fourier transform convention, the propagator acquires (2π)² factors.
    This is `P_mathlib(k) = 1/((2π)²‖k‖² + m²)` which equals `P_phys(2πk)`.
-/
noncomputable def freePropagatorMomentumMathlib (m : ℝ) (k : SpaceTime) : ℝ :=
  1 / ((2 * Real.pi)^2 * ‖k‖^2 + m^2)

/-- The Mathlib propagator is positive for m > 0. -/
lemma freePropagatorMomentum_mathlib_pos (m : ℝ) (hm : 0 < m) (k : SpaceTime) :
    0 < freePropagatorMomentumMathlib m k := by
  have h2 : 0 < m^2 := sq_pos_of_pos hm
  unfold freePropagatorMomentumMathlib
  positivity

/-- The Mathlib propagator is non-negative. -/
lemma freePropagatorMomentum_mathlib_nonneg (m : ℝ) (hm : 0 < m) (k : SpaceTime) :
    0 ≤ freePropagatorMomentumMathlib m k :=
  le_of_lt (freePropagatorMomentum_mathlib_pos m hm k)

/-- The regulated free covariance kernel in position space.
    This is the Fourier transform of the momentum space propagator with Gaussian regulator:

    C_α(x,y) = ∫ \frac{d^d k}{(2π)^d}\; \frac{e^{-α‖k‖²} e^{-i k·(x-y)}}{‖k‖² + m²}.

    The regulator exp(-α‖k‖²) with α > 0 makes the integral absolutely convergent.
    In the limit α → 0⁺, this recovers the (conditionally convergent) Fourier integral
    which equals the Bessel form.

    We realise this as the real part of a complex Fourier integral with the
    standard 2π-normalisation.
-/
noncomputable def freeCovarianceRegulated (α : ℝ) (m : ℝ) (x y : SpaceTime) : ℝ :=
  let normalisation : ℝ := (2 * Real.pi) ^ STDimension
  let regulator : SpaceTime → ℝ := fun k => Real.exp (-α * ‖k‖^2)
  let phase : SpaceTime → ℂ := fun k =>
    Complex.exp (-Complex.I * Complex.ofReal (⟪k, x - y⟫_ℝ))
  let amplitude : SpaceTime → ℂ := fun k =>
    Complex.ofReal (regulator k * freePropagatorMomentum m k / normalisation)
  (∫ k : SpaceTime, amplitude k * phase k).re

/-! ### Schwinger Representation of the Propagator

The Schwinger (or proper-time) representation expresses the massive propagator as:

  1/(k² + m²) = ∫₀^∞ exp(-t(k² + m²)) dt

This integral is absolutely convergent for k² + m² > 0. The key insight is that
this converts the Fourier transform of the propagator into a Gaussian integral,
which can be computed explicitly using Mathlib's `fourierIntegral_gaussian_innerProductSpace`.

After applying the Gaussian Fourier transform, we get:

  ∫ dk e^{-ik·r} / (k² + m²) = ∫₀^∞ e^{-tm²} · (π/t)^{d/2} · e^{-r²/(4t)} dt / (2π)^d

In 4D (d=4), this simplifies to:

  C(r) = (1/(16π²)) ∫₀^∞ e^{-tm²} · (1/t²) · e^{-r²/(4t)} dt

The remaining 1D integral can be computed via the substitution u = m²t + r²/(4t),
which leads to the Bessel K₁ function.
-/

/-- The Schwinger integrand: exp(-t(k² + m²)) for t > 0.
    Integrating this over t ∈ (0, ∞) gives 1/(k² + m²).
-/
noncomputable def schwingerIntegrand (t : ℝ) (m : ℝ) (k : SpaceTime) : ℝ :=
  Real.exp (-t * (‖k‖^2 + m^2))


/-- Integral of exp(-a*t) over (0, ∞) equals 1/a for a > 0.
    This is the Laplace transform of 1 at parameter a.
    Proof: Change of variables u = at gives (1/a) ∫₀^∞ e^{-u} du = 1/a.
-/
lemma integral_exp_neg_mul_Ioi_eq_inv (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Ioi 0, Real.exp (-a * t) = 1 / a := by
  -- Use integral_exp_mul_Ioi with -a < 0 and c = 0
  have hna : -a < 0 := neg_neg_of_pos ha
  have h := integral_exp_mul_Ioi hna 0
  simp only [mul_zero, Real.exp_zero] at h
  -- h : ∫ x in Set.Ioi 0, rexp (-a * x) = -1 / -a = 1 / a
  rw [h]
  field_simp

/-- The Schwinger representation: ∫₀^∞ exp(-t(k² + m²)) dt = 1/(k² + m²).
    This is valid when k² + m² > 0.
-/
theorem schwinger_representation (m : ℝ) (hm : 0 < m) (k : SpaceTime) :
    ∫ t in Set.Ioi 0, schwingerIntegrand t m k = 1 / (‖k‖^2 + m^2) := by
  unfold schwingerIntegrand
  simp_rw [show ∀ t : ℝ, -t * (‖k‖^2 + m^2) = -(‖k‖^2 + m^2) * t from fun t => by ring]
  exact integral_exp_neg_mul_Ioi_eq_inv (‖k‖^2 + m^2) (by positivity)

/-- The combined Gaussian factor for the Schwinger-regulated integral.
    This combines the propagator Schwinger factor with the UV regulator.
-/
noncomputable def schwingerGaussian (α t : ℝ) (m : ℝ) (k : SpaceTime) : ℝ :=
  Real.exp (-(α + t) * ‖k‖^2 - t * m^2)

/-- The heat kernel in d dimensions for position space: (4πt)^{-d/2} · exp(-r²/(4t)).
    This is the Fourier transform of the Gaussian exp(-t·k²).
    Named with PositionSpace suffix to distinguish from momentum-space version.
-/
noncomputable def heatKernelPositionSpace (t : ℝ) (r : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(STDimension : ℝ) / 2) * Real.exp (-r^2 / (4 * t))

/-- For d = 4, the heat kernel simplifies to 1/(16π²t²) · exp(-r²/(4t)). -/
lemma heatKernelPositionSpace_4D (t : ℝ) (ht : 0 < t) (r : ℝ) :
    heatKernelPositionSpace t r = 1 / (16 * Real.pi^2 * t^2) * Real.exp (-r^2 / (4 * t)) := by
  unfold heatKernelPositionSpace
  have hd : (STDimension : ℝ) = 4 := by simp [STDimension]
  rw [hd]
  -- (4πt)^{-2} = 1/(16π²t²)
  have hpos : 0 < 4 * Real.pi * t := by positivity
  have h1 : (4 * Real.pi * t) ^ (-(4 : ℝ) / 2) = 1 / (16 * Real.pi^2 * t^2) := by
    rw [show -(4 : ℝ) / 2 = -2 by norm_num, Real.rpow_neg hpos.le, Real.rpow_two]
    field_simp
    ring
  rw [h1]

/-- The heat kernel is nonnegative. -/
lemma heatKernelPositionSpace_nonneg (t : ℝ) (ht : 0 < t) (r : ℝ) :
    0 ≤ heatKernelPositionSpace t r := by
  unfold heatKernelPositionSpace
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)


/-- The heat kernel is continuous in t for t > 0. -/
lemma heatKernelPositionSpace_continuous_at (t : ℝ) (ht : 0 < t) (r : ℝ) :
    ContinuousAt (fun s => heatKernelPositionSpace s r) t := by
  unfold heatKernelPositionSpace
  refine ContinuousAt.mul (ContinuousAt.rpow ?_ continuousAt_const (Or.inl (by positivity)))
    (Real.continuous_exp.continuousAt.comp (ContinuousAt.div continuousAt_const ?_ ?_))
  · exact continuousAt_const.mul continuousAt_id
  · exact continuousAt_const.mul continuousAt_id
  · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]; exact ht.ne'

/-- The heat kernel is bounded by a constant depending only on r > 0.
    Maximum of H(s,r) = (4πs)^{-d/2} exp(-r²/(4s)) occurs at s = r²/(2d).
-/
lemma heatKernelPositionSpace_bounded (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ s > 0, heatKernelPositionSpace s r ≤ C := by
  -- Use the bound: H(s,r) ≤ 4/(π²r⁴) derived from u² * exp(-cu) ≤ (2/c)²
  use 4 / (Real.pi^2 * r^4) + 1
  constructor
  · positivity
  · intro s hs
    -- The heat kernel is H(s,r) = (4πs)^{-2} * exp(-r²/(4s)) for d=4
    -- Substituting u = 1/s: H = u²/(16π²) * exp(-r²u/4)
    -- The key bound: u² * exp(-cu) ≤ (2/c)² from rpow_abs_le_mul_exp_abs
    -- For c = r²/4: u² * exp(-r²u/4) ≤ (8/r²)² = 64/r⁴
    -- Thus H ≤ 64/(16π²r⁴) = 4/(π²r⁴) < C
    have hst_dim : (STDimension : ℝ) = 4 := by simp [STDimension]
    unfold heatKernelPositionSpace
    rw [hst_dim]
    -- Set u = 1/s
    set u := s⁻¹ with hu_def
    have hu_pos : 0 < u := by simp [hu_def, hs]
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    have hs_eq : s = u⁻¹ := by simp [hu_def]
    -- Rewrite the heat kernel: (4πs)^{-2} * exp(-r²/(4s)) = (16π²)⁻¹ * u² * exp(-r²u/4)
    have h_kernel_eq : (4 * Real.pi * s) ^ (-(4 : ℝ) / 2) * Real.exp (-r^2 / (4 * s)) =
        (16 * Real.pi^2)⁻¹ * u^2 * Real.exp (-(r^2 / 4) * u) := by
      have hs_pos : 0 < s := hs
      have h_4pis_pos : 0 < 4 * Real.pi * s := by positivity
      -- Simplify the power: -4/2 = -2
      have h1 : (-(4 : ℝ) / 2) = -2 := by norm_num
      rw [h1]
      -- (4πs)^(-2) = 1/(4πs)² = 1/(16π²s²) = u²/(16π²)
      rw [Real.rpow_neg (le_of_lt h_4pis_pos), Real.rpow_two]
      have h2 : (4 * Real.pi * s)^2 = 16 * Real.pi^2 * s^2 := by ring
      rw [h2]
      -- s = u⁻¹, so s² = u⁻², and 1/(16π²s²) = u²/(16π²)
      have h3 : (16 * Real.pi^2 * s^2)⁻¹ = (16 * Real.pi^2)⁻¹ * u^2 := by
        rw [hs_eq]; field_simp
      rw [h3]
      -- Now simplify the exponential: -r²/(4s) = -r²u/4
      have h4 : -r^2 / (4 * s) = -(r^2 / 4) * u := by
        rw [hs_eq]; field_simp
      rw [h4]
    rw [h_kernel_eq]
    -- Apply the bound u² * exp(-cu) ≤ (2/c)² where c = r²/4
    have hc : r^2 / 4 > 0 := by positivity
    have hc_ne : r^2 / 4 ≠ 0 := ne_of_gt hc
    -- Use the lemma: |x|^p ≤ (p/|t|)^p * exp(|t| * |x|)
    have h_abs_u : |u| = u := abs_of_pos hu_pos
    have h_abs_c : |r^2 / 4| = r^2 / 4 := abs_of_pos hc
    have h_bound := ProbabilityTheory.rpow_abs_le_mul_exp_abs u (p := 2) (by norm_num : (0 : ℝ) ≤
      2) hc_ne
    rw [h_abs_u, h_abs_c] at h_bound
    -- h_bound: u^2 ≤ (2/(r²/4))² * exp((r²/4) * u)
    have h_div : u^2 * Real.exp (-(r^2 / 4) * u) ≤ (2 / (r^2 / 4))^2 := by
      have h_exp_pos : Real.exp ((r^2 / 4) * u) > 0 := Real.exp_pos _
      have h_exp_nonneg : 0 ≤ Real.exp ((r^2 / 4) * u) := le_of_lt h_exp_pos
      have := div_le_div_of_nonneg_right h_bound h_exp_nonneg
      simp only [mul_div_assoc] at this
      have h_cancel : Real.exp ((r^2 / 4) * u) / Real.exp ((r^2 / 4) * u) = 1 := by
        exact div_self (ne_of_gt h_exp_pos)
      rw [h_cancel] at this
      simp only [mul_one] at this
      have h_rpow_sq : u ^ (2 : ℝ) = u^2 := Real.rpow_natCast u 2
      have h_rpow_sq' : (2 / (r^2 / 4)) ^ (2 : ℝ) = (2 / (r^2 / 4))^2 := Real.rpow_natCast _ 2
      rw [h_rpow_sq, h_rpow_sq'] at this
      have h_neg_eq : -(r^2 / 4) * u = -((r^2 / 4) * u) := by ring
      calc u^2 * Real.exp (-(r^2 / 4) * u)
          = u^2 * Real.exp (-((r^2 / 4) * u)) := by rw [h_neg_eq]
        _ = u^2 * (Real.exp ((r^2 / 4) * u))⁻¹ := by rw [Real.exp_neg]
        _ = u^2 / Real.exp ((r^2 / 4) * u) := by rw [← div_eq_mul_inv]
        _ ≤ (2 / (r^2 / 4))^2 := this
    -- Simplify (2/(r²/4))² = (8/r²)² = 64/r⁴
    have h_simp : (2 / (r^2 / 4))^2 = 64 / r^4 := by field_simp; ring
    rw [h_simp] at h_div
    -- Now combine: H = (16π²)⁻¹ * u² * exp(-cu) ≤ (16π²)⁻¹ * 64/r⁴ = 4/(π²r⁴)
    calc (16 * Real.pi^2)⁻¹ * u^2 * Real.exp (-(r^2 / 4) * u)
        = (16 * Real.pi^2)⁻¹ * (u^2 * Real.exp (-(r^2 / 4) * u)) := by ring
      _ ≤ (16 * Real.pi^2)⁻¹ * (64 / r^4) := by
          apply mul_le_mul_of_nonneg_left h_div; positivity
      _ = 4 / (Real.pi^2 * r^4) := by field_simp; ring
      _ ≤ 4 / (Real.pi^2 * r^4) + 1 := by linarith

/-- **Heat kernel L¹ normalization**: The heat kernel integrates to 1 over all space.
    ∫ H(t, ‖z‖) dz = 1 for all t > 0.

    This is a fundamental property of the heat kernel as the Green's function
    for the heat equation with conservation of total probability/mass.

    **Proof:** Uses `integral_rexp_neg_mul_sq_norm` from Mathlib:
    ∫ exp(-b‖v‖²) dv = (π/b)^{d/2}

    With b = 1/(4t) and d = 4:
    ∫ (4πt)^{-2} exp(-‖z‖²/(4t)) dz = (4πt)^{-2} × (4πt)² = 1
-/
theorem heatKernelPositionSpace_integral_eq_one (t : ℝ) (ht : 0 < t) :
    ∫ z : SpaceTime, heatKernelPositionSpace t ‖z‖ = 1 := by
  unfold heatKernelPositionSpace
  -- The integral is (4πt)^{-d/2} × ∫ exp(-‖z‖²/(4t)) dz
  -- Using integral_rexp_neg_mul_sq_norm with b = 1/(4t):
  -- ∫ exp(-b‖z‖²) dz = (π/b)^{d/2} = (4πt)^{d/2}
  -- So the product is (4πt)^{-d/2} × (4πt)^{d/2} = 1
  have hd_real : (STDimension : ℝ) = 4 := by simp [STDimension]
  have h_finrank : Module.finrank ℝ SpaceTime = 4 := finrank_euclideanSpace_fin
  -- Rewrite ‖z‖² / (4t) as (1/(4t)) * ‖z‖²
  have h_exp_eq : ∀ z : SpaceTime, Real.exp (-‖z‖^2 / (4 * t)) =
      Real.exp (-(1 / (4 * t)) * ‖z‖^2) := by
    intro z; congr 1; field_simp
  simp_rw [h_exp_eq]
  -- Pull out the constant from the integral: ∫ c * f = c * ∫ f
  rw [MeasureTheory.integral_const_mul]
  -- Apply the Gaussian integral formula
  have hb : 0 < (1 / (4 * t)) := by positivity
  have h_gauss := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := SpaceTime) hb
  rw [h_gauss, h_finrank]
  -- Now: (4πt)^{-2} × (π / (1/(4t)))^2 = (4πt)^{-2} × (4πt)^2 = 1
  rw [hd_real]
  have h_div_eq : π / (1 / (4 * t)) = 4 * π * t := by field_simp
  rw [h_div_eq]
  have h_pow_eq : (4 * π * t) ^ ((4 : ℝ) / 2) = (4 * π * t) ^ (2 : ℝ) := by
    congr 1; norm_num
  rw [h_pow_eq]
  have h_neg_pow : (4 * π * t) ^ (-(4 : ℝ) / 2) = (4 * π * t) ^ (-(2 : ℝ)) := by
    congr 1; norm_num
  rw [h_neg_pow]
  have h_pos : 0 < 4 * π * t := by positivity
  rw [Real.rpow_neg (le_of_lt h_pos)]
  -- Goal: ((4πt)^2)⁻¹ * (4πt)^2 = 1
  have h_ne : (4 * π * t) ^ (2 : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.rpow_pos_of_pos h_pos
  rw [inv_mul_cancel₀ h_ne]

/-- The Schwinger representation of the position-space covariance.
    This expresses C(r) as a 1D integral over proper time.
-/
noncomputable def covarianceSchwingerRep (m : ℝ) (r : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-t * m^2) * heatKernelPositionSpace t r

/-- In 4D, the Schwinger representation of the covariance equals:
    (1/(16π²)) ∫₀^∞ exp(-tm²) · (1/t²) · exp(-r²/(4t)) dt
-/
lemma covarianceSchwingerRep_4D (m : ℝ) (_hm : 0 < m) (r : ℝ) (_hr : 0 < r) :
    covarianceSchwingerRep m r =
    (1 / (16 * Real.pi^2)) * ∫ t in Set.Ioi 0,
      Real.exp (-t * m^2) * (1 / t^2) * Real.exp (-r^2 / (4 * t)) := by
  unfold covarianceSchwingerRep
  -- Pull out the constant and use heatKernelPositionSpace_4D
  have h : ∀ t ∈ Set.Ioi 0,
      Real.exp (-t * m^2) * heatKernelPositionSpace t r =
      (1 / (16 * Real.pi^2)) * (Real.exp (-t * m^2) * (1 / t^2) * Real.exp (-r^2 / (4 * t))) := by
    intro t ht
    rw [heatKernelPositionSpace_4D t ht r]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h]
  rw [MeasureTheory.integral_const_mul]

/-- The Schwinger representation of the covariance equals the Bessel formula.
    C(r) = covarianceSchwingerRep m r = (m/(4π²r)) K₁(mr)

    This is the main result connecting the Schwinger proper-time representation
    to the explicit Bessel function formula for the free scalar propagator in 4D.
-/
theorem covarianceSchwingerRep_eq_besselFormula (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    covarianceSchwingerRep m r = (m / (4 * Real.pi^2 * r)) * besselK1 (m * r) := by
  rw [covarianceSchwingerRep_4D m hm r hr]
  -- We have: (1/(16π²)) ∫₀^∞ exp(-tm²) (1/t²) exp(-r²/(4t)) dt
  -- This equals (1/(16π²)) * (4m/r) * K₁(mr) = (m/(4π²r)) * K₁(mr)
  have h_integral := schwingerIntegral_eq_besselK1 m r hm hr
  -- First show the integrands are equal
  have h_eq : ∫ t in Set.Ioi 0, Real.exp (-t * m^2) * (1 / t^2) * Real.exp (-r^2 / (4 * t)) =
              ∫ t in Set.Ioi 0, (1 / t^2) * Real.exp (-m^2 * t - r^2 / (4 * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    change Real.exp (-t * m^2) * (1 / t^2) * Real.exp (-r^2 / (4 * t)) =
        (1 / t^2) * Real.exp (-m^2 * t - r^2 / (4 * t))
    rw [show -m^2 * t - r^2 / (4 * t) = -t * m^2 + -r^2 / (4 * t) from by ring, Real.exp_add]
    ring
  rw [h_eq, h_integral]
  ring

/-- The free covariance in position space via Bessel function representation.
    C(x,y) = (m / (4π² |x-y|)) · K₁(m |x-y|)

    This is the explicit formula for the massive scalar field propagator in 4D.
    The formula is valid for x ≠ y and m > 0.
-/
noncomputable def freeCovarianceBessel (m : ℝ) (x y : SpaceTime) : ℝ :=
  let r := ‖x - y‖
  if r = 0 then 0  -- Undefined at coincident points; regularize to 0
  else (m / (4 * Real.pi^2 * r)) * besselK1 (m * r)

/-- The free covariance in position space (abbreviation for the Bessel representation). -/
noncomputable abbrev freeCovariance (m : ℝ) (x y : SpaceTime) : ℝ :=
  freeCovarianceBessel m x y

/-- The Bessel covariance is symmetric. -/
lemma freeCovarianceBessel_symm (m : ℝ) (x y : SpaceTime) :
    freeCovarianceBessel m x y = freeCovarianceBessel m y x := by
  unfold freeCovarianceBessel
  simp only [norm_sub_rev]

/-- The Bessel covariance is positive for distinct points and m > 0. -/
lemma freeCovarianceBessel_pos (m : ℝ) (hm : 0 < m) (x y : SpaceTime) (hxy : x ≠ y) :
    0 < freeCovarianceBessel m x y := by
  unfold freeCovarianceBessel
  have hr : ‖x - y‖ ≠ 0 := by
    simpa only [ne_eq, norm_eq_zero, sub_eq_zero] using hxy
  simp only [hr, ↓reduceIte]
  apply mul_pos
  · apply div_pos hm
    apply mul_pos
    · have hpi : 0 < Real.pi := Real.pi_pos
      positivity
    · exact norm_sub_pos_iff.mpr hxy
  · exact besselK1_pos (m * ‖x - y‖) (mul_pos hm (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)))

/-! ### Connecting Fourier Representation to Schwinger Representation

The key to proving that the regulated Fourier integral converges to the Bessel form
is to use the Schwinger representation as an intermediate step:

1. **Fubini step**: Exchange the k-integral (Fourier) with the t-integral (Schwinger)
   ∫ dk e^{-α‖k‖²} e^{-ik·r} / (k² + m²) = ∫₀^∞ dt e^{-tm²} [∫ dk e^{-(α+t)‖k‖²} e^{-ik·r}]

2. **Gaussian FT**: The inner k-integral is a Gaussian Fourier transform
   ∫ dk e^{-s‖k‖²} e^{-ik·r} = (π/s)^{d/2} e^{-r²/(4s)}  (from Mathlib)

3. **Limit α → 0**: The regulated integral converges to the unregulated Schwinger form
   ∫₀^∞ dt e^{-tm²} H(t,r) = covarianceSchwingerRep m r

4. **Bessel connection**: By `covarianceSchwingerRep_eq_besselFormula`, this equals
   (m/(4π²r)) K₁(mr) = freeCovarianceBessel m x y
-/

/-- The Schwinger-regulated covariance: uses proper-time representation with regulator α.
    C_α^{Schwinger}(r) = ∫₀^∞ e^{-tm²} H(α+t, r) dt
    where H(s,r) = (4πs)^{-d/2} e^{-r²/(4s)} is the heat kernel.

    This is an intermediate form between the Fourier representation and the Bessel form.
-/
noncomputable def covarianceSchwingerRegulated (α : ℝ) (m : ℝ) (r : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-t * m^2) * heatKernelPositionSpace (α + t) r

/-- Integrability of exp(-tm²) on (0, ∞) for m > 0. -/
lemma integrableOn_exp_neg_mul_sq_Ioi (m : ℝ) (hm : 0 < m) :
    IntegrableOn (fun t => Real.exp (-t * m^2)) (Set.Ioi 0) := by
  have h : -m^2 < 0 := neg_neg_of_pos (sq_pos_of_pos hm)
  have := integrableOn_exp_mul_Ioi h 0
  convert this using 2
  congr 1
  ring

/-- Integrability of exp(-tm²) * C on (0, ∞) for m > 0 and any constant C. -/
lemma integrableOn_exp_neg_mul_sq_const_Ioi (m : ℝ) (hm : 0 < m) (C : ℝ) :
    IntegrableOn (fun t => Real.exp (-t * m^2) * C) (Set.Ioi 0) :=
  (integrableOn_exp_neg_mul_sq_Ioi m hm).mul_const C

/-- Continuity on `(0, ∞)` of `s ↦ exp(-s m²) · H(s, r)`. -/
private lemma continuousOn_exp_mul_heatKernel (m r : ℝ) :
    ContinuousOn (fun s => Real.exp (-s * m^2) * heatKernelPositionSpace s r) (Set.Ioi 0) := by
  refine ContinuousOn.mul
    ((Real.continuous_exp.comp (continuous_neg.mul continuous_const)).continuousOn) ?_
  intro s hs
  exact (heatKernelPositionSpace_continuous_at s (Set.mem_Ioi.mp hs) r).continuousWithinAt

/-- Integrability on `(0, ∞)` of `s ↦ exp(-s m²) · H(s, r)` for `m, r > 0`. -/
private lemma integrableOn_exp_mul_heatKernel (m : ℝ) (hm : 0 < m) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun s => Real.exp (-s * m^2) * heatKernelPositionSpace s r) (Set.Ioi 0) := by
  obtain ⟨C, hCpos, hCbound⟩ := heatKernelPositionSpace_bounded r hr
  refine Integrable.mono (integrableOn_exp_neg_mul_sq_const_Ioi m hm C)
    ((continuousOn_exp_mul_heatKernel m r).aestronglyMeasurable measurableSet_Ioi) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (heatKernelPositionSpace_nonneg s hs r)),
    abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) hCpos.le)]
  exact mul_le_mul_of_nonneg_left (hCbound s hs) (Real.exp_nonneg _)

/-- The Gaussian Fourier transform gives the heat kernel (times normalization).
    ∫_k e^{-s‖k‖²} e^{-ik·z} dk = (2π)^d H(s, ‖z‖)

    This is the key identity connecting momentum and position space.
-/
lemma gaussianFT_eq_heatKernel_times_norm (s : ℝ) (hs : 0 < s) (z : SpaceTime) :
    ∫ k : SpaceTime, Complex.exp (-(s : ℂ) * ‖k‖^2) * Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) =
    ((2 * Real.pi) ^ STDimension : ℝ) * (heatKernelPositionSpace s ‖z‖ : ℂ) := by
  -- Use Mathlib's integral_cexp_neg_mul_sq_norm_add
  have hs_re : 0 < (s : ℂ).re := by simp [hs]
  -- Rewrite the integrand to match the Mathlib form
  have h_integral : ∫ k : SpaceTime, Complex.exp (-(s : ℂ) * ‖k‖^2) *
      Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) =
      ∫ k : SpaceTime, Complex.exp (-(s : ℂ) * ‖k‖^2 + (-Complex.I) * ⟪z, k⟫_ℝ) := by
    congr 1
    ext k
    rw [← Complex.exp_add]
    congr 1
    have h_sym : ⟪k, z⟫_ℝ = ⟪z, k⟫_ℝ := (real_inner_comm k z).symm
    simp only [h_sym, mul_comm (-Complex.I)]
  rw [h_integral]
  have h_main := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := SpaceTime) hs_re
    (-Complex.I) z
  rw [h_main]
  -- Simplify (-I)² = -1
  have h_I_sq : (-Complex.I) ^ 2 = -1 := by rw [neg_sq, Complex.I_sq]
  rw [h_I_sq]
  -- Expand heatKernelPositionSpace
  rw [heatKernelPositionSpace_4D s hs ‖z‖]
  have h_finrank : Module.finrank ℝ SpaceTime = 4 := finrank_euclideanSpace_fin
  rw [h_finrank]
  -- The goal is now an algebraic identity involving π, s, and exponentials
  -- LHS: (π/s)^2 * exp(-‖z‖²/(4s))
  -- RHS: (2π)^4 * (1/(16π²s²) * exp(-‖z‖²/(4s))) = π²/s² * exp(-‖z‖²/(4s))
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hπ_ne : (π : ℝ) ≠ 0 := ne_of_gt hπ_pos
  have hd : STDimension = 4 := rfl
  -- Simplify the exponential arguments
  have h_exp_eq : Complex.exp (-1 * ↑‖z‖ ^ 2 / (4 * ↑s)) =
      ↑(Real.exp (-‖z‖^2 / (4 * s))) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h_exp_eq]
  -- Goal: (π/s)^(4/2) * exp(-‖z‖²/(4s)) = (2π)^4 * (1/(16π²s²) * exp(-‖z‖²/(4s)))
  -- First simplify ↑4/2 = 2
  have h_exp_four_two : (↑(4 : ℕ) : ℂ) / 2 = 2 := by norm_num
  conv_lhs => rw [h_exp_four_two]
  simp only [hd]
  -- Goal: (π/s)^2 * ↑exp = (2π)^4 * ↑(1/(16π²s²) * exp)
  -- Both sides equal ↑((π/s)² * exp(-‖z‖²/(4s)))
  -- Step 1: Show LHS = ↑((π/s)² * exp(...))
  have h_lhs : (↑π / ↑s : ℂ) ^ 2 * ↑(Real.exp (-‖z‖ ^ 2 / (4 * s))) =
      (↑((π / s) ^ 2 * Real.exp (-‖z‖ ^ 2 / (4 * s))) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div]
  -- Step 2: Show RHS = ↑((2π)^4 * (1/(16π²s²) * exp(...)))
  set a : ℝ := (2 * π) ^ 4 with ha_def
  set b : ℝ := 1 / (16 * π ^ 2 * s ^ 2) * Real.exp (-‖z‖ ^ 2 / (4 * s)) with hb_def
  have h_rhs : (↑a : ℂ) * ↑b = (↑(a * b) : ℂ) := (Complex.ofReal_mul a b).symm
  -- Step 3: Show the real parts are equal
  have h_real : (π / s) ^ 2 * Real.exp (-‖z‖ ^ 2 / (4 * s)) = a * b := by
    simp only [ha_def, hb_def]
    have hπ2_ne : (π : ℝ)^2 ≠ 0 := pow_ne_zero 2 hπ_ne
    have hs2_ne : s^2 ≠ 0 := pow_ne_zero 2 hs_ne
    have h_16 : (2 * π) ^ 4 = 16 * π^4 := by ring
    rw [h_16]
    field_simp
  -- Combine: LHS = ↑(real) = ↑(a*b) = ↑a * ↑b = RHS
  -- Note: the exponent is (2:ℂ) after rewriting h_exp_four_two
  -- Convert cpow to npow: x^(2:ℂ) = x^(2:ℕ) for x ∈ ℂ
  have h_pow_eq : (↑π / ↑s : ℂ) ^ (2 : ℂ) = (↑π / ↑s : ℂ) ^ (2 : ℕ) := by
    rw [← Complex.cpow_natCast]
    norm_cast
  rw [h_pow_eq]
  calc (↑π / ↑s : ℂ) ^ (2 : ℕ) * ↑(Real.exp (-‖z‖ ^ 2 / (4 * s)))
      = ↑((π / s) ^ 2 * Real.exp (-‖z‖ ^ 2 / (4 * s))) := h_lhs
    _ = ↑(a * b) := by rw [h_real]
    _ = ↑a * ↑b := h_rhs.symm

/-- **THEOREM**: The integrand for fubini_schwinger_fourier is integrable on SpaceTime × (0,∞).
    This justifies using Tonelli's theorem.

    **Proof:**
    - The integrand factors as exp(-(α+t)‖k‖²) × exp(-tm²)
    - For k: ∫ exp(-(α+t)‖k‖²) dk is finite (Gaussian integral, since α+t > α > 0)
    - For t: ∫_0^∞ exp(-tm²) dt = 1/m² (exponential integral)
    - The product integral converges by Tonelli since all terms are non-negative
-/
theorem integrable_schwinger_fourier_integrand (α : ℝ) (hα : 0 < α) (m : ℝ) (hm : 0 < m) :
    Integrable (fun p : SpaceTime × ℝ =>
      if p.2 > 0 then Real.exp (-(α + p.2) * ‖p.1‖^2 - p.2 * m^2)
      else 0) (volume.prod volume) := by
  -- Strategy: bound by exp(-α‖k‖²) * exp(-tm²) * 1_{t>0} and use Integrable.prod_mul
  set f := fun p : SpaceTime × ℝ =>
    if p.2 > 0 then Real.exp (-(α + p.2) * ‖p.1‖^2 - p.2 * m^2) else 0 with hf_def
  -- The dominating function: g(k) * h(t) where g is Gaussian and h is exponential decay
  set g := fun k : SpaceTime => Real.exp (-α * ‖k‖^2) with hg_def
  set h := fun t : ℝ => if t > 0 then Real.exp (-t * m^2) else 0 with hh_def
  -- Step 1: g is integrable (Gaussian on EuclideanSpace)
  have hg_int : Integrable g volume := by
    -- Use the complex Gaussian integrability and extract real part
    have hα_re : (0 : ℝ) < (α : ℂ).re := by simp [hα]
    have h_cplx : Integrable (fun v : SpaceTime =>
        Complex.exp (-(α : ℂ) * ‖v‖^2 + 0 * (inner ℝ (0 : SpaceTime) v))) volume :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace hα_re 0 0
    simp only [zero_mul, add_zero] at h_cplx
    -- Extract real part: re(exp(-α‖v‖²)) = exp(-α‖v‖²) since argument is real
    have h_re_eq : ∀ v : SpaceTime,
        Complex.re (Complex.exp (-(α : ℂ) * ‖v‖^2)) = Real.exp (-α * ‖v‖^2) := by
      intro v
      -- -(α : ℂ) * ‖v‖² = ↑(-α * ‖v‖²)
      have h_real : (-(α : ℂ) * ‖v‖^2) = ↑(-α * ‖v‖^2 : ℝ) := by
        simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow]
      rw [h_real, Complex.exp_ofReal_re]
    convert h_cplx.re using 1
    ext v
    exact (h_re_eq v).symm
  -- Step 2: h is integrable (exponential decay on (0,∞), zero elsewhere)
  have hh_int : Integrable h volume := by
    -- h(t) = exp(-tm²) for t > 0, else 0
    -- This equals the indicator function of (0,∞) applied to exp(-tm²)
    have hm2_pos : 0 < m^2 := by positivity
    have h_intOn : IntegrableOn (fun t => Real.exp (-t * m^2)) (Set.Ioi 0) volume := by
      convert exp_neg_integrableOn_Ioi 0 hm2_pos using 1
      ext t; ring_nf
    have h_indicator : Integrable ((Set.Ioi (0:ℝ)).indicator (fun t => Real.exp (-t * m^2))) volume
      :=
      IntegrableOn.integrable_indicator h_intOn measurableSet_Ioi
    -- h equals the indicator function
    have h_eq_indicator : h = (Set.Ioi (0:ℝ)).indicator (fun t => Real.exp (-t * m^2)) := by
      ext t
      simp only [Set.indicator, Set.mem_Ioi, hh_def]
    rwa [h_eq_indicator]
  -- Step 3: The product g(k) * h(t) is integrable on the product measure
  have hgh_int : Integrable (fun p : SpaceTime × ℝ => g p.1 * h p.2) (volume.prod volume) := by
    exact Integrable.mul_prod hg_int hh_int
  -- Step 4: Our function f is bounded by g * h
  have hf_le : ∀ p : SpaceTime × ℝ, ‖f p‖ ≤ g p.1 * h p.2 := by
    intro ⟨k, t⟩
    simp only [hf_def, hg_def, hh_def]
    split_ifs with ht
    · -- Case t > 0: need exp(-(α+t)‖k‖² - tm²) ≤ exp(-α‖k‖²) * exp(-tm²)
      simp only [Real.norm_eq_abs, abs_exp]
      have h1 : Real.exp (-(α + t) * ‖k‖^2 - t * m^2) =
                Real.exp (-α * ‖k‖^2) * Real.exp (-t * ‖k‖^2) * Real.exp (-t * m^2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      rw [h1]
      have h2 : Real.exp (-t * ‖k‖^2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        apply mul_nonpos_of_nonpos_of_nonneg
        · linarith
        · positivity
      calc Real.exp (-α * ‖k‖^2) * Real.exp (-t * ‖k‖^2) * Real.exp (-t * m^2)
          ≤ Real.exp (-α * ‖k‖^2) * 1 * Real.exp (-t * m^2) := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_left h2
              exact Real.exp_nonneg _
            · exact Real.exp_nonneg _
        _ = Real.exp (-α * ‖k‖^2) * Real.exp (-t * m^2) := by ring
    · -- Case t ≤ 0: f = 0, h t = 0, so ‖f‖ = 0 ≤ g * h = g * 0 = 0
      simp only [norm_zero, mul_zero, le_refl]
  -- Step 5: f is AEStronglyMeasurable
  have hf_meas : AEStronglyMeasurable f (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.ite
    · exact measurableSet_lt measurable_const measurable_snd
    · apply Measurable.exp
      -- Need to show -(α + x.2) * ‖x.1‖² - x.2 * m² is measurable
      apply Measurable.sub
      · apply Measurable.mul
        · exact (measurable_const.add measurable_snd).neg
        · exact (measurable_fst.norm).pow_const 2
      · exact measurable_snd.mul measurable_const
    · exact measurable_const
  -- Step 6: Apply Integrable.mono'
  exact Integrable.mono' hgh_int hf_meas (Filter.Eventually.of_forall hf_le)

/-- **Fubini swap lemma for the Schwinger integrand with phase.**

    This lemma asserts that the integration order can be swapped for the
    Gaussian × phase integrand appearing in the Schwinger representation:

    Re[∫_k (∫_t exp(-(α+t)‖k‖²) * exp(-tm²) dt) * phase(k) dk]
      = ∫_t exp(-tm²) * Re[∫_k exp(-(α+t)‖k‖²) * phase(k) dk] dt

    **Justification:** Both sides are the same double integral of
    `exp(-(α+t)‖k‖² - tm²) * exp(-i⟪k, x-y⟫)` with integration order swapped.
    Fubini applies because the absolute value is integrable (the phase has norm 1).

    This follows from `MeasureTheory.integral_integral_swap` together with
    integrability bounds from the Gaussian decay.
-/
theorem fubini_schwinger_integrand (α : ℝ) (hα : 0 < α) (m : ℝ) (hm : 0 < m)
    (x y : SpaceTime) (_hxy : x ≠ y) :
    (∫ k : SpaceTime, (↑(∫ t in Set.Ioi 0, Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2)) : ℂ) *
      Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re =
    ∫ t in Set.Ioi 0, Real.exp (-t * m^2) *
      (∫ k : SpaceTime, Complex.exp (-(↑(α + t) : ℂ) * ‖k‖^2) *
        Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re := by
  -- Define the phase factor
  set phase : SpaceTime → ℂ := fun k => Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ) with hphase_def
  -- The phase has norm 1 (since -I * real has real part 0)
  have hphase_norm : ∀ k, ‖phase k‖ = 1 := fun k => by
    simp only [hphase_def]
    exact norm_exp_neg_I_mul_real ⟪k, x - y⟫_ℝ
  -- Define the complex integrand on the product space
  set f : SpaceTime × ℝ → ℂ := fun p =>
    if p.2 > 0 then Complex.exp (-(↑(α + p.2) : ℂ) * ‖p.1‖^2 - ↑(p.2 * m^2)) * phase p.1
    else 0 with hf_def
  -- The absolute value of the integrand
  set f_abs : SpaceTime × ℝ → ℝ := fun p =>
    if p.2 > 0 then Real.exp (-(α + p.2) * ‖p.1‖^2 - p.2 * m^2) else 0 with hf_abs_def
  -- Key: ‖f p‖ ≤ f_abs p (since |phase| = 1)
  have hf_bound : ∀ p, ‖f p‖ ≤ f_abs p := fun p => by
    simp only [hf_def, hf_abs_def]
    split_ifs with ht
    · rw [norm_mul, hphase_norm, mul_one, Complex.norm_exp]
      apply le_of_eq
      -- Simplify the real part of the complex exponent
      -- (↑‖p.1‖)^2 = ↑(‖p.1‖^2), so its real part is ‖p.1‖^2
      simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, ← Complex.ofReal_pow, mul_zero, sub_zero]
    · simp only [norm_zero, le_refl]
  have hf_abs_int : Integrable f_abs (volume.prod volume) := by
    simpa only [hf_abs_def] using integrable_schwinger_fourier_integrand α hα m hm
  have hf_meas : AEStronglyMeasurable f (volume.prod volume) := by
    simp only [hf_def, hphase_def]
    refine (StronglyMeasurable.ite (measurableSet_lt measurable_const measurable_snd)
      ?_ stronglyMeasurable_const).aestronglyMeasurable
    exact (by fun_prop : Continuous _).stronglyMeasurable
  have hf_int : Integrable f (volume.prod volume) :=
    hf_abs_int.mono' hf_meas (Filter.Eventually.of_forall hf_bound)
  -- Relate LHS to integrals of f
  have h_lhs : (∫ k : SpaceTime, (↑(∫ t in Set.Ioi 0,
      Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2)) : ℂ) *
      Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re =
      (∫ k : SpaceTime, ∫ t in Set.Ioi 0, f (k, t)).re := by
    congr 1; apply integral_congr_ae; filter_upwards with k
    rw [← integral_complex_ofReal, mul_comm]
    rw [show Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ) *
        ∫ t in Set.Ioi 0, (↑(Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2)) : ℂ) =
        ∫ t in Set.Ioi 0, Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ) *
          ↑(Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2)) from
      (MeasureTheory.integral_const_mul _ _).symm]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [Set.mem_Ioi] at ht
    simp only [hf_def, ht, ↓reduceIte, Complex.ofReal_mul, Complex.ofReal_exp]
    rw [mul_comm, ← Complex.exp_add]; congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_add, ← Complex.ofReal_pow]; ring_nf
  -- Convert set integrals to full integrals (f=0 for t≤0)
  have h_set_to_full_lhs : (∫ k : SpaceTime, ∫ t in Set.Ioi 0, f (k, t)) =
      ∫ k : SpaceTime, ∫ t : ℝ, f (k, t) := by
    apply integral_congr_ae; filter_upwards with k
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]; intro t ht
    simp only [Set.mem_Ioi, not_lt] at ht; simp only [hf_def, not_lt.mpr ht, ↓reduceIte]
  have h_set_to_full_rhs : (∫ t in Set.Ioi 0, ∫ k : SpaceTime, f (k, t)) =
      ∫ t : ℝ, ∫ k : SpaceTime, f (k, t) := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]; intro t ht
    simp only [Set.mem_Ioi, not_lt] at ht; simp only [hf_def, not_lt.mpr ht, ↓reduceIte,
      integral_zero]
  -- Fubini swap and Re inside integral
  have h_fubini : (∫ k : SpaceTime, ∫ t : ℝ, f (k, t)) = ∫ t : ℝ, ∫ k : SpaceTime, f (k, t) :=
    MeasureTheory.integral_integral_swap hf_int
  have h_re_inside : (∫ t : ℝ, ∫ k : SpaceTime, f (k, t)).re =
      ∫ t : ℝ, (∫ k : SpaceTime, f (k, t)).re := (integral_re hf_int.integral_prod_right).symm
  -- For t > 0, factor out exp(-tm²)
  have h_factor : ∀ t : ℝ, (∫ k : SpaceTime, f (k, t)).re =
      if t > 0 then Real.exp (-t * m^2) * (∫ k : SpaceTime, Complex.exp (-(↑(α + t) : ℂ) * ‖k‖^2) *
        Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re else 0 := fun t => by
    split_ifs with ht
    · simp only [hf_def, ht, ↓reduceIte, hphase_def]
      have h_split : ∀ k : SpaceTime, Complex.exp (-(↑(α + t) : ℂ) * ‖k‖^2 - ↑(t * m^2)) *
          Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ) = ↑(Real.exp (-t * m^2)) *
          (Complex.exp (-(↑(α + t) : ℂ) * ‖k‖^2) * Complex.exp (-Complex.I * ⟪k,
            x - y⟫_ℝ)) := fun k => by
        rw [← Complex.exp_add, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]; congr 1
        simp only [Complex.ofReal_neg, Complex.ofReal_mul]; ring
      simp_rw [h_split, ← smul_eq_mul, integral_smul, smul_eq_mul, Complex.re_ofReal_mul]
    · simp only [hf_def, ht, ↓reduceIte, integral_zero, Complex.zero_re]
  -- Combine all steps
  rw [h_lhs, h_set_to_full_lhs, h_fubini, h_re_inside]
  rw [show (∫ t : ℝ, (∫ k : SpaceTime, f (k, t)).re) = ∫ t in Set.Ioi 0, (∫ k : SpaceTime, f (k,
    t)).re
      from by rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]; intro t ht
              simp only [Set.mem_Ioi, not_lt] at ht; simp [h_factor, not_lt.mpr ht]]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by simp [h_factor, Set.mem_Ioi.mp ht]

/-- The regulated Fourier integral equals the Schwinger-regulated form via Fubini/Tonelli. -/
theorem fubini_schwinger_fourier (α : ℝ) (hα : 0 < α) (m : ℝ) (hm : 0 < m) (x y : SpaceTime) (hxy :
  x ≠ y) :
    freeCovarianceRegulated α m x y = covarianceSchwingerRegulated α m ‖x - y‖ := by
  -- Expand definitions
  unfold freeCovarianceRegulated covarianceSchwingerRegulated
  set r := x - y with hr_def
  set normalisation := (2 * Real.pi) ^ STDimension with hnorm_def
  -- Step 1: Use Schwinger representation to rewrite the propagator
  have h_schwinger : ∀ k : SpaceTime, freePropagatorMomentum m k =
      ∫ t in Set.Ioi 0, schwingerIntegrand t m k := by
    intro k
    rw [schwinger_representation m hm k]
    unfold freePropagatorMomentum
    ring
  -- Key positivity facts
  have hnorm_pos : 0 < normalisation := by
    rw [hnorm_def]
    exact pow_pos two_pi_pos STDimension
  have hnorm_ne : normalisation ≠ 0 := ne_of_gt hnorm_pos
  have hr_pos : 0 < ‖r‖ := by
    rw [hr_def]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  -- Step 2: The key exponent combination identity
  have h_combine : ∀ k : SpaceTime, ∀ t : ℝ, 0 < t →
      Real.exp (-α * ‖k‖^2) * schwingerIntegrand t m k =
      Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2) := by
    intro k t _ht
    unfold schwingerIntegrand
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  -- Step 3: The Gaussian FT gives heat kernel (and its inverse)
  have h_gaussFT : ∀ t : ℝ, 0 < t →
      ∫ k : SpaceTime, Complex.exp (-↑(α + t) * ‖k‖^2) *
        Complex.exp (-Complex.I * ⟪k, r⟫_ℝ) =
      (normalisation : ℂ) * (heatKernelPositionSpace (α + t) ‖r‖ : ℂ) := by
    intro t ht
    have hαt : 0 < α + t := by linarith
    rw [hnorm_def]
    exact gaussianFT_eq_heatKernel_times_norm (α + t) hαt r
  -- Key identity: heat kernel equals k-integral (inverse of gaussFT)
  have h_heatKernel_eq_kint : ∀ s : ℝ, 0 < s →
      (heatKernelPositionSpace s ‖r‖ : ℂ) =
      (1 / normalisation : ℂ) * ∫ k : SpaceTime, Complex.exp (-↑s * ‖k‖^2) *
        Complex.exp (-Complex.I * ⟪k, r⟫_ℝ) := by
    intro s hs
    have h := gaussianFT_eq_heatKernel_times_norm s hs r
    have h_ne : (normalisation : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm_ne
    rw [← hnorm_def] at h
    rw [h, one_div]
    field_simp [h_ne]
  -- Use proven integrability
  have h_int := integrable_schwinger_fourier_integrand α hα m hm
  simp only [hr_def] at *
  -- Main computation: show both sides equal the same heat kernel integral
  -- The proof uses:
  -- 1. Schwinger representation: 1/(k²+m²) = ∫_t exp(-t(k²+m²)) dt
  -- 2. Fubini to swap k and t integrals (justified by h_int)
  -- 3. Gaussian FT: ∫_k exp(-(α+t)k²) exp(-ik·r) = (2π)^d H(α+t, r)
  -- 4. Normalization cancellation
  -- Both sides equal ∫_t exp(-tm²) H(α+t, ‖x-y‖) dt
  -- LHS via Schwinger + Fubini + Gaussian FT
  -- RHS by definition of covarianceSchwingerRegulated
  -- For the inner k-integral at each t > 0:
  have h_inner_k : ∀ t : ℝ, 0 < t →
      (∫ k : SpaceTime,
        Complex.ofReal (Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2) / normalisation) *
        Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)) =
      Complex.ofReal (Real.exp (-t * m^2) * heatKernelPositionSpace (α + t) ‖x - y‖) := by
    intro t ht
    have hαt : 0 < α + t := by linarith
    -- Factor out the constant exp(-tm²)/norm
    calc ∫ k : SpaceTime, ↑(Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2) / normalisation) *
          Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)
        = ∫ k : SpaceTime, (↑(Real.exp (-t * m^2) / normalisation) : ℂ) *
            (↑(Real.exp (-(α + t) * ‖k‖^2)) * Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)) := by
          congr 1; ext k
          simp only [Complex.ofReal_div, Complex.ofReal_mul]
          ring
      _ = (↑(Real.exp (-t * m^2) / normalisation) : ℂ) *
            ∫ k : SpaceTime, ↑(Real.exp (-(α + t) * ‖k‖^2)) *
              Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ) := MeasureTheory.integral_const_mul _ _
      _ = (↑(Real.exp (-t * m^2) / normalisation) : ℂ) *
            ∫ k : SpaceTime, Complex.exp (-↑(α + t) * ‖k‖^2) *
              Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ) := by
          congr 2; ext k
          rw [Complex.ofReal_exp]; congr 1
          push_cast; ring
      _ = (↑(Real.exp (-t * m^2) / normalisation) : ℂ) *
            (↑normalisation * ↑(heatKernelPositionSpace (α + t) ‖x - y‖)) := by
          rw [hnorm_def, gaussianFT_eq_heatKernel_times_norm (α + t) hαt (x - y)]
      _ = ↑(Real.exp (-t * m^2) * heatKernelPositionSpace (α + t) ‖x - y‖) := by
          rw [Complex.ofReal_div]
          -- exp / norm * (norm * H) = exp * H
          have h_ne : (↑normalisation : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm_ne
          field_simp
          rw [← Complex.ofReal_mul]
  -- The RHS integrand is real and integrable
  have h_rhs_integrability : IntegrableOn
      (fun t => Real.exp (-t * m^2) * heatKernelPositionSpace (α + t) ‖x - y‖) (Set.Ioi 0) := by
    -- Get a uniform bound on the heat kernel for s = α + t with t > 0
    -- Since α > 0 and t > 0, we have s > α > 0
    obtain ⟨C, hCpos, hCbound⟩ := heatKernelPositionSpace_bounded ‖x - y‖ hr_pos
    -- The bound: exp(-tm²) * H(α+t, r) ≤ exp(-tm²) * C
    have h_bound_int : IntegrableOn (fun t => Real.exp (-t * m^2) * C) (Set.Ioi 0) :=
      integrableOn_exp_neg_mul_sq_const_Ioi m hm C
    -- Apply Integrable.mono (IntegrableOn is Integrable with restricted measure)
    refine Integrable.mono h_bound_int ?_ ?_
    · -- Measurability of the integrand on (0, ∞)
      -- We need AEStronglyMeasurable on volume.restrict (Set.Ioi 0)
      -- The function is continuous on (0, ∞), hence AEStronglyMeasurable there
      have h_cont : ContinuousOn
          (fun t => Real.exp (-t * m^2) * heatKernelPositionSpace (α + t) ‖x - y‖) (Set.Ioi 0) := by
        apply ContinuousOn.mul
        · exact (Real.continuous_exp.comp (continuous_neg.mul continuous_const)).continuousOn
        · intro t ht
          have ht_pos : 0 < t := Set.mem_Ioi.mp ht
          have hαt : 0 < α + t := by linarith
          have h_add_cont : ContinuousAt (fun s => α + s) t := continuousAt_const.add
            continuousAt_id
          exact (heatKernelPositionSpace_continuous_at (α + t) hαt ‖x - y‖).comp h_add_cont
            |>.continuousWithinAt
      exact h_cont.aestronglyMeasurable measurableSet_Ioi
    · -- The pointwise bound ‖f t‖ ≤ ‖g t‖ on Ioi 0
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have ht_pos : t > 0 := Set.mem_Ioi.mp ht
      have hαt : α + t > 0 := by linarith
      have h_heat_nonneg : 0 ≤ heatKernelPositionSpace (α + t) ‖x - y‖ :=
        heatKernelPositionSpace_nonneg (α + t) hαt ‖x - y‖
      have h_exp_nonneg : 0 ≤ Real.exp (-t * m^2) := Real.exp_nonneg _
      rw [abs_of_nonneg (mul_nonneg h_exp_nonneg h_heat_nonneg)]
      rw [abs_of_nonneg (mul_nonneg h_exp_nonneg (le_of_lt hCpos))]
      exact mul_le_mul_of_nonneg_left (hCbound (α + t) hαt) h_exp_nonneg
  -- The LHS integral after Fubini equals ∫_t exp(-tm²) H(α+t, r) dt, which is the RHS.
  -- Ingredients: h_schwinger (Schwinger rep), h_combine (exponent factorization),
  -- h_gaussFT (k-integral), h_int (Fubini), h_inner_k (combination per t).
  -- Step 1: Substitute Schwinger representation
  have h_lhs_step1 : (∫ k : SpaceTime,
    ↑(Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / normalisation) *
      Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re =
      (∫ k : SpaceTime, ↑(Real.exp (-α * ‖k‖^2) * (∫ t in Set.Ioi 0,
        schwingerIntegrand t m k) / normalisation) *
        Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re := by
    congr 2
    ext k
    rw [h_schwinger k]
  rw [h_lhs_step1]
  -- Step 2: Combine exponents and prepare for Fubini
  -- exp(-α‖k‖²) * ∫_t schwinger = ∫_t exp(-α‖k‖²) * schwinger = ∫_t exp(-(α+t)‖k‖²) * exp(-tm²)
  have h_lhs_step2 : (∫ k : SpaceTime,
      ↑(Real.exp (-α * ‖k‖^2) * (∫ t in Set.Ioi 0, schwingerIntegrand t m k) / normalisation) *
        Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re =
      (∫ k : SpaceTime,
        ↑((∫ t in Set.Ioi 0, Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2)) / normalisation) *
          Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re := by
    congr 2
    ext k
    congr 2
    -- Need: exp(-α‖k‖²) * ∫_t schwinger(t,m,k) = ∫_t exp(-(α+t)‖k‖²) * exp(-tm²)
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    exact h_combine k t ht
  rw [h_lhs_step2]
  -- Step 3: Rewrite to make the structure clearer
  -- The LHS is Re[∫_k (∫_t f(k,t)) / norm * phase(k)]
  -- We want to show this equals ∫_t g(t) where g(t) = exp(-tm²) * H(α+t, r)
  -- First, rewrite the k-integral by pulling out 1/normalisation
  have h_step3 : (∫ k : SpaceTime,
      ↑((∫ t in Set.Ioi 0, Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2)) / normalisation) *
        Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re =
      ((1 / normalisation : ℝ) * ∫ k : SpaceTime,
        ↑(∫ t in Set.Ioi 0, Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2)) *
          Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re := by
    congr 2
    rw [show (↑(1 / normalisation : ℝ) : ℂ) * ∫ k : SpaceTime,
        ↑(∫ t in Set.Ioi 0, Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2)) *
          Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ) =
        ∫ k : SpaceTime, ↑(1 / normalisation : ℝ) *
          (↑(∫ t in Set.Ioi 0, Real.exp (-(α + t) * ‖k‖^2) * Real.exp (-t * m^2)) *
            Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)) from
      (MeasureTheory.integral_const_mul _ _).symm]
    congr 1 with k
    simp only [Complex.ofReal_div, Complex.ofReal_one]
    ring
  rw [h_step3]
  simp only [Complex.re_ofReal_mul, mul_comm (1 / normalisation)]
  -- Step 4: Substitute k-integral form of heat kernel in RHS
  -- H(s, r) = (1/norm) * ∫_k exp(-s‖k‖²) * phase(k)
  have h_rhs_subst : ∫ t in Set.Ioi 0, Real.exp (-t * m^2) * heatKernelPositionSpace (α + t) ‖x -
    y‖ =
      (1 / normalisation) * (∫ t in Set.Ioi 0, Real.exp (-t * m^2) *
        (∫ k : SpaceTime, Complex.exp (-↑(α + t) * ‖k‖^2) *
          Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have ht_pos : 0 < t := Set.mem_Ioi.mp ht
    have hαt : 0 < α + t := by linarith
    -- Use h_gaussFT to get the k-integral equals normalisation * H
    have h_gaussft := h_gaussFT t ht_pos
    -- ∫_k exp(-(α+t)‖k‖²) * phase = norm * H(α+t, r)
    -- Taking Re: Re[norm * H] = norm * H (both real)
    have h_real : (∫ k : SpaceTime, Complex.exp (-(↑(α + t) : ℂ) * ‖k‖^2) *
        Complex.exp (-Complex.I * ⟪k, x - y⟫_ℝ)).re =
        normalisation * heatKernelPositionSpace (α + t) ‖x - y‖ := by
      rw [h_gaussft]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    -- Now we need: exp(-tm²) * H = (1/norm) * exp(-tm²) * (norm * H)
    simp only
    rw [h_real]
    field_simp
  rw [h_rhs_subst]
  -- Now both sides have form: LHS * (1/norm) = (1/norm) * RHS
  -- Suffices to show LHS = RHS, then multiply by 1/norm
  have h_norm_factor : ∀ a b : ℝ, a * (1 / normalisation) = (1 / normalisation) * b ↔ a = b := by
    intro a b
    constructor
    · intro h
      have h1 : a * (1 / normalisation) * normalisation = (1 / normalisation) * b * normalisation
        := by
        rw [h]
      field_simp at h1
      linarith
    · intro h
      rw [h, mul_comm]
  rw [h_norm_factor]
  -- Goal: Re[∫_k (∫_t F(k,t)) * phase(k)] = ∫_t exp(-tm²) * Re[∫_k exp(-(α+t)‖k‖²) * phase(k)]
  --
  -- This is the Fubini swap. Both sides are double integrals:
  -- LHS = Re[∫_k ∫_t exp(-(α+t)‖k‖²) * exp(-tm²) * phase(k) dt dk]
  -- RHS = ∫_t ∫_k exp(-tm²) * exp(-(α+t)‖k‖²) * phase(k) dk dt
  --
  -- The integrands are identical, just with integration order swapped.
  -- Fubini's theorem applies because h_int provides integrability of the absolute value.
  -- The phase factor exp(-i⟨k, x-y⟩) has norm 1, so it doesn't affect integrability.
  --
  -- Fubini integration order swap for Gaussian × phase integrand
  exact fubini_schwinger_integrand α hα m hm x y hxy

/-- As α → 0⁺, the Schwinger-regulated covariance converges to the unregulated form. -/
lemma covarianceSchwingerRegulated_tendsto (m : ℝ) (hm : 0 < m) (r : ℝ) (hr : 0 < r) :
    Filter.Tendsto (fun α => covarianceSchwingerRegulated α m r)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (covarianceSchwingerRep m r)) := by
  unfold covarianceSchwingerRegulated covarianceSchwingerRep
  -- Get the heat kernel bound
  obtain ⟨C, hCpos, hCbound⟩ := heatKernelPositionSpace_bounded r hr
  -- Define the bound function
  let bound : ℝ → ℝ := fun t => Real.exp (-t * m^2) * C
  -- Apply dominated convergence for filters with restricted measure
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi 0)) bound
  -- 1. AE Strong Measurability (compositions of measurable functions)
  · filter_upwards with α
    apply Measurable.aestronglyMeasurable
    unfold heatKernelPositionSpace
    apply Measurable.mul
    · -- exp(-t * m²) is measurable in t
      exact (measurable_id.neg.mul measurable_const).exp
    · apply Measurable.mul
      · -- (4π(α+t))^{-d/2} is measurable in t (using MeasurablePow ℝ ℝ)
        exact (measurable_const.mul (measurable_const.add measurable_id)).pow_const
          (-(STDimension : ℝ) / 2)
      · -- exp(-r²/(4(α+t))) is measurable in t
        exact (measurable_const.div
          (measurable_const.mul (measurable_const.add measurable_id))).exp
  -- 2. Bound: ‖F α t‖ ≤ bound t for α > 0 and a.e. t > 0
  · filter_upwards [self_mem_nhdsWithin] with α hα
    have hαpos : 0 < α := Set.mem_Ioi.mp hα
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have htpos : 0 < t := Set.mem_Ioi.mp ht
    have hαtpos : 0 < α + t := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    rw [abs_of_nonneg (heatKernelPositionSpace_nonneg (α + t) hαtpos r)]
    exact mul_le_mul_of_nonneg_left (hCbound (α + t) hαtpos) (Real.exp_nonneg _)
  -- 3. Integrability of bound
  · exact integrableOn_exp_neg_mul_sq_const_Ioi m hm C
  -- 4. Pointwise convergence: F α t → f t as α → 0 for a.e. t in Ioi 0
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have htpos : 0 < t := Set.mem_Ioi.mp ht
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    · -- H(α+t, r) → H(t, r) as α → 0 by continuity at t
      have hcont := heatKernelPositionSpace_continuous_at t htpos r
      -- We need: (fun α => H(α + t, r)) → H(t, r) as α → 0 in nhdsWithin 0 (Ioi 0)
      -- This follows from continuity of H at t and the fact that α + t → t as α → 0
      have htend : Filter.Tendsto (fun α => α + t) (nhdsWithin 0 (Set.Ioi 0)) (nhds t) := by
        have h1 : Filter.Tendsto (fun α => α + t) (nhds 0) (nhds (0 + t)) :=
          tendsto_id.add tendsto_const_nhds
        simp at h1
        exact h1.mono_left nhdsWithin_le_nhds
      exact hcont.tendsto.comp htend

/-- The unregulated Schwinger form equals the Bessel form (for r > 0). -/
lemma covarianceSchwingerRep_eq_freeCovarianceBessel (m : ℝ) (hm : 0 < m) (x y : SpaceTime) (hxy :
  x ≠ y) :
    covarianceSchwingerRep m ‖x - y‖ = freeCovarianceBessel m x y := by
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [covarianceSchwingerRep_eq_besselFormula m ‖x - y‖ hm hr]
  unfold freeCovarianceBessel
  simp only [hr.ne', ↓reduceIte]

/-- **Main theorem:** The regulated Fourier covariance converges to the Bessel form.
    This follows from the Schwinger representation approach:
    1. Use `fubini_schwinger_fourier` to convert Fourier → Schwinger
    2. Use `covarianceSchwingerRegulated_tendsto` for the α → 0 limit
    3. Use `covarianceSchwingerRep_eq_freeCovarianceBessel` for Schwinger → Bessel
-/
theorem freeCovariance_regulated_tendsto_bessel (m : ℝ) (hm : 0 < m) (x y : SpaceTime) (hxy : x ≠
  y) :
    Filter.Tendsto (fun α => freeCovarianceRegulated α m x y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (freeCovarianceBessel m x y)) := by
  -- The proof outline:
  -- 1. freeCovarianceRegulated uses cos(k·(x-y)) which for radial r = ‖x-y‖ reduces to radial case
  -- 2. By fubini_schwinger_fourier, equals covarianceSchwingerRegulated α m r
  -- 3. By covarianceSchwingerRegulated_tendsto, converges to covarianceSchwingerRep m r
  -- 4. By covarianceSchwingerRep_eq_freeCovarianceBessel, equals freeCovarianceBessel
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  -- Step 1 & 2: Convert Fourier → Schwinger and use that the Schwinger form converges
  have h_schwinger_conv := covarianceSchwingerRegulated_tendsto m hm ‖x - y‖ hr
  -- Step 3: The limit equals the Bessel form
  have h_limit_eq := covarianceSchwingerRep_eq_freeCovarianceBessel m hm x y hxy
  rw [← h_limit_eq]
  -- Step 4: Use Fubini lemma to equate the Fourier and Schwinger forms
  have h_eq : ∀ α ∈ Set.Ioi (0 : ℝ), covarianceSchwingerRegulated α m ‖x - y‖ =
    freeCovarianceRegulated α m x y :=
    fun α hα => (fubini_schwinger_fourier α hα m hm x y hxy).symm
  exact h_schwinger_conv.congr' (eventually_nhdsWithin_of_forall h_eq)


/-- **The deep result:** The regulated Fourier integral converges to the Bessel form as α → 0⁺.
    This is the statement that the Fourier transform of 1/(k² + m²) in 4D equals
    (m / (4π² r)) · K₁(mr).

    The proof involves:
    1. Reducing to a 1D integral by exploiting rotational symmetry
    2. Computing the Fourier transform of a radial function in 4D
    3. Using the integral representation of K₁
    4. Taking the limit α → 0⁺ of the regulated integral

    The regulator exp(-α‖k‖²) makes the integral absolutely convergent for any α > 0.
    The limit exists and equals the Bessel form for x ≠ y.
-/
theorem freeCovariance_regulated_limit_eq_freeCovariance (m : ℝ) (hm : 0 < m) (x y : SpaceTime)
  (hxy : x ≠ y) :
    Filter.Tendsto (fun α => freeCovarianceRegulated α m x y) (nhdsWithin 0 (Set.Ioi 0)) (nhds
      (freeCovariance m x y)) :=
  -- This is exactly freeCovariance_regulated_tendsto_bessel since freeCovariance =
  -- freeCovarianceBessel
  freeCovariance_regulated_tendsto_bessel m hm x y hxy

/-- **Domination bound (Schwinger):** The Schwinger-regulated covariance is bounded by a constant
    times the unregulated form. For α ∈ (0, 1], we have:
      C_regulated(α, m, r) ≤ exp(m²) × C_Bessel(m, r)

    **Proof:** Using change of variables s = α + t:
    C_regulated = ∫₀^∞ exp(-tm²) H(α+t, r) dt
               = ∫_α^∞ exp(-(s-α)m²) H(s, r) ds   (substitute s = α + t)
               = exp(αm²) × ∫_α^∞ exp(-sm²) H(s, r) ds
               ≤ exp(αm²) × ∫₀^∞ exp(-sm²) H(s, r) ds   (since integrand ≥ 0)
               = exp(αm²) × C_Bessel(m, r)
               ≤ exp(m²) × C_Bessel(m, r)   (for α ≤ 1)
-/
lemma covarianceSchwingerRegulated_le_const_mul (m : ℝ) (hm : 0 < m) (r : ℝ) (hr : 0 < r)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    covarianceSchwingerRegulated α m r ≤ Real.exp (m^2) * covarianceSchwingerRep m r := by
  -- **Proof outline:**
  -- covarianceSchwingerRegulated α m r = ∫ t ∈ (0,∞), e^{-tm²} H(α+t, r) dt
  -- By change of variables s = α + t:
  --   = ∫ s ∈ (α,∞), e^{-(s-α)m²} H(s, r) ds
  --   = e^{αm²} ∫ s ∈ (α,∞), e^{-sm²} H(s, r) ds
  --   ≤ e^{αm²} ∫ s ∈ (0,∞), e^{-sm²} H(s, r) ds  (since integrand ≥ 0)
  --   = e^{αm²} × covarianceSchwingerRep m r
  --   ≤ e^{m²} × covarianceSchwingerRep m r  (for α ≤ 1)
  --
  -- The key steps are:
  -- 1. Change of variables s = α + t in Schwinger integral (Fubini-justified)
  -- 2. Monotonicity: ∫_{(α,∞)} ≤ ∫_{(0,∞)} for nonnegative integrands
  -- 3. Exponential bound: e^{αm²} ≤ e^{m²} for α ≤ 1
  unfold covarianceSchwingerRegulated covarianceSchwingerRep
  -- **Proof implementation:**
  -- The key insight is the change of variables s = α + t:
  --   ∫ t ∈ (0,∞), exp(-tm²) H(α+t, r) dt = ∫ s ∈ (α,∞), exp(-(s-α)m²) H(s, r) ds
  --   = exp(αm²) × ∫ s ∈ (α,∞), exp(-sm²) H(s, r) ds
  --
  -- Step 1: Apply change of variables
  have h_cov : ∫ t in Set.Ioi 0, Real.exp (-t * m^2) * heatKernelPositionSpace (α + t) r =
      Real.exp (α * m^2) * ∫ s in Set.Ioi α, Real.exp (-s * m^2) * heatKernelPositionSpace s r := by
    -- Substitution s = α + t, ds = dt
    -- exp(-(s-α)m²) = exp(αm²) × exp(-sm²)
    -- Use MeasurePreserving.setIntegral_preimage_emb with f(t) = t + α
    have h_preimage : (fun t => t + α) ⁻¹' Set.Ioi α = Set.Ioi 0 := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ioi, add_comm t α, lt_add_iff_pos_right]
    -- Change variables
    have h_subst : ∫ t in Set.Ioi 0, Real.exp (-(t + α) * m^2) * heatKernelPositionSpace (t + α) r =
        ∫ s in Set.Ioi α, Real.exp (-s * m^2) * heatKernelPositionSpace s r := by
      rw [← h_preimage]
      have h_mp : MeasureTheory.MeasurePreserving (fun t => t + α) volume volume :=
        MeasureTheory.measurePreserving_add_right volume α
      have h_me : MeasurableEmbedding (fun t => t + α) :=
        (Homeomorph.addRight α).measurableEmbedding
      exact h_mp.setIntegral_preimage_emb h_me
        (fun s => Real.exp (-s * m^2) * heatKernelPositionSpace s r) (Set.Ioi α)
    -- Rewrite exp(-t*m²) * H(α+t) = exp(αm²) * exp(-(t+α)*m²) * H(t+α)
    have h_exp_factor : ∀ t, Real.exp (-t * m^2) * heatKernelPositionSpace (α + t) r =
        Real.exp (α * m^2) * (Real.exp (-(t + α) * m^2) * heatKernelPositionSpace (t + α) r) := by
      intro t
      rw [add_comm α t, ← mul_assoc]
      congr 1
      rw [show -t * m^2 = α * m^2 + (-(t + α) * m^2) by ring, Real.exp_add]
    simp_rw [h_exp_factor, MeasureTheory.integral_const_mul (Real.exp (α * m^2)), h_subst]
  rw [h_cov]
  -- Step 2: Extend integral from (α,∞) to (0,∞) using nonnegativity
  have h_mono : ∫ s in Set.Ioi α, Real.exp (-s * m^2) * heatKernelPositionSpace s r ≤
      ∫ s in Set.Ioi 0, Real.exp (-s * m^2) * heatKernelPositionSpace s r := by
    -- Use setIntegral_mono_set: ∫_s ≤ ∫_t when s ⊆ t and f ≥ 0
    apply MeasureTheory.setIntegral_mono_set
    · exact integrableOn_exp_mul_heatKernel m hm r hr
    · -- f ≥ 0 a.e. on Ioi 0
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro s hs
      exact mul_nonneg (Real.exp_nonneg _) (heatKernelPositionSpace_nonneg s hs r)
    · -- Ioi α ⊆ Ioi 0 a.e.
      apply MeasureTheory.ae_of_all
      intro s hs
      exact Set.mem_Ioi.mpr (lt_of_lt_of_le hα (le_of_lt hs))
  -- Step 3: Bound the exponential prefactor
  have h_exp : Real.exp (α * m^2) ≤ Real.exp (m^2) := by
    apply Real.exp_le_exp_of_le
    calc α * m^2 ≤ 1 * m^2 := by apply mul_le_mul_of_nonneg_right hα1; exact sq_nonneg m
      _ = m^2 := one_mul _
  -- Step 4: Nonneg of the integral (for multiplication bound)
  have h_int_nonneg : 0 ≤ ∫ s in Set.Ioi 0, Real.exp (-s * m^2) * heatKernelPositionSpace s r := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro s hs
    apply mul_nonneg (Real.exp_nonneg _) (heatKernelPositionSpace_nonneg s hs r)
  -- Combine
  calc Real.exp (α * m^2) * ∫ s in Set.Ioi α, Real.exp (-s * m^2) * heatKernelPositionSpace s r
      ≤ Real.exp (α * m^2) * ∫ s in Set.Ioi 0, Real.exp (-s * m^2) * heatKernelPositionSpace s r :=
        by
        apply mul_le_mul_of_nonneg_left h_mono (Real.exp_nonneg _)
    _ ≤ Real.exp (m^2) * ∫ s in Set.Ioi 0, Real.exp (-s * m^2) * heatKernelPositionSpace s r := by
        apply mul_le_mul_of_nonneg_right h_exp h_int_nonneg

/-- **Domination bound:** For α ∈ (0, 1] and x ≠ y, the regulated covariance is bounded
    by a constant times the Bessel form:
      |freeCovarianceRegulated α m x y| ≤ exp(m²) × freeCovariance m x y

    This bound enables dominated convergence for the bilinear form.
-/
lemma freeCovariance_regulated_le_const_mul_freeCovariance (m : ℝ) (hm : 0 < m)
    (x y : SpaceTime) (hxy : x ≠ y) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    |freeCovarianceRegulated α m x y| ≤ Real.exp (m^2) * freeCovariance m x y := by
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  -- The regulated covariance is nonnegative (integral of positive integrand)
  have h_nonneg : 0 ≤ freeCovarianceRegulated α m x y := by
    rw [fubini_schwinger_fourier α hα m hm x y hxy]
    unfold covarianceSchwingerRegulated
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht
    apply mul_nonneg (Real.exp_nonneg _)
    exact heatKernelPositionSpace_nonneg (α + t) (by linarith [Set.mem_Ioi.mp ht]) ‖x - y‖
  rw [abs_of_nonneg h_nonneg]
  -- Use Fubini to convert to Schwinger representation
  rw [fubini_schwinger_fourier α hα m hm x y hxy]
  -- Apply the Schwinger bound
  have h_bound := covarianceSchwingerRegulated_le_const_mul m hm ‖x - y‖ hr α hα hα1
  -- Convert Schwinger to Bessel
  calc covarianceSchwingerRegulated α m ‖x - y‖
      ≤ Real.exp (m^2) * covarianceSchwingerRep m ‖x - y‖ := h_bound
    _ = Real.exp (m^2) * freeCovariance m x y := by
        rw [covarianceSchwingerRep_eq_freeCovarianceBessel m hm x y hxy]

/-- The Gaussian regulator exp(-α‖k‖²) is integrable on SpaceTime for α > 0. -/
lemma gaussian_regulator_integrable' (α : ℝ) (hα : 0 < α) :
    Integrable (fun k : SpaceTime => Real.exp (-α * ‖k‖^2)) volume := by
  have hα_re : (0 : ℝ) < (α : ℂ).re := by simp [hα]
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := SpaceTime) hα_re 0 0
  simp only [zero_mul, add_zero] at h
  have h' : Integrable (fun k : SpaceTime => (Real.exp (-α * ‖k‖^2) : ℂ)) volume := by
    have heq : ∀ k : SpaceTime, Complex.exp (-↑α * ↑‖k‖ ^ 2) = ↑(Real.exp (-α * ‖k‖ ^ 2)) := by
      intro k
      simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_pow,
        Complex.ofReal_exp]
    simp_rw [heq] at h
    exact h
  exact h'.re

/-- The regulated covariance is uniformly bounded for all (x, y).

    Since |exp(-ik·(x-y))| = 1 and the Gaussian-regulated propagator is integrable,
    we have |C_α(x,y)| ≤ ∫ exp(-α‖k‖²) * P(k) / (2π)^d ≤ ∫ exp(-α‖k‖²) / (m² (2π)^d) < ∞.

    **Proof sketch:**
    - The Fourier integrand has |phase| = 1 and |amplitude| ≤ exp(-α‖k‖²)/(m²(2π)^d)
    - The Gaussian is integrable, giving the uniform bound M = ∫ exp(-α‖k‖²)/(m²(2π)^d) dk
    - Since C_α is the real part of the integral, |C_α| ≤ M for all (x,y)
-/
lemma freeCovariance_regulated_uniformly_bounded (α : ℝ) (hα : 0 < α) (m : ℝ) (hm : 0 < m) :
    ∃ M > 0, ∀ x y : SpaceTime, |freeCovarianceRegulated α m x y| ≤ M := by
  -- The bound is ∫ exp(-α‖k‖²) / (m² (2π)^d) dk
  -- This is finite since exp(-α‖k‖²) is integrable (Gaussian)
  use ∫ k : SpaceTime, Real.exp (-α * ‖k‖^2) / (m^2 * (2 * Real.pi) ^ STDimension)
  constructor
  · -- M > 0 since the integrand is positive and integrable
    -- The Gaussian integral ∫ exp(-α‖k‖²) is positive (integrand > 0 everywhere)
    -- Dividing by positive constant m²(2π)^d preserves positivity
    have h_gauss_int := gaussian_regulator_integrable' α hα
    have h_pos : ∀ k : SpaceTime, 0 < Real.exp (-α * ‖k‖^2) / (m^2 * (2 * Real.pi) ^ STDimension)
      := by
      intro k; apply div_pos (Real.exp_pos _); positivity
    -- Rewrite as constant * exp, then use integral_exp_pos
    have h_const_pos : 0 < 1 / (m^2 * (2 * Real.pi) ^ STDimension) := by positivity
    have h_eq : ∀ k : SpaceTime, Real.exp (-α * ‖k‖^2) / (m^2 * (2 * Real.pi) ^ STDimension) =
        (1 / (m^2 * (2 * Real.pi) ^ STDimension)) * Real.exp (-α * ‖k‖^2) := by
      intro k; ring
    simp_rw [h_eq]
    rw [MeasureTheory.integral_const_mul]
    apply mul_pos h_const_pos
    exact MeasureTheory.integral_exp_pos h_gauss_int
  · -- |C_α(x,y)| ≤ M by norm bounds on the Fourier integral
    intro x y
    -- C_α is the .re of a complex integral. The bound follows from:
    -- 1. |.re z| ≤ ‖z‖ (abs_re_le_norm)
    -- 2. ‖∫ f‖ ≤ ∫ ‖f‖ (norm_integral_le_integral_norm)
    -- 3. ‖amplitude × phase‖ = |amplitude| × 1 (phase has norm 1)
    -- 4. |amplitude| = exp(-α‖k‖²) × prop(k) / (2π)^d ≤ exp(-α‖k‖²) / (m²(2π)^d)
    --    using prop(k) = 1/(‖k‖² + m²) ≤ 1/m²
    -- 5. Integrate to get M = ∫ exp(-α‖k‖²) / (m²(2π)^d) dk
    unfold freeCovarianceRegulated
    -- Step 1: |Re z| ≤ ‖z‖
    calc |_| ≤ ‖∫ k : SpaceTime, (↑(Real.exp (-α * ‖k‖^2) *
        freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension) : ℂ) *
        Complex.exp (-Complex.I * ↑⟪k, x - y⟫_ℝ)‖ := Complex.abs_re_le_norm _
      -- Step 2: ‖∫ f‖ ≤ ∫ ‖f‖
      _ ≤ ∫ k : SpaceTime, ‖(↑(Real.exp (-α * ‖k‖^2) *
          freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension) : ℂ) *
          Complex.exp (-Complex.I * ↑⟪k, x - y⟫_ℝ)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      -- Step 3: ‖a * phase‖ = |a| since ‖phase‖ = 1
      _ = ∫ k : SpaceTime, |Real.exp (-α * ‖k‖^2) *
          freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension| := by
        congr 1; ext k
        rw [Complex.norm_mul]
        rw [norm_exp_neg_I_mul_real, mul_one]
        simp only [Complex.norm_real]
        exact norm_eq_abs _
      -- Step 4: |exp * prop / norm| ≤ exp / (m² * norm) since prop ≤ 1/m²
      _ ≤ ∫ k : SpaceTime, Real.exp (-α * ‖k‖^2) / (m^2 * (2 * Real.pi) ^ STDimension) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · -- nonneg integrand
          apply Filter.Eventually.of_forall; intro k; positivity
        · -- integrability of RHS
          have h_eq : ∀ k : SpaceTime, Real.exp (-α * ‖k‖^2) / (m^2 * (2 * Real.pi) ^ STDimension) =
              (1 / (m^2 * (2 * Real.pi) ^ STDimension)) * Real.exp (-α * ‖k‖^2) := fun k => by ring
          simp_rw [h_eq]
          exact Integrable.const_mul (gaussian_regulator_integrable' α hα) _
        · -- pointwise bound
          apply Filter.Eventually.of_forall
          intro k
          simp only
          rw [abs_of_nonneg]
          · -- exp * prop / norm ≤ exp / (m² * norm) iff prop ≤ 1/m²
            have h_prop_bound : freePropagatorMomentum m k ≤ 1 / m^2 := by
              unfold freePropagatorMomentum
              have h_denom : m^2 ≤ ‖k‖^2 + m^2 := by nlinarith [sq_nonneg ‖k‖]
              apply div_le_div_of_nonneg_left _ (sq_pos_of_pos hm) h_denom
              nlinarith [sq_nonneg ‖k‖]
            calc Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension
                ≤ Real.exp (-α * ‖k‖^2) * (1 / m^2) / (2 * Real.pi) ^ STDimension := by
                    apply div_le_div_of_nonneg_right _ (by positivity)
                    apply mul_le_mul_of_nonneg_left h_prop_bound (Real.exp_pos _).le
              _ = Real.exp (-α * ‖k‖^2) / (m^2 * (2 * Real.pi) ^ STDimension) := by ring
          · -- nonneg
            have h_prop_pos : 0 < freePropagatorMomentum m k := by
              unfold freePropagatorMomentum
              apply div_pos one_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hm))
            apply div_nonneg (mul_nonneg (Real.exp_pos _).le h_prop_pos.le) (by positivity)

/-- The regulated covariance is AEStronglyMeasurable on the product space.

    **Proof:** The Schwinger representation is an integral ∫_k exp(-α‖k‖²) * prop(k) * cos(k·(x-y)).
    The integrand is continuous in (x, y) for fixed k, hence measurable.
    By Fubini theorem structure, the integral inherits measurability in (x, y).
-/
lemma aestronglyMeasurable_freeCovariance_regulated (α : ℝ) (hα : 0 < α) (m : ℝ) (hm : 0 < m) :
    AEStronglyMeasurable
      (fun p : SpaceTime × SpaceTime => (freeCovarianceRegulated α m p.1 p.2 : ℂ))
      (volume.prod volume) := by
  -- The regulated covariance is continuous in (x, y) via dominated convergence for continuity.
  -- We use MeasureTheory.continuous_of_dominated: the integrand
  --   (x, y, k) ↦ exp(-α‖k‖²) * propagator(k) * phase(k, x-y)
  -- is continuous in (x, y) for fixed k, with dominator exp(-α‖k‖²)/m² independent of (x, y).
  -- Continuous functions are AEStronglyMeasurable.
  -- Inline proof of propagator positivity (avoiding forward reference)
  have h_prop_pos : ∀ k : SpaceTime, 0 < freePropagatorMomentum m k := by
    intro k; unfold freePropagatorMomentum
    apply div_pos one_pos
    apply add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hm)
  -- Inline proof of propagator continuity
  have h_prop_cont : Continuous (freePropagatorMomentum m) := by
    unfold freePropagatorMomentum
    apply Continuous.div continuous_const (continuous_norm.pow 2 |>.add continuous_const)
    intro k; exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg ‖k‖) (sq_pos_of_pos hm))
  have h_cont : Continuous (fun p : SpaceTime × SpaceTime => freeCovarianceRegulated α m p.1 p.2)
    := by
    unfold freeCovarianceRegulated
    simp only
    -- Apply continuous_of_dominated: X = SpaceTime × SpaceTime, integrating over SpaceTime
    let F := fun p : SpaceTime × SpaceTime => fun k : SpaceTime =>
      Complex.ofReal (Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^
        STDimension) *
      Complex.exp (-Complex.I * Complex.ofReal ⟪k, p.1 - p.2⟫_ℝ)
    let bound := fun k : SpaceTime =>
      Real.exp (-α * ‖k‖^2) / (m^2 * (2 * Real.pi) ^ STDimension)
    have h_meas : ∀ p : SpaceTime × SpaceTime, AEStronglyMeasurable (F p) volume := by
      intro p
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul
      · apply Complex.continuous_ofReal.comp
        apply Continuous.div_const
        apply Continuous.mul (by fun_prop) h_prop_cont
      · apply Complex.continuous_exp.comp
        apply Continuous.mul continuous_const
        apply Complex.continuous_ofReal.comp
        apply Continuous.inner continuous_id continuous_const
    have h_bound : ∀ p : SpaceTime × SpaceTime, ∀ᵐ k ∂volume, ‖F p k‖ ≤ bound k := by
      intro p
      apply Filter.Eventually.of_forall
      intro k
      simp only [F, bound]
      rw [Complex.norm_mul, Complex.norm_real]
      rw [norm_exp_neg_I_mul_real, mul_one]
      have h_prop_bound : freePropagatorMomentum m k ≤ 1 / m^2 := by
        simp only [freePropagatorMomentum]
        apply one_div_le_one_div_of_le (by positivity : 0 < m ^ 2)
        linarith [sq_nonneg ‖k‖]
      have h_prop_nonneg : 0 ≤ freePropagatorMomentum m k := le_of_lt (h_prop_pos k)
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (-α * ‖k‖ ^ 2) * freePropagatorMomentum
        m k /
          (2 * Real.pi) ^ STDimension)]
      calc Real.exp (-α * ‖k‖ ^ 2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension
          ≤ Real.exp (-α * ‖k‖ ^ 2) * (1 / m^2) / (2 * Real.pi) ^ STDimension := by
            apply div_le_div_of_nonneg_right
            · apply mul_le_mul_of_nonneg_left h_prop_bound (Real.exp_nonneg _)
            · positivity
        _ = Real.exp (-α * ‖k‖ ^ 2) / (m^2 * (2 * Real.pi) ^ STDimension) := by ring
    have h_bound_int : Integrable bound volume := (gaussian_regulator_integrable' α hα).div_const _
    have h_cont_k : ∀ᵐ k ∂volume, Continuous fun p => F p k := by
      apply Filter.Eventually.of_forall
      intro k
      simp only [F]
      apply Continuous.mul continuous_const
      apply Complex.continuous_exp.comp
      apply Continuous.mul continuous_const
      apply Complex.continuous_ofReal.comp
      apply Continuous.inner continuous_const (continuous_fst.sub continuous_snd)
    have h := MeasureTheory.continuous_of_dominated h_meas h_bound h_bound_int h_cont_k
    exact Complex.continuous_re.comp h
  -- The goal is AEStronglyMeasurable of the Complex version, so compose with ofReal
  exact (Complex.continuous_ofReal.comp h_cont).aestronglyMeasurable

/-- The unregulated Bessel covariance is AEStronglyMeasurable on the product space.

    **Proof:** The Bessel covariance is continuous on the off-diagonal set {(x,y) | x ≠ y},
    which has full measure in the product space (diagonal has measure zero).
    Continuity implies strong measurability, hence AEStronglyMeasurable.
-/
lemma aestronglyMeasurable_freeCovariance (m : ℝ) [Fact (0 < m)] :
    AEStronglyMeasurable
      (fun p : SpaceTime × SpaceTime => (freeCovariance m p.1 p.2 : ℂ))
      (volume.prod volume) := by
  -- The Bessel covariance is continuous off the diagonal, and the diagonal has measure zero.
  -- Strategy: Show continuity on the off-diagonal (which is conull), then lift to full space.
  have hm : 0 < m := Fact.out
  -- Step 1: Define the off-diagonal set (complement of diagonal)
  let S := (Set.diagonal SpaceTime)ᶜ
  have hS_meas : MeasurableSet S := measurableSet_diagonal.compl
  -- Step 2: Show the diagonal has measure zero (NoAtoms for Lebesgue measure)
  have h_diag_null : (volume.prod volume) (Set.diagonal SpaceTime) = 0 := by
    apply MeasureTheory.Measure.measure_prod_null_of_ae_null
    · exact measurableSet_diagonal
    · -- For each x, the slice {y | (x,y) ∈ diagonal} = {x} has measure zero
      -- Need: (fun x => volume {y | (x, y) ∈ diagonal}) =ᶠ[ae volume] 0
      -- The slice is {y | x = y} = {x}, which has measure zero (NoAtoms)
      rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      intro x _
      simp only [Set.diagonal, Set.preimage, Set.mem_setOf_eq, Pi.zero_apply]
      have h_eq : {y : SpaceTime | x = y} = {x} := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, eq_comm]
      rw [h_eq]
      exact measure_singleton x
  -- Step 3: Helper lemma - AEStronglyMeasurable on a conull set implies full AEStronglyMeasurable
  have h_lift : ∀ {f : SpaceTime × SpaceTime → ℂ} {s : Set (SpaceTime × SpaceTime)},
      MeasurableSet s → (volume.prod volume) sᶜ = 0 →
      AEStronglyMeasurable f ((volume.prod volume).restrict s) →
      AEStronglyMeasurable f (volume.prod volume) := by
    intro f s hs_meas hs_null hf
    obtain ⟨g, hg_meas, hfg⟩ := hf
    refine ⟨g, hg_meas, ?_⟩
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hs_meas] at hfg
    filter_upwards [hfg, compl_mem_ae_iff.mpr hs_null] with p hps hpnotin
    simp only [Set.mem_compl_iff, not_not] at hpnotin
    exact hps hpnotin
  -- Step 4: Apply the lift with off-diagonal set
  apply h_lift hS_meas
  · rw [compl_compl]; exact h_diag_null
  -- Step 5: Show continuity on the off-diagonal
  have hS_open : IsOpen S := isOpen_compl_iff.mpr isClosed_diagonal
  have hcont : ContinuousOn (fun p : SpaceTime × SpaceTime => (freeCovariance m p.1 p.2 : ℂ)) S :=
    by
    apply Complex.continuous_ofReal.comp_continuousOn
    -- freeCovariance m p.1 p.2 = (m / (4π²‖p.1-p.2‖)) * K₁(m‖p.1-p.2‖) on off-diagonal
    -- This factors as g ∘ (‖fst - snd‖) where g(r) = (m/(4π²r)) * K₁(mr)
    have h_norm_cont : Continuous (fun p : SpaceTime × SpaceTime => ‖p.1 - p.2‖) :=
      continuous_norm.comp (continuous_fst.sub continuous_snd)
    have h_formula_cont : ContinuousOn (fun r : ℝ => (m / (4 * Real.pi^2 * r)) * besselK1 (m * r))
        (Set.Ioi 0) := by
      apply ContinuousOn.mul
      · apply ContinuousOn.div continuousOn_const
        · exact continuousOn_const.mul continuousOn_id
        · intro r hr; simp only [Set.mem_Ioi] at hr
          exact mul_ne_zero (by positivity : (4 : ℝ) * Real.pi^2 ≠ 0) (ne_of_gt hr)
      · apply besselK1_continuousOn.comp (continuousOn_const.mul continuousOn_id)
        intro r hr; simp only [Set.mem_Ioi] at hr
        exact mul_pos hm hr
    -- Show the composed function is continuous on S
    -- On S, the function equals the formula (since ‖p.1 - p.2‖ ≠ 0)
    have h_eq : Set.EqOn (fun p => freeCovariance m p.1 p.2)
        (fun p => (m / (4 * Real.pi^2 * ‖p.1 - p.2‖)) * besselK1 (m * ‖p.1 - p.2‖)) S := by
      intro p hp
      rw [Set.mem_compl_iff, Set.mem_diagonal_iff] at hp
      have hr_ne : ‖p.1 - p.2‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)
      unfold freeCovariance freeCovarianceBessel
      simp only [hr_ne, ↓reduceIte]
    -- The formula is continuous on S (composition of continuous functions)
    have h_comp_cont : ContinuousOn
        (fun p : SpaceTime × SpaceTime =>
          (m / (4 * Real.pi^2 * ‖p.1 - p.2‖)) *
            besselK1 (m * ‖p.1 - p.2‖)) S := by
      apply h_formula_cont.comp h_norm_cont.continuousOn
      intro p hp
      rw [Set.mem_compl_iff, Set.mem_diagonal_iff] at hp
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hp)
    exact h_comp_cont.congr h_eq
  -- Step 6: ContinuousOn on measurable set implies AEStronglyMeasurable on restriction
  exact hcont.aestronglyMeasurable hS_meas

/-- The bilinear form f(x) * C_α(x,y) * g(y) is integrable for regulated covariance
with Schwartz f, g.

    Since C_α is uniformly bounded and f, g are Schwartz (hence integrable), the product is
    integrable.

    **Proof:** With bound M from `freeCovariance_regulated_uniformly_bounded`:
    |f(x) * C_α(x,y) * g(y)| ≤ M * |f(x)| * |g(y)|
    The RHS is integrable since f, g ∈ L¹ (Schwartz functions are integrable).
-/
theorem freeCovariance_regulated_bilinear_integrable (α : ℝ) (hα : 0 < α) (m : ℝ) [Fact (0 < m)]
    (f g : TestFunctionℂ) :
    Integrable (fun p : SpaceTime × SpaceTime =>
      (f p.1) * (freeCovarianceRegulated α m p.1 p.2 : ℂ) * (g p.2)) volume := by
  have hm : 0 < m := Fact.out
  obtain ⟨M, hM_pos, hM_bound⟩ := freeCovariance_regulated_uniformly_bounded α hα m hm
  -- The bound is M * ‖f(x)‖ * ‖g(y)‖, integrable since f, g are Schwartz
  set bound : SpaceTime × SpaceTime → ℝ := fun p => M * ‖f p.1‖ * ‖g p.2‖ with hbound_def
  -- Schwartz functions are integrable
  have hf_int : Integrable (fun x => ‖f x‖) volume := (SchwartzMap.integrable f).norm
  have hg_int : Integrable (fun y => ‖g y‖) volume := (SchwartzMap.integrable g).norm
  -- Product integrability: M * ‖f(x)‖ * ‖g(y)‖ is integrable on product space
  have hbound_int : Integrable bound (volume.prod volume) := by
    have hprod := Integrable.mul_prod hf_int hg_int
    convert hprod.const_mul M using 1
    ext p; simp only [bound, mul_assoc]
  -- AE Strong Measurability: Schwartz functions are continuous hence strongly measurable
  -- The product f(x) * C_α(x,y) * g(y) is AEStronglyMeasurable by product of:
  -- 1. f ∘ fst is strongly measurable (Schwartz is continuous)
  -- 2. C_α ∘ (fst, snd) is strongly measurable (Schwinger integral is measurable)
  -- 3. g ∘ snd is strongly measurable (Schwartz is continuous)
  have hmeas : AEStronglyMeasurable
      (fun p : SpaceTime × SpaceTime => f p.1 * (freeCovarianceRegulated α m p.1 p.2 : ℂ) * g p.2)
      (volume.prod volume) := by
    have hf_meas : StronglyMeasurable (fun p : SpaceTime × SpaceTime => f p.1) :=
      (f.continuous.comp continuous_fst).stronglyMeasurable
    have hg_meas : StronglyMeasurable (fun p : SpaceTime × SpaceTime => g p.2) :=
      (g.continuous.comp continuous_snd).stronglyMeasurable
    -- The regulated covariance is bounded and AEStronglyMeasurable as a Schwinger integral
    -- Proof: freeCovarianceRegulated is defined as an integral ∫_k exp(-α‖k‖²) * prop(k) *
    -- cos(k·(x-y))
    -- This is measurable in (x, y) by Fubini and continuity of the integrand in (x, y).
    have hC_meas : AEStronglyMeasurable
        (fun p : SpaceTime × SpaceTime => (freeCovarianceRegulated α m p.1 p.2 : ℂ))
        (volume.prod volume) := by
      -- Standard measure theory: integral of measurable function is measurable in parameters
      -- The Schwinger integrand is continuous in (x, y) (cosine term), hence measurable
      -- and the integral inherits measurability via Fubini theorem structure.
      -- Technical proof: the covariance is continuous on SpaceTime × SpaceTime
      -- (off-diagonal; diagonal has measure zero), hence strongly measurable.
      exact aestronglyMeasurable_freeCovariance_regulated α hα m hm
    exact (hf_meas.aestronglyMeasurable.mul hC_meas).mul hg_meas.aestronglyMeasurable
  -- Norm bound: ‖f(x) * C_α * g(y)‖ ≤ M * ‖f(x)‖ * ‖g(y)‖
  have hnorm : ∀ᵐ p ∂(volume.prod volume), ‖f p.1 * (freeCovarianceRegulated α m p.1 p.2 : ℂ) * g
    p.2‖ ≤ bound p := by
    apply Eventually.of_forall
    intro p
    rw [norm_mul, norm_mul, Complex.norm_real]
    calc ‖f p.1‖ * |freeCovarianceRegulated α m p.1 p.2| * ‖g p.2‖
        ≤ ‖f p.1‖ * M * ‖g p.2‖ := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left (hM_bound p.1 p.2) (norm_nonneg _)
          · exact norm_nonneg _
      _ = M * ‖f p.1‖ * ‖g p.2‖ := by ring
  -- Apply Integrable.mono'
  exact Integrable.mono' hbound_int hmeas hnorm

/-- The free covariance kernel (alternative name for compatibility) -/
noncomputable def freeCovarianceKernel (m : ℝ) (z : SpaceTime) : ℝ :=
  freeCovariance m 0 z

/-- The Bessel covariance kernel is L¹ (integrable on SpaceTime).

    In d=4 dimensions with f(r) = (m/(4π²r)) K₁(mr):
    ∫_{ℝ⁴} |K(z)| dz ↔ ∫₀^∞ r³ |f(r)| dr = (m/4π²) ∫₀^∞ r² K₁(mr) dr

    This is finite by `radial_besselK1_integrable`.
-/
lemma freeCovarianceKernel_integrable (m : ℝ) (hm : 0 < m) :
    Integrable (freeCovarianceKernel m) volume := by
  -- The kernel is a radial function: K(z) = f(‖z‖) where
  -- f(r) = (m/(4π²r)) K₁(mr) for r > 0, f(0) = 0
  let f : ℝ → ℝ := fun r => if r = 0 then 0 else (m / (4 * Real.pi^2 * r)) * besselK1 (m * r)
  have h_kernel_eq : ∀ z : SpaceTime, freeCovarianceKernel m z = f ‖z‖ := by
    intro z
    simp only [freeCovarianceKernel, freeCovariance, freeCovarianceBessel]
    simp only [zero_sub, norm_neg]
    rfl
  rw [show (freeCovarianceKernel m) = (fun z => f ‖z‖) from funext h_kernel_eq]
  rw [integrable_fun_norm_addHaar volume (f := f)]
  have h_dim : Module.finrank ℝ SpaceTime = 4 := finrank_euclideanSpace
  have h_intgd : ∀ r ∈ Set.Ioi (0 : ℝ), r ^ (Module.finrank ℝ SpaceTime - 1) • f r =
      (m / (4 * Real.pi^2)) * (r ^ 2 * besselK1 (m * r)) := by
    intro r hr
    simp only [h_dim, f, Set.mem_Ioi] at hr ⊢
    simp only [ne_of_gt hr, ↓reduceIte, smul_eq_mul]
    have hr_ne : r ≠ 0 := ne_of_gt hr
    field_simp
  rw [integrableOn_congr_fun h_intgd measurableSet_Ioi]
  exact (radial_besselK1_integrable m hm).const_mul (m / (4 * Real.pi^2))

/-- **Polynomial decay bound for the free covariance kernel.**

    The free covariance kernel satisfies |C(z)| ≤ C/‖z‖² for some C > 0.

    This uses the Bessel function bounds:
    - Near origin (mr ≤ 1): K₁(mr) ≤ (cosh(1) + 2)/(mr), giving C(z) ≤ (cosh(1)+2)/(4π²r²)
    - Far from origin (mr > 1): K₁(mr) ≤ (sinh(1) + 2)·exp(-mr), decays faster than 1/r²

    The bound is essential for OS1 local integrability in d=4 dimensions.
-/
lemma freeCovarianceKernel_decay_bound (m : ℝ) (hm : 0 < m) :
    ∃ C : ℝ, C > 0 ∧ ∀ z : SpaceTime, |freeCovarianceKernel m z| ≤ C * ‖z‖ ^ (-2 : ℝ) := by
  -- Define the constant C = (cosh(1) + 2) / (4π²)
  -- This works for both near and far from origin
  set C := (Real.cosh 1 + 2) / (4 * Real.pi^2) with hC_def
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, ?_⟩
  intro z
  by_cases hz : ‖z‖ = 0
  · -- z = 0: kernel is 0, bound is trivially satisfied since 0^(-2) = 0
    have hz' : z = 0 := norm_eq_zero.mp hz
    simp only [hz', norm_zero, freeCovarianceKernel, freeCovariance, freeCovarianceBessel,
               sub_zero, if_true, abs_zero]
    rw [Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0), mul_zero]
  · -- z ≠ 0: use Bessel bounds
    have hr_pos : 0 < ‖z‖ := norm_pos_iff.mpr (norm_ne_zero_iff.mp hz)
    -- Rewrite kernel in terms of Bessel function
    have h_kernel : freeCovarianceKernel m z = (m / (4 * Real.pi^2 * ‖z‖)) * besselK1 (m * ‖z‖) :=
      by
      simp only [freeCovarianceKernel, freeCovariance, freeCovarianceBessel, zero_sub, norm_neg, hz,
                 if_false]
    rw [h_kernel]
    -- The kernel is nonnegative for m > 0 and z ≠ 0
    have hK_pos : 0 < besselK1 (m * ‖z‖) := besselK1_pos (m * ‖z‖) (by positivity)
    have h_kernel_nonneg : 0 ≤ (m / (4 * Real.pi^2 * ‖z‖)) * besselK1 (m * ‖z‖) := by
      apply mul_nonneg
      · apply div_nonneg hm.le; nlinarith [Real.pi_pos]
      · exact hK_pos.le
    rw [abs_of_nonneg h_kernel_nonneg]
    -- Use the near-origin bound K₁(z) ≤ (cosh(1) + 2)/z for z > 0
    -- This actually works for all z > 0 (even large z), since K₁ decays exponentially for large z
    by_cases hmr_small : m * ‖z‖ ≤ 1
    · -- Case: mr ≤ 1, use besselK1_near_origin_bound
      have hmr_pos : 0 < m * ‖z‖ := by positivity
      have h_bessel_bound := besselK1_near_origin_bound (m * ‖z‖) hmr_pos hmr_small
      calc (m / (4 * Real.pi^2 * ‖z‖)) * besselK1 (m * ‖z‖)
          ≤ (m / (4 * Real.pi^2 * ‖z‖)) * ((Real.cosh 1 + 2) / (m * ‖z‖)) := by
              apply mul_le_mul_of_nonneg_left h_bessel_bound
              apply div_nonneg hm.le; nlinarith [Real.pi_pos]
        _ = (Real.cosh 1 + 2) / (4 * Real.pi^2 * ‖z‖^2) := by
              field_simp [ne_of_gt hr_pos, ne_of_gt hm]
        _ = C * ‖z‖^(-2 : ℝ) := by
              rw [hC_def]
              have h_rpow : ‖z‖ ^ (-2 : ℝ) = (‖z‖ ^ (2 : ℝ))⁻¹ := by
                rw [rpow_neg (norm_nonneg z)]
              rw [h_rpow, rpow_two]
              field_simp [ne_of_gt hr_pos]
    · -- Case: mr > 1, use besselK1_asymptotic
      push Not at hmr_small
      have hmr_ge : 1 ≤ m * ‖z‖ := le_of_lt hmr_small
      have h_bessel_bound := besselK1_asymptotic (m * ‖z‖) hmr_ge
      -- For mr ≥ 1: exp(-mr) ≤ 1/(mr), so K₁(mr) ≤ (sinh 1 + 2)/(mr), giving the 1/r² bound.
      -- Since cosh 1 + 2 > sinh 1 + 2, the constant C works for both cases.
      have hmr_pos : 0 < m * ‖z‖ := by positivity
      have h_exp_bound : Real.exp (-(m * ‖z‖)) ≤ 1 / (m * ‖z‖) := by
        rw [one_div]
        -- Use x ≤ exp(x), which is a consequence of 1 + x ≤ exp(x)
        have h1 : m * ‖z‖ ≤ Real.exp (m * ‖z‖) := by
          have := add_one_le_exp (m * ‖z‖)
          linarith
        -- Invert the inequality (anti-monotonicity of inverse)
        have h2 : (Real.exp (m * ‖z‖))⁻¹ ≤ (m * ‖z‖)⁻¹ := inv_anti₀ hmr_pos h1
        calc Real.exp (-(m * ‖z‖)) = (Real.exp (m * ‖z‖))⁻¹ := by rw [Real.exp_neg]
          _ ≤ (m * ‖z‖)⁻¹ := h2
      have h_K_bound : besselK1 (m * ‖z‖) ≤ (Real.sinh 1 + 2) / (m * ‖z‖) := by
        calc besselK1 (m * ‖z‖) ≤ (Real.sinh 1 + 2) * Real.exp (-(m * ‖z‖)) := h_bessel_bound
          _ ≤ (Real.sinh 1 + 2) * (1 / (m * ‖z‖)) := by
              apply mul_le_mul_of_nonneg_left h_exp_bound
              have : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr (by norm_num : (0:ℝ) < 1)
              linarith
          _ = (Real.sinh 1 + 2) / (m * ‖z‖) := by ring
      have h_sinh_le_cosh : Real.sinh 1 + 2 ≤ Real.cosh 1 + 2 := by
        have h1 : Real.sinh 1 = (Real.exp 1 - Real.exp (-1)) / 2 := Real.sinh_eq (1:ℝ)
        have h2' : Real.cosh 1 = (Real.exp 1 + Real.exp (-1)) / 2 := Real.cosh_eq (1:ℝ)
        rw [h1, h2']
        linarith [Real.exp_pos (-1 : ℝ)]
      calc (m / (4 * Real.pi^2 * ‖z‖)) * besselK1 (m * ‖z‖)
          ≤ (m / (4 * Real.pi^2 * ‖z‖)) * ((Real.sinh 1 + 2) / (m * ‖z‖)) := by
              apply mul_le_mul_of_nonneg_left h_K_bound
              apply div_nonneg hm.le; nlinarith [Real.pi_pos]
        _ = (Real.sinh 1 + 2) / (4 * Real.pi^2 * ‖z‖^2) := by
              field_simp [ne_of_gt hr_pos, ne_of_gt hm]
        _ ≤ (Real.cosh 1 + 2) / (4 * Real.pi^2 * ‖z‖^2) := by
              apply div_le_div_of_nonneg_right h_sinh_le_cosh
              nlinarith [Real.pi_pos, sq_nonneg ‖z‖]
        _ = C * ‖z‖^(-2 : ℝ) := by
              rw [hC_def]
              have h_rpow : ‖z‖ ^ (-2 : ℝ) = (‖z‖ ^ (2 : ℝ))⁻¹ := by
                rw [rpow_neg (norm_nonneg z)]
              rw [h_rpow, rpow_two]
              field_simp [ne_of_gt hr_pos]

/-- **Exponential decay bound for the free covariance.**

    For m > 0 and u, v ∈ ℝ⁴ with m‖u - v‖ ≥ 1:
      |C(u, v)| ≤ (m² · (sinh 1 + 2) / (4π²)) · e^{-m‖u-v‖}

    This combines:
    - The covariance formula: C(u,v) = (m / (4π² ‖u-v‖)) · K₁(m‖u-v‖)
    - The Bessel asymptotic: K₁(z) ≤ (sinh 1 + 2) · e^{-z} for z ≥ 1
    - The condition m‖u-v‖ ≥ 1, which implies ‖u-v‖ ≥ 1/m, so m/‖u-v‖ ≤ m²
-/
lemma freeCovariance_exponential_bound (m : ℝ) (hm : 0 < m) (u v : SpaceTime)
    (h_sep : 1 ≤ m * ‖u - v‖) :
    |freeCovariance m u v| ≤ (m^2 * (Real.sinh 1 + 2) / (4 * Real.pi^2)) * Real.exp (-m * ‖u - v‖)
       := by
  -- The covariance is positive for distinct points, so |C| = C
  have huv : u ≠ v := by
    intro heq
    simp [heq] at h_sep
    linarith
  rw [abs_of_pos (freeCovarianceBessel_pos m hm u v huv)]
  -- Let r = ‖u - v‖
  set r := ‖u - v‖ with hr_def
  -- From h_sep: mr ≥ 1, so r > 0
  have hmr_ge1 : 1 ≤ m * r := h_sep
  have hr_pos : 0 < r := by
    by_contra h_neg
    push Not at h_neg
    have : m * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm) h_neg
    linarith
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  -- Unfold the covariance: C(u,v) = (m / (4π²r)) · K₁(mr)
  unfold freeCovarianceBessel
  simp only [← hr_def, hr_ne, if_false]
  -- Use the Bessel asymptotic bound: K₁(mr) ≤ (sinh 1 + 2) · e^{-mr}
  have hK1_bound := besselK1_asymptotic (m * r) hmr_ge1
  -- Key step: m/r ≤ m² because r ≥ 1/m (from mr ≥ 1)
  have hr_ge_inv : 1/m ≤ r := by
    rwa [one_div, inv_le_iff_one_le_mul₀ hm, mul_comm]
  have hm_over_r_le : m / r ≤ m^2 := by
    rw [div_le_iff₀ hr_pos, sq]
    calc m = m * 1 := by ring
      _ ≤ m * (m * r) := by nlinarith
      _ = m * m * r := by ring
  -- Combine: (m / (4π²r)) · K₁(mr) ≤ (m / (4π²r)) · (sinh 1 + 2) · e^{-mr}
  --                                 ≤ (m² / (4π²)) · (sinh 1 + 2) · e^{-mr}
  have hpi_sq_pos : 0 < 4 * Real.pi^2 := by positivity
  have hcoeff_pos : 0 < m / (4 * Real.pi^2 * r) := by positivity
  calc m / (4 * Real.pi^2 * r) * besselK1 (m * r)
      ≤ m / (4 * Real.pi^2 * r) * ((Real.sinh 1 + 2) * Real.exp (-(m * r))) := by
          apply mul_le_mul_of_nonneg_left hK1_bound (le_of_lt hcoeff_pos)
    _ = (m / r) * (Real.sinh 1 + 2) / (4 * Real.pi^2) * Real.exp (-(m * r)) := by ring
    _ ≤ m^2 * (Real.sinh 1 + 2) / (4 * Real.pi^2) * Real.exp (-(m * r)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          apply div_le_div_of_nonneg_right _ (le_of_lt hpi_sq_pos)
          apply mul_le_mul_of_nonneg_right hm_over_r_le
          positivity
    _ = m^2 * (Real.sinh 1 + 2) / (4 * Real.pi^2) * Real.exp (-m * r) := by
          congr 1
          ring_nf

/-! ### Fact versions of decay bounds

These are convenience wrappers that use `[Fact (0 < m)]` instead of explicit `(hm : 0 < m)`,
for compatibility with code that uses the Fact type class.
-/

/-- Exponential bound with `[Fact (0 < m)]` type class. -/
lemma freeCovariance_exponential_bound' (m : ℝ) [Fact (0 < m)] (u v : SpaceTime)
    (h_sep : 1 ≤ m * ‖u - v‖) :
    |freeCovariance m u v| ≤ (m^2 * (Real.sinh 1 + 2) / (4 * Real.pi^2)) * Real.exp (-m * ‖u - v‖)
       :=
  freeCovariance_exponential_bound m Fact.out u v h_sep

/-- **Continuity of the free covariance kernel away from the origin.**

    The kernel C(z) = (m/(4π²‖z‖)) K₁(m‖z‖) is continuous on {z | z ≠ 0}.

    This follows from:
    - ‖z‖ is continuous
    - K₁ is continuous on (0, ∞) (see `besselK1_continuousOn`)
    - Division by ‖z‖ is continuous for z ≠ 0

    This is essential for the double mollifier convergence theorem.
-/
lemma freeCovarianceKernel_continuousOn (m : ℝ) (hm : 0 < m) :
    ContinuousOn (freeCovarianceKernel m) {z : SpaceTime | z ≠ 0} := by
  -- The kernel is f(‖z‖) where f(r) = (m/(4π²r)) K₁(mr)
  -- We show continuity by composition
  -- First show that the kernel (without the if) is continuous on {z ≠ 0}
  have hg_cont : ContinuousOn (fun r : ℝ => (m / (4 * Real.pi^2 * r)) * besselK1 (m * r))
      (Set.Ioi 0) := by
    apply ContinuousOn.mul
    · -- m/(4π²r) is continuous on (0, ∞)
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_const.mul continuousOn_id
      · intro r hr
        simp only [Set.mem_Ioi] at hr
        positivity
    · -- K₁(mr) is continuous on (0, ∞)
      have h := besselK1_continuousOn.comp (continuousOn_const.mul continuousOn_id)
        (fun r hr => by simp only [Set.mem_Ioi] at hr ⊢; exact mul_pos hm hr)
      exact h
  -- Now compose with ‖·‖ and use that z ≠ 0 implies ‖z‖ ≠ 0
  have h_norm_cont : ContinuousOn (fun z : SpaceTime => ‖z‖) {z | z ≠ 0} :=
    continuous_norm.continuousOn
  have h_norm_pos : ∀ z ∈ ({z : SpaceTime | z ≠ 0} : Set SpaceTime), ‖z‖ ∈ Set.Ioi 0 := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_Ioi]
    exact norm_pos_iff.mpr hz
  -- The composed function agrees with freeCovarianceKernel on {z ≠ 0}
  have h_eq : ∀ z ∈ ({z : SpaceTime | z ≠ 0} : Set SpaceTime),
      freeCovarianceKernel m z = (m / (4 * Real.pi^2 * ‖z‖)) * besselK1 (m * ‖z‖) := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    unfold freeCovarianceKernel freeCovariance freeCovarianceBessel
    simp only [zero_sub, norm_neg]
    have h_norm_ne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp only [h_norm_ne, ↓reduceIte]
  apply ContinuousOn.congr _ h_eq
  exact hg_cont.comp h_norm_cont h_norm_pos

/-- The bilinear form f(x) * C(x,y) * g(y) is integrable on product space for Schwartz f, g.
    This uses the L¹ integrability of the translation-invariant Bessel kernel.
-/
theorem freeCovarianceℂ_bilinear_integrable' (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
    Integrable (fun p : SpaceTime × SpaceTime =>
      (f p.1) * (freeCovariance m p.1 p.2 : ℂ) * (g p.2)) volume := by
  have h_transl_inv : ∀ x y, freeCovariance m x y = freeCovarianceKernel m (x - y) := by
    intro x y
    simp only [freeCovarianceKernel, freeCovariance, freeCovarianceBessel, zero_sub, norm_neg]
  have h_eq : (fun p : SpaceTime × SpaceTime => f p.1 * (freeCovariance m p.1 p.2 : ℂ) * g p.2) =
      (fun p => f p.1 * ((freeCovarianceKernel m (p.1 - p.2) : ℝ) : ℂ) * g p.2) := by
    ext p
    rw [h_transl_inv p.1 p.2]
  rw [h_eq]
  have hK_int : Integrable (fun z : SpaceTime => (freeCovarianceKernel m z : ℂ)) volume :=
    Integrable.ofReal (freeCovarianceKernel_integrable m (Fact.out))
  exact schwartz_bilinear_integrable_of_translationInvariant_L1
    (fun z => (freeCovarianceKernel m z : ℂ)) hK_int f g

/-- Negation as a linear isometry equivalence on SpaceTime. -/
def negSpaceTime : SpaceTime ≃ₗᵢ[ℝ] SpaceTime where
  toLinearEquiv := LinearEquiv.neg ℝ
  norm_map' := norm_neg

/-- Helper lemma: Integral with change of variables k ↦ -k for SpaceTime.
    This uses that linear isometries preserve measure on finite-dimensional inner product spaces.
-/
theorem integral_comp_neg_spacetime {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : SpaceTime → E) : ∫ k, f (-k) = ∫ k, f k := by
  have h := (LinearIsometryEquiv.measurePreserving negSpaceTime).integral_comp
    negSpaceTime.toHomeomorph.measurableEmbedding f
  simpa [negSpaceTime] using h

/-- Position-space free covariance is symmetric: `C(x,y) = C(y,x)`. -/
lemma freeCovariance_symmetric (m : ℝ) (x y : SpaceTime) :
    freeCovariance m x y = freeCovariance m y x :=
  freeCovarianceBessel_symm m x y

/-- The position-space free covariance is real-valued after ℂ coercion. -/
lemma freeCovariance_star (m : ℝ) (x y : SpaceTime) :
  star (freeCovariance m x y : ℂ) = (freeCovariance m x y : ℂ) := by
  simp

/-- Hermiticity of the complex-lifted position-space kernel. -/
lemma freeCovariance_hermitian (m : ℝ) (x y : SpaceTime) :
  (freeCovariance m x y : ℂ) = star (freeCovariance m y x : ℂ) := by
  -- symmetry plus real-valuedness
  simp [freeCovariance_symmetric m x y]

/-- The free propagator function is smooth (infinitely differentiable). -/
lemma freePropagator_smooth (m : ℝ) [Fact (0 < m)] :
  ContDiff ℝ (⊤ : ℕ∞) (fun k => freePropagatorMomentum m k) := by
  unfold freePropagatorMomentum
  refine ContDiff.div contDiff_const ((contDiff_norm_sq ℝ).add contDiff_const)
    (fun k => ne_of_gt ?_)
  exact add_pos_of_nonneg_of_pos (sq_nonneg ‖k‖) (pow_pos (Fact.out : 0 < m) 2)

/-- The complex-valued free propagator function is smooth. -/
lemma freePropagator_complex_smooth (m : ℝ) [Fact (0 < m)] :
  ContDiff ℝ (⊤ : ℕ∞) (fun k : SpaceTime => (freePropagatorMomentum m k : ℂ)) :=
  ofRealCLM.contDiff.comp (freePropagator_smooth m)

/-- The free propagator is positive -/
lemma freePropagator_pos {m : ℝ} [Fact (0 < m)] (k : SpaceTime) : 0 < freePropagatorMomentum m k :=
  by
  unfold freePropagatorMomentum
  exact div_pos one_pos (add_pos_of_nonneg_of_pos (sq_nonneg ‖k‖) (pow_pos (Fact.out : 0 < m) 2))

/-- The free propagator is bounded above by 1/m² -/
lemma freePropagator_bounded {m : ℝ} [Fact (0 < m)] (k : SpaceTime) :
  freePropagatorMomentum m k ≤ 1 / m^2 := by
  unfold freePropagatorMomentum
  exact div_le_div_of_nonneg_left one_pos.le (pow_pos (Fact.out : 0 < m) 2)
    (le_add_of_nonneg_left (sq_nonneg ‖k‖))

/-- The free propagator is continuous -/
lemma freePropagator_continuous {m : ℝ} [Fact (0 < m)] :
  Continuous (freePropagatorMomentum m) := by
  unfold freePropagatorMomentum
  refine Continuous.div continuous_const ((continuous_norm.pow 2).add continuous_const)
    (fun k => ?_)
  exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg ‖k‖) (pow_pos (Fact.out : 0 < m) 2))

/-! ## Complex conjugation properties of the propagator -/

/-- The momentum-space propagator is real-valued: its star (complex conjugate) equals itself. -/
@[simp] lemma freePropagatorMomentum_star (m : ℝ) (k : SpaceTime) :
  star (freePropagatorMomentum m k : ℂ) = (freePropagatorMomentum m k : ℂ) := by
  simp

/-- Same statement via the star ring endomorphism (complex conjugate). -/
lemma freePropagatorMomentum_starRing (m : ℝ) (k : SpaceTime) :
  (starRingEnd ℂ) (freePropagatorMomentum m k : ℂ) = (freePropagatorMomentum m k : ℂ) := by
  simp

/-- In particular, the imaginary part of the momentum-space propagator vanishes. -/
@[simp] lemma freePropagatorMomentum_im (m : ℝ) (k : SpaceTime) :
  (freePropagatorMomentum m k : ℂ).im = 0 := by
  simp

/-! ### Momentum weight functions for L² embedding -/

/-- The weight function in momentum space (physics convention): 1 / (‖k‖² + m²) -/
noncomputable def momentumWeight (m : ℝ) (k : SpaceTime) : ℝ :=
  1 / (‖k‖^2 + m^2)

/-- The weight function in momentum space (Mathlib convention): 1 / ((2π)²‖k‖² + m²)
    This is the correct weight to use with Mathlib's Fourier transform.
-/
noncomputable def momentumWeightMathlib (m : ℝ) (k : SpaceTime) : ℝ :=
  freePropagatorMomentumMathlib m k

/-- The square root of the weight function (physics convention). -/
noncomputable def momentumWeightSqrt (m : ℝ) (k : SpaceTime) : ℝ :=
  1 / Real.sqrt (‖k‖^2 + m^2)

/-- The square root of the weight function (Mathlib convention).
    This is the correct weight to use with Mathlib's Fourier transform.
-/
noncomputable def momentumWeightSqrtMathlib (m : ℝ) (k : SpaceTime) : ℝ :=
  1 / Real.sqrt ((2 * Real.pi)^2 * ‖k‖^2 + m^2)

/-- The square root weight is positive (Mathlib convention). -/
lemma momentumWeightSqrt_mathlib_pos (m : ℝ) [Fact (0 < m)] (k : SpaceTime) :
    0 < momentumWeightSqrtMathlib m k := by
  unfold momentumWeightSqrtMathlib
  refine div_pos one_pos (Real.sqrt_pos.mpr ?_)
  exact add_pos_of_nonneg_of_pos (by positivity) (sq_pos_of_pos (Fact.out : 0 < m))

/-- The square of the sqrt weight equals the weight (Mathlib convention). -/
lemma momentumWeightSqrt_mathlib_sq (m : ℝ) [Fact (0 < m)] (k : SpaceTime) :
    (momentumWeightSqrtMathlib m k)^2 = momentumWeightMathlib m k := by
  unfold momentumWeightSqrtMathlib momentumWeightMathlib freePropagatorMomentumMathlib
  have h_pos : 0 < (2 * Real.pi)^2 * ‖k‖^2 + m^2 := by
    have h1 : 0 ≤ (2 * Real.pi)^2 * ‖k‖^2 := by positivity
    have h2 : 0 < m^2 := sq_pos_of_pos (Fact.out : 0 < m)
    linarith
  rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt h_pos)]

/-- The momentum weight sqrt function is continuous (physics convention). -/
lemma momentumWeightSqrt_continuous (m : ℝ) [Fact (0 < m)] :
    Continuous (fun k : SpaceTime => momentumWeightSqrt m k) := by
  unfold momentumWeightSqrt
  refine Continuous.div continuous_const (by fun_prop) (fun k => ne_of_gt ?_)
  exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (Fact.out : 0 < m) 2))

/-- The momentum weight sqrt function is continuous (Mathlib convention). -/
lemma momentumWeightSqrt_mathlib_continuous (m : ℝ) [Fact (0 < m)] :
    Continuous (fun k : SpaceTime => momentumWeightSqrtMathlib m k) := by
  unfold momentumWeightSqrtMathlib
  refine Continuous.div continuous_const (by fun_prop) (fun k => ne_of_gt ?_)
  exact Real.sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (by positivity) (sq_pos_of_pos (Fact.out : 0 < m)))

/-- The momentum weight sqrt function is measurable (physics convention). -/
lemma momentumWeightSqrt_measurable (m : ℝ) [Fact (0 < m)] :
    Measurable (fun k : SpaceTime => momentumWeightSqrt m k) :=
  (momentumWeightSqrt_continuous m).measurable

/-- The momentum weight sqrt function is measurable (Mathlib convention). -/
lemma momentumWeightSqrt_mathlib_measurable (m : ℝ) [Fact (0 < m)] :
    Measurable (fun k : SpaceTime => momentumWeightSqrtMathlib m k) :=
  (momentumWeightSqrt_mathlib_continuous m).measurable

/-- Helper: `1 / √(A + m²) ≤ 1 / m` for `0 < m` and `0 ≤ A`. -/
private lemma one_div_sqrt_add_sq_le_inv (m : ℝ) (hm : 0 < m) {A : ℝ} (hA : 0 ≤ A) :
    1 / Real.sqrt (A + m^2) ≤ 1 / m := by
  refine one_div_le_one_div_of_le hm ?_
  calc m = Real.sqrt (m^2) := (Real.sqrt_sq hm.le).symm
    _ ≤ Real.sqrt (A + m^2) := Real.sqrt_le_sqrt (by linarith)

/-- Helper: The weight function as an L^∞ function (essentially bounded). -/
lemma momentumWeightSqrt_bounded_ae (m : ℝ) [Fact (0 < m)] :
    ∀ᵐ k ∂(volume : Measure SpaceTime), ‖(momentumWeightSqrt m k : ℂ)‖ ≤ 1 / m := by
  filter_upwards with k
  simp only [Complex.norm_real, momentumWeightSqrt, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.sqrt (‖k‖^2 + m^2))]
  exact one_div_sqrt_add_sq_le_inv m Fact.out (sq_nonneg _)

/-- Helper: The mathlib weight function as an L^∞ function (essentially bounded). -/
lemma momentumWeightSqrt_mathlib_bounded_ae (m : ℝ) [Fact (0 < m)] :
    ∀ᵐ k ∂(volume : Measure SpaceTime), ‖(momentumWeightSqrtMathlib m k : ℂ)‖ ≤ 1 / m := by
  filter_upwards with k
  simp only [Complex.norm_real, momentumWeightSqrtMathlib, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.sqrt ((2 * Real.pi)^2 * ‖k‖^2 + m^2))]
  exact one_div_sqrt_add_sq_le_inv m Fact.out (by positivity)

/-- Multiplication by the square-root momentum weight defines a bounded
    linear operator on complex L² (physics convention).
-/
noncomputable def momentumWeightSqrtMulCLM (m : ℝ) [Fact (0 < m)] :
    Lp ℂ 2 (volume : Measure SpaceTime) →L[ℂ]
      Lp ℂ 2 (volume : Measure SpaceTime) :=
  have hg_meas : Measurable (fun k => (momentumWeightSqrt m k : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (momentumWeightSqrt_measurable m)
  linftyMulL2CLM
    (fun k => (momentumWeightSqrt m k : ℂ))
    hg_meas
    (1 / m)
    (momentumWeightSqrt_bounded_ae m)

/-- Multiplication by the square-root momentum weight defines a bounded
    linear operator on complex L² (Mathlib convention).
-/
noncomputable def momentumWeightSqrtMathlibMulCLM (m : ℝ) [Fact (0 < m)] :
    Lp ℂ 2 (volume : Measure SpaceTime) →L[ℂ]
      Lp ℂ 2 (volume : Measure SpaceTime) :=
  have hg_meas : Measurable (fun k => (momentumWeightSqrtMathlib m k : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (momentumWeightSqrt_mathlib_measurable m)
  linftyMulL2CLM
    (fun k => (momentumWeightSqrtMathlib m k : ℂ))
    hg_meas
    (1 / m)
    (momentumWeightSqrt_mathlib_bounded_ae m)

lemma momentumWeightSqrt_mathlib_mul_CLM_spec (m : ℝ) [Fact (0 < m)]
    (f : Lp ℂ 2 (volume : Measure SpaceTime)) :
    (momentumWeightSqrtMathlibMulCLM m f) =ᵐ[volume]
      fun k => (momentumWeightSqrtMathlib m k : ℂ) * f k := by
  unfold momentumWeightSqrtMathlibMulCLM
  exact linfty_mul_L2_CLM_spec _ _ _ _ f

/-- The square-root momentum weight is pointwise bounded by `1 / m` (Mathlib convention). -/
lemma momentumWeightSqrt_mathlib_le_inv_mass (m : ℝ) [Fact (0 < m)] :
    ∀ k : SpaceTime, momentumWeightSqrtMathlib m k ≤ 1 / m := fun k => by
  simpa [momentumWeightSqrtMathlib] using
    one_div_sqrt_add_sq_le_inv m Fact.out (A := (2 * Real.pi)^2 * ‖k‖^2) (by positivity)
