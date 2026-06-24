/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.OS.OS3MixedRepInfra

/-!
# OS3 — Mixed Representation via Schwinger Parametrization

Derives the mixed (momentum-position) representation of the covariance bilinear form
by performing the Fubini exchanges justified in `OS3_MixedRepInfra`. The chain is:

1. Schwinger → heat kernel: ⟨Θf, Cf⟩ = ∫₀^∞ e^{−sm²} [∫∫ f*(x) f(y) H(s,|Θx−y|)] ds
2. Fourier representation of heat kernel introduces spatial momenta kbar
3. k₀ Gaussian integral: ∫ e^{ik₀(x₀+y₀)} e^{−sk₀²} dk₀ = √(π/s) e^{−(x₀+y₀)²/4s}
4. Laplace transform in s: ∫₀^∞ s^{−1/2} e^{−(x₀+y₀)²/4s − sω²} ds = √(π/ω²) e^{−ω|x₀+y₀|}

The final result (Bessel K_{1/2} identity) is:

  ⟨Θf, Cf⟩ = (1/2(2π)³) ∫_{kbar} ∫∫ f*(x) f(y) (1/ω) e^{−ω|x₀+y₀|} e^{ikbar·(xbar−ybar)} dkbar dx dy

This is the integration order exchange from eq. (4.19) that the naive approach could
not justify due to the non-absolute-integrability of 1/√(k²+m²) in 3D.

5. **Fubini Theorems** (from `OS3_MixedRepInfra`): Justify all changes in integration order
   using the integrability bounds.

## Physical Interpretation

The mixed representation exhibits:
- **Causality**: Exponential decay `e^(-ω|x⁰+y⁰|)` for `x⁰,y⁰ ≤ 0` (reflection positivity support).
- **On-shell condition**: The energy-momentum relation `ω² = |k|² + m²` is built into the structure.
- **Feynman propagator**: The k⁰ integral has poles at ±iω, corresponding to particle propagation.

## References

- Osterwalder & Schrader, "Axioms for Euclidean Green's Functions I & II" (1973, 1975)
- Glimm & Jaffe, "Quantum Physics: A Functional Integral Point of View" (1987), §11.4
- Haag, "Local Quantum Physics" (1996), §V.3
-/

open MeasureTheory Complex Real Filter QFT LaplaceIntegral
open TopologicalSpace
open scoped Real InnerProductSpace BigOperators

noncomputable section

variable {m : ℝ} [Fact (0 < m)]

/-- The 1D Gaussian Fourier transform in real form:
    ∫ exp(-ik₀t) exp(-sk₀²) dk₀ = √(π/s) exp(-t²/(4s))

    This follows from Mathlib's `fourierIntegral_gaussian`.
-/
lemma gaussian_fourier_1d (s : ℝ) (hs : 0 < s) (t : ℝ) :
    ∫ k₀ : ℝ, Complex.exp (-Complex.I * k₀ * t) * Complex.exp (-(s : ℂ) * k₀^2) =
    Real.sqrt (π / s) * Complex.exp (-(t^2 / (4 * s) : ℝ)) := by
  -- Use Mathlib's fourierIntegral_gaussian with b = s and t' = -t
  -- Mathlib: ∫ x, cexp(I * t * x) * cexp(-b * x²) = (π/b)^(1/2) * cexp(-t²/(4b))
  have hs_re : 0 < (s : ℂ).re := by simp [hs]
  have h := fourierIntegral_gaussian hs_re ((-t : ℝ) : ℂ)
  -- Rewrite LHS to match Mathlib's form
  have h_lhs : ∫ k₀ : ℝ, Complex.exp (-Complex.I * k₀ * t) * Complex.exp (-(s : ℂ) * k₀^2) =
               ∫ x : ℝ, Complex.exp (Complex.I * (-t : ℂ) * x) * Complex.exp (-(s : ℂ) * x^2) := by
    congr 1
    ext x
    congr 2
    ring
  -- Need to convert ↑(-t) to -↑t
  have h_neg : ((-t : ℝ) : ℂ) = -(t : ℂ) := by push_cast; ring
  simp only [h_neg] at h
  rw [h_lhs, h]
  -- Now simplify RHS: (π/s)^(1/2) * cexp(-(-t)²/(4s)) = √(π/s) * cexp(-t²/(4s))
  congr 1
  · -- (π/s)^(1/2) = √(π/s) as complex
    have h_pos : 0 < π / s := div_pos Real.pi_pos hs
    -- Key: (x : ℂ)^(1/2 : ℂ) = (x^(1/2) : ℂ) for x ≥ 0
    have h_half : (1 / 2 : ℂ) = (↑(1 / 2 : ℝ) : ℂ) := by norm_num
    rw [h_half]
    have h_cpow : (↑(π / s : ℝ) : ℂ) ^ (↑(1 / 2 : ℝ) : ℂ) = ↑((π / s : ℝ) ^ (1 / 2 : ℝ)) :=
      (Complex.ofReal_cpow (le_of_lt h_pos) (1 / 2)).symm
    have h_div : (↑π / ↑s : ℂ) = (↑(π / s : ℝ) : ℂ) := by push_cast; ring
    rw [h_div, h_cpow]
    congr 1
    rw [Real.sqrt_eq_rpow]
  · -- (-t)² = t²
    congr 1
    push_cast
    ring

/-- Gaussian exponential factorizes: exp(-s‖k‖²) = exp(-sk₀²) × exp(-s‖k_sp‖²) -/
lemma gaussian_exp_factorize (s : ℂ) (k : SpaceTime) :
    Complex.exp (-s * ‖k‖^2) =
    Complex.exp (-s * (k 0)^2) * Complex.exp (-s * ‖spatialPart k‖^2) := by
  rw [← Complex.exp_add]
  congr 1
  -- Use the real decomposition: ‖k‖^2 = (k 0)^2 + ‖spatialPart k‖^2
  have h : (‖k‖^2 : ℝ) = (k 0)^2 + ‖spatialPart k‖^2 := spacetime_norm_sq_decompose k
  -- Note: the goal has (↑‖k‖)^2 not ↑(‖k‖^2), so we need to simplify first
  simp only [← Complex.ofReal_pow]
  -- Now goal is: -s * ↑(‖k‖^2) = -s * ↑((k 0)^2) + -s * ↑(‖spatialPart k‖^2)
  rw [h]
  push_cast
  ring

/-- The k₀-integral evaluates to √(π/s) exp(-t²/(4s)) times the k_sp-dependent factor.

    For z = Θx - y with z₀ = -x₀ - y₀:
    ∫_k exp(-ik·z) exp(-s|k|²) = (∫_{k₀} exp(-ik₀z₀) exp(-sk₀²)) × (∫_{k_sp} exp(-ik_sp·z_sp)
    exp(-s|k_sp|²))
                                = √(π/s) exp(-z₀²/(4s)) × ∫_{k_sp} exp(-ik_sp·z_sp) exp(-s|k_sp|²)
-/
lemma k_integral_after_k0_eval (s : ℝ) (hs : 0 < s) (z : SpaceTime) :
    ∫ k : SpaceTime, Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) * Complex.exp (-(s : ℂ) * ‖k‖^2) =
    (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((z 0)^2 / (4 * s)) : ℝ)) *
      ∫ k_sp : SpatialCoords, Complex.exp (-Complex.I * spatialDot k_sp (spatialPart z)) *
                               Complex.exp (-(s : ℂ) * ‖k_sp‖^2) := by
  -- Step 1: Factor the integrand into k₀-part × k_sp-part using existing lemmas
  have h_factor : ∀ k : SpaceTime,
      Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) * Complex.exp (-(s : ℂ) * ‖k‖^2) =
      (Complex.exp (-Complex.I * (k 0 * z 0)) * Complex.exp (-(s : ℂ) * (k 0)^2)) *
      (Complex.exp (-Complex.I * spatialDot (spatialPart k) (spatialPart z)) *
       Complex.exp (-(s : ℂ) * ‖spatialPart k‖^2)) := by
    intro k
    -- Use gaussian_exp_factorize for the norm part
    have h_gauss := gaussian_exp_factorize (s : ℂ) k
    -- Use spacetime_inner_decompose for the inner product part
    have h_inner := spacetime_inner_decompose k z
    -- Factor the inner product exponential
    have h_inner_exp : Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) =
        Complex.exp (-Complex.I * (k 0 * z 0)) *
        Complex.exp (-Complex.I * spatialDot (spatialPart k) (spatialPart z)) := by
      rw [h_inner, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h_inner_exp, h_gauss]
    ring
  -- Step 2: Rewrite integrand using factorization
  conv_lhs => arg 2; ext k; rw [h_factor k]
  -- Step 3: Integrability for k₀ (1D Gaussian)
  -- Use Mathlib's integrable_cexp_neg_mul_sq_norm_add with V = ℝ, d = 1
  -- This gives ∫ exp(-s * k₀² + c * ⟪1, k₀⟫) where ⟪1, k₀⟫_ℝ = k₀
  have h_int_k0 : Integrable (fun k₀ : ℝ =>
      Complex.exp (-Complex.I * (k₀ * z 0)) * Complex.exp (-(s : ℂ) * k₀^2)) volume := by
    have hs_cplx : 0 < (s : ℂ).re := by simp [hs]
    have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℝ) hs_cplx (-Complex.I * z
      0) 1
    -- The lemma gives: Integrable (fun k₀ ↦ cexp(-s * |k₀|² + (-I * z0) * ⟪1, k₀⟫_ℝ))
    -- Since ⟪1, k₀⟫_ℝ = 1 * k₀ = k₀ in ℝ, this is: cexp(-s * k₀² - I * z0 * k₀)
    convert h using 1
    ext k₀
    rw [← Complex.exp_add]
    congr 1
    -- Goal: -I * (k₀ * z0) + (-s * k₀²) = -s * |k₀|² + (-I * z0) * ⟪1, k₀⟫
    -- Use real_inner_eq_mul: ⟪1, k₀⟫_ℝ = 1 * k₀ = k₀
    rw [real_inner_eq_mul, one_mul]
    simp only [Real.norm_eq_abs, sq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_neg]
    -- The goal is now algebraic - both sides are equal by commutativity/associativity
    -- -I * (↑k₀ * ↑z0) + ↑(-s) * ↑(k₀²) = ↑(-s) * ↑(k₀²) + -I * ↑z0 * ↑k₀
    ring
  -- Step 4: Integrability for k_sp (3D Gaussian)
  -- The lemma gives: Integrable (fun v ↦ cexp(-s * ‖v‖² + (-I) * ⟪z_sp, v⟫_ℝ))
  have h_int_ksp : Integrable (fun k_sp : SpatialCoords =>
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart z)) *
      Complex.exp (-(s : ℂ) * ‖k_sp‖^2)) volume := by
    have hs_cplx : 0 < (s : ℂ).re := by simp [hs]
    have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
      hs_cplx (-Complex.I) (spatialPart z)
    convert h using 1
    ext k_sp
    rw [← Complex.exp_add]
    congr 1
    -- Goal: match -I * spatialDot(k_sp, z_sp) + (-s * ‖k_sp‖²) with -s * ‖k_sp‖² + (-I) * ⟪z_sp,
    -- k_sp⟫
    -- Use spatialDot_eq_inner: spatialDot k z = ⟪k, z⟫_ℝ, and inner product is symmetric
    rw [spatialDot_eq_inner]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
    -- The inner product is symmetric
    rw [real_inner_comm]
    push_cast
    ring
  -- Step 5: Apply integral_spacetime_prod_split
  rw [integral_spacetime_prod_split h_int_k0 h_int_ksp]
  -- Step 6: Apply gaussian_fourier_1d to k₀ integral
  have h_k0 : ∫ k₀ : ℝ, Complex.exp (-Complex.I * (k₀ * z 0)) * Complex.exp (-(s : ℂ) * k₀^2) =
              Real.sqrt (π / s) * Complex.exp (-(((z 0)^2 / (4 * s)) : ℝ)) := by
    rw [← gaussian_fourier_1d s hs (z 0)]
    refine integral_congr_ae (.of_forall fun k₀ => ?_)
    ring_nf
  rw [h_k0]

/-- The time component of (timeReflection x - y). -/
lemma timeReflection_sub_zero (x y : SpaceTime) :
    (timeReflection x - y) 0 = -(x 0) - y 0 := rfl

/-- The spatial part of (timeReflection x - y) equals spatialPart x - spatialPart y. -/
lemma spatialPart_timeReflection_sub (x y : SpaceTime) :
    spatialPart (timeReflection x - y) = spatialPart x - spatialPart y := rfl

/-- **THEOREM**: Heat kernel bilinear form after k₀ integration.

    Starting from the Schwinger representation with heat kernel H(s,r):

    ∫₀^∞ exp(-sm²) ∫∫ fbar(x)f(y) H(s, |Θx-y|) dx dy ds

    After substituting H(s,r) = (2π)^{-d} ∫_k exp(-ik·z) exp(-s|k|²) and
    performing the k₀ integral using the 1D Gaussian FT:

    ∫_{-∞}^∞ exp(-ik₀t) exp(-sk₀²) dk₀ = √(π/s) · exp(-t²/(4s))

    we obtain:

    (2π)^{-4} ∫₀^∞ ∫_pbar ∫∫ fbar(x)f(y) √(π/s) exp(-t²/(4s))
    exp(-s(|pbar|² + m²)) exp(-ipbar·rbar) dx dy
    d³pbar ds

    where t = -x₀ - y₀ (time separation under reflection) and
    rbar = xbar - ybar (spatial separation).

    The exp(-sm²) factor combines with exp(-s|pbar|²) to give exp(-s(|pbar|² + m²)).
-/
theorem heatKernel_bilinear_fourier_form (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * f y * heatKernelPositionSpace s ‖timeReflection x - y‖ =
    (1 / (2 * π) ^ STDimension : ℝ) *
    ∫ s in Set.Ioi 0, ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
  -- Step 1: For s > 0, substitute heatKernel_eq_gaussianFT
  have h_hk : ∀ s : ℝ, 0 < s → ∀ z : SpaceTime,
      (heatKernelPositionSpace s ‖z‖ : ℂ) =
      (1 / (2 * π) ^ STDimension : ℝ) *
      ∫ k : SpaceTime, Complex.exp (-Complex.I * ⟪k, z⟫_ℝ) * Complex.exp (-(s : ℂ) * ‖k‖^2) :=
    fun s hs z => heatKernel_eq_gaussianFT s hs z
  -- Step 2: Rewrite LHS using h_hk under the s-integral
  have h_step1 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * f y * heatKernelPositionSpace s ‖timeReflection x - y‖ =
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ∫ x : SpaceTime, ∫ y : SpaceTime,
          (starRingEnd ℂ (f x)) * f y *
          ((1 / (2 * π) ^ STDimension : ℝ) *
           ∫ k : SpaceTime, Complex.exp (-Complex.I * ⟪k, timeReflection x - y⟫_ℝ) *
                            Complex.exp (-(s : ℂ) * ‖k‖^2)) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    exact h_hk s (Set.mem_Ioi.mp hs) (timeReflection x - y)
  -- Step 3: Apply k_integral_after_k0_eval to evaluate the k-integral
  -- For each (s, x, y), this replaces the k-integral with:
  -- √(π/s) exp(-z₀²/(4s)) × ∫_{k_sp} exp(-I k_sp·z_sp) exp(-s‖k_sp‖²)
  -- where z = Θx - y, z₀ = -(x₀) - y₀, z_sp = x_sp - y_sp
  have h_step2 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * f y *
        ((1 / (2 * π) ^ STDimension : ℝ) *
         ∫ k : SpaceTime, Complex.exp (-Complex.I * ⟪k, timeReflection x - y⟫_ℝ) *
                          Complex.exp (-(s : ℂ) * ‖k‖^2)) =
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ∫ x : SpaceTime, ∫ y : SpaceTime,
          (starRingEnd ℂ (f x)) * f y *
          ((1 / (2 * π) ^ STDimension : ℝ) *
           ((Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
            ∫ k_sp : SpatialCoords,
              Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) *
              Complex.exp (-(s : ℂ) * ‖k_sp‖^2))) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    have hs_pos : 0 < s := Set.mem_Ioi.mp hs
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    congr 1
    -- Apply k_integral_after_k0_eval
    have h_k := k_integral_after_k0_eval s hs_pos (timeReflection x - y)
    -- Rewrite using helper lemmas for time and spatial components
    rwa [timeReflection_sub_zero, spatialPart_timeReflection_sub] at h_k
  -- Step 4: Rearrange the integrand to match fubini_ksp_xy_swap LHS form
  -- Move the constant outside x,y integrals and swap k_sp integrand order
  have h_step3 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * f y *
        ((1 / (2 * π) ^ STDimension : ℝ) *
         ((Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
          ∫ k_sp : SpatialCoords,
            Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) *
            Complex.exp (-(s : ℂ) * ‖k_sp‖^2))) =
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ((1 / (2 * π) ^ STDimension : ℝ) *
         ∫ x : SpaceTime, ∫ y : SpaceTime,
           (starRingEnd ℂ (f x)) * f y *
           (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
           ∫ k_sp : SpatialCoords,
             Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
             Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    congr 1
    -- First reorder the k_sp integrand using mul_comm
    have h_ksp_reorder : ∀ x y : SpaceTime,
        (∫ k_sp : SpatialCoords,
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) *
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2)) =
        (∫ k_sp : SpatialCoords,
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) := by
      intro x y
      apply integral_congr_ae
      filter_upwards with k_sp
      ring
    -- Now show the full equality
    simp_rw [h_ksp_reorder]
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  -- Step 5: Apply fubini_ksp_xy_swap to swap k_sp outside (x, y)
  have h_step4 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ((1 / (2 * π) ^ STDimension : ℝ) *
       ∫ x : SpaceTime, ∫ y : SpaceTime,
         (starRingEnd ℂ (f x)) * f y *
         (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
         ∫ k_sp : SpatialCoords,
           Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
           Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) =
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ((1 / (2 * π) ^ STDimension : ℝ) *
         ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
           (starRingEnd ℂ (f x)) * f y *
           (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
           Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
           Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    have hs_pos : 0 < s := Set.mem_Ioi.mp hs
    congr 1
    congr 1
    exact fubini_ksp_xy_swap s hs_pos f
  -- Step 6: Factor out (1/(2π)^4) from the s-integral
  have h_step5 : ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ((1 / (2 * π) ^ STDimension : ℝ) *
       ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
         (starRingEnd ℂ (f x)) * f y *
         (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
         Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
         Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y))) =
      (1 / (2 * π) ^ STDimension : ℝ) *
        ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
            (starRingEnd ℂ (f x)) * f y *
            (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
            Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
            Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    -- Use smul version for set integrals
    rw [← smul_eq_mul, ← smul_eq_mul]
    rw [← integral_smul]
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    simp only [smul_eq_mul]
    ring
  -- Step 7: Push exp(-sm²) inside k_sp integral and combine exponentials
  have h_step6 : (1 / (2 * π) ^ STDimension : ℝ) *
      ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
        ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
          (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
          Complex.exp (-(s : ℂ) * ‖k_sp‖^2) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      (1 / (2 * π) ^ STDimension : ℝ) *
        ∫ s in Set.Ioi 0, ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
          (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-(((-(x 0) - y 0)^2 / (4 * s)) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    congr 1
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with s hs
    -- First push exp(-sm²) into all the integrals
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with k_sp
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    -- Combine exp(-sm²) with exp(-s‖k_sp‖²) to get exp(-s(‖k_sp‖² + m²))
    -- First convert ↑(rexp ...) to cexp(↑...)
    rw [Complex.ofReal_exp]
    -- Combine exp(-sm²) with exp(-s‖k_sp‖²) into exp(-s(‖k_sp‖²+m²)), then reorder
    have h_exp_combine : Complex.exp (↑(-s * m^2)) * Complex.exp (-(s : ℂ) * ‖k_sp‖^2) =
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← h_exp_combine]
    ring
  -- Chain all steps together
  exact h_step1.trans (h_step2.trans (h_step3.trans (h_step4.trans (h_step5.trans h_step6))))

/-! ### Helper lemmas for Laplace s-integral evaluation -/

/-- ω = √(‖k_sp‖² + m²) is positive for m > 0. -/
lemma omega_pos (k_sp : SpatialCoords) (m : ℝ) (hm : 0 < m) :
    0 < Real.sqrt (‖k_sp‖^2 + m^2) := by positivity

/-- The normalization constant relation:
    (1/(2π)⁴) × π = 1/(2(2π)³)

    Proof: (2π)⁴ = 2 × (2π)³ × π, so π/(2π)⁴ = 1/(2(2π)³)
-/
lemma normalization_constant_laplace :
    (1 / (2 * π) ^ 4 : ℝ) * π = 1 / (2 * (2 * π) ^ 3) := by field_simp

/-- The s-integral evaluation for fixed (k_sp, x, y):

    ∫_s √(π/s) exp(-t²/(4s)) exp(-s·ω²) ds = (π/ω) exp(-ω|t|)

    where t = -(x₀) - y₀ and ω = √(‖k_sp‖² + m²).

    This uses `laplace_integral_half_power_nonneg` from LaplaceIntegral.lean.

    **Proof outline:**
    1. Factor √(π/s) = √π · s^(-1/2)
    2. Combine exponentials: exp(-t²/(4s)) * exp(-s*ω²) = exp(-t²/(4s) - s*ω²)
    3. Apply laplace_integral_half_power_nonneg with a = t²/4, b = ω²
    4. Result: √π * √(π/ω²) * exp(-2√((t²/4)*ω²)) = (π/ω) * exp(-ω|t|)
-/
lemma s_integral_eval (t : ℝ) (ω : ℝ) (hω : 0 < ω) :
    ∫ s in Set.Ioi 0, Real.sqrt (π / s) * Real.exp (-(t^2 / (4 * s))) *
      Real.exp (-s * ω^2) = (π / ω) * Real.exp (-ω * |t|) := by
  -- Setup hypotheses
  have ha : 0 ≤ t^2/4 := div_nonneg (sq_nonneg t) (by norm_num : (0:ℝ) ≤ 4)
  have hb : 0 < ω^2 := sq_pos_of_pos hω
  -- Step 1: Rewrite integrand to match laplace_integral_half_power_nonneg form
  -- √(π/s) * exp(-t²/(4s)) * exp(-sω²) = √π * s^(-1/2) * exp(-(t²/4)/s - ω²*s)
  have h_integrand : ∀ s ∈ Set.Ioi (0:ℝ),
      Real.sqrt (π / s) * Real.exp (-(t^2 / (4 * s))) * Real.exp (-s * ω^2) =
      Real.sqrt π * (s^(-(1/2 : ℝ)) * Real.exp (-(t^2/4)/s - ω^2*s)) := by
    intro s hs
    have hs' : 0 < s := hs
    -- sqrt(π/s) = sqrt(π) * s^(-1/2)
    have h_sqrt : Real.sqrt (π / s) = Real.sqrt π * s^(-(1/2 : ℝ)) := by
      rw [Real.sqrt_div Real.pi_pos.le, div_eq_mul_inv]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs'.le]
    -- Combine exponentials: exp(-t²/(4s)) * exp(-sω²) = exp(-(t²/(4s)) - sω²)
    have h_exp : Real.exp (-(t^2 / (4 * s))) * Real.exp (-s * ω^2) =
                 Real.exp (-(t^2/4)/s - ω^2*s) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [h_sqrt, mul_assoc, mul_assoc, h_exp]
  -- Step 2: Rewrite integral using the integrand equivalence
  rw [setIntegral_congr_fun measurableSet_Ioi h_integrand]
  -- Step 3: Factor out √π from the integral
  rw [MeasureTheory.integral_const_mul]
  -- Step 4: Apply laplace_integral_half_power_nonneg
  have h_laplace := laplace_integral_half_power_nonneg (t^2/4) (ω^2) ha hb
  rw [h_laplace]
  -- Step 5: Algebraic simplification
  -- √π * (√(π/ω²) * exp(-2√((t²/4)*ω²))) = (π/ω) * exp(-ω|t|)
  -- First simplify sqrt(π/ω²) = sqrt(π)/ω
  have h_sqrt_div : Real.sqrt (π / ω^2) = Real.sqrt π / ω := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq_eq_abs, abs_of_pos hω]
  rw [h_sqrt_div]
  -- Now LHS = sqrt(π) * ((sqrt(π)/ω) * exp(-2*sqrt(t²ω²/4)))
  have h_prod_sqrt : Real.sqrt π * (Real.sqrt π / ω) = π / ω := by
    field_simp
    exact Real.sq_sqrt Real.pi_pos.le
  rw [← mul_assoc, h_prod_sqrt]
  -- Now simplify the exponent: 2*sqrt((t²/4)*ω²) = ω*|t|
  congr 2
  rw [Real.sqrt_mul ha, Real.sqrt_sq_eq_abs, abs_of_pos hω]
  have h2 : Real.sqrt (t^2/4) = |t|/2 := by
    rw [Real.sqrt_div (sq_nonneg t), Real.sqrt_sq_eq_abs]
    congr 1
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [h2]
  ring

/-- **Complex version of s_integral_eval**: The Laplace integral identity in ℂ.

    This is a direct corollary of `s_integral_eval`, converting the real integral
    to complex form. The key observation is that all terms in the integrand are
    real numbers cast to ℂ, so we can use `integral_ofReal` to relate the integrals.

    ∫_s (↑√(π/s)) * cexp(-↑(t²/(4s))) * cexp(-↑(sω²)) ds = ↑((π/ω) * exp(-ω|t|))
-/
lemma s_integral_eval_complex (t : ℝ) (ω : ℝ) (hω : 0 < ω) :
    ∫ s in Set.Ioi 0, (Real.sqrt (π / s) : ℂ) *
      Complex.exp (-(t^2 / (4 * s) : ℝ)) *
      Complex.exp (-(s * ω^2 : ℝ)) =
    (((π / ω) * Real.exp (-ω * |t|) : ℝ) : ℂ) := by
  -- Step 1: Convert integrand to single real cast: ↑a * ↑b * ↑c = ↑(a * b * c)
  have h_integrand : ∀ s ∈ Set.Ioi (0:ℝ),
      (Real.sqrt (π / s) : ℂ) * Complex.exp (-(t^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s * ω^2 : ℝ)) =
      (((Real.sqrt (π / s) * Real.exp (-(t^2 / (4 * s))) * Real.exp (-(s * ω^2))) : ℝ) : ℂ) := by
    intro s _
    -- cexp(-↑r) = ↑(Real.exp(-r)); combine with ofReal_mul: ↑a * ↑b = ↑(a*b)
    push_cast [Complex.ofReal_exp]
    norm_cast
  rw [setIntegral_congr_fun measurableSet_Ioi h_integrand]
  -- Step 2: Normalize -(x * ω²) to -x * ω² to match s_integral_eval
  have h_form : ∀ x : ℝ, -(x * ω^2) = -x * ω^2 := by intro x; ring
  simp_rw [h_form]
  -- Step 3: Goal is ∫ x in S, ↑(f x) = ↑(result)
  -- Use integral_complex_ofReal: ∫ x in S, ↑(f x) = ↑(∫ x in S, f x)
  rw [integral_complex_ofReal]
  -- Now goal is: ↑(∫ x in S, f x) = ↑(result), which follows from s_integral_eval
  exact congrArg Complex.ofReal (s_integral_eval t ω hω)

/-- **Complex-valued s-integral**: For fixed (k_sp, x, y, f), the inner s-integral
    with complex exponentials evaluates to the propagator form.

    This wraps `s_integral_eval` by:
    1. Factoring out constant terms (fbarf and phase)
    2. Converting Complex.exp to Real.exp for real arguments
    3. Applying s_integral_eval
    4. Reassembling the complex result

    Note: The integrand has the form:
    fbar * f * √(π/s) * cexp(-t²/(4s)) * cexp(-sω²) * cexp(-I*phase)

    where all exponentials have real arguments (cast to ℂ).
-/
lemma s_integral_complex_eval (k_sp : SpatialCoords) (x y : SpaceTime) (m : ℝ) (hm : 0 < m)
    (f : TestFunctionℂ) :
    ∫ s in Set.Ioi 0, (starRingEnd ℂ (f x)) * f y *
      (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
      Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
    (starRingEnd ℂ (f x)) * f y * (π / Real.sqrt (‖k_sp‖^2 + m^2) : ℂ) *
      Complex.exp (-(|-(x 0) - y 0| : ℝ) * Real.sqrt (‖k_sp‖^2 + m^2)) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
  -- The key insight: all s-dependent terms have real arguments
  -- We factor out constant terms, apply s_integral_eval, and reassemble
  let t := -(x 0) - y 0
  let ω := Real.sqrt (‖k_sp‖^2 + m^2)
  have hω : 0 < ω := omega_pos k_sp m hm
  -- Factor out terms not depending on s
  have h_factor : ∀ s ∈ Set.Ioi (0:ℝ),
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      (starRingEnd ℂ (f x)) * f y *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) *
        ((Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
         Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2))) := by
    intro s _
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_factor]
  rw [MeasureTheory.integral_const_mul]
  -- Goal: C * ∫ a, [√(π/a) * cexp(-t²/(4a)) * cexp(-↑a*(↑‖k_sp‖²+↑m²))] = C * (π/ω) * cexp(-ω|t|) *
  -- phase
  -- where C = fbarf * cexp(-I*...) and ω = √(‖k_sp‖² + m²)
  --
  -- Step 1: Convert cexp(-↑a * (↑‖k_sp‖² + ↑m²)) to cexp(-(a * ω²) : ℝ)
  -- using ω² = ‖k_sp‖² + m²
  have h_omega_sq : ω^2 = ‖k_sp‖^2 + m^2 := by
    simp only [ω]
    exact Real.sq_sqrt (by nlinarith [sq_nonneg ‖k_sp‖, sq_pos_of_pos hm])
  have h_exp_conv : ∀ a ∈ Set.Ioi (0:ℝ),
      Complex.exp (-(a : ℂ) * ((‖k_sp‖^2 : ℂ) + (m^2 : ℂ))) =
      Complex.exp (-(a * ω^2 : ℝ)) := by
    intro a _
    congr 1
    rw [h_omega_sq]
    push_cast
    ring
  have h_integrand_conv : ∀ a ∈ Set.Ioi (0:ℝ),
      (Real.sqrt (π / a) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * a) : ℝ)) *
        Complex.exp (-(a : ℂ) * ((‖k_sp‖^2 : ℂ) + (m^2 : ℂ))) =
      (Real.sqrt (π / a) : ℂ) * Complex.exp (-(t^2 / (4 * a) : ℝ)) *
        Complex.exp (-(a * ω^2 : ℝ)) := by
    intro a ha
    rw [h_exp_conv a ha]
  rw [setIntegral_congr_fun measurableSet_Ioi h_integrand_conv]
  -- Step 2: Apply s_integral_eval_complex
  rw [s_integral_eval_complex t ω hω]
  -- Step 3: Algebraic simplification to match the goal
  -- After s_integral_eval_complex:
  -- LHS: C * ↑((π / ω) * Real.exp (-ω * |t|))
  -- RHS: fbarf * (↑π / ↑ω) * cexp(-↑|t| * ↑ω) * phase
  --
  -- We need to:
  -- 1. Split the single cast: ↑(a * b) = ↑a * ↑b
  -- 2. Convert Real.exp to Complex.exp: ↑(rexp r) = cexp ↑r
  -- 3. Rearrange using ring
  --
  -- Split the cast, convert Real.exp to Complex.exp, and reorder the exp argument
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  rw [Complex.ofReal_exp,
    show ((-ω * |t| : ℝ) : ℂ) = ((-|t| * ω : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_mul, Complex.ofReal_neg]
  simp only [t, ω]
  ring

/-- **THEOREM**: Laplace transform evaluation for the s-integral.

    The key identity (Bessel K_{1/2} / modified Laplace transform):

    √π · ∫₀^∞ s^{-1/2} exp(-t²/(4s) - sω²) ds = (π/ω) · exp(-ω|t|)

    where ω = √(|pbar|² + m²) is the relativistic dispersion relation.

    This transforms the Schwinger proper-time representation into the
    Euclidean propagator in mixed (pbar, x₀) representation:

    1/(2π)⁴ · ∫_pbar ∫₀^∞ √(π/s) exp(-t²/(4s)) exp(-s(|pbar|² + m²)) exp(-ipbar·rbar) ds d³pbar
    = 1/(2(2π)³) · ∫_pbar (1/ω) exp(-ω|t|) exp(-ipbar·rbar) d³pbar

    **Normalization:** (1/(2π)⁴) × π = 1/(2(2π)³) ✓

    **Proof:** Uses `fubini_s_xy_swap` to move s inside, then
    `s_integral_eval` to evaluate the Laplace transform.
-/
theorem laplace_s_integral_with_norm (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    (1 / (2 * π) ^ STDimension : ℝ) *
    ∫ k_sp : SpatialCoords, ∫ s in Set.Ioi 0, ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
    (1 / (2 * (2 * π) ^ (STDimension - 1)) : ℝ) *
      ∫ k_spatial : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
        let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
        (starRingEnd ℂ (f x)) * f y * (1 / ω : ℝ) *
          Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
          Complex.exp (-Complex.I * spatialDot k_spatial (spatialPart x - spatialPart y)) := by
  have hm : 0 < m := Fact.out
  -- Step 1: For each k_sp, swap s with (x, y) using fubini_s_xy_swap
  have h_lhs_fubini : ∫ k_sp : SpatialCoords, ∫ s in Set.Ioi 0, ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
        Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime, ∫ s in Set.Ioi 0,
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    congr 1
    ext k_sp
    exact fubini_s_xy_swap m f k_sp
  rw [h_lhs_fubini]
  -- Step 3: For each (k_sp, x, y), the s-integral evaluates via the Laplace transform
  -- Apply s_integral_complex_eval to the inner s-integral
  have h_inner_eval : ∫ (k_sp : SpatialCoords) (x : SpaceTime) (y : SpaceTime),
      ∫ (s : ℝ) in Set.Ioi 0,
        (starRingEnd ℂ (f x)) * f y *
          (Real.sqrt (π / s) : ℂ) * Complex.exp (-((-(x 0) - y 0)^2 / (4 * s) : ℝ)) *
          Complex.exp (-(s : ℂ) * (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      ∫ (k_sp : SpatialCoords) (x : SpaceTime) (y : SpaceTime),
        (starRingEnd ℂ (f x)) * f y * (π / Real.sqrt (‖k_sp‖^2 + m^2) : ℂ) *
          Complex.exp (-(|-(x 0) - y 0| : ℝ) * Real.sqrt (‖k_sp‖^2 + m^2)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
    congr 1
    ext k_sp
    congr 1
    ext x
    congr 1
    ext y
    exact s_integral_complex_eval k_sp x y m hm f
  rw [h_inner_eval]
  -- Step 4: Apply normalization constant identity (1/(2π)^4) * π = 1/(2(2π)^3),
  -- pulling π out of π/ω into the front constant.
  simp only [STDimension]
  norm_num
  -- Goal: ((2 * ↑π) ^ 4)⁻¹ * ∫ ... (↑π / ↑√ω) ... = ((2 * ↑π) ^ 3)⁻¹ * (1/2) * ∫ ... (↑√ω)⁻¹ ...
  -- Step B: Front constant identity (complex version)
  have h_const : ((2 * (π : ℂ)) ^ 4)⁻¹ * (π : ℂ) = ((2 * (π : ℂ)) ^ 3)⁻¹ * (1 / 2) := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have h2π : (2 * (π : ℂ)) ≠ 0 := by simp [hπ]
    field_simp
  -- Step C: Rewrite the integrand to factor out π: (π/ω) = π * (1/ω)
  have h_integrand : ∀ k_sp : SpatialCoords, ∀ x y : SpaceTime,
      (starRingEnd ℂ) (f x) * f y * ((π : ℂ) / ↑(Real.sqrt (‖k_sp‖^2 + m^2))) *
        Complex.exp (-(↑|-x.ofLp 0 - y.ofLp 0| * ↑(Real.sqrt (‖k_sp‖^2 + m^2)))) *
        Complex.exp (-(Complex.I * ↑(spatialDot k_sp (spatialPart x - spatialPart y)))) =
      (π : ℂ) * ((starRingEnd ℂ) (f x) * f y * (↑(Real.sqrt (‖k_sp‖^2 + m^2)))⁻¹ *
        Complex.exp (-(↑|-x.ofLp 0 - y.ofLp 0| * ↑(Real.sqrt (‖k_sp‖^2 + m^2)))) *
        Complex.exp (-(Complex.I * ↑(spatialDot k_sp (spatialPart x - spatialPart y))))) := by
    intro k_sp x y
    have hω : (↑(Real.sqrt (‖k_sp‖^2 + m^2)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (omega_pos k_sp m hm).ne'
    field_simp
  -- Step D: Apply the integrand factorization across the triple integral
  have h_integral_eq : ∫ (k_sp : SpatialCoords) (x : SpaceTime) (y : SpaceTime),
        (starRingEnd ℂ) (f x) * f y * ((π : ℂ) / ↑(Real.sqrt (‖k_sp‖^2 + m^2))) *
          Complex.exp (-(↑|-x.ofLp 0 - y.ofLp 0| * ↑(Real.sqrt (‖k_sp‖^2 + m^2)))) *
          Complex.exp (-(Complex.I * ↑(spatialDot k_sp (spatialPart x - spatialPart y)))) =
      (π : ℂ) * ∫ (k_sp : SpatialCoords) (x : SpaceTime) (y : SpaceTime),
        (starRingEnd ℂ) (f x) * f y * (↑(Real.sqrt (‖k_sp‖^2 + m^2)))⁻¹ *
          Complex.exp (-(↑|-x.ofLp 0 - y.ofLp 0| * ↑(Real.sqrt (‖k_sp‖^2 + m^2)))) *
          Complex.exp (-(Complex.I * ↑(spatialDot k_sp (spatialPart x - spatialPart y)))) := by
    simp_rw [h_integrand]
    simp only [← smul_eq_mul (π : ℂ)]
    simp_rw [MeasureTheory.integral_smul]
  -- Step E: factor π out of the integral, then absorb it into the front constant via h_const
  rw [h_integral_eq, ← mul_assoc, h_const]

/-- **THEOREM**: The triple product (s, x, y) of the
    Schwinger-heat kernel bilinear form is integrable.

    This allows applying Fubini to swap ∫_s with ∫_x ∫_y.

    **Proof:**
    Uses `Integrable.mono'` with the bound from `schwinger_bound_integrable`.
    The pointwise bound |integrand| ≤ bound is verified for s > 0,
    and the set s ≤ 0 has measure zero under the restricted measure.
-/
theorem schwinger_bilinear_integrable (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    Integrable (fun (p : ℝ × SpaceTime × SpaceTime) =>
      (starRingEnd ℂ (f p.2.1)) * f p.2.2 *
      Real.exp (-p.1 * m^2) * heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖)
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  -- Get the mass positivity
  have hm : 0 < m := Fact.out
  -- Get boundedness of f: Schwartz functions are bounded
  have hf_bdd : ∃ Cf, ∀ x, ‖f x‖ ≤ Cf := by
    use ‖f.toBoundedContinuousFunction‖
    intro x
    exact BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction x
  obtain ⟨Cf, hCf⟩ := hf_bdd
  -- The bound separates: |integrand| ≤ ‖f(x)‖ * Cf * exp(-sm²) * H(s, ‖Θx-y‖), whose triple
  -- integral is Cf * ‖f‖_{L¹} / m² < ∞ (heat kernel L¹-normalized, exp(-sm²) integrable).
  -- Define the integrand
  let F : ℝ × SpaceTime × SpaceTime → ℂ := fun p =>
    (starRingEnd ℂ (f p.2.1)) * f p.2.2 *
    Real.exp (-p.1 * m^2) * heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖
  -- Define the real-valued dominating function
  let bound : ℝ × SpaceTime × SpaceTime → ℝ := fun p =>
    ‖f p.2.1‖ * Cf * Real.exp (-p.1 * m^2) * heatKernelPositionSpace p.1 ‖timeReflection p.2.1 -
      p.2.2‖
  -- The measure
  let μ : Measure (ℝ × SpaceTime × SpaceTime) :=
    (volume.restrict (Set.Ioi 0)).prod ((volume : Measure SpaceTime).prod volume)
  -- Pointwise bound: ‖F p‖ ≤ bound p for s > 0
  have h_bound : ∀ p : ℝ × SpaceTime × SpaceTime, p.1 ∈ Set.Ioi 0 →
      ‖F p‖ ≤ bound p := by
    intro p hp
    simp only [F, bound, Set.mem_Ioi] at hp ⊢
    rw [norm_mul, norm_mul, norm_mul]
    -- ‖conj(f x)‖ = ‖f x‖
    have h1 : ‖(starRingEnd ℂ) (f p.2.1)‖ = ‖f p.2.1‖ := RCLike.norm_conj _
    rw [h1]
    -- ‖exp(-sm²)‖ = exp(-sm²) since exp is positive
    have h2 : ‖(Real.exp (-p.1 * m^2) : ℂ)‖ = Real.exp (-p.1 * m^2) := by
      simp only [Complex.norm_real]
      exact abs_of_pos (Real.exp_pos _)
    rw [h2]
    -- ‖H(s,r)‖ = H(s,r) since H is non-negative for s > 0
    have h3 : ‖(heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖ : ℂ)‖ =
        heatKernelPositionSpace p.1 ‖timeReflection p.2.1 - p.2.2‖ := by
      simp only [Complex.norm_real]
      exact abs_of_nonneg (heatKernelPositionSpace_nonneg p.1 hp _)
    rw [h3]
    -- Now: ‖f x‖ * ‖f y‖ * exp * H ≤ ‖f x‖ * Cf * exp * H, from ‖f y‖ ≤ Cf
    gcongr
    · exact heatKernelPositionSpace_nonneg p.1 hp _
    · exact hCf p.2.2
  -- The bound ∫∫∫ = Cf * ‖f‖_{L¹} / m² is integrable by Tonelli (order y, x, s).
  have h_bound_integrable : Integrable bound μ :=
    schwinger_bound_integrable m f Cf hCf
  -- AEStronglyMeasurable of F
  have h_meas : AEStronglyMeasurable F μ := by
    -- F involves products of continuous functions
    -- F p = conj(f p.2.1) * f p.2.2 * exp(-p.1 * m²) * H(p.1, ‖Θ p.2.1 - p.2.2‖)
    apply AEStronglyMeasurable.mul
    · apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · -- conj(f p.2.1) is measurable
          apply Continuous.aestronglyMeasurable
          exact continuous_star.comp (f.continuous.comp continuous_snd.fst)
        · -- f p.2.2 is measurable
          apply Continuous.aestronglyMeasurable
          exact f.continuous.comp continuous_snd.snd
      · -- exp(-p.1 * m²) : ℂ is measurable
        apply Continuous.aestronglyMeasurable
        exact continuous_ofReal.comp (Real.continuous_exp.comp
          ((continuous_fst.neg).mul continuous_const))
    · -- H(p.1, ‖Θ p.2.1 - p.2.2‖) : ℂ is AEStronglyMeasurable
      -- Use heatKernelPositionSpace_aestronglyMeasurable
      exact heatKernelPositionSpace_aestronglyMeasurable
  -- Apply Integrable.mono'
  apply Integrable.mono' h_bound_integrable h_meas
  -- Show ‖F p‖ ≤ bound p a.e. under the restricted measure
  -- Since μ = (volume.restrict (Set.Ioi 0)).prod (volume.prod volume),
  -- we only need to verify the bound for s > 0 (μ-a.e.)
  -- The set {p | p.1 ∉ Ioi 0} has μ-measure zero since the first marginal is restricted to Ioi 0
  rw [ae_iff]
  -- First show that {p | p.1 ≤ 0} has μ-measure zero
  have h_null : μ {p : ℝ × SpaceTime × SpaceTime | p.1 ≤ 0} = 0 := by
    have h_preimage : {p : ℝ × SpaceTime × SpaceTime | p.1 ≤ 0} = Set.Iic 0 ×ˢ Set.univ := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true]
    rw [h_preimage, Measure.prod_prod]
    rw [Measure.restrict_apply measurableSet_Iic]
    simp only [Set.Iic_inter_Ioi, Set.Ioc_self, measure_empty, zero_mul]
  -- The set where the bound fails is contained in {p | p.1 ≤ 0}
  apply measure_mono_null _ h_null
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  by_contra h_pos
  exact hp (h_bound p (not_le.mp h_pos))

/-- The permutation map (x, (y, s)) ↦ (s, (x, y)) as a measurable equivalence.
    Constructed by composing prodAssoc.symm (reassociating) with prodComm (swapping).
-/
private def schwinger_tripleReorder :
    SpaceTime × (SpaceTime × ℝ) ≃ᵐ ℝ × (SpaceTime × SpaceTime) :=
  MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm

/-- The schwinger_tripleReorder map is measure-preserving on product Lebesgue measures
    with the s-measure restricted to Ioi 0.
-/
private lemma measurePreserving_schwinger_tripleReorder :
    MeasurePreserving schwinger_tripleReorder
      ((volume : Measure SpaceTime).prod (volume.prod (volume.restrict (Set.Ioi 0))))
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  unfold schwinger_tripleReorder
  -- Step 1: prodAssoc.symm preserves measure from μ.prod(μ.prod ν) to (μ.prod μ).prod ν
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodAssoc (α := SpaceTime) (β := SpaceTime) (γ := ℝ)).symm
      ((volume : Measure SpaceTime).prod (volume.prod (volume.restrict (Set.Ioi 0))))
      ((volume.prod volume).prod (volume.restrict (Set.Ioi 0))) :=
    (measurePreserving_prodAssoc volume volume (volume.restrict (Set.Ioi 0))).symm
      MeasurableEquiv.prodAssoc
  -- Step 2: prodComm preserves measure from (μ.prod μ).prod ν to ν.prod(μ.prod μ)
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodComm (α := SpaceTime × SpaceTime) (β := ℝ))
      (((volume : Measure SpaceTime).prod volume).prod (volume.restrict (Set.Ioi 0)))
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) :=
    MeasureTheory.Measure.measurePreserving_swap
  exact h2.comp h1

/-- **Fubini swap for the Schwinger integrand.**

    Given integrability of the Schwinger integrand on the product space,
    the iterated integrals can be computed in either order:
    ∫_x ∫_y ∫_s F = ∫_s ∫_x ∫_y F

    **Proof:**
    Both sides equal ∫∫∫ F over (Ioi 0) × SpaceTime × SpaceTime by Fubini-Tonelli.
    The proof uses `integral_prod` to convert iterated integrals to product integrals,
    and the measure-preserving map `schwinger_tripleReorder` to connect them.
-/
theorem schwinger_fubini_core (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    ∫ x : SpaceTime, ∫ y : SpaceTime, ∫ s in Set.Ioi 0,
      (starRingEnd ℂ (f x)) * f y *
        (Real.exp (-s * m^2) : ℂ) * heatKernelPositionSpace s ‖timeReflection x - y‖ =
    ∫ s in Set.Ioi 0, ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (Real.exp (-s * m^2) : ℂ) * heatKernelPositionSpace s ‖timeReflection x - y‖ := by
  -- Define the integrand function
  let F : SpaceTime → SpaceTime → ℝ → ℂ := fun x y s =>
    (starRingEnd ℂ (f x)) * f y *
      (Real.exp (-s * m^2) : ℂ) * heatKernelPositionSpace s ‖timeReflection x - y‖
  -- Define product functions for LHS and RHS orderings
  let fL : SpaceTime × (SpaceTime × ℝ) → ℂ := fun p => F p.1 p.2.1 p.2.2
  let fR : ℝ × (SpaceTime × SpaceTime) → ℂ := fun q => F q.2.1 q.2.2 q.1
  -- Get integrability on (s, (x, y)) from schwinger_bilinear_integrable
  have h_int_sxy := schwinger_bilinear_integrable m f
  -- Show h_int_sxy equals Integrable fR on the (s, x, y) measure
  have h_int_fR : Integrable fR ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
    convert h_int_sxy using 1
  -- Transfer to (x, (y, s)) via measure-preserving map
  have h_int_xys : Integrable fL
      ((volume : Measure SpaceTime).prod (volume.prod (volume.restrict (Set.Ioi 0)))) := by
    have hcomp : fL = fR ∘ schwinger_tripleReorder := rfl
    rw [hcomp]
    exact (measurePreserving_schwinger_tripleReorder.integrable_comp_emb
        schwinger_tripleReorder.measurableEmbedding).mpr h_int_fR
  -- LHS = ∫ fL on product space (via Fubini twice)
  have hLHS : ∫ x, ∫ y, ∫ s in Set.Ioi 0, F x y s ∂volume ∂volume ∂volume =
      ∫ p, fL p ∂((volume : Measure SpaceTime).prod (volume.prod (volume.restrict (Set.Ioi 0)))) :=
        by
    -- Convert inner ∫y ∫s → ∫(y,s) using Fubini
    have inner_fubini : ∀ᵐ x ∂(volume : Measure SpaceTime),
        ∫ y, ∫ s in Set.Ioi 0, F x y s ∂volume =
        ∫ ys, F x ys.1 ys.2 ∂(volume.prod (volume.restrict (Set.Ioi 0))) := by
      filter_upwards [h_int_xys.prod_right_ae] with x hx
      exact (integral_prod (fun ys => F x ys.1 ys.2) hx).symm
    rw [integral_congr_ae inner_fubini]
    exact (integral_prod fL h_int_xys).symm
  -- RHS = ∫ fR on product space (via Fubini twice)
  have hRHS : ∫ s in Set.Ioi 0, ∫ x, ∫ y, F x y s ∂volume ∂volume =
      ∫ q, fR q ∂((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
    -- Convert inner ∫x ∫y → ∫(x,y) using Fubini
    have inner_fubini : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0) : Measure ℝ),
        ∫ x, ∫ y, F x y s ∂volume ∂volume =
        ∫ xy, F xy.1 xy.2 s ∂(volume.prod volume) := by
      filter_upwards [h_int_sxy.prod_right_ae] with s hs
      exact (integral_prod (fun xy => F xy.1 xy.2 s) hs).symm
    rw [integral_congr_ae inner_fubini]
    exact (integral_prod fR h_int_sxy).symm
  -- Key identity: fL = fR ∘ schwinger_tripleReorder
  have hfL_eq : ∀ p, fL p = fR (schwinger_tripleReorder p) := fun _ => rfl
  -- Connect via measure-preserving transformation
  calc ∫ x, ∫ y, ∫ s in Set.Ioi 0, F x y s ∂volume ∂volume ∂volume
      = ∫ p, fL p ∂((volume : Measure SpaceTime).prod (volume.prod (volume.restrict (Set.Ioi 0))))
        := hLHS
    _ = ∫ p, fR (schwinger_tripleReorder p)
          ∂((volume : Measure SpaceTime).prod (volume.prod (volume.restrict (Set.Ioi 0)))) := rfl
    _ = ∫ q, fR q ∂((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) :=
        measurePreserving_schwinger_tripleReorder.integral_comp
          schwinger_tripleReorder.measurableEmbedding fR
    _ = ∫ s in Set.Ioi 0, ∫ x, ∫ y, F x y s ∂volume ∂volume := hRHS.symm

/-- **Triple integral order swap.**

    Given integrability (from `schwinger_bilinear_integrable`), Fubini's theorem ensures:
    ∫ x ∫ y, F(x,y) * [∫ s, G(s,x,y)] = ∫ s, [∫ x ∫ y, F(x,y) * G(s,x,y)]

    **Proof sketch:**
    This follows from Mathlib's `MeasureTheory.integral_integral_swap` (Fubini-Tonelli)
    applied to the integrable function from `schwinger_bilinear_integrable`.
    The key steps:
    1. Rewrite both sides as integrals over ℝ × SpaceTime × SpaceTime
    2. Apply Fubini to swap the order of integration
    3. Use the integrability hypothesis to justify the swap
-/
theorem schwinger_fubini_swap (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          heatKernelPositionSpace s ‖timeReflection x - y‖) =
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * f y * heatKernelPositionSpace s ‖timeReflection x - y‖ := by
  -- This follows from Fubini's theorem applied to the integrable function
  -- from schwinger_bilinear_integrable.
  --
  -- The proof uses:
  -- 1. Pull fbar(x) * f(y) into the s-integral (independent of s)
  -- 2. Fubini: swap ∫ x ∫ y ∫ s → ∫ s ∫ x ∫ y
  -- 3. Factor exp(-sm²) out of spatial integrals (independent of x, y)
  --
  -- The key technical ingredient is schwinger_bilinear_integrable which ensures
  -- integrability on the triple product space, justifying the Fubini swap.
  have h_int := schwinger_bilinear_integrable m f
  -- Step 1: Rewrite LHS by pulling fbar f into the s-integral
  have h_pull_in : ∀ x y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          heatKernelPositionSpace s ‖timeReflection x - y‖) =
      ∫ s in Set.Ioi 0, (starRingEnd ℂ (f x)) * f y *
        (Real.exp (-s * m^2) : ℂ) * heatKernelPositionSpace s ‖timeReflection x - y‖ := by
    intro x y
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext s
    ring
  simp_rw [h_pull_in]
  -- Step 2: Rewrite RHS by factoring exp(-sm²) out of spatial integrals
  have h_factor_out : ∀ s : ℝ,
      (Real.exp (-s * m^2) : ℂ) *
        ∫ x : SpaceTime, ∫ y : SpaceTime,
          (starRingEnd ℂ (f x)) * f y * heatKernelPositionSpace s ‖timeReflection x - y‖ =
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * f y *
          (Real.exp (-s * m^2) : ℂ) * heatKernelPositionSpace s ‖timeReflection x - y‖ := by
    intro s
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext x
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext y
    ring
  simp_rw [h_factor_out]
  -- Step 3: Apply Fubini to swap ∫_x ∫_y ∫_s with ∫_s ∫_x ∫_y
  --
  -- After steps 1 and 2, both sides have the integrand:
  -- F(s,x,y) = fbar(x) * f(y) * exp(-sm²) * H(s, ‖Θx-y‖)
  --
  -- LHS = ∫_x ∫_y [∫_s F(s,x,y) ds] dy dx
  -- RHS = ∫_s [∫_x ∫_y F(s,x,y) dy dx] ds
  --
  -- By Fubini-Tonelli, given F is integrable on the product space (h_int),
  -- both equal the triple integral ∫∫∫ F over (Ioi 0) × SpaceTime × SpaceTime.
  --
  -- The formal proof requires showing:
  -- (a) ∫_x ∫_y ∫_s F = ∫_{(x,y)} ∫_s F = ∫_{(s,x,y)} F  (by integral_integral twice)
  -- (b) ∫_s ∫_x ∫_y F = ∫_s ∫_{(x,y)} F = ∫_{(s,x,y)} F  (by integral_integral twice)
  -- Hence (a) = (b).
  exact schwinger_fubini_core m f

/-- The kernel-level Schwinger representation holds for Θx ≠ y.
    This follows from `covarianceSchwingerRep_eq_freeCovarianceBessel`.
-/
lemma freeCovariance_eq_schwingerRep (m : ℝ) (hm : 0 < m) (x y : SpaceTime)
    (hxy : timeReflection x ≠ y) :
    (freeCovariance m (timeReflection x) y : ℂ) =
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      heatKernelPositionSpace s ‖timeReflection x - y‖ := by
  -- Use covarianceSchwingerRep_eq_freeCovarianceBessel + definitions
  have h := covarianceSchwingerRep_eq_freeCovarianceBessel m hm (timeReflection x) y hxy
  -- h : covarianceSchwingerRep m ‖Θx - y‖ = freeCovarianceBessel m (Θx) y
  -- freeCovariance = freeCovarianceBessel by definition (abbrev)
  -- So h says: covarianceSchwingerRep m ‖Θx-y‖ = freeCovariance m (Θx) y
  -- Unfold covarianceSchwingerRep in h
  simp only [covarianceSchwingerRep] at h
  -- Now h : ∫ t in Ioi 0, exp(-t*m²) * H(t, ‖Θx-y‖) = freeCovarianceBessel m (Θx) y
  -- Since freeCovariance = freeCovarianceBessel (by abbrev):
  have h' : freeCovariance m (timeReflection x) y =
      ∫ t in Set.Ioi 0, Real.exp (-t * m^2) * heatKernelPositionSpace t ‖timeReflection x - y‖ :=
    h.symm
  -- Cast to complex
  rw [h']
  -- Convert real integral to complex integral
  -- Goal: ↑(∫ t in Ioi 0, f t) = ∫ s in Ioi 0, ↑(f s)
  -- Use integral_complex_ofReal (reversed)
  rw [← integral_complex_ofReal]
  congr 1
  ext s
  push_cast
  ring

/-- **Bessel bilinear form equals the Schwinger heat kernel form.**

    This follows from:
    1. **Kernel equality** (a.e.): For Θx ≠ y (which is a.e. in the product measure),
       freeCovariance(Θx, y) = covarianceSchwingerRep(|Θx - y|) = ∫₀^∞ e^{-sm²} H(s, |Θx-y|) ds
       This is proven via `covarianceSchwingerRep_eq_freeCovarianceBessel`.

    2. **Fubini swap**: Exchanging the s-integral with the x,y-integrals.
       Uses `schwinger_bilinear_integrable`.

    **Mathematical statement:**
    ∫∫ conj(f(x)) C(Θx,y) f(y) dx dy = ∫₀^∞ e^{-sm²} [∫∫ conj(f) f H(s,|Θx-y|) dx dy] ds
-/
theorem bilinear_schwinger_eq_heatKernel (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * (freeCovariance m (timeReflection x) y : ℂ) * f y =
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * f y * heatKernelPositionSpace s ‖timeReflection x - y‖ := by
  -- Substitute the Schwinger representation off the measure-zero diagonal {Θx = y}, then
  -- swap the s-integral outward by Fubini (schwinger_fubini_swap).
  have hm : 0 < m := Fact.out
  -- Step 1: Rewrite LHS using kernel equality (for Θx ≠ y)
  have h_kernel_eq : ∀ x y, timeReflection x ≠ y →
      (starRingEnd ℂ (f x)) * (freeCovariance m (timeReflection x) y : ℂ) * f y =
      (starRingEnd ℂ (f x)) * f y *
        (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          heatKernelPositionSpace s ‖timeReflection x - y‖) := by
    intro x y hxy
    rw [freeCovariance_eq_schwingerRep m hm x y hxy]
    ring
  -- Step 2: h_kernel_eq holds a.e. since for each x the diagonal {y : Θx = y} = {Θx}
  -- is a singleton (measure zero by NoAtoms).
  have h_ae : ∀ᵐ x ∂(volume : Measure SpaceTime), ∀ᵐ y ∂volume,
      (starRingEnd ℂ (f x)) * (freeCovariance m (timeReflection x) y : ℂ) * f y =
      (starRingEnd ℂ (f x)) * f y *
        (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
          heatKernelPositionSpace s ‖timeReflection x - y‖) := by
    filter_upwards with x
    have h_compl : ∀ᵐ y ∂(volume : Measure SpaceTime), y ≠ timeReflection x := by
      rw [ae_iff]
      simp
    filter_upwards [h_compl] with y hy
    exact h_kernel_eq x y (Ne.symm hy)
  -- Step 3: Rewrite LHS using a.e. equality
  have lhs_eq : ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * (freeCovariance m (timeReflection x) y : ℂ) * f y =
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * f y *
          (∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
            heatKernelPositionSpace s ‖timeReflection x - y‖) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [h_ae] with x hx
    exact MeasureTheory.integral_congr_ae hx
  rw [lhs_eq]
  -- Step 4: Apply Fubini to swap the integration order
  -- This uses schwinger_fubini_swap
  exact schwinger_fubini_swap m f

/-- **Heat kernel bilinear form equals the mixed representation.**

    This encapsulates the multi-step transformation from heat kernel to mixed rep:
    1. Apply `heatKernel_eq_gaussianFT`: H(s,r) = (1/(2π)^d) ∫_k exp(-ik·z) exp(-s|k|²)
    2. Decompose k = (k₀, k_sp) into time and spatial momenta
    3. Do k₀ integral using `gaussian_fourier_1d`: gives √(π/s) exp(-t²/(4s))
    4. Fubini swap: exchange s and k_sp integrals (justified by Schwartz decay)
    5. Do s-integral using `laplace_integral_half_power` with a = t²/4, b = |k_sp|² + m²:
       √π ∫₀^∞ s^{-1/2} exp(-t²/(4s) - (|k_sp|²+m²)s) ds = (π/ω) exp(-ω|t|)
    6. Normalize: (1/(2π)^4) × π = 1/(2(2π)³)

    **Dependencies:**
    - `heatKernel_eq_gaussianFT` (PROVEN, line 153)
    - `gaussian_fourier_1d` (PROVEN, line 814)
    - `laplace_integral_half_power` (THEOREM, line 135)
    - Fubini applications (require integrability - uses Schwartz decay)
-/
theorem heatKernel_bilinear_to_mixed_rep (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (hf_supp : ∀ x, x 0 ≤ 0 → f x = 0) :
    ∫ s in Set.Ioi 0, (Real.exp (-s * m^2) : ℂ) *
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * f y * heatKernelPositionSpace s ‖timeReflection x - y‖ =
    (1 / (2 * (2 * π) ^ (STDimension - 1)) : ℝ) *
      ∫ k_spatial : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
        let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
        (starRingEnd ℂ (f x)) * f y * (1 / ω : ℝ) *
          Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
          Complex.exp (-Complex.I * spatialDot k_spatial (spatialPart x - spatialPart y)) := by
  -- Substitute heat kernel FT (heatKernel_bilinear_fourier_form), swap s ↔ k_sp
  -- (fubini_s_ksp_swap), then evaluate the s-integral (laplace_s_integral_with_norm).
  rw [heatKernel_bilinear_fourier_form m f, ← laplace_s_integral_with_norm m f]
  congr 1
  exact @fubini_s_ksp_swap m _ f hf_supp

/-- **THEOREM**: The Bessel bilinear form equals the mixed representation form.

    This connects the position-space Bessel kernel to its momentum-space
    mixed representation (spatial in momentum, time in position).

    ∫∫ conj(f(x)) C(Θx, y) f(y) dx dy
    = (1/(2(2π)^{d-1})) ∫_{k_sp} ∫_x ∫_y conj(f) f (1/ω) exp(-ω|t|) exp(-i k_sp·r_sp)

    where ω = √(|k_sp|² + m²), t = -x₀ - y₀, r_sp = x_sp - y_sp.

    **Proof outline** (directly at bilinear level):

    1. **Schwinger representation**: Insert C(Θx,y) = ∫₀^∞ exp(-sm²) H(s,|Θx-y|) ds

    2. **Heat kernel as Gaussian FT**: By `heatKernel_eq_gaussianFT`,
       H(s,r) = (1/(2π)^d) ∫_k exp(-ik·z) exp(-s|k|²) d^d k

    3. **Decompose k = (k₀, k_sp)**: The 4D k-integral becomes product of 1D and 3D integrals

    4. **Do k₀ integral**: By `gaussian_fourier_1d` (PROVEN),
       ∫ exp(-ik₀t) exp(-sk₀²) dk₀ = √(π/s) exp(-t²/(4s))

    5. **Fubini to swap s and k_sp**: Justified by Schwartz decay of f (absolute convergence)

    6. **Do s-integral**: By `laplace_integral_half_power` (THEOREM) with a = t²/4, b = ω²:
       √π · ∫₀^∞ s^{-1/2} exp(-t²/(4s) - ω²s) ds = (π/ω) exp(-ω|t|)

    7. **Normalize**: (1/(2π)^4) × π = 1/(2(2π)³) ✓

    **Note**: Working directly at bilinear level ensures absolute convergence
    (Schwartz test functions provide decay even when t = 0).
-/
theorem bessel_bilinear_eq_mixed_representation (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (hf_supp : ∀ x, x 0 ≤ 0 → f x = 0) :
  ∫ x : SpaceTime, ∫ y : SpaceTime,
    (starRingEnd ℂ (f x)) *
    (freeCovariance m (timeReflection x) y : ℂ) *
    f y =
  (1 / (2 * (2 * π) ^ (STDimension - 1)) : ℝ) *
  ∫ k_spatial : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
    let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
    (starRingEnd ℂ (f x)) * f y *
    (1 / ω : ℝ) *
    Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
    Complex.exp (-Complex.I * spatialDot k_spatial (spatialPart x - spatialPart y)) := by
  -- Step 1: Convert Bessel bilinear form to heat kernel form via Schwinger representation
  rw [bilinear_schwinger_eq_heatKernel]
  -- Step 2: Convert heat kernel form to mixed representation
  exact heatKernel_bilinear_to_mixed_rep m f hf_supp

/-- The mixed representation integrand can be converted to the k₀-inside form
    using the Fourier inversion identity for the Lorentzian.

    By `fourier_lorentzian_1d_neg`:
    (π/ω) exp(-ω|t|) = ∫_{k₀} exp(-ik₀t)/(k₀²+ω²) dk₀

    So: (1/ω) exp(-ω|t|) = (1/π) ∫_{k₀} exp(-ik₀t)/(k₀²+ω²) dk₀
-/
lemma mixed_rep_to_k0_inside_integrand (k_spatial : SpatialCoords) (m : ℝ) [Fact (0 < m)]
    (t : ℝ) :
    let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
    ((1 / ω : ℝ) : ℂ) * Complex.exp (-(|t| : ℝ) * ω) =
    (1 / π : ℝ) * ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2) := by
  intro ω
  have hω_pos : 0 < ω := by
    simp only [ω]
    apply Real.sqrt_pos_of_pos
    have hm : 0 < m := Fact.out
    nlinarith [sq_nonneg ‖k_spatial‖]
  -- By fourier_lorentzian_1d_neg: ∫ exp(-ik₀t)/(k₀²+ω²) = (π/ω) exp(-ω|t|)
  have h_fourier := fourier_lorentzian_1d_neg ω hω_pos t
  -- Rearrange: (1/ω) exp(-ω|t|) = (1/π) * (π/ω) exp(-ω|t|) = (1/π) * ∫...
  rw [h_fourier]
  push_cast
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hω_ne : ω ≠ 0 := ne_of_gt hω_pos
  field_simp

/-- **Bessel covariance bilinear form equals the k₀-inside momentum form.**

    This follows from:
    1. `bessel_bilinear_eq_mixed_representation`: Bessel = mixed rep
    2. `mixed_rep_to_k0_inside_integrand`: mixed rep integrand = k₀-inside integrand

    The conversion between normalizations works out because:
    - Mixed rep has factor: 1/(2(2π)^{d-1})
    - Converting (1/ω) to (1/π)∫... multiplies by (1/π)
    - Combined: 1/(2π(2π)^{d-1}) = 1/(2π)^d ✓

    **Proof sketch**:
    1. Apply `bessel_bilinear_eq_mixed_representation` to convert LHS to mixed rep
    2. Use `mixed_rep_to_k0_inside_integrand`: (1/ω) exp(-ω|t|) = (1/π) ∫_{k₀}...
    3. Factor the spatial phase into the k₀ integral
    4. Combine normalizations: 1/(2(2π)^{d-1}) × (1/π) = 1/(2π)^d
-/
theorem bilinear_to_k0_inside (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (hf_supp : ∀ x, x 0 ≤ 0 → f x = 0) :
  ∫ x : SpaceTime, ∫ y : SpaceTime,
    (starRingEnd ℂ (f x)) *
    (freeCovariance m (timeReflection x) y : ℂ) *
    f y =
  (1 / (2 * π) ^ STDimension : ℝ) *
  ∫ k_spatial : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
    (starRingEnd ℂ (f x)) * f y *
    (∫ k0 : ℝ, Complex.exp (-Complex.I * (k0 * (-(x 0) - y 0) +
      spatialDot k_spatial (spatialPart x - spatialPart y))) /
        (k0^2 + (Real.sqrt (‖k_spatial‖^2 + m^2))^2)) := by
  -- Step 1: Convert LHS to mixed representation
  rw [bessel_bilinear_eq_mixed_representation m f hf_supp]
  -- Now LHS = (1/(2(2π)^{d-1})) * ∫_{k_sp} ∫_x ∫_y fbar f (1/ω) exp(-ω|t|) exp(-i k·r)
  -- RHS = (1/(2π)^d) * ∫_{k_sp} ∫_x ∫_y fbar f [∫_{k₀} exp(-iφ)/(k₀²+ω²)]
  -- Step 2: Prove normalization identity (as complex numbers)
  have h_norm : ((1 / (2 * (2 * π) ^ (STDimension - 1)) : ℝ) : ℂ) =
      ((1 / (2 * π) ^ STDimension : ℝ) : ℂ) * (π : ℂ) := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    rw [show STDimension = 4 from rfl]
    push_cast
    field_simp
  -- Step 3: Rewrite coefficient using h_norm; ((1/(2π)^d) * π) * ∫ = (1/(2π)^d) * (π * ∫)
  conv_lhs => rw [h_norm]
  rw [mul_assoc]
  -- Step 4: Show the integrals are equal
  congr 1
  -- Need to show: π * ∫_{k_sp} ... (mixed rep integrand) = ∫_{k_sp} ... (k₀-inside integrand)
  -- Pull π into the integral
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with k_spatial
  -- For each k_spatial, show the inner integrals are equal
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  -- Now at the pointwise level:
  -- LHS: π * (fbar f (1/ω) exp(-ω|t|) exp(-i k·r))
  -- RHS: fbar f [∫_{k₀} exp(-i(k₀t + k·r))/(k₀²+ω²)]
  set ω := Real.sqrt (‖k_spatial‖^2 + m^2) with hω_def
  set t := -(x 0) - y 0 with ht_def
  set r_spatial := spatialPart x - spatialPart y
  -- Use the key identity: (1/ω) exp(-ω|t|) = (1/π) ∫_{k₀} exp(-ik₀t)/(k₀²+ω²)
  have h_key := mixed_rep_to_k0_inside_integrand k_spatial m t
  simp only at h_key
  -- Factor the spatial phase into the k₀ integral
  have h_phase_factor : ∀ k0 : ℝ,
      Complex.exp (-Complex.I * (k0 * t + spatialDot k_spatial r_spatial)) =
      Complex.exp (-Complex.I * k0 * t) * Complex.exp (-Complex.I * spatialDot k_spatial r_spatial)
        := by
    intro k0
    rw [← Complex.exp_add]
    congr 1
    ring
  -- Factor spatial phase out of the k₀ integral
  have h_integral_factor :
      ∫ k0 : ℝ, Complex.exp (-Complex.I * (k0 * t + spatialDot k_spatial r_spatial)) /
        (k0^2 + ω^2) =
      (Complex.exp (-Complex.I * spatialDot k_spatial r_spatial)) *
      ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with k0
    rw [h_phase_factor]
    ring
  -- The goal is now at the pointwise level:
  -- LHS: π * (fbar f (1/ω) exp(-|t|ω) exp(-i k·r))
  -- RHS: fbar f [∫_{k₀} exp(-i(k₀t + k·r))/(k₀²+ω²)]
  -- h_integral_factor says:
  -- ∫_{k₀} exp(-i(k₀t + k·r))/(k₀²+ω²) = exp(-i k·r) * ∫_{k₀} exp(-ik₀t)/(k₀²+ω²)
  -- h_key says: (1/ω) exp(-|t|ω) = (1/π) ∫_{k₀} exp(-ik₀t)/(k₀²+ω²)
  -- First, convert the RHS to use t instead of the explicit expression
  have ht_eq : (-↑(x.ofLp 0) - ↑(y.ofLp 0) : ℂ) = (t : ℂ) := by
    simp only [ht_def]
    push_cast
    ring
  -- Rewrite the RHS to use t
  conv_rhs => rw [ht_eq]
  -- Substitute RHS using h_integral_factor
  rw [h_integral_factor]
  -- Now RHS = fbar f (exp(-i k·r) * ∫_{k₀} exp(-ik₀t)/(k₀²+ω²))
  -- Simplify LHS using h_key
  simp only [hω_def] at h_key ⊢
  -- LHS: π * (fbar f (1/ω) exp(-|t|ω) exp(-i k·r)); use h_key and π * (1/π) = 1
  have h_pi_cancel : ((π : ℝ) : ℂ) * ((1 / π : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  calc ↑π * ((starRingEnd ℂ) (f x) * f y * ↑(1 / ω) *
        Complex.exp (-(|t| : ℝ) * ω) * Complex.exp (-Complex.I * spatialDot k_spatial r_spatial))
    = (starRingEnd ℂ) (f x) * f y * (↑π * (↑(1 / ω) * Complex.exp (-(|t| : ℝ) * ω))) *
        Complex.exp (-Complex.I * spatialDot k_spatial r_spatial) := by ring
    _ = (starRingEnd ℂ) (f x) * f y * (↑π * (↑(1 / π) * ∫ k0 : ℝ,
      Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2))) *
        Complex.exp (-Complex.I * spatialDot k_spatial r_spatial) := by rw [h_key]
    _ = (starRingEnd ℂ) (f x) * f y * (∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2)) *
        Complex.exp (-Complex.I * spatialDot k_spatial r_spatial) := by
          -- π * (1/π * ...) = (π * 1/π) * ... = 1 * ... = ...
          have h1 : (↑π * (↑(1 / π) * ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2)))
                  = (↑π * ↑(1 / π)) * ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2) :=
                    by ring
          rw [h1, h_pi_cancel, one_mul]
    _ = (starRingEnd ℂ) (f x) * f y *
        (Complex.exp (-Complex.I * spatialDot k_spatial r_spatial) *
          ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2)) := by ring

/-! ## Non-negativity -/


end
