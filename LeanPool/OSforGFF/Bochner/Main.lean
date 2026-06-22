/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/


import LeanPool.OSforGFF.Bochner.PositiveDefinite
import LeanPool.OSforGFF.Bochner.FejerPD
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Measure.IntegralCharFun

/-!
# Bochner's Theorem

Bochner's theorem states that a continuous function φ : V → ℂ on a
finite-dimensional real inner product space is positive definite with φ(0) = 1
if and only if it is the characteristic function of a unique probability
measure on V.

## Proof strategy

We prove the hard direction (PD → measure) via **Gaussian regularization**,
avoiding the Riesz-Markov-Kakutani theorem entirely:

1. **Phase 1** (`pd_l1_fourier_nonneg`): An L¹ positive-definite function has
   a nonneg real Fourier transform. Proved by testing the PD double integral
   against explicit shifted Gaussians g(x) = exp(-a‖x‖² - i⟨ξ₀,x⟩). Since
   |ĝ(ξ)|² forms a Dirac sequence as a → 0, continuity of φ̂ (from
   Riemann-Lebesgue) forces φ̂(ξ₀) ≥ 0 at every point.

2. **Phase 2** (`gaussian_regularization`): Define φ_ε(x) = φ(x) · exp(-ε‖x‖²).
   By Schur (pointwise product of PD is PD), φ_ε is PD. Gaussian decay
   guarantees φ_ε ∈ L¹.

3. **Phase 3** (`measure_of_pd_l1`): Apply Phase 1 to get φ̂_ε ≥ 0, then
   define dμ_ε = φ̂_ε dλ. Since ∫ φ̂_ε = φ_ε(0) = 1, this is a probability
   measure. By Fourier inversion, charFun(μ_ε) = φ_ε.

4. **Phase 4** (`tightness_from_charfun`): As ε → 0, charFun(μ_ε)(x) → φ(x)
   pointwise. Tightness of {μ_ε} follows from the standard bound
   μ({‖x‖ > R}) ≤ C ∫_{‖ξ‖≤δ} (1 - Re(φ̂_ε(ξ))) dξ → 0, using continuity
   of φ at 0. Prokhorov's theorem (in Mathlib) extracts a weakly convergent
   subsequence μ_{ε_k} → μ. Testing against x ↦ exp(i⟨ξ,x⟩) shows
   charFun(μ) = φ.

5. **Phase 5** (`Measure.ext_of_charFun`): Uniqueness is already in Mathlib.

## Main results

- `bochner_theorem`: the full theorem
- `pd_l1_fourier_nonneg`: L¹ PD ⟹ nonneg Fourier transform (Phase 1)

## References

- S. Bochner, "Monotone Funktionen, Stieltjessche Integrale und harmonische
  Analyse", Math. Annalen 108 (1933), 378–410
- W. Rudin, *Fourier Analysis on Groups*, Wiley (1962), Theorem 1.4.3
- G.B. Folland, *A Course in Abstract Harmonic Analysis*, CRC Press (2016), §4.2
-/

open MeasureTheory Complex Filter Topology
open scoped Real InnerProductSpace FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ## Phase 1: L¹ positive-definite functions have nonneg Fourier transform

The proof uses explicit shifted Gaussians rather than abstract Plancherel.

Given φ ∈ L¹ with φ positive-definite, we want φ̂(ξ₀) ≥ 0 for each ξ₀.

Test the PD condition with g_a(x) = exp(-a‖x‖²) exp(-i⟨ξ₀,x⟩):
  0 ≤ ∫∫ gbar_a(x) g_a(y) φ(x-y) dx dy = ∫ |ĝ_a(ξ)|² φ̂(ξ) dξ

Since ĝ_a is an explicit Gaussian (Mathlib: `fourier_gaussian_innerProductSpace'`),
|ĝ_a|² is a Gaussian centered at ξ₀ with width ~ 1/√a. As a → 0⁺, this
concentrates at ξ₀. Since φ̂ is continuous (Riemann-Lebesgue), the integral
converges to φ̂(ξ₀) · (const), giving φ̂(ξ₀) ≥ 0.
-/

/-- The double sum ∑ᵢ ∑ⱼ conj(aᵢ) * aⱼ equals normSq(∑ₖ aₖ). -/
private lemma sum_star_mul_eq_normSq {m : ℕ} (a : Fin m → ℂ) :
    ∑ i, ∑ j, starRingEnd ℂ (a i) * a j = ↑(Complex.normSq (∑ k, a k)) := by
  have h : (↑(Complex.normSq (∑ k, a k)) : ℂ) =
      (starRingEnd ℂ) (∑ k, a k) * ∑ k, a k := by
    rw [starRingEnd_apply, star_def, Complex.normSq_eq_conj_mul_self]
  rw [h, map_sum, Finset.sum_mul_sum]

/-! ## Phase 1.5: Characteristic functions are positive definite

The "forward" direction of Bochner: the characteristic function of any
finite measure is positive definite. This gives us PD of the Gaussian
as a corollary: exp(-ε‖x‖²) is the charFun of a Gaussian measure.
-/

omit [FiniteDimensional ℝ V] in
/-- Forward Bochner: the characteristic function of any finite measure is PD.

    Proof: charFun(μ)(t) = ∫ exp(i⟨x,t⟩) dμ(x). So
    ∑ᵢⱼ cbarᵢcⱼ charFun(tᵢ-tⱼ) = ∫ |∑ₖ cₖ exp(i⟨x,tₖ⟩)|² dμ(x) ≥ 0.

    The key steps are: (1) swap finite sum and integral, (2) recognize
    the integrand as a norm squared.
-/
lemma isPositiveDefinite_charFun (μ : Measure V) [IsFiniteMeasure μ] :
    IsPositiveDefinite (fun t : V => charFun μ t) where
  hermitian t := by
    rw [starRingEnd_apply, star_def]
    exact charFun_neg t
  nonneg m t c := by
    -- Step 1: Unfold charFun
    simp only [charFun_apply]
    -- Step 2: Show the .re of the sum equals ∫ normSq(∑ₖ cₖ e^{-i⟨x,tₖ⟩}) dμ ≥ 0
    suffices h : (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
        ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ).re =
        ∫ x, Complex.normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I)) ∂μ by
      rw [h]
      exact integral_nonneg (fun x => Complex.normSq_nonneg _)
    -- Integrability of exponentials on a finite measure (norm ≤ 1)
    have hexp_int : ∀ v : V, Integrable (fun x : V =>
        cexp (↑⟪x, v⟫_ℝ * I)) μ :=
      fun v => (memLp_top_of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
        (ae_of_all _ fun x => by simp [Complex.norm_exp_ofReal_mul_I])).integrable le_top
    -- Integrability of each summand cbarᵢcⱼ·exp
    have hterm_int : ∀ i j, Integrable (fun x : V =>
        (starRingEnd ℂ) (c i) * c j * cexp (↑⟪x, t i - t j⟫_ℝ * I)) μ :=
      fun i j => (hexp_int (t i - t j)).const_mul _
    -- Step A: Complex equality: ∑ᵢ∑ⱼ cbarᵢcⱼ ∫ exp = ∫ ↑(normSq(∑ cₖexp))
    have hcomplex : ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
        ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ =
        ∫ x, ↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I))) ∂μ := by
      -- Pull constants into integrals and merge sums
      calc ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
              ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ
          = ∑ i, ∑ j, ∫ x, (starRingEnd ℂ) (c i) * c j *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            congr 1; ext i; congr 1; ext j; exact (integral_const_mul _ _).symm
        _ = ∑ i, ∫ x, ∑ j, (starRingEnd ℂ) (c i) * c j *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            congr 1; ext i
            exact (integral_finsetSum _ (fun j _ => hterm_int i j)).symm
        _ = ∫ x, ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            exact (integral_finsetSum _ (fun i _ =>
              integrable_finsetSum _ (fun j _ => hterm_int i j))).symm
        _ = ∫ x, ↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I))) ∂μ := by
            congr 1; ext x
            -- Algebraic identity: ∑ᵢ∑ⱼ cbarᵢcⱼe^{i⟨x,tᵢ-tⱼ⟩} = ↑(normSq(∑ cₖe^{-i⟨x,tₖ⟩}))
            -- Use sum_star_mul_eq_normSq with aₖ = cₖ * exp(-i⟨x,tₖ⟩)
            rw [← sum_star_mul_eq_normSq]
            congr 1; ext i; congr 1; ext j
            -- Goal: cbarᵢ * cⱼ * exp(⟨x,tᵢ-tⱼ⟩*I) = conj(cᵢ*exp(-⟨x,tᵢ⟩*I)) * (cⱼ*exp(-⟨x,tⱼ⟩*I))
            rw [map_mul, mul_mul_mul_comm]
            congr 1
            -- conj(exp(-⟨x,tᵢ⟩*I)) * exp(-⟨x,tⱼ⟩*I) = exp(⟨x,tᵢ-tⱼ⟩*I)
            -- conj(exp(-r*I)) = exp(r*I)
            rw [starRingEnd_apply, star_def, ← Complex.exp_conj]
            simp only [Complex.conj_ofReal, Complex.conj_I, map_mul, mul_neg]
            -- exp(⟨x,tᵢ⟩*I) * exp(-⟨x,tⱼ⟩*I) = exp((⟨x,tᵢ⟩-⟨x,tⱼ⟩)*I)
            rw [← Complex.exp_add]
            congr 1
            rw [inner_sub_right]; push_cast; ring
    -- Step B: .re of the complex integral = real integral
    rw [hcomplex]
    have hnorm_int : Integrable (fun x : V =>
        (↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I))) : ℂ)) μ := by
      apply Integrable.ofReal
      exact (memLp_top_of_bound
        ((Complex.continuous_normSq.comp (by fun_prop : Continuous _)).aestronglyMeasurable)
        ((∑ k, ‖c k‖) ^ 2)
        (ae_of_all _ fun x => by
          simp only [Function.comp_def, Real.norm_eq_abs,
            abs_of_nonneg (Complex.normSq_nonneg _)]
          rw [Complex.normSq_eq_norm_sq]
          gcongr
          calc ‖∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I)‖
              ≤ ∑ k, ‖c k * cexp (↑(-⟪x, t k⟫_ℝ) * I)‖ := norm_sum_le _ _
            _ = ∑ k, ‖c k‖ := by
                congr 1; ext k; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
          )).integrable le_top
    -- Move .re inside the integral using reCLM
    -- reCLM.integral_comp_comm gives: ∫ reCLM(f x) = reCLM(∫ f x)
    -- Since reCLM ↑(normSq z) = normSq z and reCLM(∫ ...) = (∫ ...).re,
    -- this gives ∫ normSq ... = (∫ ↑(normSq ...) ∂μ).re
    have hre_swap := Complex.reCLM.integral_comp_comm hnorm_int
    -- hre_swap : ∫ reCLM ↑(normSq ...) = reCLM (∫ ↑(normSq ...))
    -- LHS simplifies: reCLM ↑r = r, so LHS = ∫ normSq ...
    -- RHS is reCLM applied to integral, which = (integral).re
    change ∫ x, Complex.re (↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I)))) ∂μ =
        Complex.re (∫ x, ↑(normSq (∑ k, c k * cexp (↑(-⟪x, t k⟫_ℝ) * I))) ∂μ) at hre_swap
    simp only [Complex.ofReal_re] at hre_swap
    exact hre_swap.symm

omit [FiniteDimensional ℝ V] in
/-- Pointwise product of a PD function and the characteristic function of a
    finite measure is PD. This is a "continuous Schur product" — the same
    algebraic trick as `isPositiveDefinite_charFun` but with modified
    coefficients d_k(x) = c_k · exp(-i⟨x, t_k⟩) absorbed into the PD condition.
-/
lemma isPositiveDefinite_mul_charFun {φ : V → ℂ} (hpd : IsPositiveDefinite φ)
    (μ : Measure V) [IsFiniteMeasure μ] :
    IsPositiveDefinite (fun t => φ t * charFun μ t) where
  hermitian t := by
    change φ (-t) * charFun μ (-t) = (starRingEnd ℂ) (φ t * charFun μ t)
    rw [map_mul, ← hpd.hermitian t]
    congr 1
    rw [starRingEnd_apply, star_def]
    exact charFun_neg t
  nonneg m t c := by
    simp only [charFun_apply]
    -- Integrability of exponentials on a finite measure (norm ≤ 1)
    have hexp_int : ∀ v : V, Integrable (fun x : V =>
        cexp (↑⟪x, v⟫_ℝ * I)) μ :=
      fun v => (memLp_top_of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
        (ae_of_all _ fun x => by simp [Complex.norm_exp_ofReal_mul_I])).integrable le_top
    -- Integrability of each summand cbarᵢcⱼφ(dᵢⱼ)·exp
    have hterm_int : ∀ i j, Integrable (fun x : V =>
        (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
        cexp (↑⟪x, t i - t j⟫_ℝ * I)) μ :=
      fun i j => (hexp_int (t i - t j)).const_mul _
    -- Step A: Swap double sum and integral
    have hswap : ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
        (φ (t i - t j) * ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ) =
        ∫ x, ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
        cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
      calc ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
              (φ (t i - t j) * ∫ x, cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ)
          = ∑ i, ∑ j, ∫ x, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            congr 1; ext i; congr 1; ext j
            rw [← mul_assoc]; exact (integral_const_mul (L := ℂ) _ _).symm
        _ = ∑ i, ∫ x, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            congr 1; ext i
            exact (integral_finsetSum _ (fun j _ => hterm_int i j)).symm
        _ = ∫ x, ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
              cexp (↑⟪x, t i - t j⟫_ℝ * I) ∂μ := by
            exact (integral_finsetSum _ (fun i _ =>
              integrable_finsetSum _ (fun j _ => hterm_int i j))).symm
    -- Step B: Algebraic identity — absorb exponentials into modified coefficients
    -- For each x: cbarᵢcⱼφ(dᵢⱼ)e^{i⟨x,dᵢⱼ⟩} = conj(cᵢe^{-i⟨x,tᵢ⟩})(cⱼe^{-i⟨x,tⱼ⟩})φ(dᵢⱼ)
    -- Exponential splitting: exp(i⟨x,tᵢ-tⱼ⟩) = conj(exp(-i⟨x,tᵢ⟩)) * exp(-i⟨x,tⱼ⟩)
    have hexp_split : ∀ (x : V) (i j : Fin m),
        cexp (↑⟪x, t i - t j⟫_ℝ * I) =
        (starRingEnd ℂ) (cexp (-(↑⟪x, t i⟫_ℝ) * I)) * cexp (-(↑⟪x, t j⟫_ℝ) * I) := by
      intro x i j
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      have : (starRingEnd ℂ) (-(↑⟪x, t i⟫_ℝ : ℂ) * I) = ↑⟪x, t i⟫_ℝ * I := by
        rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]; ring
      rw [this, inner_sub_right]; push_cast; ring
    have halg : ∀ x : V,
        ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
        cexp (↑⟪x, t i - t j⟫_ℝ * I) =
        ∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j) := by
      intro x; congr 1; ext i; congr 1; ext j
      rw [hexp_split, map_mul]; ring
    -- Step C: Combine and take .re inside integral
    rw [hswap]
    simp_rw [halg]
    -- Goal: 0 ≤ (∫ x, ∑ᵢⱼ conj(c'ᵢ(x)) c'ⱼ(x) φ(dᵢⱼ) ∂μ).re
    -- The integrand .re ≥ 0 by PD of φ with modified coefficients
    -- First, show the integrand is integrable
    have hint_sum : Integrable (fun x : V =>
        ∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j)) μ := by
      -- This equals the original sum (by halg), which is integrable
      rw [show (fun x => ∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j)) =
        (fun x => ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (t i - t j) *
        cexp (↑⟪x, t i - t j⟫_ℝ * I)) from funext (fun x => (halg x).symm)]
      exact integrable_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun j _ => hterm_int i j))
    -- Pull .re inside the integral using reCLM
    have hre_swap := Complex.reCLM.integral_comp_comm hint_sum
    change ∫ x, Complex.re (∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j)) ∂μ =
        Complex.re (∫ x, ∑ i, ∑ j, (starRingEnd ℂ) (c i * cexp (-(↑⟪x, t i⟫_ℝ) * I)) *
        (c j * cexp (-(↑⟪x, t j⟫_ℝ) * I)) * φ (t i - t j) ∂μ) at hre_swap
    rw [← hre_swap]
    exact integral_nonneg (fun x =>
      hpd.nonneg m t (fun k => c k * cexp (-(↑⟪x, t k⟫_ℝ) * I)))

/-- There exists a centered Gaussian measure whose characteristic function is
    exp(-ε‖t‖²). This is the forward direction of Bochner for Gaussian measures.

    On ℝⁿ with standard inner product, the Gaussian measure with density
    (4πε)^{-n/2} exp(-‖x‖²/(4ε)) has charFun(t) = exp(-ε‖t‖²).

    Proof: define μ = C · exp(-a‖x‖²) · dλ where a = 1/(4ε) and C normalizes.
    Use `integral_cexp_neg_mul_sq_norm_add` for the charFun computation.
-/
private lemma gaussian_eq_charFun (ε : ℝ) (hε : 0 < ε) :
    ∃ (μ : Measure V), IsFiniteMeasure μ ∧
    ∀ t, charFun μ t = cexp (-(ε : ℂ) * ↑(‖t‖ ^ 2)) := by
  -- Parameters: a = 1/(4ε), so ε = 1/(4a) and ‖t‖²/(4a) = ε‖t‖²
  set a : ℝ := 1 / (4 * ε) with ha_def
  have ha : 0 < a := by positivity
  -- Normalization constant
  set n : ℕ := Module.finrank ℝ V
  set Cnorm : ℝ := (π / a) ^ (n / 2 : ℝ)
  have hCnorm_pos : 0 < Cnorm := by positivity
  set C : ℝ := Cnorm⁻¹
  have hC_pos : 0 < C := inv_pos.mpr hCnorm_pos
  -- The ENNReal-valued density
  set density : V → ENNReal := fun x => ENNReal.ofReal (C * rexp (-a * ‖x‖ ^ 2))
  have hdensity_meas : Measurable density := by
    apply ENNReal.measurable_ofReal.comp
    exact measurable_const.mul (by fun_prop)
  -- Define the measure
  set μ := volume.withDensity density
  -- Integrability of the complex Gaussian
  have hgauss_cint : Integrable (fun x : V => cexp (-(a : ℂ) * ↑(‖x‖ ^ 2))) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (show 0 < ((a : ℂ)).re by simp [ha]) (0 : ℂ) (0 : V)
    simp only [neg_mul] at this
    convert this using 1
    ext x
    simp [Complex.ofReal_pow]
  -- The real Gaussian is integrable (derived from complex version)
  have hgauss_rint : Integrable (fun x : V => C * rexp (-a * ‖x‖ ^ 2)) := by
    apply Integrable.const_mul
    have : (fun x : V => rexp (-a * ‖x‖ ^ 2)) =
        (fun x : V => ‖cexp (-(a : ℂ) * ↑(‖x‖ ^ 2))‖) := by
      ext x
      rw [Complex.norm_exp]; congr 1
      simp [- Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
    rw [this]; exact hgauss_cint.norm
  have hnn : 0 ≤ᵐ[volume] (fun x : V => C * rexp (-a * ‖x‖ ^ 2)) :=
    ae_of_all _ (fun x => by positivity)
  refine ⟨μ, ?_, ?_⟩
  -- IsFiniteMeasure: ∫⁻ density = ENNReal.ofReal(∫ C*exp(...)) < ⊤
  · apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hgauss_rint hnn]
    exact ENNReal.ofReal_ne_top
  -- charFun computation: charFun μ t = ∫ exp(i⟪x,t⟫) C exp(-a‖x‖²) dx
  --   = C * ∫ exp(-a‖x‖² + i⟪t,x⟫) dx = C * Cnorm * exp(-ε‖t‖²) = exp(-ε‖t‖²)
  · intro t
    rw [charFun_apply]
    -- Rewrite integral w.r.t. withDensity as integral w.r.t. volume
    rw [integral_withDensity_eq_integral_toReal_smul₀ hdensity_meas.aemeasurable
      (ae_of_all _ (fun x => by simp [density]))]
    -- Simplify: (density x).toReal • cexp(⟪x,t⟫ * I) = C * cexp(-a‖x‖² + I*⟪t,x⟫)
    -- Target form matches Mathlib's integral_cexp_neg_mul_sq_norm_add pattern
    have hintegrand : ∀ x : V, (density x).toReal • cexp (↑⟪x, t⟫_ℝ * I) =
        (C : ℂ) * cexp (-(a : ℂ) * ↑‖x‖ ^ 2 + I * ↑⟪t, x⟫_ℝ) := by
      intro x
      simp only [density, ENNReal.toReal_ofReal (by positivity : 0 ≤ C * rexp (-a * ‖x‖ ^ 2))]
      rw [Complex.real_smul, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp,
        ← Complex.exp_add, real_inner_comm x t]
      congr 2; push_cast; ring
    -- Use calc to step through the computation
    have hb : 0 < ((a : ℂ)).re := by simp [ha]
    calc ∫ x, (density x).toReal • cexp (↑⟪x, t⟫_ℝ * I) ∂volume
        _ = ∫ x, (C : ℂ) * cexp (-(a : ℂ) * ↑‖x‖ ^ 2 + I * ↑⟪t, x⟫_ℝ) ∂volume := by
          refine MeasureTheory.integral_congr_ae ?_; exact ae_of_all _ hintegrand
        _ = (C : ℂ) * ∫ x, cexp (-(a : ℂ) * ↑‖x‖ ^ 2 + I * ↑⟪t, x⟫_ℝ) ∂volume :=
          integral_const_mul _ _
        _ = cexp (-(ε : ℂ) * ↑(‖t‖ ^ 2)) := by
          rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb I t]
          -- Cancel C * Cnorm = 1
          have hcpow : (↑π / (↑a : ℂ)) ^ ((↑n : ℂ) / 2) = (Cnorm : ℂ) := by
            rw [← Complex.ofReal_natCast n, ← Complex.ofReal_ofNat 2,
              ← Complex.ofReal_div, ← Complex.ofReal_div]
            exact (Complex.ofReal_cpow (le_of_lt (by positivity : (0 : ℝ) < π / a)) _).symm
          rw [hcpow, ← mul_assoc]
          rw [show (C : ℂ) * (Cnorm : ℂ) = 1 from by
            rw [show (C : ℝ) = Cnorm⁻¹ from rfl, Complex.ofReal_inv,
              inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hCnorm_pos))]]
          rw [one_mul, I_sq, ha_def]
          push_cast; field_simp

/-- The Gaussian function x ↦ exp(-ε‖x‖²) is positive definite.

    Proved by showing it is the characteristic function of a centered
    Gaussian measure with variance 1/(2ε).
-/
lemma isPositiveDefinite_gaussian (ε : ℝ) (hε : 0 < ε) :
    IsPositiveDefinite (fun x : V => cexp (-(ε : ℂ) * ↑(‖x‖ ^ 2))) := by
  obtain ⟨μ, hfin, hcharFun⟩ := gaussian_eq_charFun (V := V) ε hε
  haveI := hfin
  have hpd := isPositiveDefinite_charFun μ
  convert hpd using 1; ext t; exact (hcharFun t).symm

/-! ## Phase 2: Gaussian regularization

φ_ε(x) = φ(x) · exp(-ε‖x‖²) is PD (Schur) and L¹ (bounded × Gaussian).
-/

/-- The Gaussian-regularized function. -/
noncomputable def gaussianRegularize (φ : V → ℂ) (ε : ℝ) : V → ℂ :=
  fun x => φ x * cexp (-(ε : ℂ) * ↑(‖x‖ ^ 2))

/-- φ_ε is positive definite (Schur product of PD functions).

    Direct proof via the Fourier representation of the Gaussian, avoiding
    the general Schur product theorem.

    exp(-ε‖xᵢ-xⱼ‖²) = ∫ exp(2πi⟨ξ,xᵢ-xⱼ⟩) g(ξ) dξ  where g ≥ 0

    So ∑ᵢⱼ cbarᵢcⱼ φ(xᵢ-xⱼ) exp(-ε‖xᵢ-xⱼ‖²)
      = ∫ g(ξ) [∑ᵢⱼ (cᵢ e^{2πi⟨xᵢ,ξ⟩})* (cⱼ e^{2πi⟨xⱼ,ξ⟩}) φ(xᵢ-xⱼ)] dξ

    The inner sum has .re ≥ 0 by PD of φ, and g ≥ 0, so the integral ≥ 0.
-/
lemma gaussianRegularize_pd (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (ε : ℝ) (hε : 0 < ε) :
    IsPositiveDefinite (gaussianRegularize φ ε) where
  hermitian x := by
    simp only [gaussianRegularize, norm_neg]
    rw [hpd.hermitian x, starRingEnd_apply, star_def, map_mul, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  nonneg m x c := by
    -- gaussianRegularize φ ε = fun t => φ t * cexp(...)
    -- By gaussian_eq_charFun, cexp(-ε‖t‖²) = charFun μ t for some Gaussian μ
    -- So gaussianRegularize φ ε t = φ t * charFun μ t
    -- and isPositiveDefinite_mul_charFun gives the result
    obtain ⟨μ, hfin, hcharFun⟩ := gaussian_eq_charFun (V := V) ε hε
    haveI := hfin
    have hmul := isPositiveDefinite_mul_charFun hpd μ
    have heq : ∀ t, gaussianRegularize φ ε t = φ t * charFun μ t := by
      intro t; simp only [gaussianRegularize]; rw [← hcharFun t]
    simp_rw [heq]
    exact hmul.nonneg m x c

/-- φ_ε is integrable (φ is bounded by φ(0), times Gaussian decay). -/
lemma gaussianRegularize_integrable (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hcont : Continuous φ) (ε : ℝ) (hε : 0 < ε) :
    Integrable (gaussianRegularize φ ε) := by
  -- The Gaussian exp(-ε‖x‖²) is integrable
  have hgauss : Integrable (fun x : V => cexp (-(↑ε : ℂ) * ↑(‖x‖ ^ 2))) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (show 0 < (↑ε : ℂ).re by simp [hε]) (0 : ℂ) (0 : V)
    simp only [neg_mul] at this
    convert this using 1
    ext x
    simp [Complex.ofReal_pow]
  -- φ is bounded: ‖φ(x)‖ ≤ (φ 0).re
  -- So ‖φ(x) * exp(-ε‖x‖²)‖ = ‖φ(x)‖ * ‖exp(-ε‖x‖²)‖ ≤ (φ 0).re * ‖exp(-ε‖x‖²)‖
  -- The bound function (φ 0).re * ‖exp(-ε‖x‖²)‖ is integrable
  refine (hgauss.norm.const_mul (φ 0).re).mono
    ((hcont.mul (by fun_prop : Continuous (fun x : V => cexp (-(↑ε : ℂ) * ↑(‖x‖ ^
        2))))).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  simp only [gaussianRegularize, norm_mul, Real.norm_eq_abs, abs_of_nonneg hpd.eval_zero_nonneg,
    abs_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (hpd.bounded_by_zero x) (norm_nonneg _)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- φ_ε(0) = φ(0). -/
lemma gaussianRegularize_zero (φ : V → ℂ) (ε : ℝ) :
    gaussianRegularize φ ε 0 = φ 0 := by
  simp [gaussianRegularize, norm_zero]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- φ_ε → φ pointwise as ε → 0⁺. -/
lemma gaussianRegularize_tendsto (φ : V → ℂ) (x : V) :
    Tendsto (fun ε => gaussianRegularize φ ε x) (𝓝[>] 0) (𝓝 (φ x)) := by
  simp only [gaussianRegularize]
  suffices h : Tendsto (fun ε : ℝ => cexp (-(ε : ℂ) * ↑(‖x‖ ^ 2))) (𝓝[>] 0) (𝓝 1) by
    conv_rhs => rw [show φ x = φ x * 1 from (mul_one _).symm]
    exact Filter.Tendsto.mul tendsto_const_nhds h
  have h0 : cexp (-(0 : ℂ) * ↑(‖x‖ ^ 2)) = 1 := by simp
  rw [← h0]
  apply Filter.Tendsto.cexp
  apply Filter.Tendsto.mul _ tendsto_const_nhds
  exact Filter.Tendsto.neg (tendsto_nhdsWithin_of_tendsto_nhds
    Complex.continuous_ofReal.continuousAt)

/-! ## Phase 1 proof: Re(𝓕φ(ξ)) ≥ 0 for L¹ PD functions

The proof approximates 𝓕φ(ξ) by 𝓕(φ_ε)(ξ) where φ_ε = φ·exp(-ε‖·‖²).
By DCT, 𝓕(φ_ε)(ξ) → 𝓕(φ)(ξ) as ε → 0⁺. We show Re(𝓕(φ_ε)(ξ)) ≥ 0
for each ε > 0 via Fejér sums using the discrete PD condition.

The Fejér sum argument: For ψ PD continuous integrable with Gaussian decay,
take N lattice points in each direction. The PD double sum with Fourier
coefficients gives a Fejér-weighted Riemann sum S_N with Re(S_N) ≥ 0.
As the lattice refines and grows, S_N → 𝓕ψ(ξ), giving Re(𝓕ψ(ξ)) ≥ 0.
-/

/-- The Fourier transform of a continuous integrable positive-definite function
    on a finite-dimensional real inner product space has nonneg real part.

    Proved in `Bochner.FejerPD` via Fejér-weighted PD sums.
    Refs: Rudin, Theorem 1.4.3; Folland, §4.2, Lemma 4.8.
-/
theorem pd_l1_fourier_re_nonneg_ax
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (φ : V → ℂ) (hpd : IsPositiveDefinite φ) (hint : Integrable φ) (hcont : Continuous φ)
    (ξ : V) : 0 ≤ (𝓕 φ ξ).re :=
  pd_l1_fourier_re_nonneg_theorem φ hpd hint hcont ξ

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- 𝓕(φ_ε)(ξ) → 𝓕(φ)(ξ) as ε → 0⁺, by dominated convergence.
    The integrand φ_ε(x)·e^{-2πi⟨x,ξ⟩} is dominated by |φ(x)|.
-/
private lemma gaussianRegularize_norm_le (φ : V → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (x : V) :
    ‖gaussianRegularize φ ε x‖ ≤ ‖φ x‖ := by
  simp only [gaussianRegularize, norm_mul]
  calc ‖φ x‖ * ‖cexp (-(↑ε : ℂ) * ↑(‖x‖ ^ 2))‖
      ≤ ‖φ x‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [Complex.norm_exp, Real.exp_le_one_iff]
        simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
        exact neg_nonpos_of_nonneg (mul_nonneg hε (by positivity))
    _ = ‖φ x‖ := mul_one _

private lemma ft_gaussianRegularize_tendsto (φ : V → ℂ) (hint : Integrable φ) (ξ : V) :
    Tendsto (fun ε => 𝓕 (gaussianRegularize φ ε) ξ) (𝓝[>] 0) (𝓝 (𝓕 φ ξ)) := by
  -- Unfold 𝓕 to VectorFourier.fourierIntegral and then to the integral definition
  change Tendsto (fun ε => ∫ v, 𝐞 (-(innerₗ V) v ξ) • gaussianRegularize φ ε v) (𝓝[>] 0)
    (𝓝 (∫ v, 𝐞 (-(innerₗ V) v ξ) • φ v))
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖φ x‖)
  · -- AEStronglyMeasurable
    apply eventually_nhdsWithin_of_forall; intro ε hε
    have hεnn : (0 : ℝ) ≤ ε := le_of_lt hε
    have : Integrable (gaussianRegularize φ ε) :=
      hint.mono (hint.aestronglyMeasurable.mul (by fun_prop))
        (ae_of_all _ (fun x => gaussianRegularize_norm_le φ hεnn x))
    exact ((VectorFourier.fourierIntegral_convergent_iff
      Real.continuous_fourierChar
      (show Continuous fun p : V × V => (innerₗ V) p.1 p.2 from continuous_inner) ξ).mpr this).1
  · -- Norm bound: ‖e(⟪x,ξ⟫) • φ_ε(x)‖ ≤ ‖φ(x)‖
    apply eventually_nhdsWithin_of_forall; intro ε hε
    exact ae_of_all _ (fun x => by
      simp only [Circle.norm_smul]; exact gaussianRegularize_norm_le φ (le_of_lt hε) x)
  · -- Bound integrable
    exact hint.norm
  · -- Pointwise convergence
    exact ae_of_all _ (fun x => Tendsto.smul tendsto_const_nhds (gaussianRegularize_tendsto φ x))

/-- The real part of the Fourier transform of an L¹ PD function is nonneg.
    Ref: Folland, *A Course in Abstract Harmonic Analysis*, §4.2, Lemma 4.8.
-/
theorem pd_l1_fourier_re_nonneg (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hint : Integrable φ) (hcont : Continuous φ) (ξ : V) : 0 ≤ (𝓕 φ ξ).re :=
  pd_l1_fourier_re_nonneg_ax V φ hpd hint hcont ξ

/-- An L¹ positive-definite function has a nonneg real Fourier transform.
    Continuity of φ̂ (from Riemann-Lebesgue) means this holds everywhere,
    not just a.e.
-/
lemma pd_l1_fourier_nonneg (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hint : Integrable φ) (hcont : Continuous φ) (ξ : V) :
    0 ≤ (𝓕 φ ξ).re ∧ (𝓕 φ ξ).im = 0 := by
  -- Part 1: Im = 0 from Hermitian symmetry φ(-x) = conj(φ(x))
  -- conj(φ̂(ξ)) = ∫ conj(𝐞(-⟪v,ξ⟫) • φ v) = ∫ 𝐞(⟪v,ξ⟫) • φ(-v)
  -- = ∫ 𝐞(-⟪w,ξ⟫) • φ(w)  (w = -v) = φ̂(ξ)
  have hft_conj : starRingEnd ℂ (𝓕 φ ξ) = 𝓕 φ ξ := by
    change starRingEnd ℂ (∫ v, 𝐞 (-⟪v, ξ⟫_ℝ) • φ v) = ∫ v, 𝐞 (-⟪v, ξ⟫_ℝ) • φ v
    rw [show starRingEnd ℂ (∫ v, 𝐞 (-⟪v, ξ⟫_ℝ) • φ v) =
      ∫ v, starRingEnd ℂ (𝐞 (-⟪v, ξ⟫_ℝ) • φ v) from integral_conj.symm]
    -- Goal: ∫ v, conj(𝐞(-⟪v,ξ⟫) • φ v) = ∫ v, 𝐞(-⟪v,ξ⟫) • φ v
    simp_rw [Circle.smul_def, smul_eq_mul, map_mul,
      Circle.starRingEnd_addChar, neg_neg,
      show ∀ v, starRingEnd ℂ (φ v) = φ (-v) from
        fun v => (hpd.hermitian v).symm]
    -- Goal: ∫ v, ↑(𝐞(⟪v,ξ⟫)) * φ(-v) = ∫ v, ↑(𝐞(-⟪v,ξ⟫)) * φ v
    -- Substitute v → -v in LHS using integral_neg_eq_self
    -- Change variables: v → -v
    have hsub := integral_neg_eq_self
      (fun v => (↑(𝐞 (⟪v, ξ⟫_ℝ)) : ℂ) * φ (-v)) (volume : Measure V)
    simp only [inner_neg_left, neg_neg] at hsub
    exact hsub.symm
  have him : (𝓕 φ ξ).im = 0 := by
    have := congr_arg Complex.im hft_conj
    simp only [Complex.conj_im] at this
    linarith
  exact ⟨pd_l1_fourier_re_nonneg φ hpd hint hcont ξ, him⟩

/-- The Fourier transform of an L¹ PD function is real and nonneg. -/
lemma pd_l1_fourier_real_nonneg (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hint : Integrable φ) (hcont : Continuous φ) (ξ : V) :
    𝓕 φ ξ = ↑((𝓕 φ ξ).re) ∧ 0 ≤ (𝓕 φ ξ).re := by
  obtain ⟨hre, him⟩ := pd_l1_fourier_nonneg φ hpd hint hcont ξ
  constructor
  · apply Complex.ext <;> simp [him]
  · exact hre

/-! ## Phase 3: Construct probability measures from L¹ PD functions

Given φ ∈ L¹ PD with φ(0) = 1, define dμ = φ̂ · dλ. Since φ̂ ≥ 0 (Phase 1)
and ∫ φ̂ = φ(0) = 1 (Fourier inversion at 0), μ is a probability measure.
By Fourier inversion, charFun(μ) = φ.
-/

/-- Given an L¹ PD function with φ(0) = 1, there exists a probability measure
    whose characteristic function equals φ.

    Key idea: define ψ(x) = φ(2πx) to absorb the 2π convention difference
    between charFun (uses e^{i⟪x,t⟫}) and 𝓕 (uses e^{-2πi⟪x,ξ⟫}).
    Then dμ = 𝓕ψ · dλ is a probability measure with charFun(μ) = φ.
-/
lemma measure_of_pd_l1 (φ : V → ℂ)
    (hpd : IsPositiveDefinite φ) (hint : Integrable φ)
    (hcont : Continuous φ) (hnorm : φ 0 = 1)
    (hint_ft : Integrable (𝓕 φ)) :
    ∃ μ : ProbabilityMeasure V,
      ∀ ξ, MeasureTheory.charFun (μ : Measure V) ξ = φ ξ := by
  -- Step 1: Define ψ(x) = φ(2πx) to match charFun ↔ 𝓕 conventions
  set τ : ℝ := 2 * Real.pi with hτ_def
  have hτ_pos : 0 < τ := by positivity
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
  -- The scaling map T(x) = τ • x as a linear map
  set T : V →ₗ[ℝ] V := τ • LinearMap.id with hT_def
  set ψ : V → ℂ := fun x => φ (T x) with hψ_def
  -- Step 2: ψ is PD (composition with linear map)
  have hψ_pd : IsPositiveDefinite ψ := isPositiveDefinite_precomp_linear φ hpd T
  -- Step 3: ψ is continuous
  have hψ_cont : Continuous ψ := hcont.comp (continuous_const_smul τ)
  -- Step 4: ψ is integrable (change of variables: ∫|ψ| = τ⁻ⁿ ∫|φ|)
  have hψ_int : Integrable ψ := by
    rw [show ψ = (fun x => φ (τ • x)) from rfl]
    exact (integrable_comp_smul_iff volume φ hτ_ne).mpr hint
  -- Step 5: 𝓕ψ is integrable (from hint_ft via Fourier scaling)
  -- Key formula: 𝓕(φ(τ·))(ξ) = |τ⁻ⁿ| · 𝓕φ(τ⁻¹·ξ)
  -- So Integrable(𝓕ψ) ↔ Integrable(𝓕φ)
  have hψ_ft_int : Integrable (𝓕 ψ) := by
    -- Step A: Show 𝓕ψ(ξ) = |(τ^n)⁻¹| • 𝓕φ(τ⁻¹ • ξ) pointwise
    set n' := Module.finrank ℝ V
    have hkey : ∀ ξ, 𝓕 ψ ξ = |(τ ^ n')⁻¹| • 𝓕 φ (τ⁻¹ • ξ) := by
      intro ξ
      -- Unfold to integral form
      change (∫ v, Real.fourierChar (-⟪v, ξ⟫_ℝ) • φ (τ • v)) =
        |(τ ^ n')⁻¹| • ∫ v, Real.fourierChar (-⟪v, τ⁻¹ • ξ⟫_ℝ) • φ v
      -- Change of variables: ∫ g(τ • v) = |(τ^n)⁻¹| • ∫ g(v)
      -- Change of variables via integral_comp_smul, then simplify inner products
      have hcov := Measure.integral_comp_smul volume
        (fun y => Real.fourierChar (-⟪τ⁻¹ • y, ξ⟫_ℝ) • φ y) τ
      simp only [inv_smul_smul₀ hτ_ne] at hcov
      rw [hcov]
      congr 1
      refine MeasureTheory.integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [real_inner_smul_left, real_inner_smul_right]
    -- Step B: Transfer integrability
    have hfun_eq : 𝓕 ψ = fun ξ => |(τ ^ n')⁻¹| • 𝓕 φ (τ⁻¹ • ξ) := funext hkey
    rw [hfun_eq]
    exact Integrable.smul |(τ ^ n')⁻¹|
      ((integrable_comp_smul_iff volume (𝓕 φ) (inv_ne_zero hτ_ne)).mpr hint_ft)
  -- Step 6: 𝓕ψ is real and nonneg (from pd_l1_fourier_nonneg)
  have hψ_ft_nonneg : ∀ x, 0 ≤ (𝓕 ψ x).re ∧ (𝓕 ψ x).im = 0 :=
    fun x => pd_l1_fourier_nonneg ψ hψ_pd hψ_int hψ_cont x
  -- Step 7: Define the density and measure
  set density : V → ENNReal := fun x => ENNReal.ofReal (𝓕 ψ x).re
  have hψ_ft_cont : Continuous (𝓕 ψ) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V) ψ)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hψ_int
  have hdensity_meas : Measurable density := by
    exact ENNReal.measurable_ofReal.comp ((Complex.continuous_re.comp hψ_ft_cont).measurable)
  set μ_raw := volume.withDensity density
  -- Step 8: Total mass = ψ(0) = φ(0) = 1 (Fourier inversion at 0)
  have htotal : μ_raw Set.univ = 1 := by
    -- μ_raw = withDensity(ofReal (Re(𝓕ψ))), so total mass = ∫⁻ ofReal(Re(𝓕ψ))
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    -- Re(𝓕ψ) is integrable and ≥ 0
    have hre_int : Integrable (fun x => (𝓕 ψ x).re) := hψ_ft_int.re
    have hre_nn : 0 ≤ᵐ[volume] fun x => (𝓕 ψ x).re :=
      ae_of_all _ fun x => (hψ_ft_nonneg x).1
    rw [show density = fun x => ENNReal.ofReal (𝓕 ψ x).re from rfl,
      ← ofReal_integral_eq_lintegral_ofReal hre_int hre_nn]
    -- Goal: ofReal (∫ Re(𝓕ψ)) = 1
    -- Key chain: ∫ Re(𝓕ψ) = Re(∫ 𝓕ψ) = Re(𝓕⁻(𝓕ψ)(0)) = Re(ψ(0)) = Re(φ(0)) = 1
    -- Step A: Fourier inversion at 0: 𝓕⁻(𝓕ψ)(0) = ψ(0)
    have hinv : 𝓕⁻ (𝓕 ψ) 0 = ψ 0 :=
      hψ_int.fourierInv_fourier_eq hψ_ft_int hψ_cont.continuousAt
    -- Step B: ψ(0) = φ(T 0) = φ(0) = 1
    have hψ0 : ψ 0 = 1 := by
      change φ (T 0) = 1
      simp [T, smul_zero, hnorm]
    -- Step C: ∫ 𝓕ψ = ψ(0) = 1 via Fourier inversion at 0
    have hint_eq : ∫ x, 𝓕 ψ x = 1 := by
      -- Fourier inversion: 𝓕⁻(𝓕ψ) = ψ, evaluate at 0
      have hfinv := hψ_cont.fourierInv_fourier_eq hψ_int hψ_ft_int
      have h0 := congr_fun hfinv 0
      -- h0 : 𝓕⁻(𝓕ψ)(0) = ψ(0)
      -- Expand LHS: 𝓕⁻(𝓕ψ)(0) = ∫ 𝓕ψ
      rw [Real.fourierInv_eq'] at h0
      simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
        Complex.exp_zero, one_smul] at h0
      -- h0 : ∫ 𝓕ψ v = ψ(0); need ∫ 𝓕ψ x = 1
      convert h0.trans hψ0
    -- Step D: ∫ Re(𝓕ψ) = Re(∫ 𝓕ψ) = 1
    have hre_eq : ∫ x, (𝓕 ψ x).re = 1 := by
      have h1 := Complex.reCLM.integral_comp_comm hψ_ft_int
      change ∫ x, (𝓕 ψ x).re = (∫ x, 𝓕 ψ x).re at h1
      rw [h1, hint_eq]; simp
    rw [hre_eq]; simp
  -- Step 9: Package as ProbabilityMeasure
  have hfm : IsFiniteMeasure μ_raw := by
    constructor; rw [htotal]; exact ENNReal.one_lt_top
  have hprob : IsProbabilityMeasure μ_raw := ⟨htotal⟩
  set μ : ProbabilityMeasure V := ⟨μ_raw, hprob⟩
  -- Step 10: charFun(μ)(t) = φ(t) via Fourier inversion
  refine ⟨μ, fun ξ => ?_⟩
  -- charFun μ ξ = ∫ (𝓕ψ x).re • e^{i⟪x,ξ⟫} dx = 𝓕⁻(𝓕ψ)(τ⁻¹ξ) = ψ(τ⁻¹ξ) = φ(ξ)
  -- Step A: Fourier inversion gives 𝓕⁻(𝓕ψ) = ψ
  have hfinv := hψ_cont.fourierInv_fourier_eq hψ_int hψ_ft_int
  -- Step B: ψ(τ⁻¹ • ξ) = φ(T(τ⁻¹ • ξ)) = φ(ξ)
  have hψ_eval : ψ (τ⁻¹ • ξ) = φ ξ := by
    change φ (T (τ⁻¹ • ξ)) = φ ξ
    simp [T, smul_smul, inv_mul_cancel₀ hτ_ne]
  -- Step C: charFun computation via withDensity integral
  -- charFun is ∫ cexp(i⟪x,ξ⟫) ∂↑μ, and ↑μ = μ_raw = volume.withDensity density
  change ∫ x, cexp (↑⟪x, ξ⟫_ℝ * I) ∂μ_raw = φ ξ
  rw [show μ_raw = volume.withDensity density from rfl]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hdensity_meas.aemeasurable
    (ae_of_all _ (fun x => by simp [density]))]
  -- Goal: ∫ x, (density x).toReal • cexp(⟪x,ξ⟫ * I) = φ ξ
  -- Simplify density toReal
  have hdensity_simp : ∀ x, (density x).toReal = (𝓕 ψ x).re := by
    intro x
    simp only [density, ENNReal.toReal_ofReal (hψ_ft_nonneg x).1]
  -- Rewrite using 𝓕⁻(𝓕ψ)(τ⁻¹ξ) = ψ(τ⁻¹ξ)
  rw [← hψ_eval, ← congr_fun hfinv (τ⁻¹ • ξ)]
  -- Goal: ∫ (density x).toReal • cexp(⟪x,ξ⟫ * I) = 𝓕⁻(𝓕ψ)(τ⁻¹ξ)
  -- Expand 𝓕⁻ using fourierInv_eq'
  rw [Real.fourierInv_eq']
  -- Goal: ∫ (density x).toReal • cexp(⟪x,ξ⟫*I) = ∫ v, cexp(2π⟪v,τ⁻¹ξ⟫*I) • 𝓕ψ v
  -- Both sides are integrals over V. Match integrands.
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [hdensity_simp]
  -- Goal: (𝓕ψ x).re • cexp(⟪x,ξ⟫ * I) = cexp(2π⟪x,τ⁻¹ξ⟫ * I) • 𝓕ψ x
  have him : (𝓕 ψ x).im = 0 := (hψ_ft_nonneg x).2
  have hre_cast : 𝓕 ψ x = ↑((𝓕 ψ x).re) := by
    apply Complex.ext <;> simp [him]
  -- 2π⟪x,τ⁻¹ξ⟫ = 2π · τ⁻¹ · ⟪x,ξ⟫ = ⟪x,ξ⟫ (since τ = 2π)
  have hinner : 2 * π * ⟪x, τ⁻¹ • ξ⟫_ℝ = ⟪x, ξ⟫_ℝ := by
    rw [real_inner_smul_right, hτ_def]
    field_simp
  rw [hinner]
  simp only [smul_eq_mul]
  conv_rhs => rw [hre_cast]
  exact mul_comm _ _

/-! ## Phase 4: Tightness and weak limit

The family {μ_ε} is tight because:
  μ_ε({‖x‖ > R}) ≤ (2/R²) ∫_{‖ξ‖≤δ} (1 - Re(charFun(μ_ε)(ξ))) dξ

Since charFun(μ_ε) = φ_ε → φ and φ is continuous at 0, the right side → 0
uniformly in ε as R → ∞.

Prokhorov's theorem (Mathlib: `isCompact_closure_of_isTightMeasureSet`)
extracts a weakly convergent subsequence. Testing the limit against
x ↦ exp(i⟨ξ,x⟩) identifies charFun(μ) = φ.
-/

/-- L¹ Parseval/Fubini: ∫ (𝓕 f) • g = ∫ f • (𝓕 g) for f, g ∈ L¹.
    This is `integral_fourierIntegral_smul_eq_flip` with L.flip = L (symmetric IP).
-/
private lemma parseval_l1 (f g : V → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  have hL : Continuous fun p : V × V => (innerₗ V) p.1 p.2 :=
    continuous_inner
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    Real.continuous_fourierChar hL hf hg
    (ν := volume) (μ := volume) (F := ℂ)
  simp only [smul_eq_mul] at h
  rw [flip_innerₗ] at h
  exact h

/-- Gaussian x ↦ cexp(-t‖x‖²) is integrable for t > 0. -/
private lemma gaussian_cexp_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : V => cexp (-(t : ℂ) * ↑(‖x‖ ^ 2))) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (t : ℂ)) (show 0 < ((t : ℂ)).re from by simp [ht]) 0 (0 : V)
  simp only [add_zero, zero_mul] at this
  convert this using 1; ext x; push_cast; ring

/-- The Fourier transform of a Gaussian is integrable (it's also a Gaussian). -/
private lemma ft_gaussian_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (𝓕 (fun ξ : V => cexp (-(t : ℂ) * ↑(‖ξ‖ ^ 2)))) := by
  have htre : 0 < ((t : ℂ)).re := by simp [ht]
  -- Bridge ↑(‖v‖²) vs ↑‖v‖² to match fourier_gaussian_innerProductSpace
  rw [show (fun ξ : V => cexp (-(t : ℂ) * ↑(‖ξ‖ ^ 2))) =
    fun v => cexp (-(t : ℂ) * ↑‖v‖ ^ 2) from by ext; simp [Complex.ofReal_pow]]
  rw [funext (fourier_gaussian_innerProductSpace htre : ∀ w : V, _)]
  apply Integrable.const_mul
  have : Integrable (fun w : V => cexp (-(↑(π ^ 2 / t)) * ↑(‖w‖ ^ 2))) :=
    gaussian_cexp_integrable (π ^ 2 / t) (by positivity)
  convert this using 1; ext w; congr 1; push_cast; ring

/-- The Fourier transform of a Gaussian has integral equal to 1.
    Uses Fourier inversion: 𝓕⁻(𝓕 g)(0) = g(0) = 1, and 𝓕⁻(h)(0) = ∫ h.
-/
private lemma integral_ft_gaussian_eq_one (t : ℝ) (ht : 0 < t) :
    ∫ x : V, 𝓕 (fun ξ : V => cexp (-(t : ℂ) * ↑(‖ξ‖ ^ 2))) x = 1 := by
  set g := fun ξ : V => cexp (-(t : ℂ) * ↑(‖ξ‖ ^ 2))
  have hg_int : Integrable g := gaussian_cexp_integrable t ht
  have hg_cont : Continuous g := by fun_prop
  have hft_int : Integrable (𝓕 g) := ft_gaussian_integrable t ht
  have hinv := hg_cont.fourierInv_fourier_eq hg_int hft_int
  have h0 := congr_fun hinv 0
  rw [Real.fourierInv_eq'] at h0
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] at h0
  convert h0 using 1; simp [g]

/-- The integral of ‖𝓕 g_t‖ equals 1, since 𝓕 g_t is nonneg real (Gaussian is PD). -/
private lemma integral_norm_ft_gaussian_eq_one (t : ℝ) (ht : 0 < t) :
    ∫ x : V, ‖𝓕 (fun ξ : V => cexp (-(t : ℂ) * ↑(‖ξ‖ ^ 2))) x‖ = 1 := by
  set g := fun ξ : V => cexp (-(t : ℂ) * ↑(‖ξ‖ ^ 2))
  have hg_int : Integrable g := gaussian_cexp_integrable t ht
  have hft_int : Integrable (𝓕 g) := ft_gaussian_integrable t ht
  -- 𝓕 g is nonneg real (since g is PD and integrable)
  have hg_pd : IsPositiveDefinite g := isPositiveDefinite_gaussian t ht
  have hg_cont : Continuous g := by fun_prop
  have hft_nonneg := pd_l1_fourier_nonneg g hg_pd hg_int hg_cont
  -- ‖𝓕 g(w)‖ = (𝓕 g(w)).re since 𝓕 g is nonneg real
  have hnorm_eq_re : ∀ w : V, ‖𝓕 g w‖ = (𝓕 g w).re := by
    intro w; have ⟨hre, him⟩ := hft_nonneg w
    rw [← RCLike.sqrt_normSq_eq_norm, RCLike.normSq_apply]
    have : RCLike.im (𝓕 g w) = 0 := him
    rw [this, mul_zero, add_zero]
    have : RCLike.re (𝓕 g w) = (𝓕 g w).re := rfl
    rw [this, Real.sqrt_mul_self hre]
  -- ∫ ‖𝓕 g‖ = ∫ (𝓕 g).re = Re(∫ 𝓕 g) = Re(1) = 1
  simp_rw [hnorm_eq_re, show ∀ x : V, (𝓕 g x).re = RCLike.re (𝓕 g x) from fun _ => rfl]
  rw [integral_re hft_int]
  change RCLike.re (∫ x : V, 𝓕 g x) = 1
  rw [show (∫ x : V, 𝓕 g x) = (∫ x : V, 𝓕 (fun ξ : V => cexp (-(t : ℂ) * ↑(‖ξ‖ ^ 2))) x)
    from rfl, integral_ft_gaussian_eq_one t ht]; simp

/-- The Fourier transform of a Gaussian-regularized PD function is integrable.
    Proof: 𝓕(φ_ε) ≥ 0 (from PD), and for each t > 0 the Parseval/Fubini identity
    gives ∫ (𝓕 φ_ε) * g_t = ∫ φ_ε * (𝓕 g_t), bounded by ‖φ_ε‖∞ * ‖𝓕 g_t‖₁ = (φ 0).re.
    Monotone convergence (g_t ↗ 1) gives ∫⁻ ‖𝓕 φ_ε‖ ≤ (φ 0).re < ∞.
    Ref: Folland, A Course in Abstract Harmonic Analysis, 4.2.
-/
theorem gaussianRegularize_ft_integrable (φ : V → ℂ)
    (hpd : IsPositiveDefinite φ) (hcont : Continuous φ)
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (𝓕 (gaussianRegularize φ ε)) := by
  set φ_ε := gaussianRegularize φ ε
  have hφε_int := gaussianRegularize_integrable φ hpd hcont ε hε
  have hφε_pd := gaussianRegularize_pd φ hpd ε hε
  have hφε_cont : Continuous φ_ε := hcont.mul (by fun_prop)
  have hft_nonneg := pd_l1_fourier_nonneg φ_ε hφε_pd hφε_int hφε_cont
  -- φ_ε is bounded by (φ 0).re
  have hφε0 : (φ_ε 0).re = (φ 0).re := by
    change (gaussianRegularize φ ε 0).re = _; rw [gaussianRegularize_zero]
  have hφε_bound : ∀ x : V, ‖φ_ε x‖ ≤ (φ 0).re := by
    intro x; rw [← hφε0]; exact hφε_pd.bounded_by_zero x
  -- 𝓕(φ_ε) is continuous
  have hft_cont : Continuous (𝓕 φ_ε) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V) φ_ε)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hφε_int
  have hft_meas : AEStronglyMeasurable (𝓕 φ_ε) volume := hft_cont.aestronglyMeasurable
  -- 𝓕 φ_ε is bounded (FT of L¹ function)
  have hft_bdd : ∀ ξ : V, ‖𝓕 φ_ε ξ‖ ≤ ∫ x, ‖φ_ε x‖ := fun ξ =>
    VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ V) φ_ε ξ
  -- Key bound: for each t > 0, Re(∫ (𝓕 φ_ε) * g_t) ≤ (φ 0).re
  -- This is ∫ (𝓕 φ_ε).re * exp(-t‖ξ‖²) by linearity of Re and g_t being real.
  have hbound : ∀ t : ℝ, 0 < t →
      (∫ ξ : V, 𝓕 φ_ε ξ * cexp (-(t : ℂ) * ↑(‖ξ‖ ^ 2))).re ≤ (φ 0).re := by
    intro t ht
    set g_t := fun ξ : V => cexp (-(t : ℂ) * ↑(‖ξ‖ ^ 2))
    have hgt_int : Integrable g_t := gaussian_cexp_integrable t ht
    have hparseval := parseval_l1 φ_ε g_t hφε_int hgt_int
    -- Re(∫ (𝓕 φ_ε) * g_t) = Re(∫ φ_ε * (𝓕 g_t))
    rw [hparseval]
    -- Bound: Re(z) ≤ ‖z‖ ≤ ∫ ‖⋯‖ ≤ (φ 0).re * ∫ ‖𝓕 g_t‖ = (φ 0).re
    have hft_gt_int : Integrable (𝓕 g_t) := ft_gaussian_integrable t ht
    have hprod_rhs_int : Integrable (fun x => φ_ε x * 𝓕 g_t x) :=
      hft_gt_int.bdd_mul hφε_cont.aestronglyMeasurable (ae_of_all _ hφε_bound)
    calc (∫ x, φ_ε x * 𝓕 g_t x).re
        ≤ ‖∫ x, φ_ε x * 𝓕 g_t x‖ := Complex.re_le_norm _
      _ ≤ ∫ x, ‖φ_ε x * 𝓕 g_t x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, (φ 0).re * ‖𝓕 g_t x‖ := by
          apply integral_mono hprod_rhs_int.norm (hft_gt_int.norm.const_mul _)
          intro x; change ‖φ_ε x * 𝓕 g_t x‖ ≤ (φ 0).re * ‖𝓕 g_t x‖
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hφε_bound x) (norm_nonneg _)
      _ = (φ 0).re * ∫ x, ‖𝓕 g_t x‖ := integral_const_mul _ _
      _ = (φ 0).re * 1 := by rw [integral_norm_ft_gaussian_eq_one t ht]
      _ = (φ 0).re := mul_one _
  -- MCT: ∫⁻ ‖𝓕 φ_ε‖₊ ≤ (φ 0).re using monotone convergence
  -- Define f_n(ξ) = ‖𝓕 φ_ε ξ‖₊ * exp(-‖ξ‖²/(n+1)); this increases to ‖𝓕 φ_ε ξ‖₊
  have hlintegral_bound : ∫⁻ ξ, ‖𝓕 φ_ε ξ‖₊ ≤ ENNReal.ofReal (φ 0).re := by
    -- Fatou's lemma with f_n(ξ) = ‖(𝓕 φ_ε ξ) * cexp(-‖ξ‖²/(n+1))‖ₑ
    -- These tend to ‖𝓕 φ_ε ξ‖ₑ pointwise and each has bounded integral
    -- Helper: cexp of a real argument is real
    have cexp_arg_real : ∀ (t : ℝ) (ξ : V),
        -(↑t : ℂ) * ↑(‖ξ‖ ^ 2) = ↑(-t * ‖ξ‖ ^ 2) := by
      intro t ξ; push_cast; ring
    -- Helper: cexp of a real argument has zero imaginary part
    have cexp_im_zero : ∀ (t : ℝ) (ξ : V),
        (cexp (-(↑t : ℂ) * ↑(‖ξ‖ ^ 2))).im = 0 := by
      intro t ξ; rw [cexp_arg_real, ← Complex.ofReal_exp]; exact Complex.ofReal_im _
    -- Helper: cexp of a negative real argument has nonneg real part
    have cexp_re_nonneg : ∀ (t : ℝ) (ξ : V),
        0 ≤ (cexp (-(↑t : ℂ) * ↑(‖ξ‖ ^ 2))).re := by
      intro t ξ
      rw [show -(↑t : ℂ) * ↑(‖ξ‖ ^ 2) = ↑(-t * ‖ξ‖ ^ 2) from cexp_arg_real t ξ,
        ← Complex.ofReal_exp, Complex.ofReal_re]
      exact Real.exp_nonneg _
    -- For each n, define h_n and its properties
    set tn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have htn_pos : ∀ n, 0 < tn n := fun n => by positivity
    -- h_n(ξ) = 𝓕 φ_ε ξ * cexp(-(tn n)·‖ξ‖²)
    -- f_n(ξ) = ‖h_n(ξ)‖ₑ
    let f : ℕ → V → ENNReal := fun n ξ =>
      ‖𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))‖ₑ
    -- Measurability: each h_n is continuous
    have hcexp_cont : ∀ n, Continuous fun ξ : V =>
        cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2)) := by
      intro n
      apply Continuous.cexp
      exact (continuous_const).mul (Complex.continuous_ofReal.comp (continuous_norm.pow 2))
    have hf_meas : ∀ n, Measurable (f n) := by
      intro n; exact (hft_cont.mul (hcexp_cont n)).measurable.enorm
    -- Tendsto: h_n(ξ) → 𝓕 φ_ε(ξ) as cexp → 1, so ‖h_n‖ₑ → ‖𝓕 φ_ε‖ₑ
    have hf_tendsto : ∀ ξ, Tendsto (fun n => f n ξ) atTop
        (𝓝 ((‖𝓕 φ_ε ξ‖₊ : ENNReal))) := by
      intro ξ
      apply (Filter.Tendsto.enorm (a := 𝓕 φ_ε ξ) _).congr (fun n => rfl)
      show Tendsto (fun n => 𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2)))
        atTop (𝓝 (𝓕 φ_ε ξ))
      conv_rhs => rw [show 𝓕 φ_ε ξ = 𝓕 φ_ε ξ * 1 from (mul_one _).symm]
      apply Filter.Tendsto.const_mul
      rw [show (1 : ℂ) = cexp 0 from Complex.exp_zero.symm]
      apply Complex.continuous_exp.continuousAt.tendsto.comp
      change Tendsto (fun n => -(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2)) atTop (𝓝 0)
      rw [show (0 : ℂ) = -(0 : ℂ) * ↑(‖ξ‖ ^ 2) from by simp]
      apply Filter.Tendsto.mul_const
      apply Filter.Tendsto.neg
      rw [show (0 : ℂ) = (↑(0 : ℝ) : ℂ) from by simp]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp
        (show Tendsto tn atTop (𝓝 0) from by
          simp only [tn]
          have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
            (tendsto_add_atTop_nat 1)
          simp only [Function.comp_def, Nat.cast_add, Nat.cast_one] at h
          exact h)
    have hf_liminf : ∀ ξ, liminf (fun n => f n ξ) atTop = (‖𝓕 φ_ε ξ‖₊ : ENNReal) :=
      fun ξ => (hf_tendsto ξ).liminf_eq
    -- Bound: for each n, ∫⁻ f_n ≤ ENNReal.ofReal (φ 0).re
    have hf_bound : ∀ n, ∫⁻ ξ, f n ξ ≤ ENNReal.ofReal (φ 0).re := by
      intro n
      -- h_n is integrable (bounded FT × integrable Gaussian)
      have hhn_int : Integrable (fun ξ : V =>
          𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))) :=
        (gaussian_cexp_integrable _ (htn_pos n)).bdd_mul hft_cont.aestronglyMeasurable
          (ae_of_all _ hft_bdd)
      -- Convert ∫⁻ ‖h_n‖ₑ to ENNReal.ofReal (∫ ‖h_n‖)
      rw [← ofReal_integral_norm_eq_lintegral_enorm hhn_int]
      apply ENNReal.ofReal_le_ofReal
      -- Key: ‖h_n(ξ)‖ = (h_n(ξ)).re since h_n is nonneg real-valued
      -- Then ∫ ‖h_n‖ = ∫ h_n.re = (∫ h_n).re ≤ (φ 0).re
      have hnorm_eq_re : ∀ ξ : V,
          ‖𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))‖ =
          (𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))).re := by
        intro ξ
        obtain ⟨hre, him⟩ := hft_nonneg ξ
        have hprod_im : (𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))).im = 0 := by
          rw [Complex.mul_im, him, cexp_im_zero]; ring
        have hprod_re_nn : 0 ≤ (𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))).re := by
          rw [Complex.mul_re, him, cexp_im_zero]
          simp only [mul_zero, sub_zero]
          exact mul_nonneg hre (cexp_re_nonneg _ _)
        rw [Complex.norm_eq_sqrt_sq_add_sq, hprod_im, sq (0 : ℝ), mul_zero, add_zero,
          Real.sqrt_sq hprod_re_nn]
      calc ∫ ξ, ‖𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))‖
          = ∫ ξ, (𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))).re :=
            integral_congr_ae (ae_of_all _ hnorm_eq_re)
        _ = RCLike.re (∫ ξ, 𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))) :=
            integral_re hhn_int
        _ = (∫ ξ, 𝓕 φ_ε ξ * cexp (-(↑(tn n) : ℂ) * ↑(‖ξ‖ ^ 2))).re := rfl
        _ ≤ (φ 0).re := hbound _ (htn_pos n)
    -- Combine via Fatou's lemma
    calc ∫⁻ ξ, (‖𝓕 φ_ε ξ‖₊ : ENNReal)
        = ∫⁻ ξ, liminf (fun n => f n ξ) atTop := by simp_rw [hf_liminf]
      _ ≤ liminf (fun n => ∫⁻ ξ, f n ξ) atTop := lintegral_liminf_le hf_meas
      _ ≤ ENNReal.ofReal (φ 0).re := by
          apply liminf_le_of_le (h := fun b hb => ?_)
          obtain ⟨n, hn⟩ := hb.exists
          exact hn.trans (hf_bound n)
  exact ⟨hft_meas, hlintegral_bound.trans_lt ENNReal.ofReal_lt_top⟩

/-- 1 - exp(-x) ≤ x for x ≥ 0. From Mathlib: 1 - x ≤ exp(-x) rearranged. -/
private lemma one_sub_exp_neg_le {x : ℝ} (_hx : 0 ≤ x) : 1 - Real.exp (-x) ≤ x := by
  linarith [Real.one_sub_le_exp_neg x]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Bound on ‖1 - gaussianRegularize φ ε v‖ in terms of ‖1 - φ v‖ and ‖v‖².
    Uses triangle inequality, bounded_by_zero, and 1-exp(-x) ≤ x.
-/
private lemma gaussianRegularize_deviation_bound (φ : V → ℂ)
    (hpd : IsPositiveDefinite φ) (hnorm : φ 0 = 1)
    (v : V) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖(1 : ℂ) - gaussianRegularize φ ε v‖ ≤ ‖(1 : ℂ) - φ v‖ + ‖v‖ ^ 2 := by
  -- 1 - φ(v) * exp(-ε‖v‖²) = (1 - φ(v)) + φ(v) * (1 - exp(-ε‖v‖²))
  have hdecomp : (1 : ℂ) - gaussianRegularize φ ε v =
      (1 - φ v) + φ v * (1 - cexp (-(ε : ℂ) * ↑(‖v‖ ^ 2))) := by
    simp only [gaussianRegularize]; ring
  rw [hdecomp]
  -- Triangle inequality
  calc ‖(1 - φ v) + φ v * (1 - cexp (-(ε : ℂ) * ↑(‖v‖ ^ 2)))‖
      ≤ ‖1 - φ v‖ + ‖φ v * (1 - cexp (-(ε : ℂ) * ↑(‖v‖ ^ 2)))‖ := norm_add_le _ _
    _ = ‖1 - φ v‖ + ‖φ v‖ * ‖1 - cexp (-(ε : ℂ) * ↑(‖v‖ ^ 2))‖ := by
        rw [norm_mul]
    _ ≤ ‖1 - φ v‖ + 1 * ‖1 - cexp (-(ε : ℂ) * ↑(‖v‖ ^ 2))‖ := by
        gcongr
        -- ‖φ v‖ ≤ (φ 0).re = 1
        have hb := hpd.bounded_by_zero v
        rw [hnorm] at hb; simpa using hb
    _ = ‖1 - φ v‖ + ‖1 - cexp (-(ε : ℂ) * ↑(‖v‖ ^ 2))‖ := by rw [one_mul]
    _ ≤ ‖1 - φ v‖ + ε * ‖v‖ ^ 2 := by
        gcongr
        -- ‖1 - cexp(-(ε : ℂ) * ↑(‖v‖²))‖ = 1 - exp(-ε‖v‖²) ≤ ε‖v‖²
        have harg_nn : 0 ≤ ε * ‖v‖ ^ 2 := by positivity
        have hcexp_real : cexp (-(ε : ℂ) * ↑(‖v‖ ^ 2)) = ↑(Real.exp (-(ε * ‖v‖ ^ 2))) := by
          push_cast; congr 1; ring
        rw [hcexp_real, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg (by linarith [Real.exp_le_one_iff.mpr (by linarith : -(ε * ‖v‖ ^ 2) ≤ 0)])]
        exact one_sub_exp_neg_le harg_nn
    _ ≤ ‖1 - φ v‖ + 1 * ‖v‖ ^ 2 := by gcongr
    _ = ‖1 - φ v‖ + ‖v‖ ^ 2 := by rw [one_mul]

omit [FiniteDimensional ℝ V] in
/-- Key bound: for a probability measure μ with charFun μ = gaussianRegularize φ ε (ε ≤ 1),
    and for any y and r > 0:
    μ.real {x | r < |⟪y,x⟫|} ≤ 2 * C + 8 * ‖y‖² * r⁻²
    where C bounds ‖1 - φ(t•y)‖ for |t| ≤ 2/r.
-/
private lemma charFun_measure_inner_bound (φ : V → ℂ)
    (hpd : IsPositiveDefinite φ) (hnorm : φ 0 = 1)
    {μ : Measure V} [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcharfun : ∀ ξ, charFun μ ξ = gaussianRegularize φ ε ξ)
    {y : V} {r : ℝ} (hr : 0 < r) {C : ℝ} (_hC : 0 ≤ C)
    (hCbound : ∀ t : ℝ, t ∈ Set.uIoc (-(2 * r⁻¹)) (2 * r⁻¹) →
      ‖(1 : ℂ) - φ (t • y)‖ ≤ C) :
    μ.real {x | r < |⟪y, x⟫_ℝ|} ≤ 2 * C + 8 * ‖y‖ ^ 2 * r⁻¹ ^ 2 := by
  -- Apply Mathlib's charFun tail bound
  have hcf := measureReal_abs_inner_gt_le_integral_charFun (a := y) (μ := μ) hr
  -- Bound the integral using norm_integral_le_of_norm_le_const
  have hdeviation_bound : ∀ t : ℝ, t ∈ Set.uIoc (-(2 * r⁻¹)) (2 * r⁻¹) →
      ‖(1 : ℂ) - charFun μ (t • y)‖ ≤ C + 4 * ‖y‖ ^ 2 * r⁻¹ ^ 2 := by
    intro t ht
    rw [hcharfun]
    calc ‖(1 : ℂ) - gaussianRegularize φ ε (t • y)‖
        ≤ ‖(1 : ℂ) - φ (t • y)‖ + ‖t • y‖ ^ 2 :=
          gaussianRegularize_deviation_bound φ hpd hnorm _ ε hε hε1
      _ ≤ C + ‖t • y‖ ^ 2 := by gcongr; exact hCbound t ht
      _ = C + t ^ 2 * ‖y‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      _ ≤ C + (2 * r⁻¹) ^ 2 * ‖y‖ ^ 2 := by
          have hle : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by linarith [inv_pos.mpr hr]
          rw [Set.uIoc_of_le hle] at ht
          have h_abs : |t| ≤ 2 * r⁻¹ := abs_le.mpr ⟨by linarith [ht.1.le], ht.2⟩
          have h_sq : t ^ 2 ≤ (2 * r⁻¹) ^ 2 := by
            rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) h_abs 2
          nlinarith [sq_nonneg ‖y‖]
      _ = C + 4 * ‖y‖ ^ 2 * r⁻¹ ^ 2 := by ring
  have hnorm_bound := intervalIntegral.norm_integral_le_of_norm_le_const hdeviation_bound
  -- Combine: μ.real ≤ 2⁻¹ * r * ‖∫...‖ ≤ 2⁻¹ * r * ((C + 4‖y‖²/r²) * (4/r))
  -- Align -2*r⁻¹ and -(2*r⁻¹) notation
  simp only [neg_mul] at hcf hnorm_bound
  calc μ.real {x | r < |⟪y, x⟫_ℝ|}
      ≤ 2⁻¹ * r * ‖∫ t in -(2 * r⁻¹)..2 * r⁻¹, (1 : ℂ) - charFun μ (t • y)‖ := hcf
    _ ≤ 2⁻¹ * r * ((C + 4 * ‖y‖ ^ 2 * r⁻¹ ^ 2) * |2 * r⁻¹ - -(2 * r⁻¹)|) :=
        mul_le_mul_of_nonneg_left hnorm_bound (by positivity)
    _ = 2 * C + 8 * ‖y‖ ^ 2 * r⁻¹ ^ 2 := by
        rw [show |2 * r⁻¹ - -(2 * r⁻¹)| = 4 * r⁻¹ from by
          rw [show 2 * r⁻¹ - -(2 * r⁻¹) = 4 * r⁻¹ from by ring]
          exact abs_of_nonneg (by positivity)]
        field_simp
        ring

/-- The family of measures constructed from Gaussian regularization is tight.
    For each ε > 0, μ_ε is the probability measure with charFun(μ_ε) = φ_ε.
    The tightness bound follows from: for any probability measure μ,
    μ({|⟪a,x⟫| > r}) ≤ C · r · ∫_{-2/r}^{2/r} (1 - Re(charFun μ (t·a))) dt
    (Mathlib: `measureReal_abs_inner_gt_le_integral_charFun`).
    Since charFun(μ_ε) = φ_ε → φ uniformly on compacts and φ is continuous
    at 0 with φ(0) = 1, the RHS → 0 uniformly in ε as r → ∞.
    Ref: Folland, §4.2, proof of Theorem 4.15.
-/
theorem gaussianRegularize_measures_tight (φ : V → ℂ)
    (hpd : IsPositiveDefinite φ) (hcont : Continuous φ) (hnorm : φ 0 = 1) :
    IsTightMeasureSet
      {(μ : Measure V) | ∃ ε, 0 < ε ∧ ε ≤ 1 ∧ ∃ (_ : IsProbabilityMeasure μ),
        ∀ ξ, charFun μ ξ = gaussianRegularize φ ε ξ} := by
  set S := {(μ : Measure V) | ∃ ε, 0 < ε ∧ ε ≤ 1 ∧ ∃ (_ : IsProbabilityMeasure μ),
    ∀ ξ, charFun μ ξ = gaussianRegularize φ ε ξ}
  -- Use the inner product criterion for tightness
  apply isTightMeasureSet_of_inner_tendsto (𝕜 := ℝ)
  intro y
  -- Need: Tendsto (fun r ↦ ⨆ μ ∈ S, μ {x | r < ‖⟪y, x⟫_ℝ‖}) atTop (𝓝 0)
  -- Show via tendsto_order: for all a > 0, eventually the iSup < a
  refine tendsto_order.mpr ⟨fun a ha => absurd ha (not_lt.mpr zero_le), fun a ha => ?_⟩
  -- Given a > 0 in ENNReal, need: ∀ᶠ r in atTop, ⨆ μ ∈ S, μ {x | r < ‖⟪y,x⟫_ℝ‖} < a
  -- Step 1: Get a real δ > 0 with ENNReal.ofReal δ < a
  obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ < a := by
    by_cases ha_top : a = ⊤
    · exact ⟨1, one_pos, ha_top ▸ ENNReal.ofReal_lt_top⟩
    · have ha_real := ENNReal.toReal_pos ha.ne' ha_top
      refine ⟨a.toReal / 2, by positivity, ?_⟩
      calc ENNReal.ofReal (a.toReal / 2)
          < ENNReal.ofReal a.toReal := (ENNReal.ofReal_lt_ofReal_iff ha_real).mpr (by linarith)
        _ = a := ENNReal.ofReal_toReal ha_top
  -- Step 2: By continuity of φ at 0 with φ(0) = 1, get η > 0 with
  --   ‖v‖ < η → ‖1 - φ v‖ < δ/4
  have hcont0 : ∀ η' > (0 : ℝ), ∃ ξ > 0, ∀ v : V, ‖v‖ < ξ → ‖(1:ℂ) - φ v‖ < η' := by
    intro η' hη'
    have h1 : ∃ ξ > 0, ∀ v : V, dist v 0 < ξ → dist (φ v) (φ 0) < η' :=
      Metric.continuousAt_iff.mp hcont.continuousAt η' hη'
    obtain ⟨ξ, hξ, hball⟩ := h1
    refine ⟨ξ, hξ, fun v hv => ?_⟩
    have := hball v (by rwa [dist_zero_right])
    rwa [hnorm, Complex.dist_eq, norm_sub_rev] at this
  obtain ⟨η, hη, hη_bound⟩ := hcont0 (δ / 4) (by positivity)
  -- Step 3: Choose R large enough
  -- Need: 2‖y‖/r < η (so |t|≤2/r gives ‖t•y‖ < η)
  -- Need: 8‖y‖²/r² < δ/2
  set R : ℝ := max (2 * ‖y‖ / η + 1) (max (Real.sqrt (16 * ‖y‖ ^ 2 / δ) + 1) 1)
  refine Filter.eventually_atTop.mpr ⟨R, fun r hr => ?_⟩
  -- Step 4: Bound the iSup
  -- For each μ ∈ S: μ {x | r < ‖⟪y,x⟫_ℝ‖} < a
  -- Note: ‖⟪y,x⟫_ℝ‖ = |⟪y,x⟫_ℝ| for real inner product
  have hr_pos : 0 < r := lt_of_lt_of_le one_pos (le_max_right _ _ |>.trans (le_max_right _ _)
    |>.trans hr)
  -- For r ≥ R: 2‖y‖/r < η
  have hsmall : 2 * ‖y‖ * r⁻¹ < η := by
    have hR1 : 2 * ‖y‖ / η + 1 ≤ r := (le_max_left _ _).trans hr
    -- 2‖y‖ < η * r since 2‖y‖/η + 1 ≤ r and η > 0
    have h1 : 2 * ‖y‖ < η * r := by
      have h2 : 2 * ‖y‖ / η < r := by linarith
      rw [div_lt_iff₀ hη] at h2; linarith
    rwa [mul_inv_lt_iff₀ hr_pos]
  -- For r ≥ R: 8‖y‖²/r² < δ/2
  have hsmall2 : 8 * ‖y‖ ^ 2 * r⁻¹ ^ 2 < δ / 2 := by
    have hR2 : Real.sqrt (16 * ‖y‖ ^ 2 / δ) + 1 ≤ r :=
      (le_max_left _ _ |>.trans (le_max_right _ _)).trans hr
    -- r² > 16‖y‖²/δ since r > sqrt(16‖y‖²/δ)
    have hsqrt_le : Real.sqrt (16 * ‖y‖ ^ 2 / δ) < r := by linarith
    have hr_sq : 16 * ‖y‖ ^ 2 / δ < r ^ 2 := by
      calc 16 * ‖y‖ ^ 2 / δ
          ≤ Real.sqrt (16 * ‖y‖ ^ 2 / δ) ^ 2 :=
            le_of_eq (Real.sq_sqrt (by positivity)).symm
        _ < r ^ 2 := by
            exact pow_lt_pow_left₀ hsqrt_le (Real.sqrt_nonneg _) (by norm_num)
    rw [inv_pow, mul_inv_lt_iff₀ (sq_pos_of_pos hr_pos)]
    -- hr_sq: 16 * ‖y‖² / δ < r², i.e. 16 * ‖y‖² < δ * r²
    rw [div_lt_iff₀ hδ_pos] at hr_sq
    linarith
  -- Bound for each μ ∈ S
  have hmu_bound : ∀ μ ∈ S, μ {x | r < ‖⟪y, x⟫_ℝ‖} ≤ ENNReal.ofReal δ := by
    intro μ hμS
    obtain ⟨ε, hε, hε1, hprob, hcf⟩ := hμS
    haveI := hprob
    -- Convert ‖⟪y,x⟫_ℝ‖ = |⟪y,x⟫_ℝ| for real scalars
    have hset_eq : {x : V | r < ‖⟪y, x⟫_ℝ‖} = {x | r < |⟪y, x⟫_ℝ|} := by
      ext x; simp [Real.norm_eq_abs]
    rw [hset_eq]
    -- Apply the key bound
    have hCval : ∀ t : ℝ, t ∈ Set.uIoc (-(2 * r⁻¹)) (2 * r⁻¹) →
        ‖(1 : ℂ) - φ (t • y)‖ ≤ δ / 4 := by
      intro t ht
      apply le_of_lt
      apply hη_bound
      rw [norm_smul, Real.norm_eq_abs]
      calc |t| * ‖y‖ ≤ 2 * r⁻¹ * ‖y‖ := by
            gcongr
            -- t ∈ uIoc (-(2*r⁻¹)) (2*r⁻¹) implies |t| ≤ 2*r⁻¹
            have hle : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by linarith [inv_pos.mpr hr_pos]
            rw [Set.uIoc_of_le hle] at ht
            exact abs_le.mpr ⟨by linarith [ht.1.le], ht.2⟩
        _ = 2 * ‖y‖ * r⁻¹ := by ring
        _ < η := hsmall
    have hreal_bound := charFun_measure_inner_bound φ hpd hnorm hε hε1 hcf hr_pos
      (by positivity : (0:ℝ) ≤ δ/4) hCval
    -- μ.real {r < |⟪y,x⟫|} ≤ 2*(δ/4) + 8‖y‖²/r² = δ/2 + 8‖y‖²/r² < δ
    -- Convert from μ.real to μ (ENNReal)
    rw [show μ {x | r < |⟪y, x⟫_ℝ|} = ENNReal.ofReal (μ.real {x | r < |⟪y, x⟫_ℝ|}) from by
      rw [Measure.real, ENNReal.ofReal_toReal]
      exact measure_ne_top μ _]
    apply ENNReal.ofReal_le_ofReal
    linarith
  -- Step 5: Conclude iSup ≤ ENNReal.ofReal δ < a
  calc ⨆ μ ∈ S, μ {x | r < ‖⟪y, x⟫_ℝ‖}
      ≤ ENNReal.ofReal δ := iSup₂_le hmu_bound
    _ < a := hδ_lt

/-! ## Phase 5: Uniqueness (from Mathlib)

`MeasureTheory.Measure.ext_of_charFun` already proves that charFun determines
the measure uniquely.
-/

/-! ## Main Theorem -/

omit [FiniteDimensional ℝ V] in
/-- The characteristic function of the weak limit equals `φ` (per-test-vector step of
`bochner_existence`).
-/
private theorem bochner_charFun_eq (φ : V → ℂ) {μ : ProbabilityMeasure V}
    {μ_seq : ℕ → ProbabilityMeasure V} {f : ℕ → ℕ}
    (hμ_seq : ∀ n ξ, MeasureTheory.charFun (μ_seq n : Measure V) ξ
      = gaussianRegularize φ (1 / (↑n + 1)) ξ)
    (hf_strict : StrictMono f)
    (hf_conv : Filter.Tendsto (fun n => μ_seq (f n)) Filter.atTop (nhds μ))
    (ξ : V) : MeasureTheory.charFun (μ : Measure V) ξ = φ ξ := by
  -- The function x ↦ cexp(⟪x,ξ⟫ * I) is bounded continuous
  set g_ξ : BoundedContinuousFunction V ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => cexp (↑⟪x, ξ⟫_ℝ * I)) (by fun_prop) 1
    (fun x => by simp [Complex.norm_exp_ofReal_mul_I]) with hg_ξ_def
  -- Weak convergence: ∫ g_ξ ∂(μ_seq (f n)) → ∫ g_ξ ∂μ
  have hweak := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    hf_conv g_ξ
  -- LHS: ∫ g_ξ ∂(μ_seq (f n)) = charFun(μ_seq (f n))(ξ)
  have hlhs : ∀ n, ∫ x, g_ξ x ∂(μ_seq (f n) : Measure V) = charFun (μ_seq (f n) : Measure V) ξ := by
    intro n; simp [charFun_apply, hg_ξ_def]
  -- RHS: ∫ g_ξ ∂μ = charFun(μ)(ξ)
  have hrhs : ∫ x, g_ξ x ∂(μ : Measure V) = charFun (μ : Measure V) ξ := by
    simp [charFun_apply, hg_ξ_def]
  -- So charFun(μ_seq (f n))(ξ) → charFun(μ)(ξ)
  have hcharfun_conv : Tendsto (fun n => charFun (μ_seq (f n) : Measure V) ξ) atTop
      (𝓝 (charFun (μ : Measure V) ξ)) := by
    rwa [show (fun n => charFun (↑(μ_seq (f n))) ξ) =
      (fun n => ∫ x, g_ξ x ∂(μ_seq (f n) : Measure V)) from funext (fun n => (hlhs n).symm),
      show charFun (↑μ) ξ = ∫ x, g_ξ x ∂(μ : Measure V) from hrhs.symm]
  -- Also charFun(μ_seq (f n))(ξ) = gaussianRegularize φ (1/(f n + 1)) ξ → φ ξ
  have hcharfun_vals : ∀ n, charFun (μ_seq (f n) : Measure V) ξ =
      gaussianRegularize φ (1 / (↑(f n) + 1)) ξ :=
    fun n => hμ_seq (f n) ξ
  -- gaussianRegularize φ (1/(f n + 1)) ξ → φ ξ as f n → ∞
  have heps_tendsto : Tendsto (fun n => (1 : ℝ) / (↑(f n) + 1)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hfn : Tendsto (fun n => (↑(f n) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hf_strict.tendsto_atTop
      have hfn1 : Tendsto (fun n => (↑(f n) : ℝ) + 1) atTop atTop :=
        Filter.tendsto_atTop_add_const_right atTop 1 hfn
      simp_rw [one_div]
      exact tendsto_inv_atTop_zero.comp hfn1
    · exact Eventually.of_forall (fun n => Set.mem_Ioi.mpr (by positivity))
  have hgr_conv : Tendsto (fun n => gaussianRegularize φ (1 / (↑(f n) + 1)) ξ) atTop (𝓝 (φ ξ)) :=
    (gaussianRegularize_tendsto φ ξ).comp heps_tendsto
  -- The same sequence also → charFun(μ)(ξ) by weak convergence
  have hgr_conv' : Tendsto (fun n => charFun (μ_seq (f n) : Measure V) ξ) atTop (𝓝 (φ ξ)) := by
    rwa [show (fun n => charFun (↑(μ_seq (f n))) ξ) =
      (fun n => gaussianRegularize φ (1 / (↑(f n) + 1)) ξ) from funext hcharfun_vals]
  -- By uniqueness of limits: charFun μ ξ = φ ξ
  exact tendsto_nhds_unique hcharfun_conv hgr_conv'

/-- For each `ε > 0` the Gaussian-regularised functional `φ_ε` is the characteristic function
of a probability measure.
-/
private lemma bochner_mu_eps (φ : V → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefinite φ) (hnorm : φ 0 = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ_ε : ProbabilityMeasure V,
      ∀ ξ, MeasureTheory.charFun (μ_ε : Measure V) ξ = gaussianRegularize φ ε ξ :=
  measure_of_pd_l1 (gaussianRegularize φ ε)
    (gaussianRegularize_pd φ hpd ε hε)
    (gaussianRegularize_integrable φ hpd hcont ε hε)
    (hcont.mul (by fun_prop))
    (by rw [gaussianRegularize_zero]; exact hnorm)
    (gaussianRegularize_ft_integrable φ hpd hcont ε hε)

/-- The Gaussian-regularised family `μ_{1/(n+1)}` exists as a sequence of probability measures. -/
private lemma bochner_mu_seq (φ : V → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefinite φ) (hnorm : φ 0 = 1) :
    ∃ μ_seq : ℕ → ProbabilityMeasure V,
      ∀ n ξ, MeasureTheory.charFun (μ_seq n : Measure V) ξ = gaussianRegularize φ (1 / (↑n + 1)) ξ
        := by
  choose μ_seq hμ_seq using
    fun n : ℕ => bochner_mu_eps φ hcont hpd hnorm (show (0:ℝ) < 1 / (↑n + 1) by positivity)
  exact ⟨μ_seq, hμ_seq⟩

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- Each Gaussian-regularised measure lies in the tight set from
`gaussianRegularize_measures_tight`. -/
private theorem bochner_mem_tight (φ : V → ℂ) {μ_seq : ℕ → ProbabilityMeasure V}
    (hμ_seq : ∀ n ξ, MeasureTheory.charFun (μ_seq n : Measure V) ξ
      = gaussianRegularize φ (1 / (↑n + 1)) ξ) (n : ℕ) :
    (μ_seq n : Measure V) ∈ {(μ : Measure V) | ∃ ε, 0 < ε ∧ ε ≤ 1 ∧
      ∃ (_ : IsProbabilityMeasure μ), ∀ ξ, charFun μ ξ = gaussianRegularize φ ε ξ} := by
  rw [Set.mem_setOf_eq]
  refine ⟨1 / (↑n + 1), ?_, ?_, ?_, ?_⟩
  · positivity
  · have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_one₀ h1]
    linarith [n.cast_nonneg (α := ℝ)]
  · exact (μ_seq n).prop
  · exact hμ_seq n

/-- The range of the Gaussian-regularised sequence is a tight set of probability measures. -/
private lemma bochner_S_tight (φ : V → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefinite φ) (hnorm : φ 0 = 1)
    {μ_seq : ℕ → ProbabilityMeasure V}
    (hμ_seq : ∀ n ξ, MeasureTheory.charFun (μ_seq n : Measure V) ξ
      = gaussianRegularize φ (1 / (↑n + 1)) ξ) :
    IsTightMeasureSet {((μ : ProbabilityMeasure V) : Measure V) | μ ∈ Set.range μ_seq} := by
  apply IsTightMeasureSet.subset (gaussianRegularize_measures_tight φ hpd hcont hnorm)
  rintro μ ⟨ν, hνS, rfl⟩
  obtain ⟨n, rfl⟩ := hνS
  exact bochner_mem_tight φ hμ_seq n

/-- Existence half of `bochner_theorem`: from a continuous positive-definite normalized functional
build a probability measure with the given characteristic function.
-/
private theorem bochner_existence (φ : V → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefinite φ) (hnorm : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure V,
      ∀ ξ, MeasureTheory.charFun (μ : Measure V) ξ = φ ξ := by
  obtain ⟨μ_seq, hμ_seq⟩ := bochner_mu_seq φ hcont hpd hnorm
  have hcompact : IsCompact (closure (Set.range μ_seq)) :=
    isCompact_closure_of_isTightMeasureSet (bochner_S_tight φ hcont hpd hnorm hμ_seq)
  have hseq_in : ∀ n, μ_seq n ∈ closure (Set.range μ_seq) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨μ, _, f, hf_strict, hf_conv⟩ := hcompact.tendsto_subseq hseq_in
  exact ⟨μ, fun ξ => bochner_charFun_eq φ hμ_seq hf_strict hf_conv ξ⟩

/-- **Bochner's Theorem.** A continuous positive-definite function φ : V → ℂ
with φ(0) = 1 on a finite-dimensional real inner product space is the
characteristic function of a unique probability measure on V.

This is the finite-dimensional version. The infinite-dimensional
generalization (Bochner-Minlos) additionally requires nuclearity of the
domain space.
-/
theorem bochner_theorem (φ : V → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefinite φ) (hnorm : φ 0 = 1) :
    ∃! μ : ProbabilityMeasure V,
      ∀ ξ, MeasureTheory.charFun (μ : Measure V) ξ = φ ξ := by
  obtain ⟨μ, hμ⟩ := bochner_existence φ hcont hpd hnorm
  refine ⟨μ, hμ, fun ν hν => ?_⟩
  have hmeas : (μ : Measure V) = (ν : Measure V) :=
    Measure.ext_of_charFun (by ext ξ; rw [hμ ξ, hν ξ])
  exact Subtype.ext hmeas.symm
