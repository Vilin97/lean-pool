/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.ComplexTestFunction

/-!
# Generating Functional and Schwinger Functions

Defines the generating functional Z[J] = ∫ exp(i⟨ω,J⟩) dμ(ω) and
Schwinger n-point functions Sₙ(f₁,...,fₙ) = ∫ ⟨ω,f₁⟩...⟨ω,fₙ⟩ dμ(ω).

For centered Gaussian measures: Z[J] = exp(−½⟨J,CJ⟩) and all Sₙ are
determined by Wick's theorem from the two-point function S₂ = C.
-/

open MeasureTheory Complex
open TopologicalSpace

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜]

/-! ## Schwinger Functions

The Schwinger functions S_n are the n-th moments of field operators φ(f₁)...φ(fₙ)
where φ(f) = ⟨ω, f⟩ is the field operator defined by pairing the field configuration
with a test function.

Following Glimm and Jaffe, these are the fundamental correlation functions:
S_n(f₁,...,fₙ) = ∫ ⟨ω,f₁⟩ ⟨ω,f₂⟩ ... ⟨ω,fₙ⟩ dμ(ω)

The Schwinger functions contain all the physics and satisfy the OS axioms.
They can be obtained from the generating functional via exponential series:
S_n(f₁,...,fₙ) = (-i)ⁿ (coefficient of (iJ)ⁿ/n! in Z[J])
-/

/-- The n-th Schwinger function: n-point correlation function of field operators.
    S_n(f₁,...,fₙ) = ∫ ⟨ω,f₁⟩ ⟨ω,f₂⟩ ... ⟨ω,fₙ⟩ dμ(ω)

    This is the fundamental object in constructive QFT - all physics is contained
    in the infinite sequence of Schwinger functions {S_n}_{n=1}^∞.
-/
def SchwingerFunction (dμ_config : ProbabilityMeasure FieldConfiguration) (n : ℕ)
  (f : Fin n → TestFunction) : ℝ :=
  ∫ ω, (∏ i, distributionPairing ω (f i)) ∂dμ_config.toMeasure

/-- The 1-point Schwinger function: the mean field -/
def SchwingerFunction₁ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (f : TestFunction) : ℝ :=
  SchwingerFunction dμ_config 1 ![f]

/-- The 2-point Schwinger function: the covariance -/
def SchwingerFunction₂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (f g : TestFunction) : ℝ :=
  SchwingerFunction dμ_config 2 ![f, g]


/-- The Schwinger function equals the GJ mean for n=1 -/
lemma schwinger_eq_mean (dμ_config : ProbabilityMeasure FieldConfiguration) (f : TestFunction) :
  SchwingerFunction₁ dμ_config f = GJMean dμ_config f := by
  unfold SchwingerFunction₁ SchwingerFunction GJMean
  -- The product over a singleton {0} is just the single element f 0 = f
  classical
  -- simplify the finite product over Fin 1 and evaluate the single entry of ![f]
  simp

/-- The Schwinger function equals the direct covariance integral for n=2 -/
lemma schwinger_eq_covariance (dμ_config : ProbabilityMeasure FieldConfiguration) (f g :
  TestFunction) :
  SchwingerFunction₂ dμ_config f g = ∫ ω, (distributionPairing ω f) * (distributionPairing ω g)
    ∂dμ_config.toMeasure := by
  unfold SchwingerFunction₂ SchwingerFunction
  -- The product over {0, 1} expands to (f 0) * (f 1) = f * g
  classical
  simp [Fin.prod_univ_two]

/-- For centered measures (zero mean), the 1-point function vanishes -/
lemma schwinger_vanishes_centered (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_centered : ∀ f : TestFunction, GJMean dμ_config f = 0) (f : TestFunction) :
  SchwingerFunction₁ dμ_config f = 0 := by
  rw [schwinger_eq_mean]
  exact h_centered f

/-- Complex version of Schwinger functions for complex test functions -/
def SchwingerFunctionℂ (dμ_config : ProbabilityMeasure FieldConfiguration) (n : ℕ)
  (f : Fin n → TestFunctionℂ) : ℂ :=
  ∫ ω, (∏ i, distributionPairingℂReal ω (f i)) ∂dμ_config.toMeasure

/-- The complex 2-point Schwinger function for complex test functions.
    This is the natural extension of SchwingerFunction₂ to complex test functions.
-/
def SchwingerFunctionℂ₂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (φ ψ : TestFunctionℂ) : ℂ :=
  SchwingerFunctionℂ dμ_config 2 ![φ, ψ]

/-- Property that SchwingerFunctionℂ₂ is ℂ-bilinear in both arguments.
    This is a key property for Gaussian measures and essential for OS0 analyticity.
-/
def CovarianceBilinear (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (c : ℂ) (φ₁ φ₂ ψ : TestFunctionℂ),
    SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ +
      SchwingerFunctionℂ₂ dμ_config φ₂ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ) = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂) = SchwingerFunctionℂ₂ dμ_config φ₁ ψ +
      SchwingerFunctionℂ₂ dμ_config φ₁ φ₂

/-- If the product pairing is integrable for all test functions, then the complex
    2-point Schwinger function is ℂ-bilinear in both arguments.
-/
lemma CovarianceBilinear_of_integrable
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_int : ∀ (φ ψ : TestFunctionℂ),
    Integrable (fun ω => distributionPairingℂReal ω φ * distributionPairingℂReal ω ψ)
      dμ_config.toMeasure) :
  CovarianceBilinear dμ_config := by
  classical
  intro c φ₁ φ₂ ψ
  -- Abbreviations for the integrands
  let u₁ : FieldConfiguration → ℂ := fun ω => distributionPairingℂReal ω φ₁
  let u₂ : FieldConfiguration → ℂ := fun ω => distributionPairingℂReal ω φ₂
  let v  : FieldConfiguration → ℂ := fun ω => distributionPairingℂReal ω ψ
  have hint₁ : Integrable (fun ω => u₁ ω * v ω) dμ_config.toMeasure := by simpa using h_int φ₁ ψ
  have hint₂ : Integrable (fun ω => u₂ ω * v ω) dμ_config.toMeasure := by simpa using h_int φ₂ ψ
  have hint₃ : Integrable (fun ω => u₁ ω * u₂ ω) dμ_config.toMeasure := by simpa using h_int φ₁ φ₂
  -- 1) Scalar multiplication in the first argument
  have h_smul_left_integrand :
      (fun ω => distributionPairingℂReal ω (c • φ₁) * distributionPairingℂReal ω ψ)
      = (fun ω => c • (u₁ ω * v ω)) := by
    funext ω
    have h := pairing_linear_combo ω φ₁ (0 : TestFunctionℂ) c 0
    -- dp ω (c•φ₁) = c * dp ω φ₁
    have h' : distributionPairingℂReal ω (c • φ₁) = c * distributionPairingℂReal ω φ₁ := by
      simpa using h
    -- Multiply by the second factor and reassociate
    rw [h']
    simp [u₁, v, smul_eq_mul]
    ring
  have h1 :
      SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
    -- Use scalar pull-out from the integral
    have hlin : ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure
                = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := by
      simpa using (integral_smul (μ := dμ_config.toMeasure)
        (f := fun ω => u₁ ω * v ω) c)
    calc
      SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ
          = ∫ ω, distributionPairingℂReal ω (c • φ₁) * distributionPairingℂReal ω ψ
            ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two]
      _ = ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure := by
            simp [h_smul_left_integrand]
      _ = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := hlin
      _ = c • SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, v, Fin.prod_univ_two]
      _ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            rw [smul_eq_mul]
  -- 2) Additivity in the first argument
  have h_add_left_integrand :
      (fun ω => distributionPairingℂReal ω (φ₁ + φ₂) * distributionPairingℂReal ω ψ)
      = (fun ω => u₁ ω * v ω + u₂ ω * v ω) := by
    funext ω
    have h := pairing_linear_combo ω φ₁ φ₂ (1 : ℂ) (1 : ℂ)
    have h' : distributionPairingℂReal ω (φ₁ + φ₂)
              = distributionPairingℂReal ω φ₁ + distributionPairingℂReal ω φ₂ := by
      simpa using h
    rw [h']
    ring
  have hsum_left : ∫ ω, (u₁ ω * v ω + u₂ ω * v ω) ∂dμ_config.toMeasure
      = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₂ ω * v ω ∂dμ_config.toMeasure := by
    simpa using (integral_add (hf := hint₁) (hg := hint₂))
  have h2 :
      SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ
        = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ := by
    calc
      SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ
          = ∫ ω, (u₁ ω * v ω + u₂ ω * v ω) ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two, h_add_left_integrand]
      _ = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₂ ω * v ω ∂dμ_config.toMeasure := hsum_left
      _ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, u₂, v, Fin.prod_univ_two,
              Matrix.cons_val_zero]
  -- 3) Scalar multiplication in the second argument
  have h_smul_right_integrand :
      (fun ω => distributionPairingℂReal ω φ₁ * distributionPairingℂReal ω (c • ψ))
      = (fun ω => c • (u₁ ω * v ω)) := by
    funext ω
    have h := pairing_linear_combo ω ψ (0 : TestFunctionℂ) c 0
    have h' : distributionPairingℂReal ω (c • ψ) = c * distributionPairingℂReal ω ψ := by
      simpa using h
    rw [h']
    simp [u₁, v, smul_eq_mul]
    ring
  have h3 :
      SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ) = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
    have hlin : ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure
                = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := by
      simpa using (integral_smul (μ := dμ_config.toMeasure)
        (f := fun ω => u₁ ω * v ω) c)
    calc
      SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ)
          = ∫ ω, distributionPairingℂReal ω φ₁ * distributionPairingℂReal ω (c • ψ)
            ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two]
      _ = ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure := by
            simp [h_smul_right_integrand]
      _ = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := hlin
      _ = c • SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, v, Fin.prod_univ_two]
      _ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            rw [smul_eq_mul]
  -- 4) Additivity in the second argument
  have h_add_right_integrand :
      (fun ω => distributionPairingℂReal ω φ₁ * distributionPairingℂReal ω (ψ + φ₂))
      = (fun ω => u₁ ω * v ω + u₁ ω * u₂ ω) := by
    funext ω
    have h := pairing_linear_combo ω ψ φ₂ (1 : ℂ) (1 : ℂ)
    have h' : distributionPairingℂReal ω (ψ + φ₂)
              = distributionPairingℂReal ω ψ + distributionPairingℂReal ω φ₂ := by
      simpa using h
    rw [h']
    ring
  have hsum_right : ∫ ω, (u₁ ω * v ω + u₁ ω * u₂ ω) ∂dμ_config.toMeasure
      = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₁ ω * u₂ ω ∂dμ_config.toMeasure := by
    have hint₁₂ : Integrable (fun ω => u₁ ω * u₂ ω) dμ_config.toMeasure := hint₃
    simpa using (integral_add (hf := hint₁) (hg := hint₁₂))
  have h4 :
      SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂)
        = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂ := by
    calc
      SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂)
          = ∫ ω, (u₁ ω * v ω + u₁ ω * u₂ ω) ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two, h_add_right_integrand]
      _ = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₁ ω * u₂ ω ∂dμ_config.toMeasure := hsum_right
      _ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, u₂, v, Fin.prod_univ_two,
              Matrix.cons_val_zero]
  -- Bundle the four identities
  exact And.intro h1 (And.intro h2 (And.intro h3 h4))
/-! ## Exponential Series Connection to Generating Functional

The key insight: Instead of functional derivatives, we use the constructive exponential series:
Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω) = ∑_{n=0}^∞ (i)^n/n! * S_n(J,...,J)

This approach is more elementary and constructive than functional derivatives.
-/
/-- A (centered) Gaussian field measure: the generating functional is an exponential of a
quadratic form. -/
def IsGaussianMeasure (dμ : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∃ (Cov : TestFunction → TestFunction → ℝ),
    ∀ J : TestFunction,
      GJGeneratingFunctional dμ J = Complex.exp ((-(1 : ℂ) / 2) * (Cov J J : ℂ))


/-
  === Exponential series for Z[J] via Dominated Convergence (along a ray) ===

  We prove:
    Z[J] = ∑ (i)^n / n! * S_n(J,…,J),

  by expanding exp(i⟨ω,J⟩) pointwise, bounding partial sums by exp(|⟨ω,J⟩|),
  and swapping ∫ and limit. This requires only an along‑ray exponential‑moment
  hypothesis. We package that as a simple Prop and then derive your theorem.
-/

open BigOperators MeasureTheory Complex

noncomputable section
namespace AQFTExponentialSeries

variable {FieldConfiguration TestFunction : Type} -- (only to appease editors)
-- (We actually use the ones from your file; no new structures introduced.)


/-- Finite Taylor partial sum of the exponential `exp(i x)` (complex valued). -/
private def expIPartial (N : ℕ) (x : ℝ) : ℂ :=
  (Finset.range (N+1)).sum (fun n =>
    (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))

/-- Pointwise limit of the partial sums `expIPartial N x` is `exp(i x)`. -/
private lemma expIPartial_tendsto (x : ℝ) :
  Filter.Tendsto (fun N => expIPartial N x) Filter.atTop (nhds (Complex.exp (Complex.I * (x : ℂ))))
    := by
  classical
  -- Power series for the complex exponential at z = i * x
  -- Use the Banach algebra version of the exponential series has-sum.
  have hsum :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (𝔸 := ℂ)
      (x := (Complex.I * (x : ℂ))))
  -- Re-express terms to match our expIPartial integrand
  have hsum' : HasSum (fun n : ℕ =>
      (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))
      (Complex.exp (Complex.I * (x : ℂ))) := by
    -- Rewrite ((I * x)^n)/(n!) and (·)•(·) into our summand shape
    --   (n! : ℂ)⁻¹ • (I * x)^n = I^n * x^n / (n!)
    simpa [mul_pow, div_eq_mul_inv, smul_eq_mul,
           mul_comm, mul_left_comm, mul_assoc, Complex.exp_eq_exp_ℂ]
      using hsum
  -- Partial sums over range N tend to the sum
  have htend := hsum'.tendsto_sum_nat
  -- Compose with the shift N ↦ N+1 so we get range (N+1)
  have hshift : Filter.Tendsto (fun N : ℕ => N + 1) Filter.atTop Filter.atTop := by
    simpa using (Filter.tendsto_add_atTop_nat 1)
  -- Our definition uses range (N+1), align it and conclude
  have hsum_def :
      (fun N => expIPartial N x)
        = (fun N => (Finset.range (N+1)).sum
              (fun n => (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))) := by
    funext N; simp [expIPartial]
  -- Final: tendsto of our partial sums
  simpa [hsum_def, Function.comp_def] using htend.comp hshift

private lemma expIPartial_norm_le (x : ℝ) (N : ℕ) :
  ‖expIPartial N x‖ ≤ Real.exp (|x|) := by
  classical
  -- 1) Triangle inequality on the finite sum
  have h₁ :
      ‖expIPartial N x‖
        ≤ (Finset.range (N+1)).sum
            (fun n => ‖(Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)‖) := by
    simpa [expIPartial] using
      (norm_sum_le (s := Finset.range (N+1))
        (f := fun n => (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)))
  -- 2) Bound each term by (|x|^n)/n! and sum
  have h_term_le :
      ∀ n, ‖(Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)‖
            ≤ (|x| : ℝ) ^ n / (n.factorial : ℝ) := by
    intro n
    -- Use multiplicativity of the norm and basic computations via simp
    -- ‖I^n‖ = 1, ‖(x:ℂ)^n‖ = |x|^n, ‖(n! : ℂ)‖ = n!
    simp [norm_pow, div_eq_mul_inv, norm_inv]
  have h₂ :
      (Finset.range (N+1)).sum
          (fun n => ‖(Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)‖)
        ≤ (Finset.range (N+1)).sum (fun n : ℕ => (|x| : ℝ) ^ n / (n.factorial : ℝ)) := by
    exact Finset.sum_le_sum (fun n _hn => h_term_le n)
  -- 3) Partial sums of ∑ |x|^n / n! are bounded by exp |x|
  have hsumR :
      HasSum (fun n : ℕ => (|x| : ℝ) ^ n / (n.factorial : ℝ))
             (Real.exp (|x|)) := by
    -- Banach algebra exponential series over ℝ at x = |x|
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Real.exp_eq_exp_ℝ]
      using (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) (x := (|x|)))
  have h_nonneg :
      ∀ n, 0 ≤ (|x| : ℝ) ^ n / (n.factorial : ℝ) := by
    intro n
    exact div_nonneg (pow_nonneg (abs_nonneg x) n) (by exact Nat.cast_nonneg' n.factorial)
  have h₃ :
      (Finset.range (N+1)).sum (fun n => (|x| : ℝ) ^ n / (n.factorial : ℝ))
        ≤ Real.exp (|x|) := by
    -- Use the modern Summable.sum_le_tsum
    have := (hsumR.summable.sum_le_tsum (s := Finset.range (N+1))
      (by
        intro n hn
        exact h_nonneg n))
    simpa [hsumR.tsum_eq] using this
  -- 4) Chain the bounds
  exact h₁.trans (le_trans h₂ h₃)



/-- Product over `Fin n` of a constant equals the n-th power (for our integrand). -/
private lemma prod_const_pow (x : ℝ) (n : ℕ) :
  (∏ _i : Fin n, x) = x ^ n :=
  Fin.prod_const n x

/-- Identify `S_n(J,…,J)` as the integral of the n-th power of `⟨ω,J⟩`. -/
private lemma schwinger_eq_integral_pow
  (dμ : ProbabilityMeasure _root_.FieldConfiguration) (J : _root_.TestFunction) (n : ℕ) :
  (SchwingerFunction dμ n (fun _ => J) : ℝ)
  = ∫ ω, (distributionPairing ω J) ^ n ∂ dμ.toMeasure := by
  -- Unfold `SchwingerFunction` and simplify the Finite product on `Fin n`
  -- to a power using `prod_const_pow`.
  classical
  unfold SchwingerFunction
  -- integrand: ∏ i, ⟨ω,J⟩ = (⟨ω,J⟩)^n
  -- Pointwise product-to-power identity
  have hω : ∀ ω : _root_.FieldConfiguration, (∏ _i : Fin n,
    distributionPairing ω J) = (distributionPairing ω J) ^ n := by
    intro ω
    simp only [prod_const_pow]
  -- Rewrite under the integral using the pointwise identity
  simp [hω]

end AQFTExponentialSeries

/-! ## Basic Distribution Framework

The following definitions provide the foundation for viewing Schwinger functions
as distributions on product spaces. These are needed by other modules.
-/

/-- The product space of n copies of spacetime -/
abbrev SpaceTimeProduct (n : ℕ) := (Fin n) → SpaceTime

/-- Test functions on the n-fold product space -/
abbrev TestFunctionProduct (n : ℕ) := SchwartzMap (SpaceTimeProduct n) ℝ
