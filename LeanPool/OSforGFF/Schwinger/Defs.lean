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
  classical
  simp

/-- The Schwinger function equals the direct covariance integral for n=2 -/
lemma schwinger_eq_covariance (dμ_config : ProbabilityMeasure FieldConfiguration) (f g :
  TestFunction) :
  SchwingerFunction₂ dμ_config f g = ∫ ω, (distributionPairing ω f) * (distributionPairing ω g)
    ∂dμ_config.toMeasure := by
  unfold SchwingerFunction₂ SchwingerFunction
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
  let u₁ : FieldConfiguration → ℂ := fun ω => distributionPairingℂReal ω φ₁
  let u₂ : FieldConfiguration → ℂ := fun ω => distributionPairingℂReal ω φ₂
  let v  : FieldConfiguration → ℂ := fun ω => distributionPairingℂReal ω ψ
  have hint₁ : Integrable (fun ω => u₁ ω * v ω) dμ_config.toMeasure := by simpa using h_int φ₁ ψ
  have hint₂ : Integrable (fun ω => u₂ ω * v ω) dμ_config.toMeasure := by simpa using h_int φ₂ ψ
  have hint₃ : Integrable (fun ω => u₁ ω * u₂ ω) dμ_config.toMeasure := by simpa using h_int φ₁ φ₂
  have hlin : ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure
              = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := by
    simpa using (integral_smul (μ := dμ_config.toMeasure)
      (f := fun ω => u₁ ω * v ω) c)
  -- 1) Scalar multiplication in the first argument
  have h_smul_left_integrand :
      (fun ω => distributionPairingℂReal ω (c • φ₁) * distributionPairingℂReal ω ψ)
      = (fun ω => c • (u₁ ω * v ω)) := by
    funext ω
    have h := pairing_linear_combo ω φ₁ (0 : TestFunctionℂ) c 0
    have h' : distributionPairingℂReal ω (c • φ₁) = c * distributionPairingℂReal ω φ₁ := by
      simpa using h
    rw [h']
    simp [u₁, v, smul_eq_mul]
    ring
  have h1 :
      SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
    calc
      SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ
          = ∫ ω, distributionPairingℂReal ω (c • φ₁) * distributionPairingℂReal ω ψ
            ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two]
      _ = ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure := by simp [h_smul_left_integrand]
      _ = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := hlin
      _ = c • SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, v, Fin.prod_univ_two]
      _ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by rw [smul_eq_mul]
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
    calc
      SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ)
          = ∫ ω, distributionPairingℂReal ω φ₁ * distributionPairingℂReal ω (c • ψ)
            ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two]
      _ = ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure := by simp [h_smul_right_integrand]
      _ = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := hlin
      _ = c • SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, v, Fin.prod_univ_two]
      _ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by rw [smul_eq_mul]
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

/-! ## Basic Distribution Framework

The following definitions provide the foundation for viewing Schwinger functions
as distributions on product spaces. These are needed by other modules.
-/

/-- The product space of n copies of spacetime -/
abbrev SpaceTimeProduct (n : ℕ) := (Fin n) → SpaceTime

/-- Test functions on the n-fold product space -/
abbrev TestFunctionProduct (n : ℕ) := SchwartzMap (SpaceTimeProduct n) ℝ
