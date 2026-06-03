/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Analysis.Complex.OperatorNorm

import LeanPool.OSforGFF.Spacetime.Basic

/-!
## Complex Test Function Linearity

This file contains lemmas about linearity properties of complex test functions
and their pairings with field configurations.

### Main Results:

**Complex Arithmetic Helpers:**
- `re_of_complex_combination`: Real part of complex linear combination
- `im_of_complex_combination`: Imaginary part of complex linear combination

**Decomposition Linearity:**
- `ω_re_decompose_linear`: ω-linearity of real component under complex operations
- `ω_im_decompose_linear`: ω-linearity of imaginary component under complex operations

**Pairing Linearity:**
- `pairing_linear_combo`: Key result showing distributionPairingℂReal is ℂ-linear
  in the test function argument

These results are essential for proving bilinearity of Schwinger functions
and other quantum field theory constructions.
-/

open Complex MeasureTheory

/-! ## Main definitions

- `toComplex`: Embed real Schwartz functions into complex Schwartz functions
- `toComplexCLM`: The continuous ℝ-linear map version of `toComplex`
-/

noncomputable section

-- Key lemma: how reCLM behaves with complex operations
private lemma re_of_complex_combination (a b : ℂ) (u v : ℂ) :
  Complex.re (a * u + b * v) = a.re * u.re - a.im * u.im + b.re * v.re - b.im * v.im := by
  -- Use basic complex arithmetic
  simp only [add_re, mul_re]
  ring

-- Key lemma: how imCLM behaves with complex operations
private lemma im_of_complex_combination (a b : ℂ) (u v : ℂ) :
  Complex.im (a * u + b * v) = a.re * u.im + a.im * u.re + b.re * v.im + b.im * v.re := by
  -- Use basic complex arithmetic
  simp only [add_im, mul_im]
  ring

/-- ω-linearity of the real component of the complex test-function decomposition under
    complex linear combinations. This follows from ℝ-linearity of ω and pointwise
    behavior of complex operations on Schwartz functions.
-/
lemma ω_re_decompose_linear
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  ω ((complexTestFunctionDecompose (t • f + s • g)).1)
    = t.re * ω ((complexTestFunctionDecompose f).1)
      - t.im * ω ((complexTestFunctionDecompose f).2)
      + s.re * ω ((complexTestFunctionDecompose g).1)
      - s.im * ω ((complexTestFunctionDecompose g).2) := by
  -- First, identify the real-part test function of t•f + s•g as a linear combination
  have h_sum_re_eq :
      (complexTestFunctionDecompose (t • f + s • g)).1
        = t.re • (complexTestFunctionDecompose f).1
          - t.im • (complexTestFunctionDecompose f).2
          + s.re • (complexTestFunctionDecompose g).1
          - s.im • (complexTestFunctionDecompose g).2 := by
    ext x
    -- Rewrite to Complex.re/Complex.im and use algebra on ℂ
    change Complex.reCLM ((t • f + s • g) x)
        = t.re * Complex.reCLM (f x) - t.im * Complex.imCLM (f x)
          + s.re * Complex.reCLM (g x) - s.im * Complex.imCLM (g x)
    -- Evaluate pointwise scalar multiplication and addition
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, reCLM_apply,
      add_re, mul_re, imCLM_apply]
    -- Switch CLMs to the scalar functions and finish with the algebraic identity
    change Complex.re (t * f x + s * g x)
        = t.re * Complex.re (f x) - t.im * Complex.im (f x)
          + s.re * Complex.re (g x) - s.im * Complex.im (g x)
    simpa using re_of_complex_combination t s (f x) (g x)
  -- Apply ω (a real-linear functional) to both sides
  have := congrArg (fun (φ : TestFunction) => ω φ) h_sum_re_eq
  -- Simplify using linearity of ω over ℝ
  simpa [map_add, map_sub, map_smul]
    using this

/-- ω-linearity of the imaginary component of the complex test-function decomposition under
    complex linear combinations.
-/
lemma ω_im_decompose_linear
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  ω ((complexTestFunctionDecompose (t • f + s • g)).2)
    = t.re * ω ((complexTestFunctionDecompose f).2)
      + t.im * ω ((complexTestFunctionDecompose f).1)
      + s.re * ω ((complexTestFunctionDecompose g).2)
      + s.im * ω ((complexTestFunctionDecompose g).1) := by
  -- Identify the imaginary-part test function of t•f + s•g as a linear combination
  have h_sum_im_eq :
      (complexTestFunctionDecompose (t • f + s • g)).2
        = t.re • (complexTestFunctionDecompose f).2
          + t.im • (complexTestFunctionDecompose f).1
          + s.re • (complexTestFunctionDecompose g).2
          + s.im • (complexTestFunctionDecompose g).1 := by
    ext x
    -- Rewrite to Complex.im/Complex.re and use algebra on ℂ
    change Complex.imCLM ((t • f + s • g) x)
        = t.re * Complex.imCLM (f x) + t.im * Complex.reCLM (f x)
          + s.re * Complex.imCLM (g x) + s.im * Complex.reCLM (g x)
    -- Evaluate pointwise scalar multiplication and addition
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, imCLM_apply,
      add_im, mul_im, reCLM_apply]
    -- Switch CLMs to scalar functions and finish with the algebraic identity
    change Complex.im (t * f x + s * g x)
        = t.re * Complex.im (f x) + t.im * Complex.re (f x)
          + s.re * Complex.im (g x) + s.im * Complex.re (g x)
    simpa using im_of_complex_combination t s (f x) (g x)
  -- Apply ω (a real-linear functional) to both sides
  have := congrArg (fun (φ : TestFunction) => ω φ) h_sum_im_eq
  -- Simplify using linearity of ω over ℝ
  simpa [map_add, map_smul]
    using this

/-- Linearity of the complex pairing in the test-function argument. -/
lemma pairing_linear_combo
  (ω : FieldConfiguration) (f g : TestFunctionℂ) (t s : ℂ) :
  distributionPairingℂReal ω (t • f + s • g)
    = t * distributionPairingℂReal ω f + s * distributionPairingℂReal ω g := by
  classical
  apply Complex.ext
  · -- Real parts
    -- Expand both sides to re/imag pieces
    simp only [distributionPairingℂReal, add_re, mul_re]
    -- Goal is now: ω ((complexTestFunctionDecompose (t•f+s•g)).1)
    --              = (t * ((ω (..f..).1 + i ω (..f..).2)) + s * ((ω (..g..).1 + i ω (..g..).2))).re
    -- Use algebraic identity on the RHS
    have hre_rhs :
        (t * ((ω ((complexTestFunctionDecompose f).1) : ℂ) + I * (ω
           ((complexTestFunctionDecompose f).2) : ℂ))
            + s * ((ω ((complexTestFunctionDecompose g).1) : ℂ) + I * (ω
              ((complexTestFunctionDecompose g).2) : ℂ))).re
          = t.re * ω ((complexTestFunctionDecompose f).1)
              - t.im * ω ((complexTestFunctionDecompose f).2)
              + s.re * ω ((complexTestFunctionDecompose g).1)
              - s.im * ω ((complexTestFunctionDecompose g).2) := by
      simpa using re_of_complex_combination t s
        ((ω ((complexTestFunctionDecompose f).1) : ℂ) + I * (ω ((complexTestFunctionDecompose
            f).2) : ℂ))
        ((ω ((complexTestFunctionDecompose g).1) : ℂ) + I * (ω ((complexTestFunctionDecompose
            g).2) : ℂ))
    -- Use ω-linearity identity on the LHS
    have hre := ω_re_decompose_linear ω f g t s
    -- Finish by rewriting both sides to the same expression
    simpa [hre_rhs, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      using hre
  · -- Imag parts
    simp only [distributionPairingℂReal, add_im, mul_im]
    have him_rhs :
        (t * ((ω ((complexTestFunctionDecompose f).1) : ℂ) + I * (ω
           ((complexTestFunctionDecompose f).2) : ℂ))
            + s * ((ω ((complexTestFunctionDecompose g).1) : ℂ) + I * (ω
              ((complexTestFunctionDecompose g).2) : ℂ))).im
          = t.re * ω ((complexTestFunctionDecompose f).2)
              + t.im * ω ((complexTestFunctionDecompose f).1)
              + s.re * ω ((complexTestFunctionDecompose g).2)
              + s.im * ω ((complexTestFunctionDecompose g).1) := by
      simpa using im_of_complex_combination t s
        ((ω ((complexTestFunctionDecompose f).1) : ℂ) + I * (ω ((complexTestFunctionDecompose
            f).2) : ℂ))
        ((ω ((complexTestFunctionDecompose g).1) : ℂ) + I * (ω ((complexTestFunctionDecompose
            g).2) : ℂ))
    have him := ω_im_decompose_linear ω f g t s
    simpa [him_rhs, add_comm, add_left_comm, add_assoc]
      using him


/-! ## Helper lemmas for real→complex Schwartz embedding -/

/-- The norm of the ℝ-linear embedding ℝ → ℂ is exactly 1. -/
lemma Complex.norm_ofRealCLM : ‖Complex.ofRealCLM‖ = 1 :=
  ofRealCLM_norm

/-- Composing a continuous multilinear map (to ℝ) with the real→complex embedding
    preserves the operator norm, since the embedding is an isometry.
-/
lemma norm_compContinuousMultilinearMap_ofReal {n : ℕ} {E : Fin n → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (m : ContinuousMultilinearMap ℝ E ℝ) :
    ‖Complex.ofRealCLM.compContinuousMultilinearMap m‖ = ‖m‖ := by
  apply le_antisymm
  · calc ‖Complex.ofRealCLM.compContinuousMultilinearMap m‖
        ≤ ‖Complex.ofRealCLM‖ * ‖m‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ = 1 * ‖m‖ := by rw [Complex.norm_ofRealCLM]
      _ = ‖m‖ := one_mul _
  · have h_nonneg : (0 : ℝ) ≤ ‖Complex.ofRealCLM.compContinuousMultilinearMap m‖ := norm_nonneg _
    have h_bound : ∀ v, ‖m v‖ ≤ ‖Complex.ofRealCLM.compContinuousMultilinearMap m‖ * ∏ i, ‖v i‖ :=
      by
      intro v
      have h_eq : ‖m v‖ = ‖(Complex.ofRealCLM.compContinuousMultilinearMap m) v‖ := by
        simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
        exact (Complex.norm_real (m v)).symm
      rw [h_eq]
      exact (Complex.ofRealCLM.compContinuousMultilinearMap m).le_opNorm v
    exact ContinuousMultilinearMap.opNorm_le_bound h_nonneg h_bound

/-- The norm of the n-th iterated derivative of a Schwartz function composed with
    real→complex embedding equals the norm of the n-th iterated derivative of the
    original Schwartz function. This follows from the chain rule and the fact that
    the embedding is an isometry.
-/
lemma iteratedFDeriv_ofReal_norm_eq (f : TestFunction) (n : ℕ) (x : SpaceTime) :
    ‖iteratedFDeriv ℝ n (fun x ↦ (f x : ℂ)) x‖ = ‖iteratedFDeriv ℝ n f.toFun x‖ := by
  have h_comp : (fun x => (f x : ℂ)) = Complex.ofRealCLM ∘ f.toFun := rfl
  rw [h_comp]
  have hf_smooth := f.smooth'
  have hn_le : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hf_at : ContDiffAt ℝ (n : WithTop ℕ∞) f.toFun x := hf_smooth.contDiffAt.of_le hn_le
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left Complex.ofRealCLM hf_at (le_refl _)]
  exact norm_compContinuousMultilinearMap_ofReal (iteratedFDeriv ℝ n f.toFun x)

/-- Embed a real test function as a complex-valued test function by coercing values via ℝ → ℂ. -/
def toComplex (f : TestFunction) : TestFunctionℂ :=
  SchwartzMap.mk (fun x => (f x : ℂ)) (by
    -- ℝ → ℂ coercion is smooth
    exact ContDiff.comp Complex.ofRealCLM.contDiff f.smooth'
  ) (by
    -- Polynomial growth is preserved since ℝ → ℂ coercion preserves norms
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    use C
    intro x
    -- Use the fact that iteratedFDeriv commutes with continuous linear maps
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x ↦ (f x : ℂ)) x‖ ≤ C
    rw [iteratedFDeriv_ofReal_norm_eq]
    exact hC x
  )

@[simp] lemma toComplex_apply (f : TestFunction) (x : SpaceTime) :
  toComplex f x = (f x : ℂ) := by
  -- Follows from definition of toComplex
  rfl

@[simp] lemma complex_testfunction_decompose_toComplex_fst (f : TestFunction) :
  (complexTestFunctionDecompose (toComplex f)).1 = f := by
  ext x
  simp [complexTestFunctionDecompose, toComplex_apply]

@[simp] lemma complex_testfunction_decompose_toComplex_snd (f : TestFunction) :
  (complexTestFunctionDecompose (toComplex f)).2 = 0 := by
  ext x
  simp [complexTestFunctionDecompose, toComplex_apply]

@[simp] lemma toComplex_add (f g : TestFunction) :
  toComplex (f + g) = toComplex f + toComplex g := by
  ext x
  simp [toComplex_apply]

@[simp] lemma toComplex_smul (c : ℝ) (f : TestFunction) :
  toComplex (c • f) = (c : ℂ) • toComplex f := by
  ext x
  simp only [toComplex_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.ofReal_mul]

/-- The embedding of real Schwartz functions into complex Schwartz functions is a continuous
    ℝ-linear map. This follows from `SchwartzMap.mkCLM` since:
    1. The map is linear (toComplex_add, toComplex_smul)
    2. The composition with ofRealCLM is smooth
    3. Derivative norms are preserved (iteratedFDeriv_ofReal_norm_eq)
    so the Schwartz seminorm bounds are satisfied.
-/
noncomputable def toComplexCLM : TestFunction →L[ℝ] TestFunctionℂ :=
  SchwartzMap.mkCLM (𝕜 := ℝ) (𝕜' := ℝ) (G := ℂ) (σ := RingHom.id ℝ) (fun f x => (f x : ℂ))
    (fun f g x => by simp only [SchwartzMap.add_apply]; exact Complex.ofReal_add _ _)
    (fun c f x => by
      simp only [SchwartzMap.smul_apply, RingHom.id_apply]
      change (((c • f x : ℝ) : ℂ)) = c • ((f x : ℝ) : ℂ)
      rw [smul_eq_mul, Complex.ofReal_mul, ← Complex.real_smul])
    (fun f => ContDiff.comp Complex.ofRealCLM.contDiff f.smooth')
    (fun ⟨k, n⟩ => by
      use {(k, n)}, 1, zero_le_one
      intro f x
      simp only [Finset.sup_singleton, one_mul]
      change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x ↦ (f x : ℂ)) x‖ ≤ _
      rw [iteratedFDeriv_ofReal_norm_eq]
      exact SchwartzMap.le_seminorm ℝ k n f x)

@[simp] lemma toComplexCLM_apply (f : TestFunction) :
    toComplexCLM f = toComplex f := by
  ext x
  rfl

@[simp] lemma distributionPairingℂ_real_toComplex
  (ω : FieldConfiguration) (f : TestFunction) :
  distributionPairingℂReal ω (toComplex f) = distributionPairing ω f := by
  simp [distributionPairingℂReal, distributionPairing]

variable (dμ_config : ProbabilityMeasure FieldConfiguration)

@[simp] lemma GJGeneratingFunctionalℂ_toComplex
  (f : TestFunction) :
  GJGeneratingFunctionalℂ dμ_config (toComplex f) = GJGeneratingFunctional dμ_config f := by
  unfold GJGeneratingFunctionalℂ GJGeneratingFunctional
  simp [distributionPairingℂ_real_toComplex]

/-! ## Pointwise conjugation on complex Schwartz functions

For a complex-valued Schwartz function f : E → ℂ, we define the pointwise conjugate
conjSchwartz f := fun x ↦ conj (f x). This is again a Schwartz function because
conjugation is a continuous ℝ-linear map on ℂ.
-/

/-- Pointwise conjugation of a complex Schwartz function.
    (conjSchwartz f)(x) = conj(f(x))

    This is defined using the continuous ℝ-linear equivalence `Complex.conjCLE : ℂ ≃L[ℝ] ℂ`.
    Since conjugation is smooth and an isometry, it preserves all Schwartz seminorms.
-/
noncomputable def conjSchwartz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) : SchwartzMap E ℂ := {
  toFun := fun x => starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp (f.smooth ⊤)
  decay' := fun k n => by
    obtain ⟨C, hC⟩ := f.decay' k n
    use C
    intro x
    -- ‖x‖^k * ‖iteratedFDeriv ℝ n (conj ∘ f) x‖ ≤ C
    -- The key is that Complex.conjCLE is an isometry, so it preserves norms
    have h_deriv : iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f x)) x =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap (iteratedFDeriv ℝ n f x) := by
      have hf : ContDiffAt ℝ (⊤ : ℕ∞) f x := (f.smooth ⊤).contDiffAt
      have := ContinuousLinearMap.iteratedFDeriv_comp_left (x := x) (Complex.conjCLE : ℂ →L[ℝ] ℂ)
          hf (i := n) (by norm_cast; exact le_top)
      simp only [Function.comp_def] at this
      exact this
    rw [h_deriv]
    have h_norm : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap (iteratedFDeriv ℝ n f
      x)‖ ≤
        ‖iteratedFDeriv ℝ n f x‖ := by
      calc ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap (iteratedFDeriv ℝ n f x)‖
          ≤ ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ * ‖iteratedFDeriv ℝ n f x‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ = 1 * ‖iteratedFDeriv ℝ n f x‖ := by rw [Complex.conjCLE_norm]
        _ = ‖iteratedFDeriv ℝ n f x‖ := one_mul _
    calc ‖x‖ ^ k * ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).compContinuousMultilinearMap (iteratedFDeriv ℝ n
      f x)‖
        ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by
          apply mul_le_mul_of_nonneg_left h_norm (pow_nonneg (norm_nonneg _) _)
      _ ≤ C := hC x
}

@[simp] lemma conjSchwartz_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (x : E) :
    conjSchwartz f x = starRingEnd ℂ (f x) := rfl

/-- Conjugation is involutive: conj(conj(f)) = f -/
@[simp] lemma conjSchwartz_conjSchwartz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) : conjSchwartz (conjSchwartz f) = f := by
  ext x
  simp [conjSchwartz_apply]

/-- Key identity: For a real-valued distribution ω, conjugating the pairing equals
    pairing with the conjugated test function.

    conj(⟨ω, f⟩) = ⟨ω, conj(f)⟩

    This follows from:
    - ⟨ω, f⟩ = ⟨ω, f_re⟩ + i⟨ω, f_im⟩
    - conj(⟨ω, f⟩) = ⟨ω, f_re⟩ - i⟨ω, f_im⟩
    - ⟨ω, conj(f)⟩ = ⟨ω, conj(f)_re⟩ + i⟨ω, conj(f)_im⟩
    - conj(f)_re = f_re and conj(f)_im = -f_im
-/
lemma distributionPairingℂ_real_conj (ω : FieldConfiguration) (f : TestFunctionℂ) :
    starRingEnd ℂ (distributionPairingℂReal ω f) = distributionPairingℂReal ω (conjSchwartz f) :=
      by
  -- Expand distributionPairingℂReal in terms of real and imaginary parts
  simp only [distributionPairingℂReal]
  -- For the conjugate side, we need to show conj(f)_re = f_re and conj(f)_im = -f_im
  have h_conj_re : (complexTestFunctionDecompose (conjSchwartz f)).1 =
      (complexTestFunctionDecompose f).1 := by
    ext x
    simp only [complex_testfunction_decompose_fst_apply]
    change (starRingEnd ℂ (f x)).re = (f x).re
    exact Complex.conj_re (f x)
  have h_conj_im : (complexTestFunctionDecompose (conjSchwartz f)).2 =
      -(complexTestFunctionDecompose f).2 := by
    ext x
    simp only [complex_testfunction_decompose_snd_apply, SchwartzMap.neg_apply]
    change (starRingEnd ℂ (f x)).im = -(f x).im
    exact Complex.conj_im (f x)
  rw [h_conj_re, h_conj_im]
  simp only [map_neg, Complex.ofReal_neg]
  -- Now: conj(⟨ω, f_re⟩ + i⟨ω, f_im⟩) = ⟨ω, f_re⟩ - i⟨ω, f_im⟩
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re]
  · simp [Complex.add_im, Complex.mul_im]
