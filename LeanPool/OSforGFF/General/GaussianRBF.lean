/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import LeanPool.OSforGFF.General.PositiveDefinite
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import LeanPool.OSforGFF.General.HadamardExp

/-!
# Gaussian RBF Kernel is Positive Definite

Proves that the Gaussian radial basis function kernel `h ↦ exp(-‖h‖² / 2)` is a positive
definite function on any real inner product space. The proof uses three steps: (1) the inner
product kernel `⟨x, y⟩` is positive definite; (2) exponentiation preserves positive
definiteness via the Hadamard series in `HadamardExp.lean`; (3) the Gaussian kernel factors as
`exp(-‖x - y‖² / 2) = exp(-‖x‖² / 2) · exp(-‖y‖² / 2) · exp(⟨x, y⟩)`, reducing from
the RBF to the inner product kernel.
-/

open Complex BigOperators Real InnerProductSpace Matrix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition of a positive definite kernel K : α × α → ℂ. -/
def IsPositiveDefiniteKernel {α : Type*} (K : α → α → ℂ) : Prop :=
  ∀ (m : ℕ) (x : Fin m → α) (c : Fin m → ℂ),
    0 ≤ (∑ i : Fin m, ∑ j : Fin m, (star (c i)) * (c j) * K (x i) (x j)).re

/-- Step 2: The inner product kernel is positive definite. -/
lemma innerProduct_is_pd_kernel :
    IsPositiveDefiniteKernel (fun (x y : H) => (⟪x, y⟫_ℝ : ℂ)) := by
  -- Strategy:
  -- The sum ∑∑ c_i* c_j <x_i, x_j> expands to ||∑ a_i x_i||^2 + ||∑ b_i x_i||^2 ≥ 0
  -- where c_i = a_i + i b_i.
  intro m x c
  -- Decompose c into real and imaginary parts
  let a : Fin m → ℝ := fun i => (c i).re
  let b : Fin m → ℝ := fun i => (c i).im
  -- Define weighted sums of x's
  let v_a : H := ∑ i : Fin m, a i • x i
  let v_b : H := ∑ i : Fin m, b i • x i
  -- Key computation: Re(∑∑ cbarᵢcⱼ⟪xᵢ,xⱼ⟫) = ⟪v_a, v_a⟫ + ⟪v_b, v_b⟫ = ‖v_a‖² + ‖v_b‖²
  -- First, expand star(c_i) * c_j = (a_i - ib_i)(a_j + ib_j) = (a_i a_j + b_i b_j) + i(a_i b_j -
  -- b_i a_j)
  have expand_cc : ∀ i j, star (c i) * c j = (a i * a j + b i * b j : ℝ) + Complex.I * (a i * b j -
    b i * a j : ℝ) := by
    intro i j
    simp only [a, b, star_def]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                 Complex.ofReal_im, mul_zero, sub_zero, zero_mul, add_zero,
                 Complex.conj_re, Complex.conj_im]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                 Complex.ofReal_re, mul_zero, zero_add,
                 Complex.conj_re, Complex.conj_im]
      ring
  -- The product cbarᵢcⱼ⟪xᵢ,xⱼ⟫ has real part (aᵢaⱼ + bᵢbⱼ)⟪xᵢ,xⱼ⟫
  have re_prod : ∀ i j, (star (c i) * c j * (⟪x i,
    x j⟫_ℝ : ℂ)).re = (a i * a j + b i * b j) * ⟪x i, x j⟫_ℝ := by
    intro i j
    rw [expand_cc]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
               Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
    ring
  -- Sum over i,j: Re(∑∑) = ∑∑ (aᵢaⱼ + bᵢbⱼ)⟪xᵢ,xⱼ⟫
  have sum_re : (∑ i : Fin m, ∑ j : Fin m, star (c i) * c j * (⟪x i, x j⟫_ℝ : ℂ)).re =
                ∑ i : Fin m, ∑ j : Fin m, (a i * a j + b i * b j) * ⟪x i, x j⟫_ℝ := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro j _
    exact re_prod i j
  rw [sum_re]
  -- Split into two sums
  have split_sum : ∑ i : Fin m, ∑ j : Fin m, (a i * a j + b i * b j) * ⟪x i, x j⟫_ℝ =
                   (∑ i : Fin m, ∑ j : Fin m, a i * a j * ⟪x i, x j⟫_ℝ) +
                   (∑ i : Fin m, ∑ j : Fin m, b i * b j * ⟪x i, x j⟫_ℝ) := by
    simp only [add_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
  rw [split_sum]
  -- Each sum equals ⟪v_a, v_a⟫ or ⟪v_b, v_b⟫ = ‖v‖²
  have sum_w_eq (w : Fin m → ℝ) :
      ∑ i : Fin m, ∑ j : Fin m, w i * w j * ⟪x i, x j⟫_ℝ =
        ⟪(∑ i : Fin m, w i • x i), (∑ i : Fin m, w i • x i)⟫_ℝ := by
    conv_rhs => rw [sum_inner]
    apply Finset.sum_congr rfl; intro i _
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [real_inner_smul_right]
    ring
  have sum_a_eq : ∑ i : Fin m, ∑ j : Fin m, a i * a j * ⟪x i, x j⟫_ℝ = ⟪v_a, v_a⟫_ℝ := by
    simpa [v_a] using sum_w_eq a
  have sum_b_eq : ∑ i : Fin m, ∑ j : Fin m, b i * b j * ⟪x i, x j⟫_ℝ = ⟪v_b, v_b⟫_ℝ := by
    simpa [v_b] using sum_w_eq b
  rw [sum_a_eq, sum_b_eq]
  -- Both inner products are nonneg (‖·‖² ≥ 0)
  have h1 : 0 ≤ ⟪v_a, v_a⟫_ℝ := real_inner_self_nonneg
  have h2 : 0 ≤ ⟪v_b, v_b⟫_ℝ := real_inner_self_nonneg
  exact add_nonneg h1 h2

/-- Helper: For a real-valued PD kernel, the kernel matrix is PSD.
    Forward direction of the bridge between complex kernels and real matrices.
-/
lemma real_valued_PD_kernel_gives_PSD_matrix {α : Type*} (K : α → α → ℂ)
    (h_real : ∀ x y, (K x y).im = 0)
    (h_symm : ∀ x y, K x y = K y x) -- Symmetric (automatic for inner product kernels)
    (hK : IsPositiveDefiniteKernel K) (m : ℕ) (x : Fin m → α) :
    (Matrix.of fun i j => (K (x i) (x j)).re).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · -- Hermitian (symmetric for real matrices)
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    -- Use the symmetry assumption
    rw [h_symm (x j) (x i)]
  · -- Nonneg quadratic form for real vectors
    intro v
    have h := hK m x (fun i => (v i : ℂ))
    -- Convert the kernel sum to the dotProduct form
    have h_eq : (star v) ⬝ᵥ (Matrix.of fun i j => (K (x i) (x j)).re).mulVec v =
                (∑ i : Fin m, ∑ j : Fin m, star ((v i : ℂ)) * (v j : ℂ) * K (x i) (x j)).re := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      simp only [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.star_apply, star_trivial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have him := h_real (x i) (x j)
      simp only [star_def, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
                 Complex.ofReal_im, mul_zero, sub_zero, him]
      ring
    rwa [h_eq]

/-- Step 3b: Exponential of a symmetric real-valued PD kernel is PD.
    Uses the Hadamard series machinery from HadamardExp.lean (same as OS3 proof).
-/
lemma exp_is_pd_kernel {α : Type*} (K : α → α → ℂ) (hK : IsPositiveDefiniteKernel K)
    (h_real : ∀ x y, (K x y).im = 0)
    (h_symm : ∀ x y, K x y = K y x) :
    IsPositiveDefiniteKernel (fun x y => cexp (K x y)) := by
  -- Strategy: For any finite set of points, the kernel matrix is PSD.
  -- Use OSforGFF.posSemidef_entrywiseExp_hadamardSeries_of_posSemidef to show exp preserves PSD.
  intro m x c
  -- The kernel matrix M_{ij} = K(x_i, x_j) is PSD (real part)
  let M : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => (K (x i) (x j)).re
  -- M is PSD because K is a symmetric real-valued PD kernel
  have hM_psd : M.PosSemidef := real_valued_PD_kernel_gives_PSD_matrix K h_real h_symm hK m x
  -- Apply the Hadamard series result: entrywiseExp M is PSD
  have hExpM_psd : (OSforGFF.entrywiseExp M).PosSemidef := by
    have h := OSforGFF.posSemidef_entrywiseExp_hadamardSeries_of_posSemidef M hM_psd
    simpa [OSforGFF.entrywiseExp_eq_hadamardSeries] using h
  -- Now translate back to the complex kernel statement
  -- exp(K(x,y)) = exp(Re(K(x,y))) since K is real-valued
  have h_exp_eq : ∀ i j, cexp (K (x i) (x j)) = (Real.exp ((K (x i) (x j)).re) : ℂ) := by
    intro i j
    have him : (K (x i) (x j)).im = 0 := h_real (x i) (x j)
    have hK_real_eq : K (x i) (x j) = ((K (x i) (x j)).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hK_real_eq, ← Complex.ofReal_exp]
    simp only [Complex.ofReal_re]
  -- The sum ∑∑ cbarᵢcⱼ exp(K_{ij}) has nonneg real part
  -- Decompose c = a + ib and use that exp(M) is PSD
  let a : Fin m → ℝ := fun i => (c i).re
  let b : Fin m → ℝ := fun i => (c i).im
  -- For PSD real matrix N and real vectors a, b: aᵀNa + bᵀNb ≥ 0
  let N : Matrix (Fin m) (Fin m) ℝ := OSforGFF.entrywiseExp M
  have hN_psd : N.PosSemidef := hExpM_psd
  -- Compute: Re(∑∑ cbarᵢcⱼ exp(K_{ij})) = aᵀNa + bᵀNb
  have h_sum_eq : (∑ i : Fin m, ∑ j : Fin m, star (c i) * c j * cexp (K (x i) (x j))).re =
                  (a ⬝ᵥ (N.mulVec a)) + (b ⬝ᵥ (N.mulVec b)) := by
    -- Similar to innerProduct_is_pd_kernel proof
    simp only [Complex.re_sum]
    have h_entry : ∀ i j, (star (c i) * c j * cexp (K (x i) (x j))).re =
                         (a i * a j + b i * b j) * N i j := by
      intro i j
      rw [h_exp_eq]
      simp only [a, b, star_def, N, OSforGFF.entrywiseExp, M, Matrix.of_apply]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im,
                 mul_zero, sub_zero]
      ring
    simp_rw [h_entry]
    -- Split and rearrange to matrix form
    simp only [add_mul, Finset.sum_add_distrib]
    -- Rewrite each quadratic sum as a dotProduct.
    have sum_w_matrix (w : Fin m → ℝ) :
        ∑ i : Fin m, ∑ j : Fin m, w i * w j * N i j = w ⬝ᵥ (N.mulVec w) := by
      simp only [dotProduct, Matrix.mulVec]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp [sum_w_matrix a, sum_w_matrix b]
  rw [h_sum_eq]
  exact add_nonneg (hN_psd.dotProduct_mulVec_nonneg a) (hN_psd.dotProduct_mulVec_nonneg b)



/-- The Gaussian RBF kernel is positive definite on any inner product space. -/
theorem gaussian_rbf_pd_innerProduct_proof :
    GFF4D.IsPositiveDefinite (fun h : H => cexp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) := by
  -- Strategy:
  -- 1. Use the polarization identity: ‖x - y‖² = ‖x‖² + ‖y‖² - 2⟨x, y⟩
  -- 2. Factor the Gaussian kernel:
  --    exp(-½‖x-y‖²) = exp(-½‖x‖²) · exp(-½‖y‖²) · exp(⟨x,y⟩)
  -- 3. Define d_i = c_i * exp(-½‖x_i‖²). Then:
  --    ∑∑ cbarᵢcⱼ exp(-½‖xᵢ-xⱼ‖²) = ∑∑ dbarᵢdⱼ exp(⟨xᵢ,xⱼ⟩) ≥ 0
  -- 4. The RHS is ≥ 0 by exp_is_pd_kernel + innerProduct_is_pd_kernel.
  intro m x c
  -- Define the scaled coefficients
  let d : Fin m → ℂ := fun i => c i * cexp (-(1/2 : ℂ) * (‖x i‖^2 : ℝ))
  -- Polarization identity: ‖x - y‖² = ‖x‖² + ‖y‖² - 2⟨x,y⟩
  have polar : ∀ i j, (‖x i - x j‖^2 : ℝ) = ‖x i‖^2 + ‖x j‖^2 - 2 * ⟪x i, x j⟫_ℝ := by
    intro i j
    rw [norm_sub_pow_two_real]
    ring
  -- Factor the exponential using polar identity
  have factor : ∀ i j, cexp (-(1/2 : ℂ) * (‖x i - x j‖^2 : ℝ)) =
      cexp (-(1/2 : ℂ) * (‖x i‖^2 : ℝ)) * cexp (-(1/2 : ℂ) * (‖x j‖^2 : ℝ)) * cexp (⟪x i,
        x j⟫_ℝ : ℂ) := by
    intro i j
    rw [polar]
    simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- The key fact: exp(-½‖x‖²) is real, so star(exp) = exp
  have exp_real : ∀ i, (cexp (-(1/2 : ℂ) * (‖x i‖^2 : ℝ))).im = 0 := by
    intro i
    have h : (-(1/2 : ℂ) * (‖x i‖^2 : ℝ)).im = 0 := by
      simp only [Complex.mul_im, Complex.neg_im, Complex.ofReal_im, mul_zero,
                 Complex.neg_re, Complex.div_ofNat_im, Complex.one_im]
      ring
    rw [Complex.exp_im, h, Real.sin_zero, mul_zero]
  have star_exp : ∀ i, star (cexp (-(1/2 : ℂ) * (‖x i‖^2 : ℝ))) = cexp (-(1/2 : ℂ) * (‖x i‖^2 : ℝ))
    := by
    intro i
    rw [star_def]
    exact Complex.conj_eq_iff_im.mpr (exp_real i)
  have star_d : ∀ i, star (d i) = star (c i) * cexp (-(1/2 : ℂ) * (‖x i‖^2 : ℝ)) := by
    intro i
    simp only [d, StarMul.star_mul, star_exp]
    ring
  -- Rewrite the sum using the factorization
  have h_sum : ∑ i : Fin m, ∑ j : Fin m, star (c i) * c j * cexp (-(1/2 : ℂ) * (‖x i - x j‖^2 : ℝ))
    =
               ∑ i : Fin m, ∑ j : Fin m, star (d i) * d j * cexp (⟪x i, x j⟫_ℝ : ℂ) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [factor, star_d]
    simp only [d]
    ring
  -- The goal uses star which equals starRingEnd for Complex
  change 0 ≤ (∑ i : Fin m, ∑ j : Fin m,
      (starRingEnd ℂ) (c i) * c j * (fun h => cexp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) (x i - x j)).re
  -- Convert star to starRingEnd in h_sum
  have h_sum' : ∑ i : Fin m, ∑ j : Fin m, (starRingEnd ℂ) (c i) * c j * cexp (-(1/2 : ℂ) * (‖x i -
    x j‖^2 : ℝ)) =
               ∑ i : Fin m, ∑ j : Fin m, (starRingEnd ℂ) (d i) * d j * cexp (⟪x i, x j⟫_ℝ : ℂ) := by
    simp only [star_def] at h_sum
    convert h_sum using 2
  rw [h_sum']
  -- Now apply that exp(⟨·,·⟩) is a PD kernel
  have h_inner_pd : IsPositiveDefiniteKernel (fun (u v : H) => (⟪u,
    v⟫_ℝ : ℂ)) := innerProduct_is_pd_kernel
  have h_exp_inner_pd : IsPositiveDefiniteKernel (fun (u v : H) => cexp (⟪u, v⟫_ℝ : ℂ)) := by
    apply exp_is_pd_kernel _ h_inner_pd
    · exact fun _ _ => ofReal_im ⟪_, _⟫_ℝ
    · intro u v
      simp only [real_inner_comm]
  exact h_exp_inner_pd m x d
