/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.PositiveTimeTestFunction
import LeanPool.OSforGFF.Spacetime.DiscreteSymmetry
import LeanPool.OSforGFF.OS.Axioms
import LeanPool.OSforGFF.Measure.Construct
import LeanPool.OSforGFF.General.HadamardExp
import LeanPool.OSforGFF.Covariance.RealForm
import LeanPool.OSforGFF.OS.OS3CovarianceRP
import LeanPool.OSforGFF.Measure.IsGaussian

/-!
# OS3 — Reflection Positivity for the GFF

Lifts covariance reflection positivity to the full generating functional via
the Schur product theorem.

**Real version** (complete): For positive-time real fⱼ and real coefficients cⱼ:

  ∑ᵢⱼ cᵢcⱼ Z[fᵢ − Θfⱼ] = ∑ᵢⱼ cᵢ'cⱼ' exp(Rᵢⱼ) ≥ 0

where Rᵢⱼ = ⟨Θfᵢ, Cfⱼ⟩ is PSD by covariance reflection positivity,
cᵢ' = cᵢ exp(−½⟨fᵢ,Cfᵢ⟩), and exp(Rᵢⱼ) is PSD by the Schur product
theorem (entrywise exponential of a PSD matrix is PSD).

**Complex version**: For positive-time complex fⱼ and complex coefficients cⱼ:

  ∑ᵢⱼ cbarᵢcⱼ Z_ℂ[fᵢ − star fⱼ] ≥ 0

where `star f = conj ∘ f ∘ Θ`.  The factorisation gives `Z_ℂ[fᵢ − star fⱼ] =
conj(Aᵢ)·Aⱼ·exp(Rᵢⱼ)` with Hermitian PSD R, requiring the complex entrywise
exponential PSD theorem.

## Main results

- `gaussianFreeField_OS3_real`: `os3ReflectionPositivityReal (muGFF m)`
- `gaussianFreeField_OS3`: `os3ReflectionPositivity (muGFF m)`  (complex)
-/

open MeasureTheory Complex Matrix
open scoped Real InnerProductSpace BigOperators

noncomputable section

namespace QFT

/-- Reflection positivity for a single positive-time test function in the real setting. -/
private lemma freeCovarianceFormR_reflection_nonneg
    (m : ℝ) [Fact (0 < m)] (f : PositiveTimeTestFunction) :
    0 ≤ freeCovarianceFormR m (QFT.compTimeReflectionReal f.val) f.val := by
  classical
  have hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f.val x = 0 := fun x hx => by
    apply f.zero_on_nonpositive
    unfold getTimeComponent
    exact hx
  have h := freeCovariance_reflection_positive_real (m := m) (f := f.val) hf_supp
  simpa [freeCovarianceFormR] using h

/-- Entrywise exponential preserves PSD on real symmetric PSD matrices (finite index).
    Bridge lemma to be discharged using HadamardExp (Hadamard series) machinery.
-/
private lemma entrywiseExp_posSemidef_of_posSemidef
  {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
  (hR : R.PosSemidef) : Matrix.PosSemidef (fun i j => Real.exp (R i j)) := by
  classical
  -- PSD for the Hadamard-series exponential
  have hS : (OSforGFF.entrywiseExpHadamardSeries (ι := Fin n) R).PosSemidef :=
    OSforGFF.posSemidef_entrywiseExp_hadamardSeries_of_posSemidef (ι := Fin n) R hR
  -- Convert to PSD for the entrywise exponential
  have hExp : (OSforGFF.entrywiseExp (ι := Fin n) R).PosSemidef := by
    simpa [OSforGFF.entrywiseExp_eq_hadamardSeries (ι := Fin n) R] using hS
  -- Unfold the definition of entrywiseExp
  change (OSforGFF.entrywiseExp (ι := Fin n) R).PosSemidef
  exact hExp

-- We recall the standard Gram-matrix positivity result from Mathlib. -/
attribute [local simp] inner_sub_right inner_sub_left


/-- Reflection matrix built from the real covariance is positive semidefinite.
    This is the real analogue of covariance reflection positivity.
-/
lemma freeCovarianceFormR_reflection_matrix_posSemidef
    (m : ℝ) [Fact (0 < m)]
    {n : ℕ} (f : Fin n → PositiveTimeTestFunction) :
    Matrix.PosSemidef (fun i j : Fin n =>
      freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val) := by
  -- The matrix R_{ij} = C(θf_i, f_j) is symmetric by freeCovarianceFormR_reflection_cross
  -- We'll prove positive semidefiniteness directly by showing the quadratic form is nonnegative
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val
  -- First prove the matrix is Hermitian (symmetric since entries are real)
  have h_herm : M.IsHermitian := by
    ext i j
    simp only [M, conjTranspose_apply]
    -- For real entries, star is the identity, so we need to show symmetry
    simp only [star_id_of_comm]
    -- Use the symmetry from freeCovarianceFormR_reflection_cross
    exact (freeCovarianceFormR_reflection_cross (m := m) (f := (f i).val) (g := (f j).val)).symm
  -- Use the constructor for regular functions
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h_herm
  -- Second prove the quadratic form is nonnegative for all c : Fin n → ℝ
  intro c
  -- The goal is: 0 ≤ star c ⬝ᵥ M *ᵥ c
  classical
  -- For real coefficients, star c = c
  have h_star : star c = c := by ext k; simp
  -- Convert the matrix-vector form to double sum
  have h_expand : star c ⬝ᵥ M *ᵥ c =
      ∑ i, ∑ j, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val * c j
        := by
    simp only [dotProduct, Matrix.mulVec, M]
    congr 1
    ext k
    simp only [h_star]
    rw [Finset.mul_sum]
    ring_nf
  -- Step 1: Use bilinearity to collect the sums
  have h_step1 : ∑ i, ∑ j, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f
    j).val * c j =
      freeCovarianceFormR m (∑ i, c i • QFT.compTimeReflectionReal (f i).val) (∑ j,
        c j • (f j).val) := by
      -- Use induction on finite sums combined with the bilinearity axioms
      -- We'll work with the multiplication form and convert to smul at the end
      -- Apply linearity in first argument: ∑ᵢ cᵢ • θfᵢ
      have h_left : ∑ i, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (∑ j,
        c j • (f j).val) =
        freeCovarianceFormR m (∑ i, c i • QFT.compTimeReflectionReal (f i).val) (∑ j,
          c j • (f j).val) :=
          freeCovarianceFormR_left_linear_any_right m f c Finset.univ _
      have h_right : ∀ i, ∑ j, freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f
        j).val * c j =
        freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (∑ j, c j • (f j).val) := by
        intro i
        -- Use induction on the right argument with our right linearity lemmas
        induction (Finset.univ : Finset (Fin n)) using Finset.induction with
        | empty =>
          simp only [Finset.sum_empty]
          -- freeCovarianceFormR m u 0 = 0 (follows from linearity)
          rw [← freeCovarianceFormR_zero_right (m := m)]
        | insert j t hj ih_right =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj]
          -- Apply right linearity: freeCovarianceFormR_add_right and freeCovarianceFormR_smul_right
          -- First convert multiplications to scalar multiplications
          -- freeCovarianceFormR m u (f j) * c j = freeCovarianceFormR m u (c j • f j)
          have h_smul_first : freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f
            j).val * c j =
            freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (c j • (f j).val) := by
            rw [mul_comm]
            rw [freeCovarianceFormR_smul_right]
          rw [h_smul_first, ih_right]
          -- Now apply freeCovarianceFormR_add_right
          rw [← freeCovarianceFormR_add_right]
      -- Combine the results by showing both sides equal the bilinear form
      -- Left side: ∑ i, ∑ j, c i * freeCovarianceFormR m (θf_i) (f_j) * c j
      -- We need: ∑ i, c i * freeCovarianceFormR m (θf_i) (∑ j, c j • f_j)
      have h_rewrite : ∑ i, ∑ j, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val)
        (f j).val * c j =
        ∑ i, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (∑ j,
          c j • (f j).val) := by
        congr 1
        ext i
        -- The goal after ext is to show:
        -- ∑ j, c i * freeCovarianceFormR m (θf_i) (f_j) * c j = c i * freeCovarianceFormR m (θf_i)
        -- (∑ j, c j • f_j)
        -- This follows by factoring out c i and applying h_right i
        -- Goal: ∑ j, c i * freeCovarianceFormR m (θf_i) (f_j) * c j = c i * freeCovarianceFormR m
        -- (θf_i) (∑ j, c j • f_j)
        -- We need to rewrite: ∑ j, c i * freeCovarianceFormR m (θf_i) (f_j) * c j
        -- as: c i * ∑ j, freeCovarianceFormR m (θf_i) (f_j) * c j
        -- Then apply h_right i
        -- The key insight: we can rewrite each term using mul_assoc and then factor out c i
        conv_lhs =>
          rw [show ∑ j,
            c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f j).val * c j =
                  ∑ j, c i * (freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) (f
                    j).val * c j) by
                simp only [mul_assoc]]
        -- Now factor out c i
        rw [← Finset.mul_sum]
        -- Apply h_right i to both sides (after factoring out c i, we need the congr_arg version)
        rw [h_right i]
      rw [h_rewrite, h_left]
  -- Step 2: Use linearity of time reflection
  have h_step2 : ∑ i, c i • QFT.compTimeReflectionReal (f i).val =
    QFT.compTimeReflectionReal (∑ i, c i • (f i).val) := by
    exact (compTimeReflectionReal_linear_combination (fun i => (f i).val) c).symm
  -- Step 3: The sum of positive-time functions is positive-time
  obtain ⟨g, hg⟩ := PositiveTimeTestFunction.sum_smul_mem f c
  -- Step 4: Combine and apply reflection positivity
  rw [h_expand, h_step1, h_step2]
  -- Now we have: freeCovarianceFormR m (compTimeReflectionReal (∑ i, c i • (f i).val)) (∑ j, c j •
  -- (f j).val)
  -- Since g.val = ∑ i, c i • (f i).val, we get: freeCovarianceFormR m (compTimeReflectionReal
  -- g.val) g.val
  rw [← hg]
  exact freeCovarianceFormR_reflection_nonneg m g

/-- Quadratic expansion identity for reflected arguments. -/
lemma freeCovarianceFormR_reflection_expansion
    (m : ℝ) [Fact (0 < m)] (f g : TestFunction) :
    freeCovarianceFormR m
        (f - QFT.compTimeReflectionReal g)
        (f - QFT.compTimeReflectionReal g)
      = freeCovarianceFormR m f f
        + freeCovarianceFormR m g g
        - 2 * freeCovarianceFormR m (QFT.compTimeReflectionReal f) g := by
  classical
  set θf := QFT.compTimeReflectionReal f
  set θg := QFT.compTimeReflectionReal g
  set Cf : ℝ := freeCovarianceFormR m f f
  set Cg : ℝ := freeCovarianceFormR m g g
  set Cfg : ℝ := freeCovarianceFormR m θf g
  have h_neg_left : ∀ u v : TestFunction,
      freeCovarianceFormR m (-u) v = -freeCovarianceFormR m u v := by
    intro u v
    simpa using
      (freeCovarianceFormR_smul_left (m := m) (c := (-1 : ℝ)) (f := u) (g := v))
  have h_neg_right : ∀ u v : TestFunction,
      freeCovarianceFormR m u (-v) = -freeCovarianceFormR m u v := by
    intro u v
    calc
      freeCovarianceFormR m u (-v)
          = freeCovarianceFormR m (-v) u := by
              exact freeCovarianceFormR_symm m u (-v)
      _ = -freeCovarianceFormR m v u := h_neg_left v u
      _ = -freeCovarianceFormR m u v := by
            simp [freeCovarianceFormR_symm]
  have h_cross : freeCovarianceFormR m θg f = Cfg := by
    simpa [θf, θg, Cfg]
      using
        (freeCovarianceFormR_reflection_cross (m := m) (f := f) (g := g)).symm
  have h_invariant : freeCovarianceFormR m θg θg = Cg := by
    simpa [θg, Cg]
      using freeCovarianceFormR_reflection_invariant (m := m) (f := g) (g := g)
  have h_term₁ :
      freeCovarianceFormR m f (f - θg) = Cf - Cfg := by
    have h_add :=
      freeCovarianceFormR_add_left (m := m)
        (f₁ := f) (f₂ := -θg) (g := f)
    have h_add' :
        freeCovarianceFormR m (f - θg) f
          = freeCovarianceFormR m f f
              + freeCovarianceFormR m (-θg) f := by
      simpa [sub_eq_add_neg, θg] using h_add
    calc
      freeCovarianceFormR m f (f - θg)
          = freeCovarianceFormR m (f - θg) f := by
              exact freeCovarianceFormR_symm m f (f - θg)
      _ = freeCovarianceFormR m f f
            + freeCovarianceFormR m (-θg) f := h_add'
      _ = Cf + (-freeCovarianceFormR m θg f) := by
            simp [θg, Cf, h_neg_left]
      _ = Cf - Cfg := by
            simp [sub_eq_add_neg, h_cross]
  have h_term₂ :
      freeCovarianceFormR m (-θg) (f - θg) = -Cfg + Cg := by
    have h_add :=
      freeCovarianceFormR_add_left (m := m)
        (f₁ := f) (f₂ := -θg) (g := -θg)
    have h_add' :
        freeCovarianceFormR m (f - θg) (-θg)
          = freeCovarianceFormR m f (-θg)
              + freeCovarianceFormR m (-θg) (-θg) := by
      simpa [sub_eq_add_neg, θg] using h_add
    have h_negneg :
        freeCovarianceFormR m (-θg) (-θg)
          = freeCovarianceFormR m θg θg := by
      have h₁ := h_neg_left θg (-θg)
      have h₂ := h_neg_right θg θg
      have h₁' : freeCovarianceFormR m (-θg) (-θg) = -freeCovarianceFormR m θg (-θg) := by
        simpa [θg] using h₁
      have h₂' : freeCovarianceFormR m θg (-θg) = -freeCovarianceFormR m θg θg := by
        simpa [θg] using h₂
      calc
        freeCovarianceFormR m (-θg) (-θg)
            = -freeCovarianceFormR m θg (-θg) := h₁'
        _ = -(-freeCovarianceFormR m θg θg) := by
              exact neg_inj.mpr h₂'
        _ = freeCovarianceFormR m θg θg := by simp
    calc
      freeCovarianceFormR m (-θg) (f - θg)
          = freeCovarianceFormR m (f - θg) (-θg) := by
              exact freeCovarianceFormR_symm m (-θg) (f - θg)
      _ = freeCovarianceFormR m f (-θg)
            + freeCovarianceFormR m (-θg) (-θg) := h_add'
      _ = -freeCovarianceFormR m f θg
            + freeCovarianceFormR m (-θg) (-θg) := by
              simp [θg, h_neg_right]
      _ = -freeCovarianceFormR m f θg
            + freeCovarianceFormR m θg θg := by
              simp [h_negneg]
      _ = -Cfg + Cg := by
          have h_sym : freeCovarianceFormR m f θg = freeCovarianceFormR m θg f := by
            simpa using freeCovarianceFormR_symm m f θg
          simp [h_sym, h_cross, h_invariant]
  have h_total :=
      freeCovarianceFormR_add_left (m := m)
        (f₁ := f) (f₂ := -θg) (g := f - θg)
  have h_total' :
      freeCovarianceFormR m (f - θg) (f - θg)
        = freeCovarianceFormR m f (f - θg)
            + freeCovarianceFormR m (-θg) (f - θg) := by
    simpa [sub_eq_add_neg, θg] using h_total
  calc
    freeCovarianceFormR m (f - θg) (f - θg)
        = freeCovarianceFormR m f (f - θg)
            + freeCovarianceFormR m (-θg) (f - θg) := h_total'
    _ = (Cf - Cfg) + (-Cfg + Cg) := by
          simp [h_term₁, h_term₂]
    _ = Cf + Cg - 2 * Cfg := by ring

/-- Evaluate the real generating functional of the free field on a real test function. -/
lemma gaussianFreeField_real_generating_re
    (m : ℝ) [Fact (0 < m)] (h : TestFunction) :
    (GJGeneratingFunctional (gaussianFreeFieldFree m) h).re
      = Real.exp (-(1 / 2 : ℝ) * freeCovarianceFormR m h h) := by
  classical
  set r : ℝ := -(1 / 2 : ℝ) * freeCovarianceFormR m h h
  have h_char := congrArg Complex.re (gff_real_characteristic (m := m) h)
  have h_arg :
      (-(1 / 2 : ℂ) * (freeCovarianceFormR m h h : ℝ))
        = Complex.ofReal r := by
    simp [r, Complex.ofReal_mul]
  have h_exp_rewrite :
      (Complex.exp (-(1 / 2 : ℂ) * (freeCovarianceFormR m h h : ℝ))).re
        = Real.exp r := by
    simpa [h_arg, r] using (Complex.exp_ofReal_re r)
  have h_char' := h_char
  rw [h_exp_rewrite] at h_char'
  simpa [r] using h_char'

/-- Factorisation of OS3 matrix entries in the purely real setting. -/
lemma gaussianFreeField_real_entry_factor
    (m : ℝ) [Fact (0 < m)]
    {f g : PositiveTimeTestFunction} :
    (GJGeneratingFunctional (gaussianFreeFieldFree m)
        (f.val - QFT.compTimeReflectionReal g.val)).re
      = (GJGeneratingFunctional (gaussianFreeFieldFree m) (f.val)).re
        * (GJGeneratingFunctional (gaussianFreeFieldFree m) (g.val)).re
        * Real.exp
            (freeCovarianceFormR m
              (QFT.compTimeReflectionReal (f.val)) (g.val)) := by
  classical
  -- shorthand for the covariance terms appearing in the exponent
  set Cf : ℝ := freeCovarianceFormR m (f.val) (f.val)
  set Cg : ℝ := freeCovarianceFormR m (g.val) (g.val)
  set Cfg : ℝ :=
    freeCovarianceFormR m (QFT.compTimeReflectionReal (f.val)) (g.val)
  -- Evaluate the generating functionals via the real characteristic formula
  have hf := gaussianFreeField_real_generating_re (m := m) (h := f.val)
  have hg := gaussianFreeField_real_generating_re (m := m) (h := g.val)
  have hfg :=
    gaussianFreeField_real_generating_re (m := m)
      (h := f.val - QFT.compTimeReflectionReal g.val)
  -- Use the reflection expansion to rewrite the covariance of f - Θg
  have h_expansion := freeCovarianceFormR_reflection_expansion (m := m)
    (f := f.val) (g := g.val)
  -- Translate the equalities coming from the generating functionals into exponentials
  have hf' :
      (GJGeneratingFunctional (gaussianFreeFieldFree m) (f.val)).re
        = Real.exp (-(1 / 2 : ℝ) * Cf) := by simpa [Cf] using hf
  have hg' :
      (GJGeneratingFunctional (gaussianFreeFieldFree m) (g.val)).re
        = Real.exp (-(1 / 2 : ℝ) * Cg) := by simpa [Cg] using hg
  have hfg' :
      (GJGeneratingFunctional (gaussianFreeFieldFree m)
          (f.val - QFT.compTimeReflectionReal g.val)).re
        =
        Real.exp (-(1 / 2 : ℝ)
          * freeCovarianceFormR m
              (f.val - QFT.compTimeReflectionReal g.val)
              (f.val - QFT.compTimeReflectionReal g.val)) := by
    simpa using hfg
  -- Rewrite the exponent using the quadratic expansion lemma
  have h_covariance_rewrite :
      freeCovarianceFormR m
          (f.val - QFT.compTimeReflectionReal g.val)
          (f.val - QFT.compTimeReflectionReal g.val)
        = Cf + Cg - 2 * Cfg := by
    simpa [Cf, Cg, Cfg] using h_expansion
  -- Combine all exponentials and simplify
  set a : ℝ := -(1 / 2 : ℝ) * Cf
  set b : ℝ := -(1 / 2 : ℝ) * Cg
  set A : ℝ := a + b
  have hA : A = -(1 / 2 : ℝ) * Cf + -(1 / 2 : ℝ) * Cg := by
    simp [A, a, b]
  have h_factor :
      -(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg) = A + Cfg := by
    have h_ring : -(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg)
        = -(1 / 2 : ℝ) * Cf + -(1 / 2 : ℝ) * Cg + Cfg := by
          ring
    simpa [A, a, b, add_comm, add_left_comm, add_assoc, hA] using h_ring
  calc
    (GJGeneratingFunctional (gaussianFreeFieldFree m)
        (f.val - QFT.compTimeReflectionReal g.val)).re
        = Real.exp (-(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg)) := by
              simpa [h_covariance_rewrite] using hfg'
  _ =
    Real.exp (-(1 / 2 : ℝ) * Cf)
    * Real.exp (-(1 / 2 : ℝ) * Cg)
    * Real.exp (Cfg) := by
        -- Exponential of sums factorises; use `Real.exp_add` twice
        calc
        Real.exp (-(1 / 2 : ℝ) * (Cf + Cg - 2 * Cfg))
          = Real.exp (A + Cfg) := by
              exact Real.exp_eq_exp.mpr h_factor
        _ = Real.exp A * Real.exp Cfg := by
              simp [Real.exp_add]
        _ =
          (Real.exp a * Real.exp b)
            * Real.exp Cfg := by
              simp [A, a, b, Real.exp_add]
    _ =
        (GJGeneratingFunctional (gaussianFreeFieldFree m) (f.val)).re
        * (GJGeneratingFunctional (gaussianFreeFieldFree m) (g.val)).re
        * Real.exp Cfg := by
        simp [hf', hg', Cfg, a, b, one_div, mul_assoc]

section GaussianRealReflectionPositivity

variable (m : ℝ) [Fact (0 < m)]

/-- Matrix formulation of the real OS3 inequality for the Gaussian free field. -/
lemma gaussianFreeField_OS3_matrix_real
    {n : ℕ} (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℝ) :
    0 ≤ (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional (gaussianFreeFieldFree m)
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re) := by
  classical
  -- Build the auxiliary data appearing in the factorisation argument.
  let Z : Fin n → ℝ := fun i =>
    (GJGeneratingFunctional (gaussianFreeFieldFree m) (f i).val).re
  let R : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    freeCovarianceFormR m
      (QFT.compTimeReflectionReal (f i).val) (f j).val
  let E : Matrix (Fin n) (Fin n) ℝ := fun i j => Real.exp (R i j)
  let y : Fin n → ℝ := fun i => c i * Z i
  -- Use the real entry factorisation and reflection positivity for the covariance.
  -- Step 1: Apply the factorisation to each matrix entry
  have h_factor : ∀ i j,
      (GJGeneratingFunctional (gaussianFreeFieldFree m)
        ((f i).val - QFT.compTimeReflectionReal (f j).val)).re
      = Z i * Z j * E i j := by
    intro i j
    have h_entry := gaussianFreeField_real_entry_factor (m := m) (f := f i) (g := f j)
    simpa [Z, E, R] using h_entry
  -- Step 2: Rewrite the sum using the factorisation
  have h_sum₁ :
      (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional (gaussianFreeFieldFree m)
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re)
      = ∑ i, ∑ j, c i * c j * (Z i * Z j * E i j) := by
    simp_rw [h_factor]
  -- Step 3: express the quadratic form using the rescaled vector y
  have h_sum₂ :
      (∑ i, ∑ j, c i * c j * (Z i * Z j * E i j))
        = ∑ i, ∑ j, y i * y j * E i j := by
    simp [y, Z, E, R, mul_comm, mul_left_comm, mul_assoc]
  -- Step 4: Apply PSD property of E
  have h_R_psd : R.PosSemidef := by
    simpa [R] using freeCovarianceFormR_reflection_matrix_posSemidef (m := m) f
  have h_E_psd : E.PosSemidef := by
    simpa [E] using entrywiseExp_posSemidef_of_posSemidef R h_R_psd
  -- Step 5: Use PSD property - the quadratic form yᵀEy is nonnegative
  have h_quad_sum :
      (∑ i, ∑ j, y i * y j * E i j)
        = y ⬝ᵥ (E.mulVec y) := by
    classical
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_assoc]
  have hy_nonneg : 0 ≤ y ⬝ᵥ (E.mulVec y) := h_E_psd.dotProduct_mulVec_nonneg y
  have h_goal :
      0 ≤ (∑ i, ∑ j, c i * c j *
        (GJGeneratingFunctional (gaussianFreeFieldFree m)
          ((f i).val - QFT.compTimeReflectionReal (f j).val)).re) := by
    have h₁ : 0 ≤ ∑ i, ∑ j, y i * y j * E i j := by
      simpa [h_quad_sum] using hy_nonneg
    have h₂ : 0 ≤ ∑ i, ∑ j, c i * c j * (Z i * Z j * E i j) := by
      simpa [h_sum₂] using h₁
    simpa [h_sum₁] using h₂
  exact h_goal

/-- Main theorem: the Gaussian free field satisfies OS3_real (reflection positivity,
real version). -/
theorem gaussianFreeField_OS3_real :
    os3ReflectionPositivityReal (gaussianFreeFieldFree m) := by
  intro n f c
  simpa using gaussianFreeField_OS3_matrix_real (m := m) f c

end GaussianRealReflectionPositivity

section GaussianComplexReflectionPositivity

variable (m : ℝ) [Fact (0 < m)]

/-! ### Helper lemmas for the complex OS3 proof -/

/-- Bilinear expansion: `C(f − g, f − g) = C(f,f) − C(f,g) − C(g,f) + C(g,g)`.
    Proved from `freeCovarianceℂ_bilinear_add_left/right` and `_smul_left/right`.
-/
private lemma freeCovarianceℂ_bilinear_sub_sub
    (f g : TestFunctionℂ) :
    freeCovarianceℂBilinear m (f - g) (f - g) =
      freeCovarianceℂBilinear m f f
      - freeCovarianceℂBilinear m f g
      - freeCovarianceℂBilinear m g f
      + freeCovarianceℂBilinear m g g := by
  have h_sub_eq : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  simp only [h_sub_eq]
  simp only [freeCovarianceℂ_bilinear_add_left, freeCovarianceℂ_bilinear_add_right,
      freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
  ring

/-- Conjugation identity for the free covariance with star.
    `C(star f, star g) = conj(C(f, g))` when the kernel is real-valued.

    Proof sketch: `C(star f, star g) = ∫∫ conj(f(Θx)) K(x−y) conj(g(Θy)) dx dy`.
    Change variables `x → Θx`, `y → Θy` (measure-preserving, `|Θx−Θy| = |x−y|`):
    `= ∫∫ conj(f(x)) K(x−y) conj(g(y)) dx dy = conj(∫∫ f(x) K(x−y) g(y) dx dy)`.
-/
private lemma freeCovarianceℂ_bilinear_star_star_conj
    (f g : TestFunctionℂ) :
    freeCovarianceℂBilinear m (star f) (star g) =
      starRingEnd ℂ (freeCovarianceℂBilinear m f g) := by
  unfold freeCovarianceℂBilinear
  -- After unfolding:
  -- LHS = ∫∫ (star f)(x) · ↑K(x,y) · (star g)(y)
  --     = ∫∫ conj(f(Θx)) · ↑K(x,y) · conj(g(Θy))   (definitionally, by star_apply = rfl)
  -- RHS = conj(∫∫ f(x) · ↑K(x,y) · g(y))
  -- Step 1: Rewrite (star h)(z) = conj(h(Θz)) explicitly so simp_rw can work with it.
  have hstarf : ∀ x, (star f) x = starRingEnd ℂ (f (QFT.timeReflection x)) := fun _ => rfl
  have hstarg : ∀ y, (star g) y = starRingEnd ℂ (g (QFT.timeReflection y)) := fun _ => rfl
  simp_rw [hstarf, hstarg]
  -- Now LHS = ∫∫ conj(f(Θx)) · ↑K(x,y) · conj(g(Θy))
  -- Step 2: Pull conj inside the RHS integrals.
  have h_ic : ∀ (g : SpaceTime → ℂ), starRingEnd ℂ (∫ x, g x) = ∫ x, starRingEnd ℂ (g x) :=
    fun g => (integral_conj (𝕜 := ℂ)).symm
  rw [h_ic]
  simp_rw [h_ic, map_mul, Complex.conj_ofReal]
  -- Now goal: ∫∫ conj(f(Θx)) · ↑K(x,y) · conj(g(Θy))
  --         = ∫∫ conj(f(x)) · ↑K(x,y) · conj(g(y))
  -- Step 3: Use double_integral_timeReflection (in reverse).
  -- Let G(x,y) = conj(f(x)) · ↑K(x,y) · conj(g(y)).
  -- double_integral_timeReflection gives: ∫∫ G(Θx,Θy) = ∫∫ G(x,y).
  -- LHS = ∫∫ conj(f(Θx)) · ↑K(x,y) · conj(g(Θy))
  -- Rewrite LHS pointwise: K(x,y) → K(Θx,Θy) so the integrand becomes G(Θx,Θy)
  -- where G(x,y) = conj(f(x)) · ↑K(x,y) · conj(g(y)).
  have h_eq_lhs : ∀ x y,
      starRingEnd ℂ (f (QFT.timeReflection x)) *
        (freeCovariance m x y : ℂ) *
        starRingEnd ℂ (g (QFT.timeReflection y))
      = starRingEnd ℂ (f (QFT.timeReflection x)) *
        (freeCovariance m (QFT.timeReflection x) (QFT.timeReflection y) : ℂ) *
        starRingEnd ℂ (g (QFT.timeReflection y)) := by
    intro x y; rw [covariance_timeReflection_invariant]
  simp_rw [h_eq_lhs]
  -- Now LHS = ∫∫ G(Θx,Θy), RHS = ∫∫ G(x,y).
  -- Apply double_integral_timeReflection.
  -- Need integrability of (x,y) ↦ G(x,y) = conj(f(x)) · K(x,y) · conj(g(y)).
  -- This follows from freeCovarianceℂ_bilinear_integrable applied to star f, star g,
  -- which are test functions. But we need it for the "unstarred conj" versions.
  -- star f is already a TestFunctionℂ, so we can use its integrability directly.
  have h_int : Integrable (fun p : SpaceTime × SpaceTime =>
      starRingEnd ℂ (f p.1) * (freeCovariance m p.1 p.2 : ℂ) * starRingEnd ℂ (g p.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    -- (star f)(x) = conj(f(Θx)), so conj(f(x)) = (star f)(Θ⁻¹ x) = (star f)(Θx) since Θ² = id
    -- Actually, let's build the Schwartz functions conj ∘ f and conj ∘ g directly.
    -- These are exactly what starTestFunction constructs (without the time-reflection part).
    -- We can use freeCovarianceℂ_bilinear_integrable with appropriate test functions.
    -- Key insight: the integrand is just the integrand for freeCovarianceℂBilinear
    -- applied to the Schwartz functions x ↦ conj(f(x)) and x ↦ conj(g(x)).
    -- These are test functions (since conj is a smooth linear isometry).
    let f_conj : TestFunctionℂ :=
      ⟨fun x => starRingEnd ℂ (f x), by
        apply ContDiff.comp
        · exact ContinuousLinearMap.contDiff Complex.conjLIE.toContinuousLinearMap
        · exact f.smooth ⊤,
       fun k n => by
        obtain ⟨C, hC⟩ := f.decay' k n
        use C; intro x
        calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f x)) x‖
            = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by
              rw [starRingEnd_iteratedFDeriv_norm_eq]
          _ ≤ C := hC x⟩
    let g_conj : TestFunctionℂ :=
      ⟨fun x => starRingEnd ℂ (g x), by
        apply ContDiff.comp
        · exact ContinuousLinearMap.contDiff Complex.conjLIE.toContinuousLinearMap
        · exact g.smooth ⊤,
       fun k n => by
        obtain ⟨C, hC⟩ := g.decay' k n
        use C; intro x
        calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (g x)) x‖
            = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ := by
              rw [starRingEnd_iteratedFDeriv_norm_eq]
          _ ≤ C := hC x⟩
    exact freeCovarianceℂ_bilinear_integrable m f_conj g_conj
  exact double_integral_timeReflection
    (fun x y => starRingEnd ℂ (f x) * (freeCovariance m x y : ℂ) * starRingEnd ℂ (g y)) h_int

/-- A complex matrix has nonneg Hermitian quadratic form:
    `Re(∑ᵢⱼ vbarᵢ vⱼ Mᵢⱼ) ≥ 0` for all `v`.
    This avoids `Matrix.PosSemidef` which requires `PartialOrder ℂ`.
-/
private def IsRePSD {n : ℕ} (M : Fin n → Fin n → ℂ) : Prop :=
  ∀ v : Fin n → ℂ, 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (v i) * v j * M i j).re

/-- A complex matrix is Hermitian: `M j i = conj(M i j)`. -/
private def IsHermitianMatrix {n : ℕ} (M : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j, M j i = starRingEnd ℂ (M i j)

/-- Star is involutive on `TestFunctionℂ`: `star (star f) = f`. -/
private lemma star_star_testFunctionℂ (f : TestFunctionℂ) : star (star f) = f := by
  ext x
  change starRingEnd ℂ (starRingEnd ℂ (f (QFT.timeReflection (QFT.timeReflection x)))) = f x
  rw [QFT.timeReflection_involutive, RCLike.conj_conj]

/-- The reflection matrix `R_{ij} = C(fᵢ, star fⱼ)` is Hermitian.
    Proof: `R_{ji} = C(f_j, star f_i) = C(star f_i, f_j)` by symmetry
    `= C(star f_i, star(star f_j))` by star involution `= conj(C(f_i, star f_j))` by star_star_conj.
-/
private lemma reflection_matrix_IsHermitian
    {n : ℕ} (f : Fin n → PositiveTimeTestFunctionℂ) :
    IsHermitianMatrix fun i j => freeCovarianceℂBilinear m (f i).val (star (f j).val) := by
  intro i j
  -- Goal (after beta-reduction):
  -- C(f_j, star f_i) = conj(C(f_i, star f_j))
  change freeCovarianceℂBilinear m (f j).val (star (f i).val) =
    starRingEnd ℂ (freeCovarianceℂBilinear m (f i).val (star (f j).val))
  rw [freeCovarianceℂ_bilinear_symm m (f j).val (star (f i).val)]
  -- Goal: C(star f_i, f_j) = conj(C(f_i, star f_j))
  -- Write f_j = star(star f_j) on LHS
  conv_lhs => rw [show (f j).val = star (star (f j).val) from (star_star_testFunctionℂ _).symm]
  exact freeCovarianceℂ_bilinear_star_star_conj m (f i).val (star (f j).val)

-- The complex partial order is needed for Matrix.PosSemidef over ℂ.
open scoped ComplexOrder
open scoped Kronecker

/-- Bridge: `IsHermitianMatrix` implies `Matrix.IsHermitian`. -/
private lemma isHermitian_of_isHermitianMatrix
    {n : ℕ} {M : Fin n → Fin n → ℂ} (hH : IsHermitianMatrix M) :
    (Matrix.of M).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, Matrix.of_apply]
  -- Goal: star (M j i) = M i j
  -- From hH: M j i = starRingEnd ℂ (M i j), so star (M j i) = M i j
  rw [hH i j]; exact starRingEnd_self_apply (M i j)

/-- The quadratic form `star v ⬝ᵥ (of M *ᵥ v)` equals the double sum
    `∑ i, ∑ j, conj(v i) * v j * M i j`.
-/
private lemma quadForm_eq_double_sum
    {n : ℕ} (M : Fin n → Fin n → ℂ) (v : Fin n → ℂ) :
    star v ⬝ᵥ (Matrix.of M *ᵥ v) =
    ∑ i, ∑ j, starRingEnd ℂ (v i) * v j * M i j := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, starRingEnd_apply]
  congr 1; ext i
  rw [Finset.mul_sum]
  congr 1; ext j; ring

/-- For a Hermitian matrix, the quadratic form is self-conjugate (hence real). -/
private lemma quadForm_conj_self_of_hermitian
    {n : ℕ} {M : Fin n → Fin n → ℂ} (hH : IsHermitianMatrix M)
    (v : Fin n → ℂ) :
    starRingEnd ℂ (∑ i, ∑ j, starRingEnd ℂ (v i) * v j * M i j) =
    ∑ i, ∑ j, starRingEnd ℂ (v i) * v j * M i j := by
  simp only [map_sum, map_mul, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  congr 1; ext j; congr 1; ext i
  -- Goal: v i * starRingEnd ℂ (v j) * starRingEnd ℂ (M i j) = starRingEnd ℂ (v j) * v i * M j i
  -- starRingEnd ℂ (M i j) = M j i from Hermiticity
  have : starRingEnd ℂ (M i j) = M j i := by
    rw [hH j i]; exact starRingEnd_self_apply _
  rw [this]; ring

/-- For a Hermitian matrix, the imaginary part of the quadratic form is zero. -/
private lemma quadForm_im_eq_zero_of_hermitian
    {n : ℕ} {M : Fin n → Fin n → ℂ} (hH : IsHermitianMatrix M)
    (v : Fin n → ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (v i) * v j * M i j).im = 0 :=
  Complex.conj_eq_iff_im.mp (quadForm_conj_self_of_hermitian hH v)

/-- Bridge: `IsRePSD` plus `IsHermitianMatrix` implies `Matrix.PosSemidef` over `ℂ`. -/
private lemma posSemidef_of_isRePSD_isHermitian
    {n : ℕ} {M : Fin n → Fin n → ℂ} (hH : IsHermitianMatrix M) (hM : IsRePSD M) :
    (Matrix.of M).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_isHermitianMatrix hH)
  intro v
  rw [quadForm_eq_double_sum]
  rw [Complex.nonneg_iff]
  exact ⟨hM v, (quadForm_im_eq_zero_of_hermitian hH v).symm⟩

/-- Bridge: `Matrix.PosSemidef` over `ℂ` implies `IsRePSD`. -/
private lemma isRePSD_of_posSemidef
    {n : ℕ} {M : Fin n → Fin n → ℂ} (hM : (Matrix.of M).PosSemidef) :
    IsRePSD M := by
  intro v
  have h := hM.dotProduct_mulVec_nonneg v
  rw [quadForm_eq_double_sum] at h
  exact (Complex.nonneg_iff.mp h).1

/-- Complex Schur product theorem: the Hadamard product of two `PosSemidef`
    complex matrices is `PosSemidef`.  Follows from the Kronecker product
    (`PosSemidef.kronecker`) restricted to the diagonal (`PosSemidef.submatrix`).
-/
private lemma posSemidef_hadamard_complex
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.hadamard A B).PosSemidef := by
  let diag : Fin n → Fin n × Fin n := fun i => (i, i)
  suffices h : (Matrix.hadamard A B) = (A ⊗ₖ B).submatrix diag diag by
    rw [h]; exact (hA.kronecker hB).submatrix diag
  ext i j; simp [Matrix.hadamard, Matrix.submatrix, Matrix.kroneckerMap, diag]

/-- Entrywise exponential preserves IsRePSD for Hermitian matrices.
    Complex extension of `entrywiseExp_posSemidef_of_posSemidef`.

    **Proof**: Bridge to `Matrix.PosSemidef` over `ℂ`, use the Hadamard power series
    `exp(Mᵢⱼ) = ∑ₖ Mᵢⱼᵏ/k!`.  Each Hadamard power is `PosSemidef` by the complex
    Schur product theorem (Kronecker ⊗ submatrix).  Partial sums are `PosSemidef`
    (nonneg coefficients), and the limit preserves nonnegativity of the
    real part of the quadratic form.
-/
private lemma entrywiseExp_IsRePSD
    {n : ℕ} {M : Fin n → Fin n → ℂ} (hH : IsHermitianMatrix M) (hM : IsRePSD M) :
    IsRePSD fun i j => Complex.exp (M i j) := by
  -- Bridge to Matrix.PosSemidef over ℂ
  have hPSD : (Matrix.of M).PosSemidef := posSemidef_of_isRePSD_isHermitian hH hM
  -- Hadamard power: HP k i j = (M i j)^k
  let HP : ℕ → Matrix (Fin n) (Fin n) ℂ := fun k i j => (M i j) ^ k
  -- HP 0 is the all-ones matrix, which is PSD
  -- Direct proof: star v ⬝ᵥ (J *ᵥ v) = |∑ v_i|² ≥ 0
  have hHP0_psd : (HP 0).PosSemidef := by
    have h0 : HP 0 = Matrix.of (fun (_ _ : Fin n) => (1 : ℂ)) := by ext i j; simp [HP]
    rw [h0]
    -- The all-ones matrix = vecMulVec 1 (star 1) is PSD
    -- Direct proof: the quadratic form is |∑ v_i|² ≥ 0
    have hHerm : (Matrix.of (fun (_ _ : Fin n) => (1 : ℂ))).IsHermitian := by
      ext i j; simp [conjTranspose_apply, Matrix.of_apply]
    -- Use quadForm_eq_double_sum and show the IsRePSD condition directly
    -- Then convert via nonneg_iff
    have hIsRePSD : IsRePSD (fun (_ _ : Fin n) => (1 : ℂ)) := by
      intro w
      -- ∑ i, ∑ j, conj(w i) * w j * 1 = (∑ conj(w i)) * (∑ w j) = |∑ w i|²
      simp only [mul_one]
      have : (∑ i, ∑ j, starRingEnd ℂ (w i) * w j) =
          starRingEnd ℂ (∑ i, w i) * (∑ j, w j) := by
        rw [map_sum, Finset.sum_mul]; congr 1; ext i
        rw [Finset.mul_sum]
      rw [this, ← Complex.normSq_eq_conj_mul_self]
      simp only [ofReal_re, ge_iff_le]; exact Complex.normSq_nonneg _
    exact posSemidef_of_isRePSD_isHermitian
      (fun _ _ => by simp) hIsRePSD
  -- HP (k+1) = HP k ∘ₕ (of M)
  have hHP_succ : ∀ k, HP (k + 1) = Matrix.hadamard (HP k) (Matrix.of M) := by
    intro k; ext i j; simp [HP, Matrix.hadamard, pow_succ, Matrix.of_apply]
  -- Each HP k is PosSemidef (by induction using complex Schur product)
  have hHP_psd : ∀ k, (HP k).PosSemidef := by
    intro k; induction k with
    | zero => exact hHP0_psd
    | succ k ih => rw [hHP_succ]; exact posSemidef_hadamard_complex ih hPSD
  -- Partial sums: S N = ∑_{k=0}^N (k!)⁻¹ • HP k (defined as matrix sum)
  let S : ℕ → Matrix (Fin n) (Fin n) ℂ := fun N =>
    ∑ k ∈ Finset.range (N + 1), (↑(Nat.factorial k : ℕ) : ℂ)⁻¹ • HP k
  -- Each partial sum is PosSemidef
  have hS_psd : ∀ N, (S N).PosSemidef := by
    intro N
    apply posSemidef_sum
    intro k _
    have hcoeff : (0 : ℂ) ≤ (↑(Nat.factorial k : ℕ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      exact Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact (hHP_psd k).smul hcoeff
  -- S N i j = ∑_{k=0}^N (k!)⁻¹ * (M i j)^k
  have hS_entry : ∀ N i j, S N i j =
      ∑ k ∈ Finset.range (N + 1), (↑(Nat.factorial k : ℕ) : ℂ)⁻¹ * (M i j) ^ k := by
    intro N i j
    simp [S, Matrix.sum_apply, HP]
  -- Prove IsRePSD of the entrywise exp by taking the limit
  intro v
  -- The Re part of the quadratic form of S N is nonneg
  have hre_nonneg : ∀ N,
      0 ≤ (∑ i, ∑ j, starRingEnd ℂ (v i) * v j * S N i j).re := by
    intro N
    have h := (hS_psd N).dotProduct_mulVec_nonneg v
    -- Rewrite the quadratic form as a double sum
    have heq : star v ⬝ᵥ (S N *ᵥ v) =
        ∑ i, ∑ j, starRingEnd ℂ (v i) * v j * S N i j := by
      simp only [dotProduct, mulVec, Pi.star_apply]
      congr 1; ext i; rw [Finset.mul_sum]
      congr 1; ext j
      simp only [starRingEnd_apply]
      ring
    rw [heq] at h
    exact (Complex.nonneg_iff.mp h).1
  -- S N i j → exp(M i j) entrywise, using exp z = ∑ z^k / k!
  have hconv_entry : ∀ i j, Filter.Tendsto (fun N => S N i j)
      Filter.atTop (nhds (Complex.exp (M i j))) := by
    intro i j; simp_rw [hS_entry]
    -- Use the power series for exp: HasSum (fun n => (n!⁻¹ : ℂ) • z^n) (exp z)
    have h : HasSum (fun k => (↑(Nat.factorial k : ℕ) : ℂ)⁻¹ * (M i j) ^ k)
        (Complex.exp (M i j)) := by
      rw [Complex.exp_eq_exp_ℂ]
      have h' := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (M i j)
      simp only [smul_eq_mul] at h'
      convert h' using 1
    rw [HasSum] at h
    exact h.comp (Filter.tendsto_finset_range.comp (Filter.tendsto_atTop_atTop_of_monotone
      (fun a b hab => Nat.add_le_add_right hab 1) (fun b => ⟨b, Nat.le_succ b⟩)))
  -- Convergence of the quadratic form (finite sums of convergent sequences)
  have hconv_quad : Filter.Tendsto
      (fun N => ∑ i, ∑ j, starRingEnd ℂ (v i) * v j * S N i j)
      Filter.atTop
      (nhds (∑ i, ∑ j, starRingEnd ℂ (v i) * v j * Complex.exp (M i j))) := by
    apply tendsto_finsetSum _ fun i _ => ?_
    apply tendsto_finsetSum _ fun j _ => ?_
    exact Filter.Tendsto.mul (Filter.Tendsto.mul tendsto_const_nhds tendsto_const_nhds)
      (hconv_entry i j)
  -- Re is continuous, so Re(quad form) converges too
  have hconv_re := Complex.continuous_re.continuousAt.tendsto.comp hconv_quad
  -- Limit of nonneg reals is nonneg
  exact ge_of_tendsto hconv_re (Filter.eventually_atTop.mpr ⟨0, fun N _ => hre_nonneg N⟩)

/-- Entry factorization for the GFF:
    `Z[fᵢ − star fⱼ] = Aᵢ · conj(Aⱼ) · exp(Rᵢⱼ)`
    where `Aᵢ = exp(−½ C(fᵢ,fᵢ))` and `Rᵢⱼ = C(fᵢ, star fⱼ)`.
-/
private lemma gff_complexZ_entry_factor (fi fj : TestFunctionℂ) :
    Complex.exp (-(1/2 : ℂ) * freeCovarianceℂBilinear m (fi - star fj) (fi - star fj)) =
    Complex.exp (-(1/2 : ℂ) * freeCovarianceℂBilinear m fi fi) *
    starRingEnd ℂ (Complex.exp (-(1/2 : ℂ) * freeCovarianceℂBilinear m fj fj)) *
    Complex.exp (freeCovarianceℂBilinear m fi (star fj)) := by
  -- Expand C(f-star g, f-star g)
  rw [freeCovarianceℂ_bilinear_sub_sub]
  -- Use symmetry: C(star fj, fi) = C(fi, star fj)
  rw [freeCovarianceℂ_bilinear_symm m (star fj) fi]
  -- Use conj identity: C(star fj, star fj) = conj(C(fj, fj))
  rw [freeCovarianceℂ_bilinear_star_star_conj]
  -- Now goal is algebraic: exp(-½(α - 2R + conj(β))) = exp(-½α) · conj(exp(-½β)) · exp(R)
  -- where α = C(fi,fi), β = C(fj,fj), R = C(fi, star fj)
  set α := freeCovarianceℂBilinear m fi fi
  set β := freeCovarianceℂBilinear m fj fj
  set R := freeCovarianceℂBilinear m fi (star fj)
  -- conj(exp(z)) = exp(conj(z)) by Complex.exp_conj
  have h_conj_exp : starRingEnd ℂ (Complex.exp (-(1/2 : ℂ) * β)) =
      Complex.exp (starRingEnd ℂ (-(1/2 : ℂ) * β)) := (Complex.exp_conj _).symm
  rw [h_conj_exp]
  -- Factor: exp(a) * exp(b) * exp(c) = exp(a + b + c)
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_mul (starRingEnd ℂ), map_neg (starRingEnd ℂ),
             map_div₀ (starRingEnd ℂ), map_one (starRingEnd ℂ),
             map_ofNat (starRingEnd ℂ)]
  ring

/-- Star is antilinear on TestFunctionℂ: `star(∑ conj(vⱼ) fⱼ) = ∑ vⱼ star(fⱼ)`.
    Proof: pointwise, `star(c • f)(x) = conj(c f(Θx)) = conj(c) conj(f(Θx))`,
    and `compTimeReflection` is a continuous linear map.
-/
private lemma star_apply (f : TestFunctionℂ) (x : SpaceTime) :
    (star f) x = starRingEnd ℂ (f (QFT.timeReflection x)) := by
  rfl

private lemma star_sum_antilinear {n : ℕ} (v : Fin n → ℂ) (g : Fin n → TestFunctionℂ) :
    star (∑ j, starRingEnd ℂ (v j) • g j) = ∑ j, v j • star (g j) := by
  ext x
  rw [star_apply]
  simp only [SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul]
  rw [map_sum]
  congr 1; ext j
  rw [map_mul, RCLike.conj_conj, star_apply]

/-- Left-sum expansion for `freeCovarianceℂBilinear`. -/
private lemma freeCovarianceℂ_bilinear_sum_left {n : ℕ}
    (a : Fin n → TestFunctionℂ) (u : Fin n → ℂ) (g : TestFunctionℂ) :
    freeCovarianceℂBilinear m (∑ i, u i • a i) g =
    ∑ i, u i * freeCovarianceℂBilinear m (a i) g := by
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
  · simp only [Finset.sum_empty]
    have h := freeCovarianceℂ_bilinear_smul_left m (0 : ℂ) g g
    rw [zero_smul, zero_mul] at h; exact h
  · intro a' s ha' ih
    rw [Finset.sum_insert ha', Finset.sum_insert ha',
        freeCovarianceℂ_bilinear_add_left, freeCovarianceℂ_bilinear_smul_left, ih]

/-- Right-sum expansion for `freeCovarianceℂBilinear`. -/
private lemma freeCovarianceℂ_bilinear_sum_right {n : ℕ}
    (f : TestFunctionℂ) (b : Fin n → TestFunctionℂ) (w : Fin n → ℂ) :
    freeCovarianceℂBilinear m f (∑ j, w j • b j) =
    ∑ j, w j * freeCovarianceℂBilinear m f (b j) := by
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
  · simp only [Finset.sum_empty]
    have h := freeCovarianceℂ_bilinear_smul_right m (0 : ℂ) f f
    rw [zero_smul, zero_mul] at h; exact h
  · intro a' s ha' ih
    rw [Finset.sum_insert ha', Finset.sum_insert ha',
        freeCovarianceℂ_bilinear_add_right, freeCovarianceℂ_bilinear_smul_right, ih]

/-- Bilinearity of `freeCovarianceℂBilinear` on finite sums. -/
private lemma freeCovarianceℂ_bilinear_sum_sum {n : ℕ}
    (a b : Fin n → TestFunctionℂ) (u w : Fin n → ℂ) :
    freeCovarianceℂBilinear m (∑ i, u i • a i) (∑ j, w j • b j) =
    ∑ i, ∑ j, u i * w j * freeCovarianceℂBilinear m (a i) (b j) := by
  rw [freeCovarianceℂ_bilinear_sum_left]
  congr 1; ext i
  rw [freeCovarianceℂ_bilinear_sum_right, Finset.mul_sum]
  congr 1; ext j; ring

/-- The reflection matrix `R_{ij} = C(fᵢ, star fⱼ)` is IsRePSD.

    For any `v`, define `h = ∑ conj(vⱼ) fⱼ` (positive-time).  Then
    `rpInnerProduct(h) = C(star h, h) = C(∑ vⱼ star(fⱼ), ∑ conj(vᵢ) fᵢ)
      = ∑ᵢⱼ conj(vᵢ) vⱼ C(star(fⱼ), fᵢ) = ∑ᵢⱼ conj(vᵢ) vⱼ C(fᵢ, star(fⱼ))`.
    `Re(rpInnerProduct(h)) ≥ 0` by `freeCovariance_reflection_positive_bilinear`.
-/
private lemma reflection_matrix_IsRePSD
    {n : ℕ} (f : Fin n → PositiveTimeTestFunctionℂ) :
    IsRePSD fun i j => freeCovarianceℂBilinear m (f i).val (star (f j).val) := by
  intro v
  -- Define h = ∑ conj(v_j) f_j (positive-time test function)
  set h : TestFunctionℂ := ∑ j, starRingEnd ℂ (v j) • (f j).val with h_def
  -- h has positive-time support
  have hh_supp : ∀ x : SpaceTime, x 0 ≤ 0 → h x = 0 := by
    intro x hx
    -- Each (f j).val has positive-time support, so (c • f_j) x = 0 when x₀ ≤ 0
    -- and the sum of zeros is zero
    have : ∀ j, (starRingEnd ℂ (v j) • (f j).val : TestFunctionℂ) x = 0 := by
      intro j
      change starRingEnd ℂ (v j) * (f j).val x = 0
      rw [PositiveTimeTestFunctionℂ.zero_on_nonpositive (f j) hx, mul_zero]
    change h x = 0
    rw [h_def, SchwartzMap.sum_apply]
    exact Finset.sum_eq_zero fun j _ => this j
  -- star h = ∑ v_j star(f_j) by antilinearity of star
  have h_star : star h = ∑ j, v j • star ((f j).val) :=
    star_sum_antilinear v (fun j => (f j).val)
  -- Expand rpInnerProduct(h) = C(star h, h) by bilinearity
  have h_expand : rpInnerProduct m h =
      ∑ i, ∑ j, v i * starRingEnd ℂ (v j) *
        freeCovarianceℂBilinear m (star (f i).val) ((f j).val) := by
    unfold rpInnerProduct
    rw [h_star, h_def]
    exact freeCovarianceℂ_bilinear_sum_sum m
      (fun i => star (f i).val) (fun j => (f j).val) v (fun j => starRingEnd ℂ (v j))
  -- Reindex: ∑ v_i conj(v_j) C(star f_i, f_j) = ∑ conj(v_i) v_j C(f_i, star f_j)
  -- by symmetry C(star f_i, f_j) = C(f_j, star f_i) and swapping i↔j
  have h_swap :
      (∑ i, ∑ j, v i * starRingEnd ℂ (v j) *
        freeCovarianceℂBilinear m (star (f i).val) ((f j).val)).re =
      (∑ i, ∑ j, starRingEnd ℂ (v i) * v j *
        freeCovarianceℂBilinear m (f i).val (star (f j).val)).re := by
    congr 1
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j
    rw [freeCovarianceℂ_bilinear_symm]
    ring
  -- Combine: Re(∑ conj(v_i) v_j C(f_i, star f_j)) = Re(rpInnerProduct(h)) ≥ 0
  rw [← h_swap, ← h_expand]
  exact freeCovariance_reflection_positive_bilinear m h hh_supp

/-- The complex OS3 quadratic form for the GFF is nonneg. -/
private lemma gff_complexOS3_matrix
    {n : ℕ} (f : Fin n → PositiveTimeTestFunctionℂ) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        GJGeneratingFunctionalℂ (gaussianFreeFieldFree m)
          ((f i).val - star (f j).val)).re := by
  -- Step 1: Replace Z[J] with exp(-½ C(J,J))
  simp_rw [GFFIsGaussian.gff_complex_characteristic_OS0 m]
  -- Step 2: Factor each matrix entry
  simp_rw [gff_complexZ_entry_factor m]
  -- Step 3: Algebraic rewrite: conj(c_i) c_j A_i conj(A_j) E_ij = conj(w_i) w_j E_ij
  have h_rewrite : ∀ i j : Fin n,
      starRingEnd ℂ (c i) * c j *
        (Complex.exp (-(1/2 : ℂ) * freeCovarianceℂBilinear m (f i).val (f i).val) *
         starRingEnd ℂ (Complex.exp (-(1/2 : ℂ) * freeCovarianceℂBilinear m (f j).val (f j).val)) *
         Complex.exp (freeCovarianceℂBilinear m (f i).val (star (f j).val))) =
      starRingEnd ℂ (c i * starRingEnd ℂ (Complex.exp (-(1/2 : ℂ) * freeCovarianceℂBilinear m (f
        i).val (f i).val))) *
      (c j * starRingEnd ℂ (Complex.exp (-(1/2 : ℂ) * freeCovarianceℂBilinear m (f j).val (f
         j).val))) *
      Complex.exp (freeCovarianceℂBilinear m (f i).val (star (f j).val)) := by
    intro i j; simp only [map_mul, RCLike.conj_conj]; ring
  simp_rw [h_rewrite]
  -- Step 4: Apply IsRePSD chain directly
  exact entrywiseExp_IsRePSD (reflection_matrix_IsHermitian m f) (reflection_matrix_IsRePSD m f) _

/-- Main theorem: the Gaussian free field satisfies OS3 (complex reflection positivity).
    This is the standard Osterwalder–Schrader formulation with complex-valued test
    functions and complex coefficients, compatible with OS reconstruction.

    The `star` operation is `(star f)(x) = conj(f(Θx))`.  For real test functions,
    `star = compTimeReflection` (see `star_toComplex_eq_compTimeReflection`).
-/
theorem _root_.QFT.gaussianFreeField_OS3 :
    os3ReflectionPositivity (gaussianFreeFieldFree m) := by
  intro n f c
  exact gff_complexOS3_matrix m f c

end GaussianComplexReflectionPositivity

end QFT

end
