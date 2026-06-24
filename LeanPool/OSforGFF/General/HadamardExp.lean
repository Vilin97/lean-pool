/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import LeanPool.OSforGFF.General.SchurProduct
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Constructions

/-!
# Entrywise Exponential of PSD Matrices

Develops Hadamard (entrywise) operations on real matrices and proves that the entrywise
exponential preserves positive semidefiniteness. The key tool is the Schur product theorem
(from `SchurProduct.lean`): Hadamard powers of a PD matrix remain PD, so summing them with
coefficients `1/n!` yields a PD matrix. The PSD case follows by a continuity argument:
`R + ε I` is PD for every `ε > 0`, and the limit `ε → 0` uses continuity of the entrywise
exponential.
-/


open Complex
open scoped BigOperators
open Filter
open scoped Topology

namespace OSforGFF

universe u

variable {ι : Type u}

/-- Entrywise real exponential of a matrix: `(entrywiseExp R) i j = exp (R i j)`.
    Used for the OS3 proof (Glimm–Jaffe): if `R` is PSD, then `exp(R)` (entrywise) should be PSD.
-/
noncomputable def entrywiseExp (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.exp (R i j)

@[simp] lemma entrywiseExp_apply (R : Matrix ι ι ℝ) (i j : ι) :
  entrywiseExp R i j = Real.exp (R i j) := rfl

/-- Continuity of the entrywise exponential map `R ↦ exp ∘ R` on matrices. -/
lemma continuous_entrywiseExp (ι : Type u) :
  Continuous (fun R : Matrix ι ι ℝ => entrywiseExp R) := by
  classical
  -- Matrices are pi-types `ι → ι → ℝ`; use coordinatewise continuity
  refine continuous_pi_iff.2 (fun i => ?_)
  refine continuous_pi_iff.2 (fun j => ?_)
  -- Coordinate map R ↦ R i j is continuous; compose with exp
  have hcoord : Continuous (fun R : Matrix ι ι ℝ => R i j) :=
    (continuous_apply j).comp (continuous_apply i)
  change Continuous (fun R : Matrix ι ι ℝ => Real.exp (R i j))
  exact Real.continuous_exp.comp hcoord

/-- Over `ℝ`, entrywise exponential preserves Hermitian symmetry. -/
private lemma isHermitian_entrywiseExp_real (R : Matrix ι ι ℝ)
    (hR : R.IsHermitian) : (entrywiseExp R).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  have h_R_herm : R j i = R i j := by simpa using (Matrix.IsHermitian.apply hR j i).symm
  simpa [Matrix.conjTranspose, entrywiseExp] using congrArg Real.exp h_R_herm

/-- Hadamard identity element: the all-ones matrix for entrywise multiplication. -/
@[simp] def hadamardOne (ι : Type u) : Matrix ι ι ℝ := fun _ _ => 1

/-- n-fold Hadamard power of a matrix: `hadamardPow R n = R ∘ₕ ⋯ ∘ₕ R` (n times),
    with `hadamardPow R 0 = hadamardOne`.
-/
@[simp] def hadamardPow (R : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0     => hadamardOne (ι := ι)
  | n+1   => hadamardPow R n ∘ₕ R

@[simp] lemma hadamardPow_zero (R : Matrix ι ι ℝ) : hadamardPow R 0 = hadamardOne (ι := ι) := rfl
@[simp] lemma hadamardPow_succ (R : Matrix ι ι ℝ) (n : ℕ) :
  hadamardPow R (n+1) = hadamardPow R n ∘ₕ R := rfl

/-- Over `ℝ`, the Hadamard product of Hermitian matrices is Hermitian. -/
private lemma isHermitian_hadamard_real {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ∘ₕ B).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  have hAij : A i j = A j i := by simpa using (Matrix.IsHermitian.apply hA i j).symm
  have hBij : B i j = B j i := by simpa using (Matrix.IsHermitian.apply hB i j).symm
  simp [Matrix.conjTranspose, Matrix.hadamard, hAij, hBij]

/-- Hadamard powers act entrywise as usual scalar powers. -/
lemma hadamardPow_apply (R : Matrix ι ι ℝ) (n : ℕ) (i j : ι) :
  hadamardPow R n i j = (R i j) ^ n := by
  induction n with
  | zero => simp [hadamardPow, hadamardOne]
  | succ n ih => simp [Matrix.hadamard, ih, pow_succ]

/-- One term of the Hadamard-series for the entrywise exponential. -/
noncomputable def entrywiseExpSeriesTerm (R : Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  (1 / (Nat.factorial n : ℝ)) • hadamardPow R n

/-- Series definition of the entrywise exponential using Hadamard powers (entrywise `tsum`). -/
noncomputable def entrywiseExpHadamardSeries (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => tsum (fun n : ℕ => (1 / (Nat.factorial n : ℝ)) * (hadamardPow R n i j))

/-- The entrywise exponential agrees with its Hadamard series expansion.
    Uses the Taylor series for Complex.exp and converts to the real case.
-/
lemma entrywiseExp_eq_hadamardSeries (R : Matrix ι ι ℝ) :
  entrywiseExp R = entrywiseExpHadamardSeries R := by
  classical
  funext i j
  dsimp [entrywiseExp, entrywiseExpHadamardSeries]
  -- Scalar reduction
  set x : ℝ := R i j
  -- Complex Taylor series for exp at 0
  have h_taylor : ∑' n : ℕ,
      (↑n.factorial)⁻¹ * (iteratedDeriv n Complex.exp 0) * ((x : ℂ) - 0) ^ n
      = Complex.exp (x : ℂ) := by
    exact Complex.taylorSeries_eq_on_eball'
      (c := 0) (r := ⊤) (z := (x : ℂ)) (by simp)
      (by simpa using Complex.differentiable_exp.differentiableOn)
  -- iteratedDeriv n exp 0 = 1
  have h_deriv : ∀ n, iteratedDeriv n Complex.exp 0 = 1 := by
    intro n; rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp, Complex.exp_zero]
  -- Define series terms
  let fC : ℕ → ℂ := fun n => (x : ℂ) ^ n / (Nat.factorial n : ℂ)
  let fR : ℕ → ℝ := fun n => x ^ n / (Nat.factorial n : ℝ)
  -- Standard complex power series for exp
  have h_seriesC : ∑' n : ℕ, fC n = Complex.exp (x : ℂ) := by
    -- simplify Taylor series to the usual form
    simpa [fC, div_eq_mul_inv, sub_zero, h_deriv, mul_comm, mul_left_comm, mul_assoc] using h_taylor
  -- Summability of the complex series via the real one
  have hsR : Summable fR := Real.summable_pow_div_factorial x
  have hsC_ofReal : Summable (fun n : ℕ => (fR n : ℂ)) := (Complex.summable_ofReal).2 hsR
  have h_eqfun : (fun n : ℕ => (fR n : ℂ)) = fC := by
    funext n; simp [fR, fC, div_eq_mul_inv]
  have hsC : Summable fC := by simpa [h_eqfun] using hsC_ofReal
  -- Take real parts in the complex series identity
  have h_re_tsum : (∑' n : ℕ, fC n).re = ∑' n : ℕ, (fC n).re := Complex.re_tsum hsC
  have h_re_exp : (Complex.exp (x : ℂ)).re = Real.exp x := Complex.exp_ofReal_re x
  have h_re_terms : (fun n : ℕ => (fC n).re) = fR := by
    funext n
    -- First show fC n equals the complexification of fR n, then take real parts
    have hpt : fC n = (fR n : ℂ) := by simp [fC, fR, div_eq_mul_inv]
    simpa [Complex.ofReal_re] using congrArg Complex.re hpt
  -- Combine: real parts of both sides of h_seriesC give the real series identity
  have hx_sum : ∑' n : ℕ, fR n = Real.exp x := by
    have := congrArg Complex.re h_seriesC
    simpa [h_re_tsum, h_re_exp, h_re_terms] using this
  -- Massaging coefficients and finishing
  have hx_sum' : Real.exp x = ∑' n : ℕ, (1 / (Nat.factorial n : ℝ)) * x ^ n := by
    simpa [fR, one_div, div_eq_mul_inv, mul_comm] using hx_sum.symm
  simpa [x, hadamardPow_apply, one_div, div_eq_mul_inv, mul_comm] using hx_sum'

/-- Ones is the identity for the Hadamard product. -/
lemma hadamardOne_hMul_left (R : Matrix ι ι ℝ) : Matrix.hadamard (hadamardOne ι) R = R := by
  ext i j; simp [hadamardOne, Matrix.hadamard]


/-- Hadamard powers of a positive definite matrix are positive definite for all n ≥ 1. -/
lemma hadamardPow_posDef_of_posDef
  [Finite ι] (R : Matrix ι ι ℝ) (hR : R.PosDef) : ∀ n, 1 ≤ n → (hadamardPow R n).PosDef := by
  classical
  letI := Fintype.ofFinite ι
  intro n hn
  -- write n = k+1
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  subst hk
  induction k with
  | zero =>
    -- n = 1
    have hEq : hadamardPow R 1 = R := by
      ext i j; simp
    rw [hEq]; exact hR
  | succ k ih =>
    -- n = (k+1)+1 = k+2
    have hPD_k1 : (hadamardPow R (k+1)).PosDef := ih (Nat.succ_pos _)
    -- Schur product with R preserves PD
    simpa [hadamardPow_succ] using
      schur_product_posDef (A := hadamardPow R (k+1)) (B := R) hPD_k1 hR

/-- The quadratic form of the Hadamard series equals the sum of quadratic forms of individual terms.
    This lemma handles the complex interchange of summation and quadratic form evaluation.
-/
lemma quadratic_form_entrywiseExp_hadamardSeries
  [Fintype ι] (R : Matrix ι ι ℝ) (x : ι → ℝ) :
  x ⬝ᵥ (entrywiseExpHadamardSeries R).mulVec x =
  ∑' n : ℕ, (1 / (Nat.factorial n : ℝ)) * (x ⬝ᵥ (hadamardPow R n).mulVec x) := by
  classical
  -- Per entry: s_ij n := (1 / (n!)) * hadamardPow R n i j
  let s_ij (i j : ι) (n : ℕ) := (1 / (Nat.factorial n : ℝ)) * hadamardPow R n i j
  -- Summability for each entry
  have hs_ij (i j : ι) : Summable (s_ij i j) := by
    simpa [s_ij, hadamardPow_apply, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using Real.summable_pow_div_factorial (R i j)
  -- HasSum for each entry
  have hHas_ij (i j : ι) : HasSum (s_ij i j) ((entrywiseExpHadamardSeries R) i j) := by
    have h1 : (entrywiseExpHadamardSeries R) i j = tsum (s_ij i j) := by
      simp [entrywiseExpHadamardSeries, s_ij]
    rw [h1]
    exact (hs_ij i j).hasSum
  -- Push scalars inside: first x j
  have hHas_ij_xj (i j : ι) :
      HasSum (fun n => s_ij i j n * x j) ((entrywiseExpHadamardSeries R) i j * x j) :=
    (hHas_ij i j).mul_right (x j)
  -- Then x i
  have hHas_ij_xi_xj (i j : ι) :
      HasSum (fun n => x i * (s_ij i j n * x j)) (x i * ((entrywiseExpHadamardSeries R) i j * x
        j)) :=
    (hHas_ij_xj i j).mul_left (x i)
  -- Rewrite term
  have hHas_ij_rewrite (i j : ι) :
      HasSum (fun n => (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow R n i j * x j))
             (x i * ((entrywiseExpHadamardSeries R) i j) * x j) := by
    convert hHas_ij_xi_xj i j using 1
    · funext n; simp only [s_ij]; ring
    · simp [mul_assoc]
  -- Combine over j (finite) with hasSum_sum
  have hHas_sum_j (i : ι) :
      HasSum (fun n => ∑ j, (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow R n i j * x j))
             (∑ j, x i * ((entrywiseExpHadamardSeries R) i j) * x j) := by
    apply hasSum_sum
    intro j _
    exact hHas_ij_rewrite i j
  -- Combine over i (finite) similarly
  have hHas_sum_i :
      HasSum (fun n => ∑ i, ∑ j,
        (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow (ι:=ι) R n i j * x j))
             (∑ i, ∑ j, x i * ((entrywiseExpHadamardSeries (ι:=ι) R) i j) * x j) := by
    apply hasSum_sum
    intro i _
    exact hHas_sum_j i
  -- Take tsum of hHas_sum_i
  have htsum_eq := hHas_sum_i.tsum_eq
  -- Expand the RHS to x ⬝ᵥ (...) ⬝ᵥ x
  have hrhs_expand :
      ∑ i, ∑ j, x i * ((entrywiseExpHadamardSeries (ι:=ι) R) i j) * x j
      = x ⬝ᵥ (entrywiseExpHadamardSeries (ι:=ι) R).mulVec x := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    congr 1; ext i; ring_nf
  -- Identify the LHS coefficient structure
  have hlhs_identify (n : ℕ) :
      ∑ i, ∑ j, (1 / (Nat.factorial n : ℝ)) * (x i * hadamardPow (ι:=ι) R n i j * x j)
      = (1 / (Nat.factorial n : ℝ)) * (x ⬝ᵥ (hadamardPow (ι:=ι) R n).mulVec x) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  -- Put it all together
  rw [← hrhs_expand, ← htsum_eq]
  simp only [hlhs_identify]

/-- Summability of the scalar quadratic-form coefficients appearing in the
    Hadamard exponential series.
-/
lemma summable_hadamardQuadSeries
    [Fintype ι] (R : Matrix ι ι ℝ) (x : ι → ℝ) :
    Summable (fun n : ℕ =>
      (1 / (Nat.factorial n : ℝ)) * (x ⬝ᵥ (hadamardPow (ι:=ι) R n).mulVec x)) := by
  classical
  -- Each individual coordinate contributes a summable exponential series.
  have h_single :
      ∀ i j : ι,
        Summable (fun n : ℕ =>
          (1 / (Nat.factorial n : ℝ)) * (x i * (R i j) ^ n * x j)) := by
    intro i j
    have h := Real.summable_pow_div_factorial (R i j)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using h.mul_left (x i * x j)
  -- Inner sums over j are summable for every fixed i.
  have h_inner_hasSum :
      ∀ i : ι,
        HasSum (fun n : ℕ =>
          ∑ j : ι,
            (1 / (Nat.factorial n : ℝ)) * (x i * (R i j) ^ n * x j))
          (∑ j : ι, tsum (fun n : ℕ =>
            (1 / (Nat.factorial n : ℝ)) * (x i * (R i j) ^ n * x j))) := by
    intro i
    classical
    apply hasSum_sum
    exact fun j _ => (h_single i j).hasSum
  have h_inner :
      ∀ i : ι, Summable (fun n : ℕ =>
        ∑ j : ι,
          (1 / (Nat.factorial n : ℝ)) * (x i * (R i j) ^ n * x j)) :=
    fun i => (h_inner_hasSum i).summable
  -- The outer sum over i remains summable.
  have h_outer : Summable (fun n : ℕ => ∑ i : ι, ∑ j : ι,
      (1 / (Nat.factorial n : ℝ)) * (x i * (R i j) ^ n * x j)) := by
    classical
    exact summable_sum fun i a => h_inner i
  -- Identify the quadratic form with the double sum built above.
  have h_eq :
      (fun n : ℕ =>
        (1 / (Nat.factorial n : ℝ)) *
          (x ⬝ᵥ (hadamardPow (ι:=ι) R n).mulVec x)) =
      fun n : ℕ => ∑ i : ι, ∑ j : ι,
        (1 / (Nat.factorial n : ℝ)) * (x i * (R i j) ^ n * x j) := by
    funext n
    simp [Matrix.mulVec, dotProduct, hadamardPow_apply, div_eq_mul_inv,
      Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  -- Conclude summability via the established equality.
  rwa [h_eq]

/-- The Hadamard-series entrywise exponential preserves positive definiteness.
    Sketch: each Hadamard power (for n ≥ 1) is PD by the Schur product theorem and induction;
    summing with positive coefficients 1/n! yields strictly positive quadratic form for every x ≠ 0
    since the n = 1 term already contributes xᵀ R x > 0. Interchange of sum and quadratic form
    follows from absolute convergence of the scalar exp series; IsHermitian follows termwise.
-/
lemma posDef_entrywiseExp_hadamardSeries_of_posDef
  [Finite ι] (R : Matrix ι ι ℝ) (hR : R.PosDef) :
  (entrywiseExpHadamardSeries (ι:=ι) R).PosDef := by
  classical
  letI := Fintype.ofFinite ι
  -- Extract Hermitian part from PosDef
  have hHermR : R.IsHermitian := hR.isHermitian
  -- Each Hadamard power is Hermitian
  have hHermPow : ∀ n, (hadamardPow (ι:=ι) R n).IsHermitian := by
    intro n
    induction n with
    | zero =>
      rw [hadamardPow_zero]
      rw [Matrix.IsHermitian]
      ext i j
      simp [hadamardOne, Matrix.conjTranspose]
    | succ n ih =>
      rw [hadamardPow_succ]
      exact isHermitian_hadamard_real (ι:=ι) ih hHermR
  -- Show IsHermitian for the series (termwise symmetry)
  have hHermS : (entrywiseExpHadamardSeries (ι:=ι) R).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp only [entrywiseExpHadamardSeries, Matrix.conjTranspose_apply, star_trivial]
    -- Use termwise symmetry under tsum
    have hsym_term : ∀ n, (hadamardPow (ι:=ι) R n i j) = (hadamardPow (ι:=ι) R n j i) := by
      intro n
      -- from hHermPow n
      simpa using (Matrix.IsHermitian.apply (hHermPow n) i j).symm
    -- Apply symmetry termwise in the tsum
    simp_rw [hsym_term]
  -- Now show strict positivity of the quadratic form using dotProduct characterization
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHermS
  intro x hx
  -- Define the scalar series of quadratic forms
  let f : ℕ → ℝ := fun n => (1 / (Nat.factorial n : ℝ)) * (x ⬝ᵥ (hadamardPow (ι:=ι) R n).mulVec x)
  -- Identify the quadratic form of the series with the tsum of `f`
  have hq_tsum :
      x ⬝ᵥ (entrywiseExpHadamardSeries (ι:=ι) R).mulVec x
      = tsum f := by
    -- Use the helper lemma to establish the quadratic form interchange
    exact quadratic_form_entrywiseExp_hadamardSeries R x
  -- Each term f n is nonnegative, and f 1 is strictly positive
  have hterm_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    by_cases hn : n = 0
    · -- n = 0: ones matrix
      subst hn
      -- Compute the quadratic form against the ones matrix explicitly
      classical
      have hmv : (hadamardOne (ι:=ι)).mulVec x = (fun _ => ∑ j, x j) := by
        funext i; simp [hadamardOne, Matrix.mulVec, dotProduct]
      have hquad : x ⬝ᵥ (hadamardOne (ι:=ι)).mulVec x = (∑ i, x i) * (∑ i, x i) := by
        simp [hmv, dotProduct, Finset.sum_mul]
      -- Reduce to a square ≥ 0
      simpa [f, hadamardPow, Nat.factorial_zero, one_div, hquad, pow_two, inv_one] using
        sq_nonneg (∑ i, x i)
    · -- n ≥ 1: use PosSemidef from PosDef
      have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hPD : (hadamardPow (ι:=ι) R n).PosDef :=
        hadamardPow_posDef_of_posDef (ι:=ι) R hR n hn1
      -- hence PosSemidef
      have hPSD : (hadamardPow (ι:=ι) R n).PosSemidef := Matrix.PosDef.posSemidef hPD
      -- evaluate quadratic form
      have hxq : 0 ≤ x ⬝ᵥ (hadamardPow (ι:=ι) R n).mulVec x := hPSD.dotProduct_mulVec_nonneg x
      positivity
  have hterm_pos : 0 < f 1 := by
    -- n = 1 term equals xᵀ R x, which is strictly positive by hR
    have hEq1' : hadamardPow (ι:=ι) R 1 = Matrix.hadamard (hadamardOne (ι:=ι)) R := rfl
    have hRpos := hR.dotProduct_mulVec_pos hx
    simpa [f, hEq1', hadamardOne_hMul_left, Nat.factorial, one_div, inv_one] using hRpos
  -- Strict positivity of the sum from the positive n=1 term and nonnegativity of the rest
  have : 0 < tsum f := by
    -- f is summable because it comes from the quadratic form of a convergent series
    have hSumm_f : Summable f := by
      -- The summability of f follows from summable_hadamardQuadSeries
      -- f n = (1/n!) * (quadratic form in hadamardPow R n)
      exact summable_hadamardQuadSeries R x
    -- Now compare tsum with the singleton partial sum at {1}
    have h_f1_le : f 1 ≤ tsum f := by
      -- bound partial sum by tsum for nonnegative terms
      have h := (Summable.sum_le_tsum (s := ({1} : Finset ℕ)) (f := f)
        (by intro n hn; exact hterm_nonneg n) hSumm_f)
      simpa using h
    -- Use strict positivity of f 1
    exact lt_of_lt_of_le hterm_pos h_f1_le
  -- Conclude
  simpa [hq_tsum] using this

--set_option diagnostics true

/-- The Hadamard-series entrywise exponential preserves positive semidefiniteness.
    This follows from the positive definite case by continuity: if R is PSD, then
    R + εI is PD for ε > 0, so entrywiseExpHadamardSeries(R + εI) is PD, and
    taking ε → 0⁺ with continuity of entrywiseExpHadamardSeries gives that
    entrywiseExpHadamardSeries(R) is PSD.

    NOTE: This proof is simplified to avoid matrix reduction timeouts.
-/
lemma posSemidef_entrywiseExp_hadamardSeries_of_posSemidef
  [Finite ι] (R : Matrix ι ι ℝ) (hR : R.PosSemidef) :
  (entrywiseExpHadamardSeries (ι:=ι) R).PosSemidef := by
  classical
  letI := Fintype.ofFinite ι
  -- Step 1: For any ε > 0, R + εI is positive definite
  have h_perturb_posDef : ∀ (ε : ℝ), ε > 0 → (R + ε • (1 : Matrix ι ι ℝ)).PosDef := by
    intro ε hε
    -- R is PSD + εI is PD for ε > 0 gives PD
    -- This uses: (1) R + εI is Hermitian, (2) quadratic form is x^T R x + ε ||x||^2 > 0 for x ≠ 0
    have hR_herm := hR.isHermitian
    have h_add_herm : (R + ε • (1 : Matrix ι ι ℝ)).IsHermitian := by
      apply Matrix.IsHermitian.add hR_herm
      -- ε • 1 is Hermitian since 1 is Hermitian and ε is real
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      simp
    apply Matrix.PosDef.of_dotProduct_mulVec_pos h_add_herm
    intro x hx_ne_zero
    have hR_nonneg := hR.dotProduct_mulVec_nonneg x
    have hε_pos : 0 < ε * (x ⬝ᵥ x) := by
      have h_norm_pos : 0 < x ⬝ᵥ x := by
        -- For real vectors, x ⬝ᵥ x = star x ⬝ᵥ x since star = id on ℝ
        have : x ⬝ᵥ x = star x ⬝ᵥ x := by simp [star]
        rwa [this, Matrix.dotProduct_star_self_pos_iff]
      exact mul_pos hε h_norm_pos
    have h_expand : x ⬝ᵥ (R + ε • (1 : Matrix ι ι ℝ)).mulVec x =
                    x ⬝ᵥ R.mulVec x + ε * (x ⬝ᵥ x) := by
      rw [Matrix.add_mulVec, dotProduct_add]
      -- Need to show: x ⬝ᵥ ε • x = ε * x ⬝ᵥ x
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [dotProduct_smul]
      -- Now need: ε • (x ⬝ᵥ x) = ε * x ⬝ᵥ x
      rw [smul_eq_mul]
    -- Goal has star x, but for real vectors star x = x
    have : star x ⬝ᵥ (R + ε • 1).mulVec x = x ⬝ᵥ (R + ε • 1).mulVec x := by simp [star]
    rw [this, h_expand]
    exact add_pos_of_nonneg_of_pos hR_nonneg hε_pos
  -- Step 2: For each ε > 0, entrywiseExpHadamardSeries(R + εI) is positive definite
  have h_exp_perturb_posDef : ∀ (ε : ℝ), ε > 0 → (entrywiseExp (R + ε • (1 : Matrix ι ι ℝ))).PosDef
    := by
    intro ε hε
    have h := posDef_entrywiseExp_hadamardSeries_of_posDef (R + ε • (1 : Matrix ι ι ℝ))
      (h_perturb_posDef ε hε)
    simpa [entrywiseExp_eq_hadamardSeries] using h
  -- Step 3: Continuity of the map S ↦ entrywiseExpHadamardSeries(S)
  have h_continuous : Continuous (fun S : Matrix ι ι ℝ => entrywiseExp S) :=
    continuous_entrywiseExp ι
  -- Step 4: Continuity of diagonal perturbation ε ↦ R + εI
  have h_perturb_continuous : Continuous (fun ε : ℝ => R + ε • (1 : Matrix ι ι ℝ)) := by
    -- Linear in ε, hence continuous
    have : Continuous (fun ε : ℝ => ε • (1 : Matrix ι ι ℝ)) := continuous_id.smul continuous_const
    exact Continuous.add continuous_const this
  -- Step 5: Composition gives continuity of ε ↦ entrywiseExpHadamardSeries(R + εI)
  have h_comp_continuous : Continuous (fun ε : ℝ => entrywiseExp (R + ε • (1 : Matrix ι ι ℝ))) := by
    exact h_continuous.comp h_perturb_continuous
  -- Step 6: Limit as ε → 0⁺ gives the result at ε = 0
  have h_limit : entrywiseExp R =
    entrywiseExp (R + 0 • (1 : Matrix ι ι ℝ)) := by
    -- This uses continuity at ε = 0: lim_{ε→0} entrywiseExpHadamardSeries(R + εI) =
    -- entrywiseExpHadamardSeries(R)
    simp only [zero_smul, add_zero]
  -- Step 7: PosSemidef is preserved under limits of PosDef sequences
  have h_limit_posSemidef_entry : (entrywiseExp R).PosSemidef := by
    -- Use the fact that:
    -- (1) For each ε > 0, entrywiseExp (R + εI) is PosDef (hence PosSemidef)
    -- (2) The limit entrywiseExp R exists by continuity
    -- (3) PosSemidef is a closed condition (IsHermitian + nonnegative quadratic form)
    have h_herm : (entrywiseExp R).IsHermitian :=
      isHermitian_entrywiseExp_real (ι:=ι) R hR.isHermitian
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h_herm
    intro x
    -- For real vectors, star x = x
    have h_star_eq : star x = x := by simp [star]
    -- For each ε > 0: 0 ≤ xᵀ entrywiseExp(R + εI) x
    have h_nonneg_eps : ∀ (ε : ℝ), ε > 0 → 0 ≤ x ⬝ᵥ (entrywiseExp (R + ε • (1 : Matrix ι ι
      ℝ))).mulVec x := by
      intro ε hε
      -- Use the positive semidefiniteness of entrywiseExp (R + εI)
      exact (Matrix.PosDef.posSemidef (h_exp_perturb_posDef ε hε)).dotProduct_mulVec_nonneg x
    -- Quadratic form is continuous: x ⬝ᵥ A.mulVec x is continuous in A
    have h_quad_continuous : Continuous (fun A : Matrix ι ι ℝ => x ⬝ᵥ A.mulVec x) := by
      -- Quadratic forms are finite sums of coordinate functions, hence continuous
      simp only [Matrix.mulVec, dotProduct]
      apply continuous_finsetSum
      intro i _
      -- Inner sum over j is continuous, then multiply by constant x i
      have h_inner : Continuous (fun A : Matrix ι ι ℝ => ∑ j, A i j * x j) := by
        apply continuous_finsetSum
        intro j _
        have h_ij : Continuous fun A : Matrix ι ι ℝ => A i j :=
          (continuous_apply j).comp (continuous_apply i)
        exact h_ij.mul continuous_const
      exact continuous_const.mul h_inner
    -- Consider the composition ε ↦ entrywiseExp (R + εI)
    have h_path_continuous : Continuous (fun ε : ℝ => entrywiseExp (R + ε • (1 : Matrix ι ι ℝ))) :=
      h_comp_continuous
    -- Compose with the quadratic form to get the scalar function
    have h_quad_path_continuous :
        Continuous (fun ε : ℝ => x ⬝ᵥ (entrywiseExp (R + ε • (1 : Matrix ι ι ℝ))).mulVec x) :=
      h_quad_continuous.comp h_path_continuous
    -- Apply ge_of_tendsto: if f(ε) ≥ 0 eventually and f → f(0), then f(0) ≥ 0
    have h_tendsto : Tendsto (fun ε : ℝ => x ⬝ᵥ (entrywiseExp (R + ε • (1 : Matrix ι ι ℝ))).mulVec
      x)
        (𝓝[Set.Ioi 0] 0) (𝓝 (x ⬝ᵥ (entrywiseExp R).mulVec x)) := by
      -- Use the continuity at 0 to get the right-sided limit
      have h_cont_at_zero : ContinuousAt
          (fun ε : ℝ => x ⬝ᵥ (entrywiseExp (R + ε • (1 : Matrix ι ι ℝ))).mulVec x) (0 : ℝ) :=
        h_quad_path_continuous.continuousAt
      -- Show that the limit value simplifies to the desired form
      have h_limit_simplify : x ⬝ᵥ (entrywiseExp (R + (0 : ℝ) • (1 : Matrix ι ι ℝ))).mulVec x =
                              x ⬝ᵥ (entrywiseExp R).mulVec x := by
        simp only [zero_smul, add_zero]
      -- Convert continuousAt to the right-sided limit
      rw [← h_limit_simplify]
      exact tendsto_nhdsWithin_of_tendsto_nhds h_cont_at_zero.tendsto
    -- Apply ge_of_tendsto: if f(ε) ≥ 0 eventually and f → f(0), then f(0) ≥ 0
    have h_final : 0 ≤ x ⬝ᵥ (entrywiseExp R).mulVec x :=
      ge_of_tendsto h_tendsto (by
        -- Show eventually in 𝓝[Set.Ioi 0] 0, the quadratic form is nonnegative
        apply eventually_nhdsWithin_of_forall
        exact h_nonneg_eps)
    -- Convert from regular inner product to star inner product
    simpa [h_star_eq] using h_final
  -- Convert the result back to entrywiseExpHadamardSeries
  rwa [← entrywiseExp_eq_hadamardSeries]
end OSforGFF
