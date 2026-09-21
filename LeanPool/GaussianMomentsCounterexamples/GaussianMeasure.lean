/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Algebra.MvPolynomial.Eval

/-! The canonical Gaussian probability space and its polynomial integrability.
All expectations in this development are genuine Bochner integrals. -/

@[expose] public section


noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GaussianMomentsCounterexamples

/-- The law of `n` independent standard real Gaussian coordinates. -/
def gaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (n : ℕ) : IsProbabilityMeasure (gaussianMeasure n) := by
  unfold gaussianMeasure
  infer_instance

/-- Evaluate a complex polynomial on real coordinates. -/
def realEval {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) : ℂ :=
  MvPolynomial.eval (fun i => (x i : ℂ)) P

/-- Genuine Gaussian expectation of a complex polynomial. -/
def expectation {n : ℕ} (P : MvPolynomial (Fin n) ℂ) : ℂ :=
  ∫ x, realEval P x ∂gaussianMeasure n

lemma integrable_real_pow (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  exact integrable_pow_of_mem_interior_integrableExpSet (by simp) k

lemma integrable_complex_pow (k : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ k) (gaussianReal 0 1) := by
  simpa using (integrable_real_pow k).ofReal (𝕜 := ℂ)

lemma realEval_monomial {n : ℕ} (d : Fin n →₀ ℕ) (c : ℂ) (x : Fin n → ℝ) :
    realEval (MvPolynomial.monomial d c) x = c * ∏ i, (x i : ℂ) ^ d i := by
  simp [realEval, MvPolynomial.eval_monomial, Finsupp.prod_fintype]

/-- Every complex polynomial, including every mixed power, is integrable. -/
theorem integrable_realEval {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    Integrable (realEval P) (gaussianMeasure n) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    change Integrable (fun x => realEval (MvPolynomial.monomial d c) x) _
    simp_rw [realEval_monomial]
    exact (Integrable.fintype_prod (fun i => integrable_complex_pow (d i))).const_mul c
  | add P Q hP hQ =>
    have heq : realEval (P + Q) = realEval P + realEval Q := by
      funext x
      exact MvPolynomial.eval_add
    rw [heq]
    exact hP.add hQ

/-- The conjecture with its actual eventual-vanishing quantifiers. -/
def GMC (n : ℕ) : Prop :=
  ∀ P : MvPolynomial (Fin n) ℂ,
    (∀ m : ℕ, 1 ≤ m → expectation (P ^ m) = 0) →
    ∀ Q : MvPolynomial (Fin n) ℂ,
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → expectation (Q * P ^ m) = 0

@[simp] theorem expectation_add {n : ℕ} (P Q : MvPolynomial (Fin n) ℂ) :
    expectation (P + Q) = expectation P + expectation Q := by
  simp only [expectation, realEval, MvPolynomial.eval_add]
  exact integral_add (integrable_realEval P) (integrable_realEval Q)

@[simp] theorem expectation_C_mul {n : ℕ} (c : ℂ) (P : MvPolynomial (Fin n) ℂ) :
    expectation (MvPolynomial.C c * P) = c * expectation P := by
  simp only [expectation, realEval, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  exact integral_const_mul _ _

/-- Independent-coordinate factorization, with integrability established above. -/
theorem expectation_monomial {n : ℕ} (d : Fin n →₀ ℕ) (c : ℂ) :
    expectation (MvPolynomial.monomial d c) =
      c * ∏ i, ∫ x : ℝ, (x : ℂ) ^ d i ∂gaussianReal 0 1 := by
  simp only [expectation, realEval_monomial, gaussianMeasure]
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (fun i (x : ℝ) => (x : ℂ) ^ d i)

@[simp] theorem expectation_zero {n : ℕ} : expectation (0 : MvPolynomial (Fin n) ℂ) = 0 := by
  simp [expectation, realEval]

@[simp] theorem expectation_C {n : ℕ} (c : ℂ) :
    expectation (MvPolynomial.C c : MvPolynomial (Fin n) ℂ) = c := by
  simp [expectation, realEval]

@[simp] theorem expectation_one {n : ℕ} : expectation (1 : MvPolynomial (Fin n) ℂ) = 1 := by
  simp [expectation, realEval]

@[simp] theorem expectation_sub {n : ℕ} (P Q : MvPolynomial (Fin n) ℂ) :
    expectation (P - Q) = expectation P - expectation Q := by
  simp only [expectation, realEval, map_sub]
  exact integral_sub (integrable_realEval P) (integrable_realEval Q)

@[simp] theorem expectation_smul {n : ℕ} (c : ℂ) (P : MvPolynomial (Fin n) ℂ) :
    expectation (c • P) = c * expectation P := by
  rw [MvPolynomial.smul_eq_C_mul, expectation_C_mul]

/-- A single coordinate has the standard real Gaussian moments. -/
theorem expectation_X_pow {n : ℕ} (i : Fin n) (k : ℕ) :
    expectation ((MvPolynomial.X i : MvPolynomial (Fin n) ℂ) ^ k) =
      ∫ x : ℝ, (x : ℂ) ^ k ∂gaussianReal 0 1 := by
  simp only [expectation, realEval, map_pow, MvPolynomial.eval_X, gaussianMeasure]
  exact integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1) (i := i)
    (integrable_complex_pow k).aestronglyMeasurable

/-- The integral is a complex-linear functional on the entire polynomial ring. -/
def expectationLinear (n : ℕ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun := expectation
  map_add' := expectation_add
  map_smul' c P := by
    simpa only [MvPolynomial.smul_eq_C_mul, smul_eq_mul, RingHom.id_apply]
      using expectation_C_mul c P

@[simp] theorem expectation_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial (Fin n) ℂ) :
    expectation (∑ i ∈ s, P i) = ∑ i ∈ s, expectation (P i) :=
  map_sum (expectationLinear n) P s

end GaussianMomentsCounterexamples
