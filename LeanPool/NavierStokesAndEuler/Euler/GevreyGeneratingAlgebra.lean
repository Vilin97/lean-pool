/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyCompositionPartitions
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Tactic.Measurability.Init

/-! Finite polynomial majorants for factorial-square Taylor coefficients.
The polynomials below are auxiliary nonnegative scalar polynomials.  Their
composition is the exact scalar Faà di Bruno sum, not an assumed majorant
for a flow or for a solution of a differential equation. -/

@[expose] public section


noncomputable section

open scoped BigOperators ContDiff Polynomial

namespace EulerGevreyGeneratingAlgebra

open EulerGevreyComposition

lemma factorialProduct_nonneg {n : ℕ} (c : OrderedFinpartition n) :
    0 ≤ factorialProduct c :=
  Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _

/-- The factorial used by an ordered partition never exceeds the total
factorial.  This is the extra factor available in Gevrey order two. -/
theorem partition_factorial_le {n : ℕ} (c : OrderedFinpartition n) :
    (c.length.factorial : ℝ) * factorialProduct c ≤ n.factorial := by
  induction n with
  | zero =>
      have hc : c = default := Subsingleton.elim _ _
      subst c
      simp [OrderedFinpartition.default_eq, factorialProduct]
  | succ n ih =>
      obtain ⟨⟨d,o⟩,rfl⟩ := (OrderedFinpartition.extendEquiv n).surjective c
      cases o with
      | none =>
          simp only [OrderedFinpartition.extendEquiv_apply,
            OrderedFinpartition.extend_none, OrderedFinpartition.extendLeft_length,
            factorialProduct_extendLeft]
          have hl : (d.length : ℝ) + 1 ≤ (n : ℝ) + 1 := by
            exact_mod_cast Nat.succ_le_succ d.length_le
          calc
            _ = ((d.length : ℝ)+1) * ((d.length.factorial : ℝ)*factorialProduct d) := by
              simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
              ring
            _ ≤ ((n : ℝ)+1) * (n.factorial : ℝ) :=
              mul_le_mul hl (ih d)
                (mul_nonneg (Nat.cast_nonneg _) (factorialProduct_nonneg d)) (by positivity)
            _ = _ := by simp [Nat.factorial_succ]
      | some i =>
          simp only [OrderedFinpartition.extendEquiv_apply,
            OrderedFinpartition.extend_some, OrderedFinpartition.extendMiddle_length,
            factorialProduct_extendMiddle]
          have hl : (d.partSize i : ℝ)+1 ≤ (n : ℝ)+1 := by
            exact_mod_cast Nat.succ_le_succ (d.partSize_le i)
          calc
            _ = ((d.partSize i : ℝ)+1) *
                ((d.length.factorial : ℝ)*factorialProduct d) := by ring
            _ ≤ ((n : ℝ)+1) * (n.factorial : ℝ) :=
              mul_le_mul hl (ih d)
                (mul_nonneg (Nat.cast_nonneg _) (factorialProduct_nonneg d)) (by positivity)
            _ = _ := by simp [Nat.factorial_succ]

theorem polynomial_iteratedDeriv (p : ℝ[X]) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => p.eval y) x =
      (Polynomial.derivative^[n] p).eval x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (fun y => p.eval y) =
          fun y => (Polynomial.derivative^[n] p).eval y := funext ih
      rw [he, Polynomial.deriv, Function.iterate_succ_apply']

theorem polynomial_iteratedDeriv_zero (p : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun y => p.eval y) 0 = (n.factorial : ℝ)*p.coeff n := by
  rw [polynomial_iteratedDeriv, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

theorem polynomial_contDiff (p : ℝ[X]) :
    ContDiff ℝ ∞ (fun y : ℝ => p.eval y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (contDiff_const.mul (contDiff_id.pow n) : ContDiff ℝ ∞ (fun y : ℝ => a*y^n))

/-- Exact coefficient version of scalar Faà di Bruno at zero. -/
theorem comp_coefficient (p q : ℝ[X]) (hp : p.coeff 0 = 0) (n : ℕ) :
    (n.factorial : ℝ)*(q.comp p).coeff n =
      ∑ c : OrderedFinpartition n,
        ((c.length.factorial : ℝ)*q.coeff c.length) *
          ∏ i, ((c.partSize i).factorial : ℝ)*p.coeff (c.partSize i) := by
  have hp0 : p.eval 0 = 0 := by rw [← Polynomial.coeff_zero_eq_eval_zero, hp]
  have hc := iteratedDeriv_comp_eq_sum_orderedFinpartition
    ((polynomial_contDiff q).contDiffAt (x := p.eval 0))
    ((polynomial_contDiff p).contDiffAt (x := 0)) (i := n) (ENat.natCast_le_of_coe_top_le_withTop
        le_rfl _)
  have he : (fun y => (q.comp p).eval y) =
      (fun y => q.eval y) ∘ (fun y => p.eval y) := by
    funext y
    simp
  rw [← he, hp0] at hc
  simpa only [polynomial_iteratedDeriv_zero] using hc

/-- A finite scalar polynomial whose constant coefficient is zero. -/
def jetPolynomial (N : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.Icc 1 N, Polynomial.monomial j (a j)

theorem jetPolynomial_coeff (N : ℕ) (a : ℕ → ℝ) (j : ℕ) :
    (jetPolynomial N a).coeff j = if j ∈ Finset.Icc 1 N then a j else 0 := by
  simp [jetPolynomial, Polynomial.coeff_monomial]

@[simp] theorem jetPolynomial_zero (N : ℕ) (a : ℕ → ℝ) :
    (jetPolynomial N a).coeff 0 = 0 := by
  simp [jetPolynomial_coeff]

theorem jetPolynomial_coeff_of_mem (N : ℕ) (a : ℕ → ℝ) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 N) : (jetPolynomial N a).coeff j = a j := by
  simp [jetPolynomial_coeff, hj]

theorem jetPolynomial_eval (N : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    (jetPolynomial N a).eval x = ∑ j ∈ Finset.Icc 1 N, a j*x^j := by
  simp only [jetPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Nonnegative coefficients, given by `∀ n, 0 ≤ p.coeff n`. -/
def NonnegativeCoefficients (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

theorem jetPolynomial_nonnegative (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j ∈ Finset.Icc 1 N, 0 ≤ a j) :
    NonnegativeCoefficients (jetPolynomial N a) := by
  intro j
  rw [jetPolynomial_coeff]
  split_ifs with hj
  · exact ha j hj
  · exact le_rfl

theorem nonnegative_mul {p q : ℝ[X]} (hp : NonnegativeCoefficients p)
    (hq : NonnegativeCoefficients q) : NonnegativeCoefficients (p*q) := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hp _) (hq _)

theorem nonnegative_pow {p : ℝ[X]} (hp : NonnegativeCoefficients p) (n : ℕ) :
    NonnegativeCoefficients (p^n) := by
  induction n with
  | zero => intro j; simp only [pow_zero, Polynomial.coeff_one]; split_ifs <;> norm_num
  | succ n ih => simpa only [pow_succ] using nonnegative_mul ih hp

theorem nonnegative_comp {p q : ℝ[X]} (hp : NonnegativeCoefficients p)
    (hq : NonnegativeCoefficients q) : NonnegativeCoefficients (q.comp p) := by
  intro n
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun j _ => by
    rw [Polynomial.coeff_C_mul]
    exact mul_nonneg (hq _) (nonnegative_pow hp j n)

/-- A partial sum of a nonnegative polynomial is bounded by its actual
evaluation.  No bound on the degree of the composed polynomial is needed. -/
theorem coefficient_sum_le_eval (p : ℝ[X]) (hp : NonnegativeCoefficients p)
    (s : Finset ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∑ j ∈ s, p.coeff j*x^j ≤ p.eval x := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    _ ≤ ∑ j ∈ s ∪ p.support, p.coeff j*x^j :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun j _ _ => mul_nonneg (hp j) (pow_nonneg hx j))
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro j _ hj
      have hz : p.coeff j = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hj
      rw [hz, zero_mul]

end EulerGevreyGeneratingAlgebra
