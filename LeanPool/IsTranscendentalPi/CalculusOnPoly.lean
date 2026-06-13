/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Huang, Samuël Borza
-/
import LeanPool.IsTranscendentalPi.ComplexExponential

/-!
# Calculus on polynomials

The integral `∫₀¹ x · exp(-(t · x)) · T(t · x) dt` and the polynomial `∑ᵢ T⁽ⁱ⁾`,
together with the calculus identities relating them for Niven's argument.
-/

open Polynomial
open Complex

open scoped Polynomial
open scoped BigOperators

noncomputable section

/-- The integral `∫₀¹ x * exp(-(t * x)) * T(t * x) dt`. -/
def intExpNegPoly (T : ℤ[X]) (x : ℂ) : ℂ :=
  ∫ t in 0..1, (fun (t : ℝ) => x * cexp (-(t * x)) * aeval (t * x) T) t

/-- The polynomial `∑ᵢ₌₀ᵈ T⁽ⁱ⁾` with `d = deg(T)`. -/
def sumDeriv {R : Type*} [Semiring R] (T : R[X]) : R[X] :=
  ∑ i ∈ Finset.range (T.natDegree + 1), derivative^[i] T

/-- The `k`-th derivative of `z ↦ T(z)` is `z ↦ T⁽ᵏ⁾(z)`. -/
lemma iteratedDeriv_aeval_fun (T : ℤ[X]) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => aeval z T) = fun z => aeval z (derivative^[k] T) := by
  induction k with
  | zero =>
      funext z
      simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      simp [Function.iterate_succ_apply', Polynomial.deriv_aeval]

/-- The equality `∫₀¹ x * exp(-(t x)) * T(t x) dt = ∑ᵢ₌₀ᵈ T⁽ⁱ⁾(0) - e^(-x) * ∑ᵢ₌₀ᵈ T⁽ⁱ⁾(x)`. -/
lemma int_exp_neg_mul_poly
  (T : ℤ[X]) (x : ℂ) :
    intExpNegPoly T x = aeval 0 (sumDeriv T) - cexp (-x) * aeval x (sumDeriv T) := by
  have hderiv_zero : derivative^[T.natDegree + 1] T = 0 :=
    iterate_derivative_eq_zero (p := T) (x := T.natDegree + 1) (Nat.lt_succ_self _)
  have hderiv_zero' : derivative^[1 + T.natDegree] T = 0 := by
    simpa [Nat.add_comm] using hderiv_zero
  have hderiv : ∀ k ≤ T.natDegree + 1, ∀ t ∈ Set.uIcc (0:ℝ) 1,
        DifferentiableAt ℂ (iteratedDeriv k (fun z : ℂ => aeval z (-T))) (t * x) := by
    intro k hk t ht
    simpa only [iteratedDeriv_aeval_fun] using
      ((derivative^[k] (-T)).differentiableAt_aeval (x := t * x))
  have h := int_exp_neg_mul_fun (fun z : ℂ => aeval z (-T)) x T.natDegree hderiv
  rw [intExpNegPoly]
  simpa [iteratedDeriv_aeval_fun, hderiv_zero', sumDeriv, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc] using h

/-- If the multiplicity of `a` is `≥ m`, then `∑ᵢ₌₀ᵈ T⁽ⁱ⁾(a) = ∑ᵢ₌ₘᵈ T⁽ⁱ⁾(a)`. -/
lemma aeval_sumDeriv_eq_sum_Icc
    (T : ℤ[X]) (a : ℂ) (m : ℕ) (hm : m ≤ rootMultiplicity a (T.map (algebraMap ℤ ℂ))) :
    aeval a (sumDeriv T)
      = ∑ i ∈ Finset.Icc m T.natDegree, aeval a ((derivative^[i]) T) := by
  simp only [sumDeriv, map_sum]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hi).2)
  · intro i hi hnot
    have hi_lt_root : i < rootMultiplicity a (T.map (algebraMap ℤ ℂ)) :=
      lt_of_not_ge fun him =>
        hnot (Finset.mem_Icc.mpr ⟨hm.trans him, Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)⟩)
    have hroot : ((derivative^[i]) (T.map (algebraMap ℤ ℂ))).IsRoot a :=
      isRoot_iterate_derivative_of_lt_rootMultiplicity hi_lt_root
    simpa [aeval_def, eval₂_eq_eval_map, IsRoot, iterate_derivative_map] using hroot

/-- On the segment `0 < t ≤ 1`, the values `‖T(t a)‖` are bounded above by a real constant. -/
lemma T_bounded
  (T : ℤ[X]) (a : ℂ) : ∃ M : ℝ, ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖aeval (t * a) T‖ ≤ M := by
  have hcont : Continuous (fun t : ℝ => aeval (t * a) T) := by
    have hmul : Continuous (fun t : ℝ => (t : ℂ) * a) :=
      Complex.continuous_ofReal.mul continuous_const
    exact T.continuous_aeval.comp hmul
  obtain ⟨M, hM⟩ := (isCompact_uIcc : IsCompact (Set.uIcc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hcont.continuousOn
  exact ⟨M, fun t ht => hM t (Set.uIoc_subset_uIcc ht)⟩
