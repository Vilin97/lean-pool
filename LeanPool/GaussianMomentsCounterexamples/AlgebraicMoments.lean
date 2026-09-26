/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.RealMoments
public import LeanPool.GaussianMomentsCounterexamples.Coordinates
public import LeanPool.GaussianMomentsCounterexamples.CoefficientIdentities
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Algebraic Gaussian moment functionals and their coefficient identities. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial Finset
open scoped BigOperators
namespace GaussianMomentsCounterexamples

/-- The contraction of a normalized conjugate Gaussian pair. -/
@[expose] def pairMoment (a b : ℕ) : ℂ := if a = b then (a.factorial : ℂ) else 0

/-- Linear extension from monomials of the three-coordinate Gaussian moments. -/
def naturalMoment3 : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun d : Fin 3 →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ).symm
      (pairMoment (d 0) (d 1) * ∫ t : ℝ, (t : ℂ) ^ d 2 ∂gaussianReal 0 1))
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

/-- Linear extension from monomials for two independent normalized conjugate pairs. -/
def naturalMoment4 : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun d : Fin 4 →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ).symm
      (pairMoment (d 0) (d 1) * pairMoment (d 2) (d 3)))
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem naturalMoment3_monomial (d : Fin 3 →₀ ℕ) (c : ℂ) :
    naturalMoment3 (monomial d c) = c *
      (pairMoment (d 0) (d 1) * ∫ t : ℝ, (t : ℂ) ^ d 2 ∂gaussianReal 0 1) :=
  sum_monomial_eq <| map_zero _

@[simp] theorem naturalMoment4_monomial (d : Fin 4 →₀ ℕ) (c : ℂ) :
    naturalMoment4 (monomial d c) = c * (pairMoment (d 0) (d 1) * pairMoment (d 2) (d 3)) :=
  sum_monomial_eq <| map_zero _

/-- Embed a univariate polynomial in one specified natural coordinate. -/
def polyAt {n : ℕ} (i : Fin n) : Polynomial ℂ →+* MvPolynomial (Fin n) ℂ :=
  Polynomial.eval₂RingHom C (X i)

@[simp] theorem polyAt_monomial {n : ℕ} (i : Fin n) (k : ℕ) (c : ℂ) :
    polyAt i (Polynomial.monomial k c) = C c * X i ^ k := by
  exact Polynomial.eval₂_monomial C (X i)

@[simp] theorem polyAt_X {n : ℕ} (i : Fin n) : polyAt i Polynomial.X = X i := by
  exact Polynomial.eval₂_X C (X i)

@[simp] theorem naturalMoment3_C_mul (c : ℂ) (p : MvPolynomial (Fin 3) ℂ) :
    naturalMoment3 (C c * p) = c * naturalMoment3 p := by
  simpa only [← smul_eq_C_mul, smul_eq_mul] using naturalMoment3.map_smul c p

@[simp] theorem naturalMoment4_C_mul (c : ℂ) (p : MvPolynomial (Fin 4) ℂ) :
    naturalMoment4 (C c * p) = c * naturalMoment4 p := by
  simpa only [← smul_eq_C_mul, smul_eq_mul] using naturalMoment4.map_smul c p

theorem naturalMoment3_contraction (a b : ℕ) (f : Polynomial ℂ) :
    naturalMoment3 (X 0 ^ a * polyAt 1 f * X 2 ^ b) =
      (a.factorial : ℂ) * f.coeff a * ∫ t : ℝ, (t : ℂ) ^ b ∂gaussianReal 0 1 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, mul_add, add_mul, hp, hq, Polynomial.coeff_add]
  | monomial k c =>
    rw [polyAt_monomial]
    simp only [X, monomial_pow, C_mul_monomial, monomial_mul_monomial,
      naturalMoment3_monomial, one_pow, one_mul, mul_one, Finsupp.smul_single,
      smul_eq_mul]
    simp [pairMoment, Polynomial.coeff_monomial, eq_comm]
    split_ifs <;> simp_all; ring

theorem naturalMoment4_contraction (a b : ℕ) (f g : Polynomial ℂ) :
    naturalMoment4 (X 0 ^ a * polyAt 1 f * X 2 ^ b * polyAt 3 g) =
      ((a.factorial : ℂ) * f.coeff a) * ((b.factorial : ℂ) * g.coeff b) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, mul_add, add_mul, hp, hq, Polynomial.coeff_add]
  | monomial k c =>
    induction g using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [map_add, mul_add, hp, hq, Polynomial.coeff_add]
    | monomial l d =>
      rw [polyAt_monomial, polyAt_monomial]
      simp only [X, monomial_pow, C_mul_monomial, monomial_mul_monomial,
        naturalMoment4_monomial, one_pow, one_mul, mul_one, Finsupp.smul_single,
        smul_eq_mul]
      simp [pairMoment, Polynomial.coeff_monomial, eq_comm]
      split_ifs <;> simp_all; ring

lemma coeff_one_sub_X_pow (a : ℕ) :
    ((1 - Polynomial.X : Polynomial ℂ) ^ a).coeff a = (-1 : ℂ) ^ a := by
  have h := Polynomial.coeff_pow_of_natDegree_le
    (p := (1 - Polynomial.X : Polynomial ℂ)) (n := 1) (by compute_degree) (m := a)
  simpa [Polynomial.coeff_one] using h

theorem naturalMoment4_power_expansion (A : Polynomial ℂ) (m : ℕ) :
    naturalMoment4 (polyAt 3 A * naturalP4 ^ m) =
      (m.factorial : ℂ) * ∑ a ∈ Finset.range (m + 1),
        (-1 : ℂ) ^ a * (A * (1 + Polynomial.X) ^ m).coeff (m - a) := by
  unfold naturalP4
  rw [mul_pow, add_pow (X 0 * (1 - X 1)) (X 2) m, mul_sum, mul_sum, map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ham : a ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  have hterm : polyAt 3 A * ((1 + X 3) ^ m *
      ((X 0 * (1 - X 1)) ^ a * X 2 ^ (m - a) * (m.choose a : MvPolynomial (Fin 4) ℂ))) =
      C (m.choose a : ℂ) *
        (X 0 ^ a * polyAt 1 ((1 - Polynomial.X) ^ a) * X 2 ^ (m - a) *
          polyAt 3 (A * (1 + Polynomial.X) ^ m)) := by
    simp only [map_mul, map_pow, map_add, map_sub, map_one, polyAt_X, map_natCast]
    rw [mul_pow]
    ring
  rw [hterm, naturalMoment4_C_mul, naturalMoment4_contraction, coeff_one_sub_X_pow]
  have hf : (m.choose a : ℂ) * (a.factorial : ℂ) * ((m-a).factorial : ℂ) = (m.factorial : ℂ)
    := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial ham
  linear_combination (-1 : ℂ)^a * (A * (1 + Polynomial.X)^m).coeff (m-a) * hf

/-- The four-variable master identity in the natural-coordinate moment interface. -/
theorem naturalMoment4_master (A : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    naturalMoment4 (polyAt 3 A * naturalP4 ^ m) =
      (m.factorial : ℂ) * (A * (1 + Polynomial.X) ^ (m - 1)).coeff m := by
  rw [naturalMoment4_power_expansion, coefficient_identity_four A m hm]

theorem naturalMoment3_power_expansion_raw (A : Polynomial ℂ) (m : ℕ) :
    naturalMoment3 (polyAt 1 A * naturalP3 ^ m) =
      ∑ k ∈ range (m + 1), (m.choose k : ℂ) * (-1 / 2 : ℂ) ^ k *
        ((m-k).factorial : ℂ) * (A * (1 + Polynomial.X) ^ m * (2 + Polynomial.X) ^ k).coeff
          (m-k) *
        (((2*k).factorial : ℂ) / (2^k * (k.factorial : ℂ))) := by
  have hp : naturalP3 = (1 + X 1) * (C (-1 / 2) * (2 + X 1) * X 2 ^ 2 + X 0) := by
    unfold naturalP3
    rw [neg_div, map_neg]
    ring
  rw [hp, mul_pow, add_pow (C (-1 / 2) * (2 + X 1) * X 2 ^ 2) (X 0) m,
    mul_sum, mul_sum, map_sum]
  apply sum_congr rfl
  intro k hk
  have hterm : polyAt 1 A * ((1 + X 1) ^ m *
      ((C (-1 / 2) * (2 + X 1) * X 2 ^ 2) ^ k * X 0 ^ (m-k) *
        (m.choose k : MvPolynomial (Fin 3) ℂ))) =
      C ((m.choose k : ℂ) * (-1 / 2 : ℂ)^k) *
        (X 0 ^ (m-k) * polyAt 1 (A * (1 + Polynomial.X)^m * (2 + Polynomial.X)^k) *
          X 2 ^ (2*k)) := by
    simp only [map_mul, map_pow, map_add, map_one, polyAt_X, map_ofNat, map_natCast, mul_pow,
      pow_mul]
    ring
  rw [hterm, naturalMoment3_C_mul, naturalMoment3_contraction, complex_gaussian_even_moment]
  ring

theorem naturalMoment3_power_expansion (A : Polynomial ℂ) (m : ℕ) :
    naturalMoment3 (polyAt 1 A * naturalP3 ^ m) =
      (m.factorial : ℂ) * ∑ k ∈ range (m + 1),
        ((-1 : ℂ) ^ k / 4 ^ k * ((2*k).choose k : ℂ)) *
          (A * (1 + Polynomial.X)^m * (2 + Polynomial.X)^k).coeff (m-k) := by
  rw [naturalMoment3_power_expansion_raw, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hs := three_moment_scalar m k (Nat.le_of_lt_succ (mem_range.mp hk))
  linear_combination (A * (1 + Polynomial.X)^m * (2 + Polynomial.X)^k).coeff (m-k) * hs

/-- The three-variable master identity in the natural-coordinate moment interface. -/
theorem naturalMoment3_master (A : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    naturalMoment3 (polyAt 1 A * naturalP3 ^ m) =
      (m.factorial : ℂ) * (A * (1 + Polynomial.X) ^ (m - 1)).coeff m := by
  rw [naturalMoment3_power_expansion, coefficient_identity_three A m hm]

@[simp] theorem naturalMoment3_positive_power (m : ℕ) (hm : 1 ≤ m) :
    naturalMoment3 (naturalP3 ^ m) = 0 := by
  have h := naturalMoment3_master 1 m hm
  rw [master_coefficient_one m hm, mul_zero] at h
  simpa only [map_one, one_mul] using h

@[simp] theorem naturalMoment4_positive_power (m : ℕ) (hm : 1 ≤ m) :
    naturalMoment4 (naturalP4 ^ m) = 0 := by
  have h := naturalMoment4_master 1 m hm
  rw [master_coefficient_one m hm, mul_zero] at h
  simpa only [map_one, one_mul] using h

@[simp] theorem naturalMoment3_mixed_power (m : ℕ) (hm : 1 ≤ m) :
    naturalMoment3 (X 1 * naturalP3 ^ m) = (m.factorial : ℂ) := by
  have h := naturalMoment3_master Polynomial.X m hm
  simpa only [polyAt_X, master_coefficient_X m hm, mul_one] using h

@[simp] theorem naturalMoment4_mixed_power (m : ℕ) (hm : 1 ≤ m) :
    naturalMoment4 (X 3 * naturalP4 ^ m) = (m.factorial : ℂ) := by
  have h := naturalMoment4_master Polynomial.X m hm
  simpa only [polyAt_X, master_coefficient_X m hm, mul_one] using h

end GaussianMomentsCounterexamples
