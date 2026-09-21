/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.GaussianStein
public import LeanPool.GaussianMomentsCounterexamples.Coordinates

/-! Normalized complex Gaussian contractions, derived from real Gaussian Stein identities. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
namespace GaussianMomentsCounterexamples

/-- Differentiation with respect to Z in the invertible (W,Z) coordinates. -/
def derivZ {n : ℕ} (i j : Fin n) : Derivation ℂ (MvPolynomial (Fin n) ℂ)
    (MvPolynomial (Fin n) ℂ) :=
  normalization • (pderiv i - Complex.I • pderiv j)

/-- Differentiation with respect to W in the invertible (W,Z) coordinates. -/
def derivW {n : ℕ} (i j : Fin n) : Derivation ℂ (MvPolynomial (Fin n) ℂ)
    (MvPolynomial (Fin n) ℂ) :=
  normalization • (pderiv i + Complex.I • pderiv j)

theorem expectation_normalizedW_mul {n : ℕ} (i j : Fin n)
    (P : MvPolynomial (Fin n) ℂ) :
    expectation (normalizedW i j * P) = expectation (derivZ i j P) := by
  simp only [normalizedW, derivZ, Derivation.smul_apply, Derivation.sub_apply,
    expectation_smul, expectation_sub]
  rw [mul_assoc, sub_mul, mul_assoc, expectation_C_mul, expectation_sub,
    expectation_C_mul, expectation_X_mul, expectation_X_mul]

theorem expectation_normalizedZ_mul {n : ℕ} (i j : Fin n)
    (P : MvPolynomial (Fin n) ℂ) :
    expectation (normalizedZ i j * P) = expectation (derivW i j P) := by
  simp only [normalizedZ, derivW, Derivation.smul_apply, Derivation.add_apply,
    expectation_smul, expectation_add]
  rw [mul_assoc, add_mul, mul_assoc, expectation_C_mul, expectation_add,
    expectation_C_mul, expectation_X_mul, expectation_X_mul]

@[simp] theorem derivZ_normalizedW {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    derivZ i j (normalizedW i j) = 0 := by
  simp [derivZ, normalizedW, pderiv_X, hij, Ne.symm hij,
    smul_eq_C_mul]
  ring_nf
  simp only [← map_pow, Complex.I_sq, map_neg, map_one, mul_neg, mul_one,
    add_neg_cancel, or_true]

@[simp] theorem derivZ_normalizedZ {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    derivZ i j (normalizedZ i j) = 1 := by
  simp [derivZ, normalizedZ, pderiv_X, hij, Ne.symm hij,
    smul_eq_C_mul]
  ring_nf
  simp only [← map_pow, normalization_sq, Complex.I_sq, map_neg, map_one]
  norm_num [← map_add]

@[simp] theorem derivW_normalizedZ {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    derivW i j (normalizedZ i j) = 0 := by
  simp [derivW, normalizedZ, pderiv_X, hij, Ne.symm hij,
    smul_eq_C_mul]
  ring_nf
  simp only [← map_pow, Complex.I_sq, map_neg, map_one, mul_neg, mul_one,
    add_neg_cancel]

@[simp] theorem derivW_normalizedW {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    derivW i j (normalizedW i j) = 1 := by
  simp [derivW, normalizedW, pderiv_X, hij, Ne.symm hij,
    smul_eq_C_mul]
  ring_nf
  simp only [← map_pow, normalization_sq, Complex.I_sq, map_neg, map_one]
  norm_num [← map_add]

/-- Balanced contractions, allowing any residual polynomial independent of this pair.
The two derivative hypotheses express independence of the polynomial coordinates,
not moment assumptions. -/
theorem expectation_pair_mul {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a b : ℕ) (R : MvPolynomial (Fin n) ℂ)
    (hRZ : derivZ i j R = 0) (hRW : derivW i j R = 0) :
    expectation (normalizedW i j ^ a * normalizedZ i j ^ b * R) =
      (if a = b then (a.factorial : ℂ) else 0) * expectation R := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simp
    | succ b =>
      rw [pow_zero, one_mul, pow_succ', mul_assoc, expectation_normalizedZ_mul]
      simp [Derivation.leibniz, Derivation.leibniz_pow, derivW_normalizedZ hij, hRW]
  | succ a ih =>
    rw [pow_succ', mul_assoc, mul_assoc, expectation_normalizedW_mul]
    cases b with
    | zero =>
      simp [Derivation.leibniz, Derivation.leibniz_pow, derivZ_normalizedW hij, hRZ]
    | succ b =>
      have hd : derivZ i j (normalizedW i j ^ a * (normalizedZ i j ^ (b + 1) * R)) =
          (b + 1 : ℂ) • (normalizedW i j ^ a * normalizedZ i j ^ b * R) := by
        simp [Derivation.leibniz, Derivation.leibniz_pow, derivZ_normalizedW hij,
          derivZ_normalizedZ hij, hRZ, smul_eq_C_mul,
          mul_assoc]
        ring
      rw [hd, expectation_smul, ih]
      by_cases hab : a = b
      · subst b
        simp [Nat.factorial_succ, mul_assoc]
      · simp [hab]

/-- The manuscript's normalized complex Gaussian contraction in any distinct pair. -/
theorem expectation_pair {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a b : ℕ) :
    expectation (normalizedW i j ^ a * normalizedZ i j ^ b) =
      if a = b then (a.factorial : ℂ) else 0 := by
  simpa using expectation_pair_mul hij a b 1 (by simp) (by simp)

end GaussianMomentsCounterexamples
