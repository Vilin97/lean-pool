/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.Counterexamples
public import LeanPool.GaussianMomentsCounterexamples.Discovery

/-! Coefficientwise exponential generating functions of genuine Gaussian moments.
No analytic exponential integrability or infinite-sum/integral interchange is asserted. -/

public section
noncomputable section
namespace GaussianMomentsCounterexamples

/-- The formal exponential generating function of the Gaussian moments of a polynomial. -/
def momentEGF {n : ℕ} (P : MvPolynomial (Fin n) ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun m => expectation (P ^ m) / (m.factorial : ℂ)

/-- The formal generating function for mixed Gaussian moments. -/
def mixedMomentEGF {n : ℕ} (Q P : MvPolynomial (Fin n) ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun m => expectation (Q * P ^ m) / (m.factorial : ℂ)

lemma momentEGF_eq_one {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (h : ∀ m : ℕ, 1 ≤ m → expectation (P ^ m) = 0) : momentEGF P = 1 := by
  ext m
  cases m with
  | zero => simp [momentEGF]
  | succ m => simp [momentEGF, h (m + 1) (by omega)]

lemma mixedMomentEGF_eq_branch {n : ℕ} (Q P : MvPolynomial (Fin n) ℂ)
    (h0 : expectation Q = 0)
    (h : ∀ m : ℕ, 1 ≤ m → expectation (Q * P ^ m) = (m.factorial : ℂ)) :
    mixedMomentEGF Q P = branchZeta := by
  ext m
  cases m with
  | zero => simp [mixedMomentEGF, branchZeta, h0]
  | succ m =>
    have hf : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
    simp [mixedMomentEGF, h (m + 1) (by omega), hf, branchZeta]

@[simp] theorem expectation_Q3 : expectation Q3 = 0 := by
  simpa [Q3] using expectation_pair (n := 3) (i := 0) (j := 1) (by decide) 0 1

@[simp] theorem expectation_Q4 : expectation Q4 = 0 := by
  simpa [Q4] using expectation_pair (n := 4) (i := 2) (j := 3) (by decide) 0 1

/-- The displayed formal identity E(exp(t P₃)) = 1. -/
theorem P3_momentEGF : momentEGF P3 = 1 := momentEGF_eq_one P3 P3_moment

/-- The displayed formal identity E(exp(t P₄)) = 1. -/
theorem P4_momentEGF : momentEGF P4 = 1 := momentEGF_eq_one P4 P4_moment

/-- The displayed formal identity E(Q₃ exp(t P₃)) = t/(1-t). -/
theorem Q3_P3_mixedMomentEGF : mixedMomentEGF Q3 P3 =
    PowerSeries.X * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ := by
  rw [← branchZeta_eq]
  exact mixedMomentEGF_eq_branch Q3 P3 expectation_Q3 Q3_P3_moment

/-- The displayed formal identity E(Q₄ exp(t P₄)) = t/(1-t). -/
theorem Q4_P4_mixedMomentEGF : mixedMomentEGF Q4 P4 =
    PowerSeries.X * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ := by
  rw [← branchZeta_eq]
  exact mixedMomentEGF_eq_branch Q4 P4 expectation_Q4 Q4_P4_moment

/-- The explicit discovery vector field produces exactly the four-variable polynomial. -/
theorem naturalP4_discovery_correspondence : naturalP4 =
    MvPolynomial.X 0 * MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 3]
      (discoveryHPolynomial 0) +
    MvPolynomial.X 2 * MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 3]
      (discoveryHPolynomial 1) := by
  simp [naturalP4, discoveryHPolynomial]
  ring

end GaussianMomentsCounterexamples
