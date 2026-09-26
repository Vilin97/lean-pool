/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.AlgebraicMoments
public import LeanPool.GaussianMomentsCounterexamples.ComplexContractions
public import Mathlib.Data.Finset.Order

/-! Elementary weight arguments in dimension two. No claim resolving GMC(2). -/

public section
noncomputable section
open MvPolynomial Finset
open scoped BigOperators Pointwise
namespace GaussianMomentsCounterexamples

/-- Natural coordinates [W,Z] for one normalized complex Gaussian pair. -/
@[expose] def pairSub : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  aeval ![normalizedW 0 1, normalizedZ 0 1]

/-- Actual Gaussian expectation expressed in the two natural complex coordinates. -/
@[expose] def pairExpectation : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] ℂ :=
  (expectationLinear 2).comp pairSub.toLinearMap

@[simp] theorem pairExpectation_monomial (d : Fin 2 →₀ ℕ) (c : ℂ) :
    pairExpectation (monomial d c) = c * pairMoment (d 0) (d 1) := by
  change expectation (pairSub (monomial d c)) = _
  have he : pairSub (monomial d c) = C c * (normalizedW 0 1 ^ d 0 * normalizedZ 0 1 ^ d 1) := by
    simp [pairSub, aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_succ]
  rw [he, expectation_C_mul, expectation_pair (by decide : (0 : Fin 2) ≠ 1)]
  rfl

/-- Z has weight +1 and W has weight -1; sign reverses the chosen direction. -/
def signedWeight (sign : ℤ) (d : Fin 2 →₀ ℕ) : ℤ := sign * ((d 1 : ℤ) - d 0)

lemma signedWeight_add (sign : ℤ) (d e : Fin 2 →₀ ℕ) :
    signedWeight sign (d + e) = signedWeight sign d + signedWeight sign e := by
  simp only [signedWeight, Finsupp.add_apply, Nat.cast_add]
  ring

/-- Expectation kills any polynomial with no weight-zero monomials. -/
theorem pairExpectation_eq_zero_of_no_balanced (P : MvPolynomial (Fin 2) ℂ)
    (hP : ∀ d ∈ P.support, d 0 ≠ d 1) : pairExpectation P = 0 := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  simp [hP d hd, pairMoment]

/-- Every polynomial supported in one nonzero weight has zero expectation. -/
theorem pairExpectation_eq_zero_of_weight (P : MvPolynomial (Fin 2) ℂ) (w : ℤ)
    (hw : w ≠ 0) (hP : ∀ d ∈ P.support, signedWeight 1 d = w) :
    pairExpectation P = 0 := by
  apply pairExpectation_eq_zero_of_no_balanced
  intro d hd he
  have h := hP d hd
  simp [signedWeight, he] at h
  exact hw h.symm

/-- Every supported monomial has signed weight at least the given bound. -/
def WeightLowerBound (sign : ℤ) (P : MvPolynomial (Fin 2) ℂ) (k : ℤ) : Prop :=
  ∀ d ∈ P.support, k ≤ signedWeight sign d

lemma weightLowerBound_mul (sign : ℤ) (P Q : MvPolynomial (Fin 2) ℂ) (a b : ℤ)
    (hP : WeightLowerBound sign P a) (hQ : WeightLowerBound sign Q b) :
    WeightLowerBound sign (P * Q) (a + b) := by
  intro d hd
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul P Q hd)
  rw [signedWeight_add]
  exact add_le_add (hP u hu) (hQ v hv)

lemma weightLowerBound_pow (sign : ℤ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : WeightLowerBound sign P 1) (m : ℕ) : WeightLowerBound sign (P ^ m) m := by
  induction m with
  | zero =>
    intro d hd
    simp only [pow_zero, support_one, mem_singleton] at hd
    subst d
    simp [signedWeight]
  | succ m ih =>
    simpa only [pow_succ, Nat.cast_add,
      Nat.cast_one] using weightLowerBound_mul sign (P^m) P m 1 ih hP

/-- Strictly positive weights, or strictly negative weights by sign=-1, give eventual vanishing
for every polynomial multiplier. All expectations here are actual Gaussian integrals. -/
theorem one_sided_eventual_vanishing (sign : ℤ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : WeightLowerBound sign P 1) (Q : MvPolynomial (Fin 2) ℂ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → pairExpectation (Q * P ^ m) = 0 := by
  classical
  obtain ⟨M, hM⟩ := (Q.support.image (fun d => -signedWeight sign d)).exists_le
  have hQ : WeightLowerBound sign Q (-M) := by
    intro d hd
    have := hM _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
    omega
  refine ⟨M.toNat + 1, fun m hm => ?_⟩
  apply pairExpectation_eq_zero_of_no_balanced
  intro d hd he
  have hb := weightLowerBound_mul sign Q (P^m) (-M) m hQ (weightLowerBound_pow sign P hP m) d hd
  have hMnat : M ≤ (M.toNat : ℤ) := by omega
  simp only [signedWeight, he, sub_self, mul_zero] at hb
  omega

/-- The inverse linear substitution ensures one-sided claims cover arbitrary multipliers
in the original real-coordinate polynomial ring as well. -/
def pairInverseSub : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  aeval ![C normalization * (X 0 + X 1), C (Complex.I * normalization) * (X 0 - X 1)]

lemma pairSub_pairInverseSub : pairSub.comp pairInverseSub = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [pairInverseSub, pairSub] using recoverX (0 : Fin 2) 1
  · simpa [pairInverseSub, pairSub] using recoverY (0 : Fin 2) 1

/-- Original-coordinate multipliers also vanish eventually for a polynomial
supported strictly on one side of the weight grading in complex coordinates. -/
theorem one_sided_eventual_vanishing_real (sign : ℤ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : WeightLowerBound sign P 1) (Q : MvPolynomial (Fin 2) ℂ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → expectation (Q * (pairSub P) ^ m) = 0 := by
  obtain ⟨N, hN⟩ := one_sided_eventual_vanishing sign P hP (pairInverseSub Q)
  refine ⟨N, fun m hm => ?_⟩
  have h := hN m hm
  change expectation (pairSub (pairInverseSub Q * P ^ m)) = 0 at h
  rw [map_mul, map_pow] at h
  have he : pairSub (pairInverseSub Q) = Q :=
    DFunLike.congr_fun pairSub_pairInverseSub Q
  rwa [he] at h

end GaussianMomentsCounterexamples
