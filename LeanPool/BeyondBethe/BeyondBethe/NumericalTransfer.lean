/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.NumericalNearby

/-! # Numerical Transfer -/

@[expose] public section

namespace BeyondBethe

/-!
# Certified transfer from an approximate KKT point

The numerical optimizer need not return the exact regularized maximizer for
the input matrix.  It is enough to return an exactly doubly stochastic
interior matrix and row/column potentials satisfying the logarithmic KKT
equations approximately.  The nearby matrix then has those KKT equations
exactly.  This file combines the nearby-matrix comparison with the structural
certificate and records the complete two-sided loss: the transfer costs two
copies of the logarithmic KKT residual.
-/

/-- The logarithm of the one-sided certificate transferred from the nearby
matrix back to the input matrix. -/
noncomputable def nearbyCertificateLog
    {n : ℕ} (error τ : ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (r c : Fin n → ℝ) : ℝ :=
  let A' := nearbyKKTMatrix τ X r c
  betheObjective A' X + maximumMatchingGain A' X - error * n

/-- The positive certificate obtained from an approximate KKT point. -/
noncomputable def nearbyCertificateValue
    {n : ℕ} (error τ : ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (r c : Fin n → ℝ) : ℝ :=
  Real.exp (nearbyCertificateLog error τ X r c)

theorem nearbyCertificateValue_pos
    {n : ℕ} (error τ : ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (r c : Fin n → ℝ) :
    0 < nearbyCertificateValue error τ X r c := by
  exact Real.exp_pos _

/-- An approximate logarithmic KKT certificate loses exactly two copies of
its residual in the final logarithmic approximation: one when comparing the
input permanent to the nearby permanent, and one in the downward shift that
preserves the lower-bound direction. -/
theorem nearbyCertificate_twoSided
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    (s : RationalStructuralScales)
    {n : ℕ} (hn : 2 ≤ n)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {error : ℝ} {r c : Fin n → ℝ}
    (happrox : HasApproximateLogKKT error
      ((rationalRegularizationScale s n : ℚ) : ℝ) A X r c) :
    nearbyCertificateValue error
        ((rationalRegularizationScale s n : ℚ) : ℝ) X r c ≤
        Matrix.permanent A ∧
      Matrix.permanent A ≤
        (Real.sqrt 2 * Real.exp
          (-(((rationalEpsilonPlus s.completion : ℚ) : ℝ) -
            2 * error))) ^ n *
          nearbyCertificateValue error
            ((rationalRegularizationScale s n : ℚ) : ℝ) X r c := by
  let τ : ℝ := ((rationalRegularizationScale s n : ℚ) : ℝ)
  let A' := nearbyKKTMatrix τ X r c
  let F := betheObjective A' X + maximumMatchingGain A' X
  let L := nearbyCertificateValue error τ X r c
  have hXpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  have hXlt : ∀ i j, X i j < 1 := fun i j ↦ (hXint i).2 j |>.2
  have hA' : Matrix.Positive A' := nearbyKKTMatrix_positive hXpos hXlt
  have hτ : 0 ≤ τ := by
    change 0 ≤ (((rationalRegularizationScale s n : ℚ) : ℝ))
    exact_mod_cast (rationalRegularizationScale_pos s (show 0 < n by omega)).le
  have hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A' Y ≤
        regularizedBetheObjective τ A' X := by
    have hcard : 1 < Fintype.card (Fin n) := by
      simpa only [Fintype.card_fin] using (show 1 < n by omega)
    exact nearbyKKTMatrix_exact_optimizer (ι := Fin n) hcard
      hτ hX hXint r c
  have hstruct := rationalScales_certificate_of_optimizer
    stableCoefficient s hn hA' hX hXint hmax
      ⟨r, c, nearbyKKTMatrix_hasLogKKT hXpos hXlt⟩
  have hcompare := approximateLogKKT_permanent_comparison
    hA (by simpa only [τ] using happrox) hXpos hXlt
  have hcompare' :
      (Real.exp (-error)) ^ n * Matrix.permanent A' ≤
          Matrix.permanent A ∧
        Matrix.permanent A ≤
          (Real.exp error) ^ n * Matrix.permanent A' := by
    simpa only [A', τ, Fintype.card_fin] using hcompare
  have hstructLower : Real.exp F ≤ Matrix.permanent A' := by
    simpa only [F] using hstruct.1
  have hstructGap : Real.log (Matrix.permanent A') - F ≤
      (Real.log 2 / 2 -
        ((rationalEpsilonPlus s.completion : ℚ) : ℝ)) * n := by
    simpa only [F] using hstruct.2
  have hperA : 0 < Matrix.permanent A := permanent_pos_of_positive A hA
  have hperA' : 0 < Matrix.permanent A' := permanent_pos_of_positive A' hA'
  have hL : L = Real.exp (F - error * n) := by
    simp only [L, nearbyCertificateValue, nearbyCertificateLog, A', F, τ]
  have hfactor : Real.exp (F - error * n) =
      (Real.exp (-error)) ^ n * Real.exp F := by
    calc
      Real.exp (F - error * n) =
          Real.exp F * Real.exp (-(error * n)) := by
            rw [sub_eq_add_neg, Real.exp_add]
      _ = Real.exp F * Real.exp ((n : ℝ) * (-error)) := by
            congr 2
            ring
      _ = Real.exp F * (Real.exp (-error)) ^ n := by
            rw [Real.exp_nat_mul]
      _ = (Real.exp (-error)) ^ n * Real.exp F := by ring
  constructor
  · change L ≤ Matrix.permanent A
    rw [hL, hfactor]
    have hscaled : (Real.exp (-error)) ^ n * Real.exp F ≤
        (Real.exp (-error)) ^ n * Matrix.permanent A' :=
      mul_le_mul_of_nonneg_left hstructLower
        (pow_nonneg (Real.exp_pos (-error)).le n)
    exact hscaled.trans hcompare'.1
  · have hscalePos : 0 < (Real.exp error) ^ n * Matrix.permanent A' :=
      mul_pos (pow_pos (Real.exp_pos _) n) hperA'
    have hlogCompare : Real.log (Matrix.permanent A) ≤
        Real.log ((Real.exp error) ^ n * Matrix.permanent A') :=
      Real.strictMonoOn_log.monotoneOn hperA hscalePos hcompare'.2
    have hlogScale :
        Real.log ((Real.exp error) ^ n * Matrix.permanent A') =
          error * n + Real.log (Matrix.permanent A') := by
      rw [Real.log_mul (pow_ne_zero n (Real.exp_ne_zero error)) hperA'.ne',
        Real.log_pow, Real.log_exp]
      ring
    have hgap : Real.log (Matrix.permanent A) - Real.log L ≤
        (Real.log 2 / 2 -
          (((rationalEpsilonPlus s.completion : ℚ) : ℝ) -
            2 * error)) * n := by
      rw [hlogScale] at hlogCompare
      rw [hL, Real.log_exp]
      nlinarith [hstructGap]
    change Matrix.permanent A ≤
      (Real.sqrt 2 * Real.exp
        (-(((rationalEpsilonPlus s.completion : ℚ) : ℝ) -
          2 * error))) ^ n * L
    exact logGap_implies_positive_approximation
      (by rw [hL]; exact Real.exp_pos _) hperA hgap

end BeyondBethe
