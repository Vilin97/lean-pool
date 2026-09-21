/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ExecutableCertificate
import LeanPool.BeyondBethe.BeyondBethe.NumericalNearby

/-! # Executable Transfer -/

namespace BeyondBethe

/-!
# Transfer of the executable certificate

An approximate logarithmic KKT point defines a nearby matrix for which the
rational point is an exact optimizer.  The executable fixed-gain matching is
computed from that same rational point, so it transfers without any numerical
pair-gain approximation.
-/

/-- Logarithm of the executable lower certificate before its final directed
exponential evaluation. -/
noncomputable def executableNearbyCertificateLog
    {n : ℕ} (error : ℝ)
    (Xq : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℝ) : ℝ :=
  let X : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ ((Xq i j : ℚ) : ℝ)
  let A' := nearbyKKTMatrix (explicitRegularizationScale n : ℝ) X R C
  betheObjective A' X + (explicitCertifiedMatchingGain Xq : ℝ) - error * n

noncomputable def executableNearbyCertificateValue
    {n : ℕ} (error : ℝ)
    (Xq : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℝ) : ℝ :=
  Real.exp (executableNearbyCertificateLog error Xq R C)

theorem executableNearbyCertificateValue_pos
    {n : ℕ} (error : ℝ)
    (Xq : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℝ) :
    0 < executableNearbyCertificateValue error Xq R C :=
  Real.exp_pos _

/-- Approximate KKT residual `error` costs exactly `2 * error` in the
logarithmic exponent: once in comparing permanents and once in shifting the
certificate downward to preserve its lower-bound direction. -/
theorem executableNearbyCertificate_twoSided
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {n : ℕ} (hn : 2 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℝ}
    {Xq : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic
      (fun i j ↦ ((Xq i j : ℚ) : ℝ)))
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((Xq i j : ℚ) : ℝ)))
    {error : ℝ} {R C : Fin n → ℝ}
    (happrox : HasApproximateLogKKT error
      (explicitRegularizationScale n : ℝ) A
      (fun i j ↦ ((Xq i j : ℚ) : ℝ)) R C) :
    executableNearbyCertificateValue error Xq R C ≤
        Matrix.permanent A ∧
      Matrix.permanent A ≤
        (Real.sqrt 2 * Real.exp
          (-(((rationalEpsilonPlus
              explicitCertifiedCompletionScales : ℚ) : ℝ) -
            2 * error))) ^ n *
          executableNearbyCertificateValue error Xq R C := by
  let X : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ ((Xq i j : ℚ) : ℝ)
  let τ : ℝ := (explicitRegularizationScale n : ℝ)
  let A' := nearbyKKTMatrix τ X R C
  let F := betheObjective A' X + (explicitCertifiedMatchingGain Xq : ℝ)
  let L := executableNearbyCertificateValue error Xq R C
  have hXpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  have hXlt : ∀ i j, X i j < 1 := fun i j ↦ (hXint i).2 j |>.2
  have hA' : Matrix.Positive A' := nearbyKKTMatrix_positive hXpos hXlt
  have hstruct := explicitCertified_certificate_of_logKKT
    stableCoefficient hn hA' hX hXint
      (nearbyKKTMatrix_hasLogKKT hXpos hXlt)
  have hcompare := approximateLogKKT_permanent_comparison
    hA (by simpa only [τ, X] using happrox) hXpos hXlt
  have hcompare' :
      (Real.exp (-error)) ^ n * Matrix.permanent A' ≤
          Matrix.permanent A ∧
        Matrix.permanent A ≤
          (Real.exp error) ^ n * Matrix.permanent A' := by
    simpa only [A', τ, X, Fintype.card_fin] using hcompare
  have hstructLower : Real.exp F ≤ Matrix.permanent A' := by
    simpa only [F, A', X] using hstruct.1
  have hstructGap : Real.log (Matrix.permanent A') - F ≤
      (Real.log 2 / 2 -
        ((rationalEpsilonPlus explicitCertifiedCompletionScales : ℚ) : ℝ)) * n := by
    simpa only [F, A', X] using hstruct.2
  have hperA : 0 < Matrix.permanent A := permanent_pos_of_positive A hA
  have hperA' : 0 < Matrix.permanent A' := permanent_pos_of_positive A' hA'
  have hL : L = Real.exp (F - error * n) := by
    simp only [L, executableNearbyCertificateValue,
      executableNearbyCertificateLog, A', F, τ, X]
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
    exact (mul_le_mul_of_nonneg_left hstructLower
      (pow_nonneg (Real.exp_pos (-error)).le n)).trans hcompare'.1
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
          (((rationalEpsilonPlus
              explicitCertifiedCompletionScales : ℚ) : ℝ) -
            2 * error)) * n := by
      rw [hlogScale] at hlogCompare
      rw [hL, Real.log_exp]
      nlinarith [hstructGap]
    change Matrix.permanent A ≤
      (Real.sqrt 2 * Real.exp
        (-(((rationalEpsilonPlus
            explicitCertifiedCompletionScales : ℚ) : ℝ) -
          2 * error))) ^ n * L
    exact logGap_implies_positive_approximation
      (by rw [hL]; exact Real.exp_pos _) hperA hgap

end BeyondBethe
