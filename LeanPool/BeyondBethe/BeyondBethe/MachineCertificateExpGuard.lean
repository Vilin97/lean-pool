/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.CertificateMagnitude
import LeanPool.BeyondBethe.BeyondBethe.MachineCertificateAssembly

/-!
# The polynomial exponential guard for the optimizer certificate

The exponential evaluator expands its binary step count to unary.  Six fixed
applications of the verified quadratic-width constructor provide a degree-64
guard.  On positive normalized source matrices this dominates the exact
magnitude-sensitive exponential schedule.
-/

namespace BeyondBethe

open Complexity

def explicitExpReciprocalCeil : ℕ :=
  rationalCeilNat (1 / explicitExpEvaluationLoss)

def explicitCertificateExpStepBound (sourceLength : ℕ) : ℕ :=
  let K := 34 * sourceLength ^ 2
  2 * (K + K ^ 2 * explicitExpReciprocalCeil) + 1

theorem rationalCeilNat_le_of_le_nat {q : ℚ} {N : ℕ}
    (hq : q ≤ N) : rationalCeilNat q ≤ N := by
  rw [rationalCeilNat, Int.toNat_le]
  exact Int.ceil_le.mpr hq

@[simp] theorem RawRat.expMagnitude_value (q : RawRat) :
    (RawRat.expMagnitude q).value = abs q.value := by
  rcases q with ⟨num, den, hden⟩
  cases num with
  | ofNat a =>
      have hnonneg : 0 ≤ ((⟨Int.ofNat a, den, hden⟩ : RawRat).value) := by
        rw [RawRat.value]
        norm_num only [Int.cast_ofNat]
        exact div_nonneg (Nat.cast_nonneg a) (by exact_mod_cast hden.le)
      change ((⟨Int.ofNat a, den, hden⟩ : RawRat).value) =
        abs ((⟨Int.ofNat a, den, hden⟩ : RawRat).value)
      rw [abs_of_nonneg hnonneg]
  | negSucc a =>
      have hnonpos : ((⟨Int.negSucc a, den, hden⟩ : RawRat).value) ≤ 0 := by
        rw [RawRat.value]
        have hnum : (((Int.negSucc a : ℤ) : ℚ)) < 0 := by
          norm_num only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
          linarith
        exact div_nonpos_of_nonpos_of_nonneg hnum.le
          (by exact_mod_cast hden.le)
      change ((⟨Int.negSucc a, den, hden⟩ : RawRat).neg.value) =
        abs ((⟨Int.negSucc a, den, hden⟩ : RawRat).value)
      rw [RawRat.value_neg, abs_of_nonpos hnonpos]

theorem inverse_certificate_loss_le_reciprocalCeil
    {n : ℕ} (hn : 1 ≤ n) :
    1 / (explicitExpEvaluationLoss * n) ≤
      (explicitExpReciprocalCeil : ℚ) := by
  have hc : 0 < explicitExpEvaluationLoss := explicitExpEvaluationLoss_pos
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hden : explicitExpEvaluationLoss ≤
      explicitExpEvaluationLoss * n := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left hnQ hc.le
  have hinv : 1 / (explicitExpEvaluationLoss * n) ≤
      1 / explicitExpEvaluationLoss :=
    one_div_le_one_div_of_le hc hden
  have hceil := le_rationalCeilNat
    (show (0 : ℚ) ≤ 1 / explicitExpEvaluationLoss by positivity)
  exact hinv.trans hceil

/-- The source-length guard depends only on an a priori magnitude bound for
the rational logarithm.  It is intentionally independent of the optimizer
that produced that logarithm. -/
theorem certificate_expApproxSteps_le_sourceBound_of_abs_le
    (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ) (q : ℚ)
    (habsR : abs (q : ℝ) ≤ explicitCertificateMagnitudeBudget B) :
    RawRat.expApproxSteps (rawRatOfRat q)
        (rawCertificateExpLoss (m + 2)) ≤
      explicitCertificateExpStepBound
        (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩).length := by
  let source := rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩
  let S := source.length
  let t : ℚ := abs q
  let K := explicitCertificateMagnitudeBudget B
  let K₀ := 34 * S ^ 2
  have ht : t ≤ (K : ℚ) := by
    exact_mod_cast habsR
  have ht0 : 0 ≤ t := abs_nonneg q
  have hnSource : m + 2 ≤ S := by
    simpa only [S, source] using! matrix_dimension_le_code_length B
  have hBSource : rationalMatrixEntryBitBound B ≤ 32 * S := by
    simpa only [S, source] using!
      rationalMatrixEntryBitBound_le_machineCode (by omega) B
  have hS : 1 ≤ S := by omega
  have hK : K ≤ K₀ := by
    simp only [K, K₀, explicitCertificateMagnitudeBudget]
    nlinarith
  have htK₀ : t ≤ (K₀ : ℚ) := ht.trans (by exact_mod_cast hK)
  have hinv := inverse_certificate_loss_le_reciprocalCeil
    (n := m + 2) (by omega)
  have hlossValue : (rawCertificateExpLoss (m + 2)).value =
      explicitExpEvaluationLoss * ((m + 2 : ℕ) : ℚ) :=
    rawCertificateExpLoss_value (m + 2)
  have hsq : t ^ 2 ≤ (K₀ : ℚ) ^ 2 :=
    pow_le_pow_left₀ ht0 htK₀ 2
  have hinv0 : 0 ≤
      1 / (explicitExpEvaluationLoss * ((m + 2 : ℕ) : ℚ)) := by
    exact div_nonneg (by norm_num)
      (mul_nonneg explicitExpEvaluationLoss_pos.le (by positivity))
  have hC0 : (0 : ℚ) ≤ explicitExpReciprocalCeil := by positivity
  have hdiv : t ^ 2 /
      (explicitExpEvaluationLoss * ((m + 2 : ℕ) : ℚ)) ≤
      (K₀ : ℚ) ^ 2 * explicitExpReciprocalCeil := by
    calc
      t ^ 2 / (explicitExpEvaluationLoss * ((m + 2 : ℕ) : ℚ)) =
          t ^ 2 *
            (1 / (explicitExpEvaluationLoss * ((m + 2 : ℕ) : ℚ))) := by ring
      _ ≤ (K₀ : ℚ) ^ 2 *
          (1 / (explicitExpEvaluationLoss * ((m + 2 : ℕ) : ℚ))) :=
        mul_le_mul_of_nonneg_right hsq hinv0
      _ ≤ (K₀ : ℚ) ^ 2 * explicitExpReciprocalCeil :=
        mul_le_mul_of_nonneg_left hinv (sq_nonneg (K₀ : ℚ))
  have hu : t + t ^ 2 /
      (explicitExpEvaluationLoss * ((m + 2 : ℕ) : ℚ)) ≤
      (K₀ + K₀ ^ 2 * explicitExpReciprocalCeil : ℕ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat] at hdiv ⊢
    exact add_le_add htK₀ hdiv
  have hceil : rationalCeilNat
      (t + t ^ 2 /
        (explicitExpEvaluationLoss * ((m + 2 : ℕ) : ℚ))) ≤
        K₀ + K₀ ^ 2 * explicitExpReciprocalCeil :=
    rationalCeilNat_le_of_le_nat hu
  rw [RawRat.expApproxSteps, binaryRationalExpApproxSteps_eq,
    rationalExpApproxSteps, RawRat.expMagnitude_value,
    rawRatOfRat_value, hlossValue]
  simpa only [t, K₀, S, source, explicitCertificateExpStepBound] using!
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 hceil) 1

theorem optimizerCertificate_expApproxSteps_le_sourceBound
    (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (hBpos : ∀ i j, 0 < B i j)
    (hBupper : ∀ i j, B i j ≤ 1) :
    RawRat.expApproxSteps
        (rawRatOfRat
          (explicitDirectedCertificateLog
            (explicitBetheOptimizerMatrix (m := m + 1) B)
            (explicitBetheOptimizerRowPotential (m := m + 1) B)
            (explicitBetheOptimizerColumnPotential (m := m + 1) B)))
        (rawCertificateExpLoss (m + 2)) ≤
      explicitCertificateExpStepBound
        (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩).length := by
  let q := explicitDirectedCertificateLog
    (explicitBetheOptimizerMatrix (m := m + 1) B)
    (explicitBetheOptimizerRowPotential (m := m + 1) B)
    (explicitBetheOptimizerColumnPotential (m := m + 1) B)
  have habsR := explicitOptimizerCertificateLog_abs_le m B hBpos hBupper
  exact certificate_expApproxSteps_le_sourceBound_of_abs_le m B q
    (by simpa only [q] using! habsR)

def machineIteratedBinaryWidth : ℕ → List Bool → List Bool
  | 0, word => word
  | k + 1, word => machineBinaryMulWidth (machineIteratedBinaryWidth k word)

def certificateExpGuardWidth : ℕ → ℕ → ℕ
  | 0, L => L
  | k + 1, L => (certificateExpGuardWidth k L + 16) ^ 2

theorem machineIteratedBinaryWidth_mem_FP (k : ℕ) :
    machineIteratedBinaryWidth k ∈ Complexity.FP := by
  induction k with
  | zero => simpa only [machineIteratedBinaryWidth] using! id_mem_FP
  | succ k ih =>
      simpa only [machineIteratedBinaryWidth] using!
        machineCompose_mem_FP ih machineBinaryMulWidth_mem_FP

@[simp] theorem machineIteratedBinaryWidth_length (k : ℕ)
    (word : List Bool) :
    (machineIteratedBinaryWidth k word).length =
      certificateExpGuardWidth k word.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [machineIteratedBinaryWidth, machineBinaryMulWidth]
      simp only [List.length_replicate, List.length_append, ih,
        List.length_cons, List.length_nil, zero_add]
      simp only [certificateExpGuardWidth]
      ring

theorem certificateExpGuardWidth_pow_lower (k S : ℕ) :
    (S + 16) ^ (2 ^ (k + 1)) ≤ certificateExpGuardWidth (k + 1) S := by
  induction k with
  | zero => simp [certificateExpGuardWidth]
  | succ k ih =>
      rw [certificateExpGuardWidth]
      have hmono : certificateExpGuardWidth (k + 1) S ^ 2 ≤
          (certificateExpGuardWidth (k + 1) S + 16) ^ 2 := by
        exact Nat.pow_le_pow_left (Nat.le_add_right _ _) 2
      calc
        (S + 16) ^ (2 ^ (k + 1 + 1)) =
            ((S + 16) ^ (2 ^ (k + 1))) ^ 2 := by
          rw [show 2 ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 by
            rw [pow_succ]]
          rw [pow_mul]
        _ ≤ certificateExpGuardWidth (k + 1) S ^ 2 :=
          Nat.pow_le_pow_left ih 2
        _ ≤ (certificateExpGuardWidth (k + 1) S + 16) ^ 2 := hmono

def explicitCertificateExpCoefficient : ℕ :=
  2312 * explicitExpReciprocalCeil + 69

theorem explicitCertificateExpCoefficient_le :
    explicitCertificateExpCoefficient ≤ 18 ^ 60 := by
  have hrecip : explicitExpReciprocalCeil ≤ 10 ^ 69 := by
    rw [explicitExpReciprocalCeil]
    apply rationalCeilNat_le_of_le_nat
    rw [explicitExpEvaluationLoss, explicitCertifiedEpsilon,
      explicitCertifiedEpsilon_eq]
    norm_num [explicitXi, explicitDelta, explicitEta, explicitRowRatio]
  rw [explicitCertificateExpCoefficient]
  calc
    2312 * explicitExpReciprocalCeil + 69 ≤
        2312 * 10 ^ 69 + 69 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2312 hrecip) 69
    _ ≤ 18 ^ 60 := by norm_num

theorem explicitCertificateExpStepBound_le_guardWidth
    {S : ℕ} (hS : 2 ≤ S) :
    explicitCertificateExpStepBound S ≤ certificateExpGuardWidth 6 S := by
  let K₀ := 34 * S ^ 2
  have hSsq : S ^ 2 ≤ S ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hSfour : 1 ≤ S ^ 4 := Nat.one_le_pow 4 S (by omega)
  have hstepCoeff : explicitCertificateExpStepBound S ≤
      explicitCertificateExpCoefficient * S ^ 4 := by
    simp only [explicitCertificateExpStepBound, K₀,
      explicitCertificateExpCoefficient]
    nlinarith
  have hbase : 18 ≤ S + 16 := by omega
  have hpow60 : 18 ^ 60 ≤ (S + 16) ^ 60 :=
    Nat.pow_le_pow_left hbase 60
  have hpow4 : S ^ 4 ≤ (S + 16) ^ 4 :=
    Nat.pow_le_pow_left (Nat.le_add_right S 16) 4
  have hguardPolynomial : explicitCertificateExpCoefficient * S ^ 4 ≤
      (S + 16) ^ 64 := by
    calc
      explicitCertificateExpCoefficient * S ^ 4 ≤ 18 ^ 60 * S ^ 4 :=
        Nat.mul_le_mul explicitCertificateExpCoefficient_le (le_refl _)
      _ ≤ (S + 16) ^ 60 * (S + 16) ^ 4 :=
        Nat.mul_le_mul hpow60 hpow4
      _ = (S + 16) ^ 64 := by rw [← pow_add]
  exact hstepCoeff.trans <| hguardPolynomial.trans <|
    (by simpa using! certificateExpGuardWidth_pow_lower 5 S)

def machineOptimizerCertificateExpGuard (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 6 (machineCertificateSourceWord word)

theorem machineOptimizerCertificateExpGuard_mem_FP :
    machineOptimizerCertificateExpGuard ∈ Complexity.FP := by
  simpa only [machineOptimizerCertificateExpGuard] using!
    machineCompose_mem_FP machineCertificateSourceWord_mem_FP
      (machineIteratedBinaryWidth_mem_FP 6)

theorem machineOptimizerCertificateExpGuard_fits
    (m : ℕ) (B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ)
    (hBpos : ∀ i j, 0 < B i j)
    (hBupper : ∀ i j, B i j ≤ 1) :
    RawRat.expApproxSteps
        (rawRatOfRat
          (explicitDirectedCertificateLog
            (explicitBetheOptimizerMatrix (m := m + 1) B)
            (explicitBetheOptimizerRowPotential (m := m + 1) B)
            (explicitBetheOptimizerColumnPotential (m := m + 1) B)))
        (rawCertificateExpLoss (m + 2)) ≤
      (machineOptimizerCertificateExpGuard
        (pair (rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩)
          (rationalOptimizerOutputCode
            (explicitLargeOptimizerOutput m B)))).length := by
  let source := rationalMatrixBinaryEncoding.encode ⟨m + 2, B⟩
  have hsource : 2 ≤ source.length :=
    (show 2 ≤ m + 2 by omega).trans (matrix_dimension_le_code_length B)
  exact (optimizerCertificate_expApproxSteps_le_sourceBound m B hBpos hBupper).trans
    (by simpa only [machineOptimizerCertificateExpGuard,
      machineCertificateSourceWord_pair,
      machineIteratedBinaryWidth_length, source] using!
        explicitCertificateExpStepBound_le_guardWidth hsource)

theorem machineOptimizerCertificateExpGuard_fits_onPositiveNormalized :
    OptimizerCertificateExpGuardFitsOnPositiveNormalized
      machineOptimizerCertificateExpGuard := by
  intro m B hBpos hBupper
  exact machineOptimizerCertificateExpGuard_fits m B hBpos hBupper

end BeyondBethe
