/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyAnnularComparisonMaximal
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScaleOffsetBridge
public import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodSparseReduction
public import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodMaximalSparse

/-!
# Corrected sparse transfer through the actual annular comparison

The dyadic lower index is selected from the scaled radii, and both positive
majorant pairings use `normInput g`. These two corrections are essential:
an unshifted lower index does not describe arbitrary scale offsets, and
arbitrary complex test functions can cancel in the majorant pairings.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson.KrauseLaceyAnnularSparseTransfer

open KrauseLaceySparseDilation KrauseLaceyScaleOffsetPointwise
open KrauseLaceySparseReflection KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceyFiniteRadiusSmoothSparse KrauseLaceyCompactPairingStabilization
open HardyLittlewoodBoundaryControl HardyLittlewoodSparseReduction
open HardyLittlewoodMaximalSparse


noncomputable
section

/-- Sparse domination transfers through the actual norm-input comparison,
with its proved annular coefficient `24`, and no radius-cardinality loss. -/
theorem hasSparseOnePBound_finiteSmoothMax_of_dyadic_and_boundary
    (lam : ℝ) (s : Finset PositiveSmoothRadius) {C D p : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hdyadic : HasSparseOnePBound C p
      (dyadicSmoothHighPassMaxOperator lam (adjacentDyadicLowerIndex s)))
    (hboundary : HasSparseOnePBound D p centeredHardyLittlewoodBoundaryOperator) :
    HasSparseOnePBound (C + 24 * D) p (finiteSmoothMaxOperator lam s) := by
  intro f g
  obtain ⟨S, hS, hbS⟩ := hdyadic f (normInput g)
  obtain ⟨R, hR, hbR⟩ := hboundary f (normInput g)
  rw [sparseForm_normInput] at hbS hbR
  have hb : ENNReal.ofReal ‖operatorPairing (finiteSmoothMaxOperator lam s) f g‖ ≤
      ENNReal.ofReal C * sparseForm p f g S +
        ENNReal.ofReal (24 * D) * sparseForm p f g R := by
    apply (ENNReal.ofReal_le_ofReal
      (norm_pairing_finiteSmoothMax_le_dyadicMax_add_boundary lam s f g)).trans
    rw [ENNReal.ofReal_add (norm_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg _)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24), mul_assoc]
    exact add_le_add hbS (mul_le_mul' le_rfl hbR)
  rcases le_total (sparseForm p f g S) (sparseForm p f g R) with hSR | hRS
  · refine ⟨R, hR, hb.trans ?_⟩
    rw [ENNReal.ofReal_add hC (mul_nonneg (by norm_num) hD), add_mul]
    exact add_le_add (mul_le_mul' le_rfl hSR) le_rfl
  · refine ⟨S, hS, hb.trans ?_⟩
    rw [ENNReal.ofReal_add hC (mul_nonneg (by norm_num) hD), add_mul]
    exact add_le_add le_rfl (mul_le_mul' le_rfl hRS)

theorem hasSparseOnePBound_finiteSmoothMax_of_positiveSuffix_and_boundary
    (lam : ℝ) (s : Finset PositiveSmoothRadius) {C D p : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hpositive : ∀ (j : ℤ) (N : ℕ), HasSparseOnePBound C p
      (finitePositiveDyadicSuffixMaxOperator lam j N))
    (hboundary : HasSparseOnePBound D p centeredHardyLittlewoodBoundaryOperator) :
    HasSparseOnePBound (2 * C + 24 * D) p (finiteSmoothMaxOperator lam s) := by
  apply hasSparseOnePBound_finiteSmoothMax_of_dyadic_and_boundary
    lam s (mul_nonneg (by norm_num) hC) hD
  · exact hasSparseOnePBound_dyadicSmoothHighPassMax_of_uniform_positive_finiteSuffixMax
      lam (adjacentDyadicLowerIndex s) hC (hpositive (adjacentDyadicLowerIndex s))
  · exact hboundary

/-- Only the positive unit modulation is needed in the remaining native KL
analytic input. Neither other modulation signs nor scale offsets occur. -/
def HasNativeUnitPositiveSuffixSparseBound (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (p : ℝ), 1 < p → p < 2 → ∀ (j : ℤ) (N : ℕ),
    HasSparseOnePBound (C * holderConjugate p) p
      (finitePositiveDyadicSuffixMaxOperator 1 j N)

/-- The actual annular comparison extends native integer-dyadic unit-phase
suffix bounds to every finite positive smooth-radius family. -/
theorem hasUnitFiniteSmoothSparseBound_of_native_and_boundary
    {C D : ℝ} (hC : HasNativeUnitPositiveSuffixSparseBound C) (hD : 0 ≤ D)
    (hboundary : HasSparseOnePBound D 1 centeredHardyLittlewoodBoundaryOperator) :
    HasUnitFiniteSmoothSparseBound (2 * C + 24 * D) := by
  refine ⟨add_nonneg (mul_nonneg (by norm_num) hC.1) (mul_nonneg (by norm_num) hD), ?_⟩
  intro s p hp hp2
  have hp' : 1 < holderConjugate p := one_lt_holderConjugate_of_one_lt hp
  have hh := hasSparseOnePBound_finiteSmoothMax_of_positiveSuffix_and_boundary
    1 s (mul_nonneg hC.1 (zero_lt_one.trans hp').le) hD (hC.2 p hp hp2)
      (hasSparseOnePBound_of_one hp.le hboundary)
  apply hh.mono
  nlinarith

/-- Paper-facing all-nonzero smooth hypothesis from native unit suffixes and
the ordinary maximal-average sparse theorem. -/
theorem hasUniformFiniteRadiusSmoothSparseBound_of_native_and_boundary
    {C D : ℝ} (hC : HasNativeUnitPositiveSuffixSparseBound C) (hD : 0 ≤ D)
    (hboundary : HasSparseOnePBound D 1 centeredHardyLittlewoodBoundaryOperator) :
    HasUniformFiniteRadiusSmoothSparseBound (2 * C + 24 * D) :=
  hasUniformFiniteRadiusSmoothSparseBound_of_unit
    (hasUnitFiniteSmoothSparseBound_of_native_and_boundary hC hD hboundary)

/-- The ordinary maximal-average input is now fully discharged. Native
positive-unit integer-dyadic suffixes control arbitrary finite smooth radii;
the explicit extra universal constant is `24 * 480 = 11520`. -/
theorem hasUnitFiniteSmoothSparseBound_of_native
    {C : ℝ} (hC : HasNativeUnitPositiveSuffixSparseBound C) :
    HasUnitFiniteSmoothSparseBound (2 * C + 11520) := by
  simpa only [show (24 : ℝ) * 480 = 11520 by norm_num] using
    hasUnitFiniteSmoothSparseBound_of_native_and_boundary hC
    (by norm_num : (0 : ℝ) ≤ 480)
    hasSparseOneOneBound_centeredHardyLittlewoodBoundaryOperator

/-- This closes the scale-offset and nonzero-modulation adapter without any
annular-comparison, maximal-sparse, negative-sign, or dilation premise.
The only remaining input is the native positive-unit KL suffix theorem. -/
theorem hasUniformFiniteRadiusSmoothSparseBound_of_native
    {C : ℝ} (hC : HasNativeUnitPositiveSuffixSparseBound C) :
    HasUniformFiniteRadiusSmoothSparseBound (2 * C + 11520) :=
  hasUniformFiniteRadiusSmoothSparseBound_of_unit
    (hasUnitFiniteSmoothSparseBound_of_native hC)

/-- Compatibility with the older native interface, which unnecessarily
quantifies over every modulation: only its `lam = 1` component is used. -/
theorem hasNativeUnitPositiveSuffixSparseBound_of_native_allModulations
    {C : ℝ}
    (hC : KrauseLaceyScaleOffsetBridge.HasNativePositiveDyadicSuffixSparseBound C) :
    HasNativeUnitPositiveSuffixSparseBound C := by
  refine ⟨hC.1, ?_⟩
  intro p hp hp2 j N
  exact hC.2 1 j p hp hp2 N

theorem hasUnitScaleOffsetSmoothSparseBound_of_native
    {C : ℝ} (hC : HasNativeUnitPositiveSuffixSparseBound C) :
    HasUnitScaleOffsetSmoothSparseBound (2 * C + 11520) := by
  have h := hasUnitFiniteSmoothSparseBound_of_native hC
  exact ⟨h.1, fun a ha s p hp hp2 ↦ h.2 (scaleRadii a ha (roundedRadii s)) p hp hp2⟩


end
end QuadraticCarleson.KrauseLaceyAnnularSparseTransfer
