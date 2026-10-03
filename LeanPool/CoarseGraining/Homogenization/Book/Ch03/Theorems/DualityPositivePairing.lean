/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS.HarmonicRemainder
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardOverlapComparison
public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge.Contracts
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.Localization

/-! # Duality Positive Pairing -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Localized positive-test pairing

This file isolates the part of the positive-test bridge that is already
available from the standard, non-overlapping Ch3 Besov duality theorem.
-/

noncomputable section

open scoped ENNReal

/-- Standard positive-Besov version of the localized flux-defect pairing.

The remaining bridge work is to compare the corrected overlapping positive
norm used by the Dirichlet theorem with this standard positive norm. -/
theorem abs_cubeAverage_vecDot_le_localized_negative_standard_positive_besov
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} (j : ℕ)
    {F H : Vec d → Vec d} {B : ℝ}
    (hs : 0 < s) (hs_lt_one : s < 1)
    (hF : MemVectorL2 (cubeSet Q) F)
    (hH : ForceBesovRegularity Q s H)
    (hB : 0 ≤ B)
    (hHnorm : scaleNormalizedPositiveBesovVectorNormTwo Q s H ≤ B) :
    |cubeAverage Q (fun x => vecDot (F x) (H x))| ≤
      (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
        s⁻¹ * localizedFluxDefectNegativeBesovAverageTwo Q s F j * B := by
  let C0 : ℝ := 1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)
  let L : ℝ := localizedFluxDefectNegativeBesovAverageTwo Q s F j
  let P : ℝ := scaleNormalizedPositiveBesovVectorNormTwo Q s H
  have hF_lp : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hF
  have hdescBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N F) := by
    intro R hR
    have hFR : MemVectorL2 (cubeSet R) F := by
      simpa [MemVectorL2, volumeMeasureOn] using
        hF.mono_measure
          (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
            (cubeSet_subset_of_mem_descendantsAtDepth hR))
    exact cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs F
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R hFR)
  have hfull_le_L : cubeBesovNegativeVectorSeminormTwo Q s F ≤ L := by
    dsimp [L]
    exact
      cubeBesovNegativeVectorSeminormTwo_le_sqrt_descendantsAverage_sq_of_memLp_of_descendant_bddAbove
        Q hs F hF_lp j hdescBdd
  have hparentBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N F) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs F hF_lp
  have hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F ≤ L := by
    intro N
    exact (le_csSup hparentBdd ⟨N, rfl⟩).trans hfull_le_L
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact localizedFluxDefectNegativeBesovAverageTwo_nonneg Q s F j
  have hdual :
      |cubeAverage Q (fun x => vecDot (F x) (H x))| ≤ C0 * L * P := by
    simpa [C0, L, P] using
      abs_cubeAverage_vecDot_le_public_negative_positive_besov_duality_of_partial_flux_bound
        (Q := Q) (s := s) (Bflux := L) (F := F) (H := H)
        hs hs_lt_one.le hF_lp hH hL_nonneg hneg
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    exact add_nonneg zero_le_one
      (mul_nonneg (by exact_mod_cast Nat.zero_le d)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
  have hsinv_ge_one : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_lt_one.le
  have hP_le_sinv_mul_B : P ≤ s⁻¹ * B := by
    have hB_le : B ≤ s⁻¹ * B := by nlinarith
    exact hHnorm.trans hB_le
  have htarget : C0 * L * P ≤ C0 * s⁻¹ * L * B := by
    calc
      C0 * L * P = (C0 * L) * P := by ring
      _ ≤ (C0 * L) * (s⁻¹ * B) :=
        mul_le_mul_of_nonneg_left hP_le_sinv_mul_B
          (mul_nonneg hC0_nonneg hL_nonneg)
      _ = C0 * s⁻¹ * L * B := by ring
  exact hdual.trans htarget

theorem forceBesovRegularity_of_overlappingBesovHRegularity
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {H : Vec d → Vec d}
    (hH : CubeVectorOverlappingBesovHRegularity Q s H) :
    ForceBesovRegularity Q s H := by
  exact
    ⟨hH.memLp,
      cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_overlapping
        Q s H hH.partialSeminorms_bddAbove⟩

theorem scaleNormalizedPositiveBesovVectorNormTwo_le_sqrt_three_pow_mul_overlapping
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (H : Vec d → Vec d)
    (hH : CubeVectorOverlappingBesovHRegularity Q s H) :
    scaleNormalizedPositiveBesovVectorNormTwo Q s H ≤
      Real.sqrt (3 ^ d : ℝ) *
        cubeBesovOverlappingPositiveVectorNormTwo Q s H := by
  simpa [scaleNormalizedPositiveBesovVectorNormTwo,
    scaleNormalizedPositiveBesovVectorSeminormTwo] using
    positiveVectorNormTwo_le_sqrt_three_pow_mul_overlappingNorm
      Q s H hH.partialSeminorms_bddAbove

/-- Overlapping positive-Besov version of the localized flux-defect pairing.

This is the budgeted bridge needed by the restored duality argument.  It is
obtained from the standard positive-Besov pairing and the finite-overlap
comparison between the corrected overlapping positive norm and the standard
positive norm. -/
theorem abs_cubeAverage_vecDot_le_localized_negative_overlapping_positive_besov
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} (j : ℕ)
    {F H : Vec d → Vec d} {B : ℝ}
    (hs : 0 < s) (hs_lt_one : s < 1)
    (hF : MemVectorL2 (cubeSet Q) F)
    (hH : CubeVectorOverlappingBesovHRegularity Q s H)
    (hB : 0 ≤ B)
    (hHnorm : cubeBesovOverlappingPositiveVectorNormTwo Q s H ≤ B) :
    |cubeAverage Q (fun x => vecDot (F x) (H x))| ≤
      ((1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          Real.sqrt (3 ^ d : ℝ)) *
        s⁻¹ * localizedFluxDefectNegativeBesovAverageTwo Q s F j * B := by
  let C0 : ℝ := 1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)
  let K : ℝ := Real.sqrt (3 ^ d : ℝ)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact Real.sqrt_nonneg _
  have hstdReg : ForceBesovRegularity Q s H :=
    forceBesovRegularity_of_overlappingBesovHRegularity hH
  have hstdNorm :
      scaleNormalizedPositiveBesovVectorNormTwo Q s H ≤ K * B := by
    exact
      (scaleNormalizedPositiveBesovVectorNormTwo_le_sqrt_three_pow_mul_overlapping
        Q s H hH).trans
        (mul_le_mul_of_nonneg_left hHnorm hK_nonneg)
  have hKB : 0 ≤ K * B := mul_nonneg hK_nonneg hB
  have hstandard :=
    abs_cubeAverage_vecDot_le_localized_negative_standard_positive_besov
      (Q := Q) (s := s) (F := F) (H := H) (B := K * B) j
      hs hs_lt_one hF hstdReg hKB hstdNorm
  simpa [C0, K, mul_comm, mul_left_comm, mul_assoc] using hstandard

theorem localizedFluxDefectPositivePairingEstimate_standardOverlap
    (d : ℕ) [NeZero d] :
    LocalizedFluxDefectPositivePairingEstimate d
      ((1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
        Real.sqrt (3 ^ d : ℝ)) := by
  constructor
  · exact mul_nonneg
      (add_nonneg zero_le_one
        (mul_nonneg (by exact_mod_cast Nat.zero_le d)
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)))
      (Real.sqrt_nonneg _)
  · intro Q s j F H B hs hs_lt_one hF hHreg hB hHnorm
    exact
      abs_cubeAverage_vecDot_le_localized_negative_overlapping_positive_besov
        (Q := Q) (s := s) (F := F) (H := H) (B := B) j
        hs hs_lt_one hF hHreg hB hHnorm

end

end Ch03
end Book
end Homogenization
