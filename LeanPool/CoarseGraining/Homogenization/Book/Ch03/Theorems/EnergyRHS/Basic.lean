/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarsePoincareRHS
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.Flux
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergyPoincare

/-! # Basic -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Energy RHS: Basic L2 and Besov controls
-/

noncomputable section

open scoped ENNReal

private theorem vecNormSq_le_card_mul_norm_sq {d : ℕ} (v : Vec d) :
    vecNormSq v ≤ (Fintype.card (Fin d) : ℝ) * ‖v‖ ^ 2 := by
  rw [vecNormSq, vecDot]
  calc
    (∑ i : Fin d, v i * v i) ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hcoord_abs : |v i| ≤ ‖v‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
      have hcoord_sq : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
        nlinarith [abs_nonneg (v i), norm_nonneg v]
      simpa [sq_abs, pow_two] using hcoord_sq
    _ = (Fintype.card (Fin d) : ℝ) * ‖v‖ ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- The Euclidean square average of a vector field is controlled by the `L²`
cube norm coming from the ambient sup norm, with the expected dimension factor. -/
theorem cubeAverage_vecNormSq_le_card_mul_cubeLpNorm_two_sq
    {d : ℕ} {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecNormSq (F x)) ≤
      (Fintype.card (Fin d) : ℝ) * (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ 2 := by
  let card : ℝ := Fintype.card (Fin d)
  have hF_mem : MemVectorL2 (cubeSet Q) F :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hvec_int :
      MeasureTheory.IntegrableOn (fun x => vecNormSq (F x))
        (cubeSet Q) MeasureTheory.volume := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hF_mem hF_mem
  have hF_vol : MeasureTheory.MemLp F (2 : ENNReal)
      (MeasureTheory.volume.restrict (cubeSet Q)) := by
    simpa [MemVectorL2, volumeMeasureOn] using hF_mem
  have hnorm_int :
      MeasureTheory.IntegrableOn (fun x => ‖F x‖ ^ (2 : ℕ))
        (cubeSet Q) MeasureTheory.volume := by
    have h := hF_vol.integrable_norm_rpow (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    simpa using! h
  have havg :
      cubeAverage Q (fun x => vecNormSq (F x)) ≤
        cubeAverage Q (fun x => card * ‖F x‖ ^ (2 : ℕ)) := by
    unfold cubeAverage
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (cubeVolume_nonneg Q))
    exact
      MeasureTheory.integral_mono_ae hvec_int (hnorm_int.const_mul card) <|
        (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
          Filter.Eventually.of_forall fun x _hx => vecNormSq_le_card_mul_norm_sq (F x)
  have hscale :
      cubeAverage Q (fun x => card * ‖F x‖ ^ (2 : ℕ)) =
        card * cubeAverage Q (fun x => ‖F x‖ ^ (2 : ℕ)) := by
    unfold cubeAverage
    rw [MeasureTheory.integral_const_mul]
    ring
  have hlp_sq :
      (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ (2 : ℕ) =
        cubeAverage Q (fun x => ‖F x‖ ^ (2 : ℕ)) := by
    simpa using
      cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := Q) (p := (2 : ℝ≥0∞))
        (f := F) (by norm_num) (by norm_num) hF
  calc
    cubeAverage Q (fun x => vecNormSq (F x))
        ≤ cubeAverage Q (fun x => card * ‖F x‖ ^ (2 : ℕ)) := havg
    _ = card * cubeAverage Q (fun x => ‖F x‖ ^ (2 : ℕ)) := hscale
    _ = card * (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ 2 := by
        rw [hlp_sq]

/-- The depth-zero positive Besov seminorm controls the top-scale fluctuation
`L²` norm. -/
theorem cubeLpNorm_two_cubeFluctuationVec_le_scaleNormalizedPositiveBesovVectorSeminormTwo
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {F : Vec d → Vec d}
    (hF : ForceBesovRegularity Q s F) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q F) ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s F := by
  have hpartial_le :
      cubeBesovPositiveVectorPartialSeminormTwo Q s 0 F ≤
        cubeBesovPositiveVectorSeminormTwo Q s F :=
    cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
      Q s F hF.partialSeminorms_bddAbove 0
  have hpartial_eq :
      cubeBesovPositiveVectorPartialSeminormTwo Q s 0 F =
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q F) := by
    unfold cubeBesovPositiveVectorPartialSeminormTwo cubeBesovPositiveVectorDepthSeminorm
    simp [cubeBesovPositiveVectorDepthAverage_depth_zero, Real.sqrt_sq,
      cubeLpNorm_nonneg]
  simpa [scaleNormalizedPositiveBesovVectorSeminormTwo, hpartial_eq] using hpartial_le

/-- The full public positive Besov norm controls the top-scale cube `L²` norm. -/
theorem cubeLpNorm_two_le_scaleNormalizedPositiveBesovVectorNormTwo
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {F : Vec d → Vec d}
    (hF : ForceBesovRegularity Q s F) :
    cubeLpNorm Q (2 : ℝ≥0∞) F ≤
      scaleNormalizedPositiveBesovVectorNormTwo Q s F := by
  have hfluct_le :=
    cubeLpNorm_two_cubeFluctuationVec_le_scaleNormalizedPositiveBesovVectorSeminormTwo
      (Q := Q) (s := s) (F := F) hF
  have hfluct_mem : MeasureTheory.MemLp (cubeFluctuationVec Q F) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q F hF.memLp
  have hconst_mem : MeasureTheory.MemLp (fun _ : Vec d => cubeAverageVec Q F)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const (cubeAverageVec Q F)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) F
        = cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => cubeFluctuationVec Q F x + cubeAverageVec Q F) := by
          congr 1
          funext x
          simp [cubeFluctuationVec]
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q F) +
        cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => cubeAverageVec Q F) :=
          cubeLpNorm_add_le Q (2 : ℝ≥0∞) (cubeFluctuationVec Q F)
            (fun _ : Vec d => cubeAverageVec Q F) hfluct_mem hconst_mem (by norm_num)
    _ = cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q F) +
          ‖cubeAverageVec Q F‖ := by
          rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞))
            (c := cubeAverageVec Q F) (by norm_num)]
    _ ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q s F +
          Real.sqrt (vecNormSq (cubeAverageVec Q F)) := by
          exact add_le_add hfluct_le (norm_le_sqrt_vecNormSq (cubeAverageVec Q F))
    _ = scaleNormalizedPositiveBesovVectorNormTwo Q s F := by
          unfold scaleNormalizedPositiveBesovVectorNormTwo
          ring

/-- Euclidean cube `L²` size is controlled by the public positive Besov norm,
with only the ambient dimension factor coming from the sup-norm model of
`Vec d`. -/
theorem sqrt_cubeAverage_vecNormSq_le_sqrt_card_mul_scaleNormalizedPositiveBesovVectorNormTwo
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {F : Vec d → Vec d}
    (hF : ForceBesovRegularity Q s F) :
    Real.sqrt (cubeAverage Q (fun x => vecNormSq (F x))) ≤
      Real.sqrt (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s F := by
  let card : ℝ := Fintype.card (Fin d)
  let X : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let N : ℝ := scaleNormalizedPositiveBesovVectorNormTwo Q s F
  have hcard_nonneg : 0 ≤ card := by
    dsimp [card]
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have havg_le :
      cubeAverage Q (fun x => vecNormSq (F x)) ≤ card * X ^ 2 := by
    simpa [card, X] using
      cubeAverage_vecNormSq_le_card_mul_cubeLpNorm_two_sq
        (Q := Q) (F := F) hF.memLp
  have hX_le : X ≤ N := by
    simpa [X, N] using
      cubeLpNorm_two_le_scaleNormalizedPositiveBesovVectorNormTwo
        (Q := Q) (s := s) (F := F) hF
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F
  have hN_nonneg : 0 ≤ N := by
    dsimp [N, scaleNormalizedPositiveBesovVectorNormTwo]
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := Q) (s := s) (g := F) hF)
  have hsq_le : X ^ 2 ≤ N ^ 2 := by
    nlinarith
  have hfinal_avg :
      cubeAverage Q (fun x => vecNormSq (F x)) ≤ card * N ^ 2 :=
    havg_le.trans (mul_le_mul_of_nonneg_left hsq_le hcard_nonneg)
  calc
    Real.sqrt (cubeAverage Q (fun x => vecNormSq (F x)))
        ≤ Real.sqrt (card * N ^ 2) :=
          Real.sqrt_le_sqrt hfinal_avg
    _ = Real.sqrt card * N := by
          rw [Real.sqrt_mul hcard_nonneg]
          rw [Real.sqrt_sq hN_nonneg]

end

end Ch03
end Book
end Homogenization
