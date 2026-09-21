/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.AveragingGradient

/-! # Averaging Scale -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

namespace SmoothOverlapPartition

/-- Raw parent-cube coordinate-summed gradient bound for the overlap averaging
competitor.  This is still unnormalized by the parent scale. -/
theorem exists_gradientCoordL2NormSum_averagingCompetitor_le_volume_invScale_sqrt_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (P.averagingCompetitor h).gradientCoordL2NormSum ≤
        (cubeVolume Q) ^ (1 / 2 : ℝ) *
          (C / (cubeScaleFactor Q / (3 : ℝ) ^ j)) *
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  classical
  rcases
    P.exists_cubeLpNorm_euclideanCoordDeriv_averagingField_coord_le_invScale_sqrt_depthAverage
      h hloc with
    ⟨C, hC_nonneg, hC⟩
  let n : ℝ := Fintype.card (Fin d)
  let scale : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  let base : ℝ :=
    (cubeVolume Q) ^ (1 / 2 : ℝ) * (C / scale) * Real.sqrt D
  refine ⟨n * n * C, by positivity, ?_⟩
  have hvol_half_nonneg : 0 ≤ (cubeVolume Q) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (cubeVolume_nonneg Q) _
  have hcoord_raw :
      ∀ i k : Fin d,
        ‖((P.averagingCompetitor h).coord i).gradCoordToScalarL2 k‖ ≤
          base := by
    intro i k
    let f : Vec d → ℝ :=
      fun x => ((P.averagingCompetitor h).coord i).grad x k
    let hgi : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      H1Function.grad_memL2_normalizedCubeMeasure
        ((P.averagingCompetitor h).coord i) k
    have hnorm_eq :
        ‖Homogenization.toScalarL2
            (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hgi)‖ =
          ‖((P.averagingCompetitor h).coord i).gradCoordToScalarL2 k‖ := by
      congr 1
    have hnorm :
        ‖((P.averagingCompetitor h).coord i).gradCoordToScalarL2 k‖ =
          (cubeVolume Q) ^ (1 / 2 : ℝ) *
            cubeLpNorm Q (2 : ℝ≥0∞) f := by
      rw [← hnorm_eq]
      exact norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two
        Q hgi
    have hcube :
        cubeLpNorm Q (2 : ℝ≥0∞) f ≤
          (C / scale) * Real.sqrt D := by
      simpa [f, scale, D] using hC i k
    calc
      ‖((P.averagingCompetitor h).coord i).gradCoordToScalarL2 k‖
          = (cubeVolume Q) ^ (1 / 2 : ℝ) *
              cubeLpNorm Q (2 : ℝ≥0∞) f := hnorm
      _ ≤
          (cubeVolume Q) ^ (1 / 2 : ℝ) *
            ((C / scale) * Real.sqrt D) := by
          exact mul_le_mul_of_nonneg_left hcube hvol_half_nonneg
      _ = base := by
          ring
  have hsum :
      (P.averagingCompetitor h).gradientCoordL2NormSum ≤
        ∑ i : Fin d, ∑ k : Fin d, base := by
    unfold CubeVectorH1Function.gradientCoordL2NormSum
    exact Finset.sum_le_sum fun i _hi => by
      unfold H1Function.gradientCoordL2NormSum
      exact Finset.sum_le_sum fun k _hk => hcoord_raw i k
  have hsum_const :
      (∑ i : Fin d, ∑ k : Fin d, base) = n * n * base := by
    simp [n, Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    (P.averagingCompetitor h).gradientCoordL2NormSum
        ≤ ∑ i : Fin d, ∑ k : Fin d, base := hsum
    _ = n * n * base := hsum_const
    _ =
        (cubeVolume Q) ^ (1 / 2 : ℝ) *
          ((n * n * C) / (cubeScaleFactor Q / (3 : ℝ) ^ j)) *
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
        simp [base, n, scale, D]
        ring

/-- Scale-correct relative-gradient estimate for the overlap averaging
competitor.  The factor `3^{-j}` cancels the inverse overlap scale in the raw
gradient bound. -/
theorem exists_rpow_neg_mul_relativeGradientCoordL2NormSum_averagingCompetitor_le_sqrt_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      Real.rpow (3 : ℝ) (-(j : ℝ)) *
          (P.averagingCompetitor h).relativeGradientCoordL2NormSum ≤
        C * Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  classical
  rcases
    P.exists_gradientCoordL2NormSum_averagingCompetitor_le_volume_invScale_sqrt_depthAverage
      h hloc with
    ⟨C, hC_nonneg, hraw⟩
  refine ⟨C, hC_nonneg, ?_⟩
  let G : CubeVectorH1Function Q := P.averagingCompetitor h
  let t : ℝ := Real.rpow (3 : ℝ) (-(j : ℝ))
  let scale : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  let α : ℝ := cubeScaleFactor Q / Real.sqrt (cubeVolume Q)
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg
      (le_of_lt <| by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
      (Real.sqrt_nonneg _)
  have hrel_le :
      G.relativeGradientCoordL2NormSum ≤
        α * ((cubeVolume Q) ^ (1 / 2 : ℝ) *
          (C / scale) * Real.sqrt D) := by
    calc
      G.relativeGradientCoordL2NormSum
          = α * G.gradientCoordL2NormSum := by
            rfl
      _ ≤
          α * ((cubeVolume Q) ^ (1 / 2 : ℝ) *
            (C / scale) * Real.sqrt D) := by
          exact mul_le_mul_of_nonneg_left (by simpa [G, scale, D] using hraw)
            hα_nonneg
  have hscaleFactor_ne : cubeScaleFactor Q ≠ 0 := by
    exact ne_of_gt <| by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hsqrtVol_ne : Real.sqrt (cubeVolume Q) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (cubeVolume_pos Q)
  have hpow_ne : (3 : ℝ) ^ j ≠ 0 := by
    exact pow_ne_zero j (by norm_num : (3 : ℝ) ≠ 0)
  have hscale_cancel :
      t * (α * ((cubeVolume Q) ^ (1 / 2 : ℝ) *
          (C / scale) * Real.sqrt D)) =
        C * Real.sqrt D := by
    dsimp [t, α, scale]
    rw [Real.rpow_neg (by norm_num : 0 ≤ (3 : ℝ))]
    rw [Real.rpow_natCast]
    rw [← Real.sqrt_eq_rpow]
    field_simp [hscaleFactor_ne, hsqrtVol_ne, hpow_ne]
  calc
    Real.rpow (3 : ℝ) (-(j : ℝ)) *
        (P.averagingCompetitor h).relativeGradientCoordL2NormSum
        = t * G.relativeGradientCoordL2NormSum := by
          rfl
    _ ≤
        t * (α * ((cubeVolume Q) ^ (1 / 2 : ℝ) *
          (C / scale) * Real.sqrt D)) := by
          exact mul_le_mul_of_nonneg_left hrel_le ht_nonneg
    _ = C * Real.sqrt D := hscale_cancel
    _ =
        C * Real.sqrt
          (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
        rfl

end SmoothOverlapPartition


end

end Homogenization
