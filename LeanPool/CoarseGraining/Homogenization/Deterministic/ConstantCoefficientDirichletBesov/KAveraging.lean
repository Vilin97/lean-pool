/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.KFunctional

/-! # KAveraging -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

namespace SmoothOverlapPartition

/-- Phase-5 K-functional endpoint for the concrete overlap-averaging
competitor coming from a supplied smooth overlap partition. -/
theorem exists_cubeVectorKFunctional_le_mul_sqrt_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) h ≤
        C * Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  rcases P.exists_cubeLpNorm_sub_averagingField_le_mul_sqrt_depthAverage_of_memLp_overlap
      h hloc with
    ⟨Cres, hCres_nonneg, hres⟩
  rcases
    P.exists_rpow_neg_mul_relativeGradientCoordL2NormSum_averagingCompetitor_le_sqrt_depthAverage
      h hloc with
    ⟨Cgrad, hCgrad_nonneg, hgrad⟩
  refine ⟨Cres + Cgrad, add_nonneg hCres_nonneg hCgrad_nonneg, ?_⟩
  let G : CubeVectorH1Function Q := P.averagingCompetitor h
  let t : ℝ := Real.rpow (3 : ℝ) (-(j : ℝ))
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => h x - G.toField x)
  let B : ℝ := t * G.relativeGradientCoordL2NormSum
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => h x - G.toField x)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg ht_nonneg G.relativeGradientCoordL2NormSum_nonneg
  have hres' : A ≤ Cres * Real.sqrt D := by
    simpa [A, D, G] using! hres
  have hgrad' : B ≤ Cgrad * Real.sqrt D := by
    simpa [B, D, G, t] using hgrad
  have hcomp_value_le_sum :
      cubeVectorKFunctionalCompetitorValue Q t h G ≤ A + B := by
    have hright_nonneg : 0 ≤ A + B := add_nonneg hA_nonneg hB_nonneg
    have hsq :
        A ^ 2 + t ^ 2 * G.relativeGradientCoordL2NormSum ^ 2 ≤
          (A + B) ^ 2 := by
      have hBsq : B ^ 2 = t ^ 2 * G.relativeGradientCoordL2NormSum ^ 2 := by
        dsimp [B]
        ring
      rw [← hBsq]
      nlinarith [mul_nonneg hA_nonneg hB_nonneg]
    simpa [cubeVectorKFunctionalCompetitorValue, A, B] using
      (Real.sqrt_le_iff.mpr ⟨hright_nonneg, hsq⟩)
  have hcomp_value_le :
      cubeVectorKFunctionalCompetitorValue Q t h G ≤
        (Cres + Cgrad) * Real.sqrt D := by
    calc
      cubeVectorKFunctionalCompetitorValue Q t h G
          ≤ A + B := hcomp_value_le_sum
      _ ≤ Cres * Real.sqrt D + Cgrad * Real.sqrt D :=
          add_le_add hres' hgrad'
      _ = (Cres + Cgrad) * Real.sqrt D := by
          ring
  calc
    cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) h
        = cubeVectorKFunctional Q t h := by
          rfl
    _ ≤ cubeVectorKFunctionalCompetitorValue Q t h G :=
        cubeVectorKFunctional_le_competitor Q t h G
    _ ≤ (Cres + Cgrad) * Real.sqrt D := hcomp_value_le
    _ =
        (Cres + Cgrad) *
          Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
        rfl

/-- Phase-5 depth-seminorm estimate for the concrete overlap-averaging
competitor coming from a supplied smooth overlap partition. -/
theorem exists_cubeKBesovVectorDepthSeminorm_le_mul_overlapDepthSeminorm
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (s : ℝ) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      cubeKBesovVectorDepthSeminorm Q s h j ≤
        C * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s h j := by
  rcases P.exists_cubeVectorKFunctional_le_mul_sqrt_depthAverage h hloc with
    ⟨C, hC_nonneg, hK⟩
  refine ⟨C, hC_nonneg, ?_⟩
  let W : ℝ := Real.rpow (3 : ℝ) (s * (j : ℝ))
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  calc
    cubeKBesovVectorDepthSeminorm Q s h j
        =
          W * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) h := by
          rfl
    _ ≤ W * (C * Real.sqrt D) :=
          mul_le_mul_of_nonneg_left (by simpa [D] using hK) hW_nonneg
    _ = C * (W * Real.sqrt D) := by
          ring
    _ = C * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s h j := by
          rfl

/-- Concrete finite-depth Phase-6 assembly from supplied smooth overlap
partitions at every depth in the partial sum.  The constant may depend on the
finite family of supplied partitions; the later public axiom removal still
requires the uniform partition construction. -/
theorem exists_cubeKBesovVectorPartialSeminormTwo_le_mul_overlapPartialSeminorm
    {d : ℕ} {Q : TriadicCube d} {N : ℕ}
    (s : ℝ) (h : Vec d → Vec d)
    (hparent :
      MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hpart :
      ∀ j ∈ Finset.range (N + 1), Nonempty (SmoothOverlapPartition Q j)) :
    ∃ C : ℝ, 0 ≤ C ∧
      cubeKBesovVectorPartialSeminormTwo Q s N h ≤
        C * cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h := by
  classical
  let S := Finset.range (N + 1)
  have hdepth_exists :
      ∀ j ∈ S, ∃ C : ℝ, 0 ≤ C ∧
        cubeKBesovVectorDepthSeminorm Q s h j ≤
          C * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s h j := by
    intro j hj
    rcases hpart j (by simpa [S] using hj) with ⟨P⟩
    have hloc :
        ∀ R ∈ overlapCentersAtDepth Q j,
          MeasureTheory.MemLp h (2 : ℝ≥0∞)
            (normalizedOverlapCubeMeasure R) := by
      intro R hR
      exact memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure
        hR hparent
    exact P.exists_cubeKBesovVectorDepthSeminorm_le_mul_overlapDepthSeminorm
      s h hloc
  let c : ℕ → ℝ := fun j =>
    if hj : j ∈ S then Classical.choose (hdepth_exists j hj) else 0
  let C : ℝ := ∑ j ∈ S, c j
  have hc_nonneg : ∀ j ∈ S, 0 ≤ c j := by
    intro j hj
    dsimp [c]
    rw [dif_pos hj]
    exact (Classical.choose_spec (hdepth_exists j hj)).1
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun j hj => hc_nonneg j hj
  refine ⟨C, hC_nonneg, ?_⟩
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeKBesovVectorDepthSeminorm Q s h j ≤
          C * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s h j := by
    intro j hj
    have hjS : j ∈ S := by simpa [S] using hj
    have hdepth_j :
        cubeKBesovVectorDepthSeminorm Q s h j ≤
          c j * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s h j := by
      dsimp [c]
      rw [dif_pos hjS]
      exact (Classical.choose_spec (hdepth_exists j hjS)).2
    have hc_le_C : c j ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum (fun k hk => hc_nonneg k hk) hjS
    exact hdepth_j.trans
      (mul_le_mul_of_nonneg_right hc_le_C
        (cubeBesovOverlappingPositiveVectorDepthSeminorm_nonneg Q s h j))
  exact
    cubeKBesovVectorPartialSeminormTwo_le_mul_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_of_forall_depthSeminorm_le
      Q s C N h hC_nonneg hdepth

end SmoothOverlapPartition


end

end Homogenization
