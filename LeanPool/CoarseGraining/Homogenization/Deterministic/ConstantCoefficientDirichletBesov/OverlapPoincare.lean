/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.AveragingResidual

/-! # Overlap Poincare -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

theorem overlapCubeLpNorm_two_overlapCubeFluctuationVec_toField_le_scale_mul_sum_grad
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (G : CubeVectorH1Function Q) (hS : S ∈ overlapCentersAtDepth Q j) :
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S G.toField) ≤
      (overlapCubeScaleFactor S *
          (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
        ∑ i : Fin d,
          overlapCubeLpNorm S (2 : ℝ≥0∞)
            (G.restrictCoordToOpenOverlap hS i).grad := by
  have hGloc :
      MeasureTheory.MemLp G.toField (2 : ℝ≥0∞)
        (normalizedOverlapCubeMeasure S) :=
    memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure
      hS G.memLp_toField_normalizedCubeMeasure
  have hfluct :
      MeasureTheory.MemLp (overlapCubeFluctuationVec S G.toField)
        (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
    memLp_overlapCubeFluctuationVec S G.toField hGloc
  have hvec :
      overlapCubeLpNorm S (2 : ℝ≥0∞)
          (overlapCubeFluctuationVec S G.toField) ≤
        ∑ i : Fin d,
          overlapCubeLpNorm S (2 : ℝ≥0∞)
            (fun x => overlapCubeFluctuationVec S G.toField x i) :=
    overlapCubeLpNorm_two_vec_le_sum_components S
      (overlapCubeFluctuationVec S G.toField) hfluct
  have hcomponents :
      ∑ i : Fin d,
          overlapCubeLpNorm S (2 : ℝ≥0∞)
            (fun x => overlapCubeFluctuationVec S G.toField x i) ≤
        ∑ i : Fin d,
          (overlapCubeScaleFactor S *
              (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
            overlapCubeLpNorm S (2 : ℝ≥0∞)
              (G.restrictCoordToOpenOverlap hS i).grad := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    let u : H1Function (openOverlapCubeSet S) :=
      G.restrictCoordToOpenOverlap hS i
    have hcomp :
        (fun x => overlapCubeFluctuationVec S G.toField x i) =
          fun x => u x - overlapCubeAverage S (fun y => u y) := by
      funext x
      simp [u, overlapCubeFluctuationVec, overlapCubeAverageVec,
        CubeVectorH1Function.toField]
    rw [hcomp]
    exact overlapCubeLpNorm_two_sub_overlapCubeAverage_le_scale_mul_grad S u
  calc
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S G.toField)
        ≤
          ∑ i : Fin d,
            overlapCubeLpNorm S (2 : ℝ≥0∞)
              (fun x => overlapCubeFluctuationVec S G.toField x i) := hvec
    _ ≤
          ∑ i : Fin d,
            (overlapCubeScaleFactor S *
                (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
              overlapCubeLpNorm S (2 : ℝ≥0∞)
                (G.restrictCoordToOpenOverlap hS i).grad := hcomponents
    _ =
          (overlapCubeScaleFactor S *
              (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
            ∑ i : Fin d,
              overlapCubeLpNorm S (2 : ℝ≥0∞)
                (G.restrictCoordToOpenOverlap hS i).grad := by
          rw [Finset.mul_sum]

theorem overlapCubeLpNorm_two_overlapCubeFluctuationVec_toField_le_scale_mul_sum_parent_grad
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (G : CubeVectorH1Function Q) (hS : S ∈ overlapCentersAtDepth Q j) :
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S G.toField) ≤
      (overlapCubeScaleFactor S *
          (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) *
        ∑ i : Fin d,
          overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad := by
  simpa using!
    overlapCubeLpNorm_two_overlapCubeFluctuationVec_toField_le_scale_mul_sum_grad
      G hS

theorem overlapCentersAverage_finset_sum {d : ℕ} {ι : Type*}
    (Q : TriadicCube d) (j : ℕ) (s : Finset ι)
    (F : ι → TriadicCube d → ℝ) :
    overlapCentersAverage Q j (fun S => ∑ i ∈ s, F i S) =
      ∑ i ∈ s, overlapCentersAverage Q j (fun S => F i S) := by
  classical
  let D := overlapCentersAtDepth Q j
  let c : ℝ := ((D.card : ℝ)⁻¹)
  unfold overlapCentersAverage
  change c * (∑ S ∈ D, ∑ i ∈ s, F i S) =
    ∑ i ∈ s, c * (∑ S ∈ D, F i S)
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]

theorem overlapCentersAverage_overlapCubeLpNorm_grad_sq_le {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (G : CubeVectorH1Function Q) (i : Fin d) :
    overlapCentersAverage Q j
        (fun S => (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2) ≤
      (3 ^ d : ℝ) *
        (cubeLpNorm Q (2 : ℝ≥0∞) (G.coord i).grad) ^ 2 := by
  have hparent :
      MeasureTheory.MemLp (G.coord i).grad (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    apply MeasureTheory.MemLp.of_eval
    intro k
    exact H1Function.grad_memL2_normalizedCubeMeasure (G.coord i) k
  have hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (G.coord i).grad (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S) := by
    intro S hS
    exact memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS hparent
  have havg :=
    overlapCentersAverage_lintegral_rpow_enorm_two_le
      Q j (G.coord i).grad hparent hloc
  calc
    overlapCentersAverage Q j
        (fun S => (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2)
        =
          overlapCentersAverage Q j
            (fun S =>
              (∫⁻ x, ‖(G.coord i).grad x‖ₑ ^ (2 : ℝ)
                ∂ normalizedOverlapCubeMeasure S).toReal) := by
          classical
          let D := overlapCentersAtDepth Q j
          unfold overlapCentersAverage
          change ((D.card : ℝ)⁻¹) *
              D.sum (fun S =>
                (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2) =
            ((D.card : ℝ)⁻¹) *
              D.sum (fun S =>
                (∫⁻ x, ‖(G.coord i).grad x‖ₑ ^ (2 : ℝ)
                  ∂ normalizedOverlapCubeMeasure S).toReal)
          congr 1
          refine Finset.sum_congr rfl ?_
          intro S _hS
          exact overlapCubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal
            (E := Vec d) S (G.coord i).grad
    _ ≤
          (3 ^ d : ℝ) *
            (∫⁻ x, ‖(G.coord i).grad x‖ₑ ^ (2 : ℝ)
              ∂ normalizedCubeMeasure Q).toReal := havg
    _ =
          (3 ^ d : ℝ) *
            (cubeLpNorm Q (2 : ℝ≥0∞) (G.coord i).grad) ^ 2 := by
          rw [cubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal (E := Vec d)]

theorem cubeLpNorm_two_grad_le_volume_inv_rpow_half_mul_gradientCoordL2NormSum
    {d : ℕ} {Q : TriadicCube d} (u : H1Function (openCubeSet Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) u.grad ≤
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * u.gradientCoordL2NormSum := by
  have hgrad : MeasureTheory.MemLp u.grad (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    apply MeasureTheory.MemLp.of_eval
    intro k
    exact H1Function.grad_memL2_normalizedCubeMeasure u k
  have hgradNorm :
      ‖Homogenization.toVectorL2
          (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hgrad)‖ =
        ‖u.gradToVectorL2‖ := by
    have hLp :
        Homogenization.toVectorL2
            (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hgrad) =
          u.gradToVectorL2 := by
      apply MeasureTheory.Lp.ext
      filter_upwards
          [Homogenization.coeFn_toVectorL2
            (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hgrad),
            H1Function.coeFn_gradToVectorL2 u]
        with x hleft hright
      rw [hleft, hright]
    exact congrArg norm hLp
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) u.grad
        =
          ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
            ‖Homogenization.toVectorL2
              (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hgrad)‖ := by
          exact
            cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toVectorL2_openCubeSet
              Q hgrad
    _ =
          ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) * ‖u.gradToVectorL2‖ := by
          rw [hgradNorm]
    _ ≤
          ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
            u.gradientCoordL2NormSum := by
          exact mul_le_mul_of_nonneg_left
            u.norm_gradToVectorL2_le_gradientCoordL2NormSum
            (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)

theorem cubeBesovOverlappingPositiveVectorDepthAverage_toField_le_raw
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (G : CubeVectorH1Function Q) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j ≤
      (((cubeScaleFactor Q / (3 : ℝ) ^ j) *
          (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) ^ 2) *
        ((Fintype.card (Fin d) : ℝ) *
          ((3 ^ d : ℝ) *
            ((((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
              G.gradientCoordL2NormSum) ^ 2))) := by
  classical
  let C0 : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue
  let scale : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let m : ℝ := (Fintype.card (Fin d) : ℝ)
  let parent : ℝ := ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
    G.gradientCoordL2NormSum
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    exact (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    exact div_nonneg
      (le_of_lt <| by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
      (by positivity)
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    positivity
  have hparent_nonneg : 0 ≤ parent := by
    dsimp [parent]
    exact mul_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
      G.gradientCoordL2NormSum_nonneg
  have hpoint :
      ∀ S ∈ overlapCentersAtDepth Q j,
        (overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S G.toField)) ^ 2 ≤
          (scale * C0) ^ 2 *
            (m *
              ∑ i : Fin d,
                (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2) := by
    intro S hS
    let L : ℝ := overlapCubeLpNorm S (2 : ℝ≥0∞)
      (overlapCubeFluctuationVec S G.toField)
    let b : Fin d → ℝ :=
      fun i => overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad
    have hscaleS : overlapCubeScaleFactor S = scale := by
      simpa [scale] using
        overlapCubeScaleFactor_eq_cubeScaleFactor_div_pow_of_mem_overlapCentersAtDepth
          hS
    have hL_nonneg : 0 ≤ L := by
      dsimp [L]
      exact overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S G.toField)
    have hb_nonneg : ∀ i : Fin d, 0 ≤ b i := by
      intro i
      dsimp [b]
      exact overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞) (G.coord i).grad
    have hsum_nonneg : 0 ≤ ∑ i : Fin d, b i :=
      Finset.sum_nonneg fun i _hi => hb_nonneg i
    have hlocal :
        L ≤ (scale * C0) * ∑ i : Fin d, b i := by
      dsimp [L, b]
      simpa [hscaleS, C0, scale] using
        overlapCubeLpNorm_two_overlapCubeFluctuationVec_toField_le_scale_mul_sum_parent_grad
          G hS
    have hright_nonneg : 0 ≤ (scale * C0) * ∑ i : Fin d, b i :=
      mul_nonneg (mul_nonneg hscale_nonneg hC0_nonneg) hsum_nonneg
    have hsq :
        L ^ 2 ≤ ((scale * C0) * ∑ i : Fin d, b i) ^ 2 :=
      (sq_le_sq₀ hL_nonneg hright_nonneg).mpr hlocal
    have hcs :
        (∑ i : Fin d, b i) ^ 2 ≤
          m * ∑ i : Fin d, (b i) ^ 2 := by
      simpa [m] using
        (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin d))) (f := b))
    have hmul :
        (scale * C0) ^ 2 * (∑ i : Fin d, b i) ^ 2 ≤
          (scale * C0) ^ 2 * (m * ∑ i : Fin d, (b i) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg (scale * C0))
    have hsq' :
        L ^ 2 ≤ (scale * C0) ^ 2 * (∑ i : Fin d, b i) ^ 2 := by
      nlinarith [hsq]
    have htarget :
        L ^ 2 ≤ (scale * C0) ^ 2 *
            (m * ∑ i : Fin d, (b i) ^ 2) :=
      hsq'.trans hmul
    simpa [L, b, mul_assoc] using htarget
  have havg_point :
      cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j ≤
        overlapCentersAverage Q j
          (fun S =>
            (scale * C0) ^ 2 *
              (m *
                ∑ i : Fin d,
                  (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2)) := by
    unfold cubeBesovOverlappingPositiveVectorDepthAverage
    exact overlapCentersAverage_le_overlapCentersAverage Q j hpoint
  have hfactor_avg :
      overlapCentersAverage Q j
          (fun S =>
            (scale * C0) ^ 2 *
              (m *
                ∑ i : Fin d,
                  (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2)) =
        (scale * C0) ^ 2 *
          (m *
            overlapCentersAverage Q j
              (fun S =>
                ∑ i : Fin d,
                  (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2)) := by
    rw [overlapCentersAverage_mul_left]
    rw [overlapCentersAverage_mul_left]
  have havg_grad :
      overlapCentersAverage Q j
          (fun S =>
            ∑ i : Fin d,
              (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2) ≤
        (3 ^ d : ℝ) *
          ∑ i : Fin d,
            (cubeLpNorm Q (2 : ℝ≥0∞) (G.coord i).grad) ^ 2 := by
    calc
      overlapCentersAverage Q j
          (fun S =>
            ∑ i : Fin d,
              (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2)
          =
            ∑ i : Fin d,
              overlapCentersAverage Q j
                (fun S =>
                  (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2) := by
            simpa using
              overlapCentersAverage_finset_sum Q j
                (Finset.univ : Finset (Fin d))
                (fun i S =>
                  (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2)
      _ ≤
            ∑ i : Fin d,
              (3 ^ d : ℝ) *
                (cubeLpNorm Q (2 : ℝ≥0∞) (G.coord i).grad) ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            exact overlapCentersAverage_overlapCubeLpNorm_grad_sq_le Q j G i
      _ =
            (3 ^ d : ℝ) *
              ∑ i : Fin d,
                (cubeLpNorm Q (2 : ℝ≥0∞) (G.coord i).grad) ^ 2 := by
            rw [Finset.mul_sum]
  have hparent_sum :
      ∑ i : Fin d,
          (cubeLpNorm Q (2 : ℝ≥0∞) (G.coord i).grad) ^ 2 ≤
        parent ^ 2 := by
    let a : ℝ := ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ)
    let c : Fin d → ℝ := fun i => (G.coord i).gradientCoordL2NormSum
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _
    have hc_nonneg : ∀ i : Fin d, 0 ≤ c i := by
      intro i
      dsimp [c]
      exact (G.coord i).gradientCoordL2NormSum_nonneg
    have hterm :
        ∀ i : Fin d,
          (cubeLpNorm Q (2 : ℝ≥0∞) (G.coord i).grad) ^ 2 ≤
            (a * c i) ^ 2 := by
      intro i
      have hle :=
        cubeLpNorm_two_grad_le_volume_inv_rpow_half_mul_gradientCoordL2NormSum
          (Q := Q) (G.coord i)
      exact (sq_le_sq₀
        (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (G.coord i).grad)
        (mul_nonneg ha_nonneg (hc_nonneg i))).mpr (by simpa [a, c] using hle)
    calc
      ∑ i : Fin d,
          (cubeLpNorm Q (2 : ℝ≥0∞) (G.coord i).grad) ^ 2
          ≤ ∑ i : Fin d, (a * c i) ^ 2 := by
            exact Finset.sum_le_sum fun i _hi => hterm i
      _ = a ^ 2 * ∑ i : Fin d, (c i) ^ 2 := by
            simp_rw [mul_pow]
            rw [← Finset.mul_sum]
      _ ≤ a ^ 2 * (∑ i : Fin d, c i) ^ 2 := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_sq_le_sq_sum_of_nonneg
                (s := (Finset.univ : Finset (Fin d)))
                (f := c) (fun i _hi => hc_nonneg i))
              (sq_nonneg a)
      _ = parent ^ 2 := by
            simp [parent, a, c, CubeVectorH1Function.gradientCoordL2NormSum]
            ring
  calc
    cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j
        ≤
          overlapCentersAverage Q j
            (fun S =>
              (scale * C0) ^ 2 *
                (m *
                  ∑ i : Fin d,
                    (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2)) :=
          havg_point
    _ =
          (scale * C0) ^ 2 *
            (m *
              overlapCentersAverage Q j
                (fun S =>
                  ∑ i : Fin d,
                    (overlapCubeLpNorm S (2 : ℝ≥0∞) (G.coord i).grad) ^ 2)) :=
          hfactor_avg
    _ ≤
          (scale * C0) ^ 2 *
            (m *
              ((3 ^ d : ℝ) *
                ∑ i : Fin d,
                  (cubeLpNorm Q (2 : ℝ≥0∞) (G.coord i).grad) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left havg_grad hm_nonneg)
            (sq_nonneg (scale * C0))
    _ ≤
          (scale * C0) ^ 2 *
            (m * ((3 ^ d : ℝ) * parent ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hparent_sum (by positivity))
              hm_nonneg)
            (sq_nonneg (scale * C0))
    _ =
          (((cubeScaleFactor Q / (3 : ℝ) ^ j) *
              (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue) ^ 2) *
            ((Fintype.card (Fin d) : ℝ) *
              ((3 ^ d : ℝ) *
                ((((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                  G.gradientCoordL2NormSum) ^ 2))) := by
          simp [C0, scale, m, parent]

/-- Explicit constant for the averaged overlap-cube Poincare estimate. -/
noncomputable def cubeVectorH1OverlapPoincareConstant (d : ℕ) : ℝ :=
  Real.sqrt ((Fintype.card (Fin d) : ℝ) * (3 ^ d : ℝ)) *
    (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue

theorem cubeVectorH1OverlapPoincareConstant_nonneg (d : ℕ) :
    0 ≤ cubeVectorH1OverlapPoincareConstant d := by
  unfold cubeVectorH1OverlapPoincareConstant
  exact mul_nonneg (Real.sqrt_nonneg _)
    (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg

/-- Averaged overlap-cube Poincare estimate for coordinatewise `H¹` vector
competitors.

This is the scale-correct analytic input for the competitor branch of the pure
K/overlapping comparison.  The overlapping oscillations are normalized `L²`
quantities, while the `H¹` competitor carries a raw parent-cube gradient norm,
so the parent-normalized size `relativeGradientCoordL2NormSum` appears. -/
def CubeVectorH1OverlapPoincareEstimate (d : ℕ) (C : ℝ) : Prop :=
  ∀ (Q : TriadicCube d) (j : ℕ) (G : CubeVectorH1Function Q),
    Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j) ≤
      C * Real.rpow (3 : ℝ) (-(j : ℝ)) * G.relativeGradientCoordL2NormSum

theorem cubeVectorH1OverlapPoincareEstimate
    (d : ℕ) :
    CubeVectorH1OverlapPoincareEstimate d
      (cubeVectorH1OverlapPoincareConstant d) := by
  intro Q j G
  let C0 : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue
  let M : ℝ := (Fintype.card (Fin d) : ℝ) * (3 ^ d : ℝ)
  let C : ℝ := cubeVectorH1OverlapPoincareConstant d
  let t : ℝ := Real.rpow (3 : ℝ) (-(j : ℝ))
  let R : ℝ := G.relativeGradientCoordL2NormSum
  let A : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact cubeBesovOverlappingPositiveVectorDepthAverage_nonneg Q G.toField j
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact cubeVectorH1OverlapPoincareConstant_nonneg d
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact G.relativeGradientCoordL2NormSum_nonneg
  have hB_nonneg : 0 ≤ C * t * R :=
    mul_nonneg (mul_nonneg hC_nonneg ht_nonneg) hR_nonneg
  have hraw :
      A ≤
        (((cubeScaleFactor Q / (3 : ℝ) ^ j) * C0) ^ 2) *
          ((Fintype.card (Fin d) : ℝ) *
            ((3 ^ d : ℝ) *
              ((((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                G.gradientCoordL2NormSum) ^ 2))) := by
    dsimp [A, C0]
    exact cubeBesovOverlappingPositiveVectorDepthAverage_toField_le_raw Q j G
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hC_sq : C ^ 2 = M * C0 ^ 2 := by
    dsimp [C, M, C0, cubeVectorH1OverlapPoincareConstant]
    rw [mul_pow, Real.sq_sqrt hM_nonneg]
  have ht_eq : t = ((3 : ℝ) ^ j)⁻¹ := by
    dsimp [t]
    rw [Real.rpow_neg (by norm_num : 0 ≤ (3 : ℝ))]
    rw [Real.rpow_natCast]
  have hvol_half :
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) =
        (Real.sqrt (cubeVolume Q))⁻¹ := by
    rw [Real.inv_rpow (cubeVolume_nonneg Q) (1 / 2 : ℝ)]
    rw [← Real.sqrt_eq_rpow]
  have hraw_eq :
      (((cubeScaleFactor Q / (3 : ℝ) ^ j) * C0) ^ 2) *
          ((Fintype.card (Fin d) : ℝ) *
            ((3 ^ d : ℝ) *
              ((((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                G.gradientCoordL2NormSum) ^ 2))) =
        (C * t * R) ^ 2 := by
    dsimp [R, CubeVectorH1Function.relativeGradientCoordL2NormSum]
    rw [ht_eq, hvol_half]
    have hC_sq' :
        C ^ 2 =
          ((Fintype.card (Fin d) : ℝ) * (3 ^ d : ℝ)) * C0 ^ 2 := by
      simpa [M] using hC_sq
    calc
      (((cubeScaleFactor Q / (3 : ℝ) ^ j) * C0) ^ 2) *
          ((Fintype.card (Fin d) : ℝ) *
            ((3 ^ d : ℝ) *
              (((Real.sqrt (cubeVolume Q))⁻¹ *
                G.gradientCoordL2NormSum) ^ 2)))
          =
            (((Fintype.card (Fin d) : ℝ) * (3 ^ d : ℝ)) * C0 ^ 2) *
              (((cubeScaleFactor Q / (3 : ℝ) ^ j) ^ 2) *
                (((Real.sqrt (cubeVolume Q))⁻¹ *
                  G.gradientCoordL2NormSum) ^ 2)) := by
            ring
      _ =
            C ^ 2 *
              ((((3 : ℝ) ^ j)⁻¹) ^ 2 *
                ((cubeScaleFactor Q / Real.sqrt (cubeVolume Q) *
                  G.gradientCoordL2NormSum) ^ 2)) := by
            rw [← hC_sq']
            ring
      _ =
            (C * ((3 : ℝ) ^ j)⁻¹ *
              (cubeScaleFactor Q / Real.sqrt (cubeVolume Q) *
                G.gradientCoordL2NormSum)) ^ 2 := by
            ring
  have hA_le : A ≤ (C * t * R) ^ 2 :=
    hraw.trans_eq hraw_eq
  have hsqrt : Real.sqrt A ≤ C * t * R :=
    Real.sqrt_le_iff.mpr ⟨hB_nonneg, hA_le⟩
  simpa [A, C, t, R] using hsqrt

theorem exists_cubeVectorH1OverlapPoincareEstimate
    (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ CubeVectorH1OverlapPoincareEstimate d C :=
  ⟨cubeVectorH1OverlapPoincareConstant d,
    cubeVectorH1OverlapPoincareConstant_nonneg d,
    cubeVectorH1OverlapPoincareEstimate d⟩

theorem cubeBesovOverlappingPositiveVectorDepthAverage_toField_le_of_overlapPoincare
    {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hPoincare : CubeVectorH1OverlapPoincareEstimate d C)
    (Q : TriadicCube d) (j : ℕ) (G : CubeVectorH1Function Q) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j ≤
      (C * Real.rpow (3 : ℝ) (-(j : ℝ)) *
        G.relativeGradientCoordL2NormSum) ^ 2 := by
  let A : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j
  let B : ℝ := C * Real.rpow (3 : ℝ) (-(j : ℝ)) *
    G.relativeGradientCoordL2NormSum
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact cubeBesovOverlappingPositiveVectorDepthAverage_nonneg Q G.toField j
  have hB_nonneg : 0 ≤ B := by
    exact mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
      G.relativeGradientCoordL2NormSum_nonneg
  have hsqr :
      (Real.sqrt A) ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hB_nonneg).mpr (by
      simpa [A, B] using hPoincare Q j G)
  calc
    cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j
        = (Real.sqrt A) ^ 2 := by
          dsimp [A]
          rw [Real.sq_sqrt hA_nonneg]
    _ ≤ B ^ 2 := hsqr
    _ = (C * Real.rpow (3 : ℝ) (-(j : ℝ)) *
          G.relativeGradientCoordL2NormSum) ^ 2 := by
          rfl


end

end Homogenization
