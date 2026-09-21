/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2RHSComparison
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Regularity

/-! # Coarse Graining L2RHSCoefficient Localization -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

private theorem lambdaSq_half_two_inv_le_parent_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) {s : ℝ} {j : ℕ}
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtDepth Q j)
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have htoNat : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
    have hdiff : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
      ring
    simp [hdiff]
  have hbase :
      (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
        Real.rpow (3 : ℝ) (2 * (s / 2) * (j : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    simpa [htoNat] using
      (multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale
        (Q := Q) (R := R) (k := Q.scale - (j : ℤ))
        a (s / 2) 2 (by nlinarith) (by norm_num) hRscale hsumSigma)
  simpa [show 2 * (s / 2) * (j : ℝ) = s * (j : ℝ) by ring] using hbase

private theorem sqrt_lambdaSq_half_two_inv_le_parent_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) {s : ℝ} {j : ℕ}
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtDepth Q j)
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹) ≤
      Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
        Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
  have hlambda :=
    lambdaSq_half_two_inv_le_parent_of_mem_descendantsAtDepth
      (Q := Q) (R := R) a hs hR hsumSigma
  have hlambdaQ_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    exact inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
        (by norm_num) (by nlinarith))
  have hfactor_nonneg :
      0 ≤ Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hfactor_sq :
      (Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))) ^ 2 =
        Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
    calc
      (Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))) ^ 2
          = Real.rpow (Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))) (2 : ℝ) := by
              symm
              exact Real.rpow_natCast _ 2
      _ = Real.rpow (3 : ℝ) (((s / 2) * (j : ℝ)) * 2) := by
              exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
                ((s / 2) * (j : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
              congr 1
              ring
  calc
    Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹)
        ≤ Real.sqrt
            (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) :=
          Real.sqrt_le_sqrt hlambda
    _ = Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
        Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
          rw [← hfactor_sq]
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hfactor_nonneg]

private theorem sqrt_LambdaSq_half_two_le_parent_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) {s : ℝ} {j : ℕ}
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtDepth Q j)
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    Real.sqrt (LambdaSq R (s / 2) (.finite 2) a) ≤
      Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
        Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) := by
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have htoNat : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
    have hdiff : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
      ring
    simp [hdiff]
  have hbase :
      LambdaSq R (s / 2) (.finite 2) a ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          LambdaSq Q (s / 2) (.finite 2) a := by
    have hraw :=
      (multiscale_ellipticity_LambdaSq_finite_le_of_mem_descendantsAtScale
        (Q := Q) (R := R) (k := Q.scale - (j : ℤ))
        a (s / 2) 2 (by nlinarith) (by norm_num) hRscale hsumB)
    simpa [htoNat, show 2 * (s / 2) * (j : ℝ) = s * (j : ℝ) by ring] using hraw
  have hLambdaQ_nonneg :
      0 ≤ LambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith)
  have hfactor_nonneg :
      0 ≤ Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hfactor_sq :
      (Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))) ^ 2 =
        Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
    calc
      (Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))) ^ 2
          = Real.rpow (Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))) (2 : ℝ) := by
              symm
              exact Real.rpow_natCast _ 2
      _ = Real.rpow (3 : ℝ) (((s / 2) * (j : ℝ)) * 2) := by
              exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
                ((s / 2) * (j : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
              congr 1
              ring
  calc
    Real.sqrt (LambdaSq R (s / 2) (.finite 2) a)
        ≤ Real.sqrt
            (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              LambdaSq Q (s / 2) (.finite 2) a) :=
          Real.sqrt_le_sqrt hbase
    _ = Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
        Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) := by
          rw [← hfactor_sq]
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hfactor_nonneg]

/--
Pointwise descendant-to-parent coefficient localization for the §3.2.4
homogeneous response-correction component.
-/
theorem coarseFluxResponseRHSResponseCorrectionBound_le_parent_coeff_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} {j : ℕ} (g : Vec d → Vec d)
    (hs : 0 < s) (hR : R ∈ descendantsAtDepth Q j)
    (hgBddR :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
      (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
          Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
          coarseGrainingHomogenizationErrorAtDepth Q a a0 s j) *
        cubeBesovPositiveVectorSeminormTwo R s g := by
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo R s g
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove R s g hgBddR
  have hs_rpow_nonneg : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg hs.le _
  have hmat_sqrt_nonneg : 0 ≤ Real.sqrt (matNorm a0) := Real.sqrt_nonneg _
  have herror_nonneg :
      0 ≤ HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 :=
    homogenizationErrorOnCube_infinity_one_nonneg R a a0 hs.le
  have hparent_error_nonneg :
      0 ≤ coarseGrainingHomogenizationErrorAtDepth Q a a0 s j :=
    coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 j hs.le
  have herror_le :
      HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤
        coarseGrainingHomogenizationErrorAtDepth Q a a0 s j :=
    homogenizationErrorOnCube_le_coarseGrainingHomogenizationErrorAtDepth hR
  have hlambda_sqrt :
      Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹) ≤
        Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) :=
    sqrt_lambdaSq_half_two_inv_le_parent_of_mem_descendantsAtDepth
      (Q := Q) (R := R) a hs.le hR hsumSigma
  have hparent_lambda_sqrt_nonneg :
      0 ≤ Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (Real.sqrt_nonneg _)
  have hinner :
      Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹) *
          HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤
        (Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
            Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
          coarseGrainingHomogenizationErrorAtDepth Q a a0 s j :=
    mul_le_mul hlambda_sqrt herror_le herror_nonneg hparent_lambda_sqrt_nonneg
  have hcoef :
      Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
          (Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹) *
            HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) ≤
        Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
          ((Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
              Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
            coarseGrainingHomogenizationErrorAtDepth Q a a0 s j) := by
    exact mul_le_mul_of_nonneg_left hinner
      (mul_nonneg hs_rpow_nonneg hmat_sqrt_nonneg)
  calc
    coarseFluxResponseRHSResponseCorrectionBound R a a0 s g
        =
      (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
          (Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹) *
        HomogenizationErrorOnCube R s .infinity (.finite 1) a a0)) * B := by
        unfold coarseFluxResponseRHSResponseCorrectionBound
        dsimp [B]
        ring_nf
    _ ≤
      (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
          ((Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
              Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
            coarseGrainingHomogenizationErrorAtDepth Q a a0 s j)) * B := by
        exact mul_le_mul_of_nonneg_right hcoef hB_nonneg
    _ =
      (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
          Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
          coarseGrainingHomogenizationErrorAtDepth Q a a0 s j) * B := by
        ring

/--
Pointwise descendant-to-parent coefficient localization for the §3.2.4
weak-flux correction component.
-/
theorem coarseFluxResponseRHSWeakFluxCorrectionBound_le_parent_coeff_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d)
    {s : ℝ} {j : ℕ} (g : Vec d → Vec d)
    (hs : 0 < s) (hR : R ∈ descendantsAtDepth Q j)
    (hgBddR :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
      (Real.rpow s (-(5 / 2 : ℝ)) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
        cubeBesovPositiveVectorSeminormTwo R s g := by
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo R s g
  let factor : ℝ := Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove R s g hgBddR
  have hs_rpow_nonneg : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg hs.le _
  have hfactor_nonneg : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hfactor_sq :
      factor ^ 2 = Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
    dsimp [factor]
    calc
      (Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))) ^ 2
          = Real.rpow (Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))) (2 : ℝ) := by
              symm
              exact Real.rpow_natCast _ 2
      _ = Real.rpow (3 : ℝ) (((s / 2) * (j : ℝ)) * 2) := by
              exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
                ((s / 2) * (j : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
              congr 1
              ring
  have hLambda_sqrt :
      Real.sqrt (LambdaSq R (s / 2) (.finite 2) a) ≤
        factor * Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) := by
    simpa [factor] using
      sqrt_LambdaSq_half_two_le_parent_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a hs.le hR hsumB
  have hlambda_sqrt :
      Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹) ≤
        factor * Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
    simpa [factor] using
      sqrt_lambdaSq_half_two_inv_le_parent_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a hs.le hR hsumSigma
  have hparent_Lambda_nonneg :
      0 ≤ factor * Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) :=
    mul_nonneg hfactor_nonneg (Real.sqrt_nonneg _)
  have hlambda_local_nonneg :
      0 ≤ Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹) :=
    Real.sqrt_nonneg _
  have hinner :
      Real.sqrt (LambdaSq R (s / 2) (.finite 2) a) *
          Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹) ≤
        (factor * Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a)) *
          (factor * Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) :=
    mul_le_mul hLambda_sqrt hlambda_sqrt hlambda_local_nonneg hparent_Lambda_nonneg
  have hcoef :
      Real.rpow s (-(5 / 2 : ℝ)) *
          (Real.sqrt (LambdaSq R (s / 2) (.finite 2) a) *
            Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹)) ≤
        Real.rpow s (-(5 / 2 : ℝ)) *
          ((factor * Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a)) *
            (factor * Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹))) := by
    exact mul_le_mul_of_nonneg_left hinner hs_rpow_nonneg
  calc
    coarseFluxResponseRHSWeakFluxCorrectionBound R a s g
        =
      (Real.rpow s (-(5 / 2 : ℝ)) *
          (Real.sqrt (LambdaSq R (s / 2) (.finite 2) a) *
            Real.sqrt ((lambdaSq R (s / 2) (.finite 2) a)⁻¹))) * B := by
        unfold coarseFluxResponseRHSWeakFluxCorrectionBound
        dsimp [B]
        ring_nf
    _ ≤
      (Real.rpow s (-(5 / 2 : ℝ)) *
          ((factor * Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a)) *
            (factor * Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)))) * B := by
        exact mul_le_mul_of_nonneg_right hcoef hB_nonneg
    _ =
      (Real.rpow s (-(5 / 2 : ℝ)) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) * B := by
        rw [← hfactor_sq]
        ring

/--
Pointwise descendant-to-parent coefficient localization for the §3.2.4
Poincare correction component.
-/
theorem coarseFluxResponseRHSPoincareCorrectionBound_le_parent_coeff_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} {j : ℕ} (g : Vec d → Vec d)
    (hs : 0 < s) (hR : R ∈ descendantsAtDepth Q j)
    (hgBddR :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
      (Real.rpow s (-3 : ℝ) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
        cubeBesovPositiveVectorSeminormTwo R s g := by
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo R s g
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove R s g hgBddR
  have hs_rpow_nonneg : 0 ≤ Real.rpow s (-3 : ℝ) :=
    Real.rpow_nonneg hs.le _
  have hmat_nonneg : 0 ≤ matNorm a0 := matNorm_nonneg a0
  have hlambda :
      (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    lambdaSq_half_two_inv_le_parent_of_mem_descendantsAtDepth
      a hs.le hR hsumSigma
  have hcoef :
      Real.rpow s (-3 : ℝ) * matNorm a0 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
        Real.rpow s (-3 : ℝ) * matNorm a0 *
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
    exact mul_le_mul_of_nonneg_left hlambda
      (mul_nonneg hs_rpow_nonneg hmat_nonneg)
  calc
    coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g
        =
      (Real.rpow s (-3 : ℝ) * matNorm a0 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹) * B := by
        unfold coarseFluxResponseRHSPoincareCorrectionBound
        simp [B]
    _ ≤
      (Real.rpow s (-3 : ℝ) * matNorm a0 *
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) * B := by
        exact mul_le_mul_of_nonneg_right hcoef hB_nonneg
    _ =
      (Real.rpow s (-3 : ℝ) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) * B := by
        ring

/--
Two-exponent descendant-to-parent coefficient localization for the response
correction component.  The local flux-response exponent is `s`, while the
force is measured at the stronger positive exponent `t`.
-/
theorem coarseFluxResponseRHSResponseCorrectionBound_le_parent_coeff_forceExponent_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) (a0 : Mat d)
    {s t : ℝ} {j : ℕ} (g : Vec d → Vec d)
    (hs : 0 < s) (hst : s ≤ t) (hR : R ∈ descendantsAtDepth Q j)
    (hgBddR :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R t N g))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
      (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
          Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
          coarseGrainingHomogenizationErrorAtDepth Q a a0 s j) *
        cubeBesovPositiveVectorSeminormTwo R t g := by
  let C : ℝ :=
    Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
      Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
      coarseGrainingHomogenizationErrorAtDepth Q a a0 s j
  have hgBddR_s :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N g) :=
    cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_exponent_le
      R g hst hgBddR
  have hbase :
      coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
        C * cubeBesovPositiveVectorSeminormTwo R s g := by
    simpa [C] using
      coarseFluxResponseRHSResponseCorrectionBound_le_parent_coeff_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a a0 g hs hR hgBddR_s hsumSigma
  have hmono :
      cubeBesovPositiveVectorSeminormTwo R s g ≤
        cubeBesovPositiveVectorSeminormTwo R t g :=
    cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove
      R g hst hgBddR
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.sqrt_nonneg _))
            (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
          (Real.sqrt_nonneg _))
        (coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 j hs.le)
  exact hbase.trans (mul_le_mul_of_nonneg_left hmono hC_nonneg)

/--
Two-exponent descendant-to-parent coefficient localization for the weak-flux
correction component.
-/
theorem coarseFluxResponseRHSWeakFluxCorrectionBound_le_parent_coeff_forceExponent_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d)
    {s t : ℝ} {j : ℕ} (g : Vec d → Vec d)
    (hs : 0 < s) (hst : s ≤ t) (hR : R ∈ descendantsAtDepth Q j)
    (hgBddR :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R t N g))
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
      (Real.rpow s (-(5 / 2 : ℝ)) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
          Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
        cubeBesovPositiveVectorSeminormTwo R t g := by
  let C : ℝ :=
    Real.rpow s (-(5 / 2 : ℝ)) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)
  have hgBddR_s :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N g) :=
    cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_exponent_le
      R g hst hgBddR
  have hbase :
      coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
        C * cubeBesovPositiveVectorSeminormTwo R s g := by
    simpa [C] using
      coarseFluxResponseRHSWeakFluxCorrectionBound_le_parent_coeff_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a g hs hR hgBddR_s hsumB hsumSigma
  have hmono :
      cubeBesovPositiveVectorSeminormTwo R s g ≤
        cubeBesovPositiveVectorSeminormTwo R t g :=
    cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove
      R g hst hgBddR
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hs.le _)
            (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
          (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
  exact hbase.trans (mul_le_mul_of_nonneg_left hmono hC_nonneg)

/--
Two-exponent descendant-to-parent coefficient localization for the Poincare
correction component.
-/
theorem coarseFluxResponseRHSPoincareCorrectionBound_le_parent_coeff_forceExponent_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) (a0 : Mat d)
    {s t : ℝ} {j : ℕ} (g : Vec d → Vec d)
    (hs : 0 < s) (hst : s ≤ t) (hR : R ∈ descendantsAtDepth Q j)
    (hgBddR :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R t N g))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
      (Real.rpow s (-3 : ℝ) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
        cubeBesovPositiveVectorSeminormTwo R t g := by
  let C : ℝ :=
    Real.rpow s (-3 : ℝ) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  have hgBddR_s :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N g) :=
    cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_exponent_le
      R g hst hgBddR
  have hbase :
      coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
        C * cubeBesovPositiveVectorSeminormTwo R s g := by
    simpa [C] using
      coarseFluxResponseRHSPoincareCorrectionBound_le_parent_coeff_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a a0 g hs hR hgBddR_s hsumSigma
  have hmono :
      cubeBesovPositiveVectorSeminormTwo R s g ≤
        cubeBesovPositiveVectorSeminormTwo R t g :=
    cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove
      R g hst hgBddR
  have hlambda_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    exact inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
        (by norm_num) (by nlinarith))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hs.le _)
            (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
          (matNorm_nonneg a0))
        hlambda_nonneg
  exact hbase.trans (mul_le_mul_of_nonneg_left hmono hC_nonneg)

/--
Localized forcing correction absorbed into the §3.3.B forcing term, with the
three pointwise coefficient localizations discharged from descendant
multiscale-ellipticity summability.
-/
theorem localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coarseGrainingL2FluxDefectForcingTerm_of_bddAbove_of_summable
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (g : Vec d → Vec d)
    (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgBdd_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
      coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g :=
  localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coarseGrainingL2FluxDefectForcingTerm_of_pointwise_parent_coeff_bounds_of_bddAbove
    Q a a0 j g hs hgBdd hgBdd_desc
    (fun R hR =>
      coarseFluxResponseRHSResponseCorrectionBound_le_parent_coeff_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a a0 g hs hR (hgBdd_desc R hR) hsumSigma)
    (fun R hR =>
      coarseFluxResponseRHSWeakFluxCorrectionBound_le_parent_coeff_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a g hs hR (hgBdd_desc R hR) hsumB hsumSigma)
    (fun R hR =>
      coarseFluxResponseRHSPoincareCorrectionBound_le_parent_coeff_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a a0 g hs hR (hgBdd_desc R hR) hsumSigma)

/--
Two-exponent localized forcing correction with parent coefficient localization
and the inverse force-depth weight kept visible.
-/
theorem localizedCoarseFluxResponseRHSForcingCorrectionBound_le_parent_coeff_mul_depthWeight_inv_forceExponent_of_bddAbove_of_summable
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s t : ℝ} (j : ℕ) (g : Vec d → Vec d)
    (hs : 0 < s) (hst : s ≤ t)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q t N g))
    (hgBdd_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R t N g))
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
      ((Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
            Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
            Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
            coarseGrainingHomogenizationErrorAtDepth Q a a0 s j) +
          (Real.rpow s (-(5 / 2 : ℝ)) *
            Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
            Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) +
          (Real.rpow s (-3 : ℝ) *
            Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
        ((Real.rpow (3 : ℝ) (t * (j : ℝ)))⁻¹ *
          cubeBesovPositiveVectorSeminormTwo Q t g) := by
  let C₁ : ℝ :=
    Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
      Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
      coarseGrainingHomogenizationErrorAtDepth Q a a0 s j
  let C₂ : ℝ :=
    Real.rpow s (-(5 / 2 : ℝ)) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)
  let C₃ : ℝ :=
    Real.rpow s (-3 : ℝ) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  have hC₁_nonneg : 0 ≤ C₁ := by
    dsimp [C₁]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.sqrt_nonneg _))
            (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
          (Real.sqrt_nonneg _))
        (coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 j hs.le)
  have hC₂_nonneg : 0 ≤ C₂ := by
    dsimp [C₂]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hs.le _)
            (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
          (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
  have hlambda_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    exact inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
        (by norm_num) (by nlinarith))
  have hC₃_nonneg : 0 ≤ C₃ := by
    dsimp [C₃]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hs.le _)
            (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
          (matNorm_nonneg a0))
        hlambda_nonneg
  have hgBdd_desc_s :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) := by
    intro R hR
    exact
      cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_exponent_le
        R g hst (hgBdd_desc R hR)
  have hmain :=
    localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coeffSum_mul_depthWeight_inv_mul_parent_forceExponent_of_pointwise_le_of_bddAbove
      Q a a0 j g hC₁_nonneg hC₂_nonneg hC₃_nonneg hgBdd hgBdd_desc
      (fun R hR =>
        coarseFluxResponseRHSResponseCorrectionBound_nonneg_of_bddAbove
          R a a0 g hs (hgBdd_desc_s R hR))
      (fun R hR =>
        coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove
          R a g hs (hgBdd_desc_s R hR))
      (fun R hR =>
        coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove
          R a a0 g hs (hgBdd_desc_s R hR))
      (fun R hR =>
        by
          simpa [C₁] using
            coarseFluxResponseRHSResponseCorrectionBound_le_parent_coeff_forceExponent_of_mem_descendantsAtDepth
              (Q := Q) (R := R) a a0 g hs hst hR (hgBdd_desc R hR)
              hsumSigma)
      (fun R hR =>
        by
          simpa [C₂] using
            coarseFluxResponseRHSWeakFluxCorrectionBound_le_parent_coeff_forceExponent_of_mem_descendantsAtDepth
              (Q := Q) (R := R) a g hs hst hR (hgBdd_desc R hR)
              hsumB hsumSigma)
      (fun R hR =>
        by
          simpa [C₃] using
            coarseFluxResponseRHSPoincareCorrectionBound_le_parent_coeff_forceExponent_of_mem_descendantsAtDepth
              (Q := Q) (R := R) a a0 g hs hst hR (hgBdd_desc R hR)
              hsumSigma)
  simpa [C₁, C₂, C₃, add_assoc] using hmain

/--
Scalar §3.3 RHS comparison with the localized energy average and the
scale-separated two-exponent forcing correction.
-/
theorem localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBoundTwoExponent_of_bddAbove_of_isEllipticFieldOn_of_summable
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s t : ℝ} (j : ℕ) (gradU g : Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s) (hst : s ≤ t)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
        (cubeSet Q) MeasureTheory.volume)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q t N g))
    (hgBdd_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R t N g))
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      coarseGrainingL2FluxDefectBoundTwoExponent Q a a0 s t j gradU g := by
  have hgBdd_desc_s :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) := by
    intro R hR
    exact
      cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_exponent_le
        R g hst (hgBdd_desc R hR)
  have henergy :
      localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤
        coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU :=
    localizedCoarseFluxResponseRHSEnergyBound_le_coarseGrainingL2FluxDefectEnergyTerm_of_isEllipticFieldOn
      Q a a0 j gradU hs hEll henergy_int
  have hforcing :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
          localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
          localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
        coarseGrainingL2FluxDefectForcingTermTwoExponent Q a a0 s t j g := by
    simpa [coarseGrainingL2FluxDefectForcingTermTwoExponent, add_assoc] using
      localizedCoarseFluxResponseRHSForcingCorrectionBound_le_parent_coeff_mul_depthWeight_inv_forceExponent_of_bddAbove_of_summable
        Q a a0 j g hs hst hgBdd hgBdd_desc hsumB hsumSigma
  have hmain :=
    localizedCoarseFluxResponseRHSBound_le_energy_add_forcing_of_component_average_bounds
      Q a a0 j gradU g
      (fun R _ =>
        coarseFluxResponseRHSEnergyBound_nonneg R a a0 gradU hs)
      (fun R hR =>
        coarseFluxResponseRHSResponseCorrectionBound_nonneg_of_bddAbove
          R a a0 g hs (hgBdd_desc_s R hR))
      (fun R hR =>
        coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove
          R a g hs (hgBdd_desc_s R hR))
      (fun R hR =>
        coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove
          R a a0 g hs (hgBdd_desc_s R hR))
      henergy hforcing
  simpa [coarseGrainingL2FluxDefectBoundTwoExponent] using hmain

/--
Scalar §3.3 RHS comparison with the localized energy average and the three
forcing-correction coefficient localizations discharged internally.
-/
theorem localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_bddAbove_of_isEllipticFieldOn_of_summable
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
        (cubeSet Q) MeasureTheory.volume)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgBdd_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g :=
  localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_component_average_bounds_of_bddAbove
    Q a a0 j gradU g hs hgBdd_desc
    (localizedCoarseFluxResponseRHSEnergyBound_le_coarseGrainingL2FluxDefectEnergyTerm_of_isEllipticFieldOn
      Q a a0 j gradU hs hEll henergy_int)
    (localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coarseGrainingL2FluxDefectForcingTerm_of_bddAbove_of_summable
      Q a a0 j g hs hgBdd hgBdd_desc hsumB hsumSigma)

/--
§3.3 wrapper through descendant one-cube §3.2.4 RHS bounds, with the scalar
RHS comparison closed from the coefficient-localization hypotheses.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_bddAbove_of_isEllipticFieldOn_of_summable
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
        (cubeSet Q) MeasureTheory.volume)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgBdd_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
      solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
        coarseGrainingL2Rhs Cdual Q a a0 s j gradU g :=
    solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound
      hdual Q a a0 sigma0 gradU gradV g j hs_pos hs_lt_one hsigma0 ha0eq hEll
      ha0 ha0symm hcomparison
    hdefect_bdd hRhs
    (localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_bddAbove_of_isEllipticFieldOn_of_summable
      Q a a0 j gradU g hs_pos hEll henergy_int hgBdd hgBdd_desc
      hsumB hsumSigma)

/--
§3.3 wrapper through descendant one-cube §3.2.4 RHS bounds, deriving the
raw parent/descendant positive-Besov boundedness hypotheses from the note-facing
`H^s` regularity package for the right-hand side.
-/
private theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_cubeVectorBesovHRegularity_of_isEllipticFieldOn_of_summable
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
        (cubeSet Q) MeasureTheory.volume)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g)
    (hg : CubeVectorBesovHRegularity Q s g)
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
      solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
        coarseGrainingL2Rhs Cdual Q a a0 s j gradU g := by
  have hgBdd_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) := by
    intro R hR
    exact cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
      s g hR hg.partialSeminorms_bddAbove
  exact
      solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_bddAbove_of_isEllipticFieldOn_of_summable
        hdual Q a a0 sigma0 gradU gradV g j hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm
        hcomparison henergy_int hdefect_bdd hRhs hg.partialSeminorms_bddAbove
        hgBdd_desc hsumB hsumSigma

/--
Note-facing same-RHS §3.3 wrapper through descendant one-cube §3.2.4 RHS
bounds.  The energy-density integrability input is derived from the `H¹`
solution gradient and ellipticity.
-/
private theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_sameRhs_descendant_coarseFluxResponseRHSBound_of_cubeVectorBesovHRegularity_of_isEllipticFieldOn_of_summable
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 u.grad)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 u.grad) ≤
          coarseFluxResponseRHSBound R a a0 s u.grad g)
    (hg : CubeVectorBesovHRegularity Q s g)
    (hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)))
    (hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2))) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
        coarseGrainingL2Rhs Cdual Q a a0 s j u.grad g := by
  have henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u.grad)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      u.grad_memVectorL2
  exact
      solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_cubeVectorBesovHRegularity_of_isEllipticFieldOn_of_summable
        hdual Q a a0 sigma0 u.grad v.grad g j hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm
        (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
          hEll ha0 u v g hu hv hzeroTrace)
        henergy_int hdefect_bdd hRhs hg hsumB hsumSigma

/--
Same-RHS §3.3 wrapper deriving the half-scale coefficient summability inputs
from the descendant deterministic coarse-data package.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_sameRhs_descendant_coarseFluxResponseRHSBound_of_cubeVectorBesovHRegularity_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 u.grad) ≤
          coarseFluxResponseRHSBound R a a0 s u.grad g)
    (hg : CubeVectorBesovHRegularity Q s g) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
        coarseGrainingL2Rhs Cdual Q a a0 s j u.grad g := by
  have hs_half : 0 < s / 2 := by nlinarith
  have hsumB :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)) := by
    have hsum :
        Summable (fun n : ℕ =>
          geometricWeight (s / 2) 2 n *
            maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) :=
      summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) (s := s / 2) hs_half hEll hData
    simpa [Real.rpow_one] using hsum
  have hsumSigma :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)) := by
    have hsum :
        Summable (fun n : ℕ =>
          geometricWeight (s / 2) 2 n *
            maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) :=
      summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) (s := s / 2) hs_half hEll hData
    simpa [Real.rpow_one] using hsum
  have hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 u.grad)) := by
    intro R hR
    have hu_grad_memR : MemVectorL2 (cubeSet R) u.grad := by
      simpa [MemVectorL2, volumeMeasureOn] using
        u.grad_memVectorL2.mono_measure
          (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
            (cubeSet_subset_of_mem_descendantsAtDepth hR))
    have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
      hEll.mono (measurableSet_cubeSet R)
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hflux_mem :
        MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (u.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEllR hu_grad_memR
    have hEll0R :
        IsEllipticFieldOn lam0 Lam0 (cubeSet R) (constantCoeffField a0) :=
      isEllipticFieldOn_constantCoeffField (measurableSet_cubeSet R) ha0
    have ha0_mem :
        MemVectorL2 (cubeSet R) (fun x => matVecMul a0 (u.grad x)) := by
      simpa [constantCoeffField] using
        memVectorL2_matVecMul_of_isEllipticFieldOn hEll0R hu_grad_memR
    have hdefect_mem :
        MemVectorL2 (cubeSet R) (fluxDefect a a0 u.grad) := by
      unfold fluxDefect
      exact hflux_mem.sub ha0_mem
    exact cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs_pos
      (fluxDefect a a0 u.grad)
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R hdefect_mem)
  exact
      solution_diff_l2_le_coarseGrainingL2Rhs_of_sameRhs_descendant_coarseFluxResponseRHSBound_of_cubeVectorBesovHRegularity_of_isEllipticFieldOn_of_summable
        hdual Q a a0 sigma0 u v g j hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm hu hv
        hzeroTrace hdefect_bdd hRhs hg hsumB hsumSigma

end

end Homogenization
