/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletBV

/-! # RHSConstant Apex Zero Dirichlet BVForce -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Centered-force averaged `BV` localization for the zero-Dirichlet RHS apex

This leaf proves the raw averaged localization estimate for the centered-force
part of the harmonic-remainder `BV` budget.  It deliberately stops at the
natural `s^{-2} * lambda^{-1}` scale; converting this into the corrected
weak-flux compact scale is a separate coefficient-normalization step.
-/

open scoped BigOperators ENNReal

namespace ZeroTraceDirichletCorrectorData

/--
Raw averaged control of the centered-force part of the harmonic-remainder
`BV` budget.

This proves the analytic localization step before any enlargement to the
corrected weak-flux compact scale.  The natural output has
`s^{-2} * lambda^{-1}` units.
-/
theorem zeroTraceDirichletHarmonicRemainderCenteredForceAverage_le_raw_lambdaInv
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {s lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    ∀ j : ℕ,
      coarsePoincareRHSDepthWeight s j *
          descendantsAverage Q j
            (fun R =>
              250 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
                    cubeBesovPositiveVectorSeminormTwo R s
                      (fun x => g x - cubeAverageVec R g))) ^ 2) ≤
        250 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          ((s⁻¹) ^ 2 *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  intro j
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let M : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)
  let N : ℝ := M * Real.sqrt 2
  let W : ℝ := coarsePoincareRHSDepthWeight s j
  let T : ℝ := Real.rpow (3 : ℝ) (s * (j : ℝ))
  let A : TriadicCube d → ℝ := fun R =>
    250 * (s⁻¹) ^ 2 *
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
        (M *
          cubeBesovPositiveVectorSeminormTwo R s
            (fun x => g x - cubeAverageVec R g)) ^ 2
  let C : ℝ := 250 * (s⁻¹) ^ 2 * (T * L) * M ^ 2
  have hs_half : 0 < s / 2 := by nlinarith
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)
  have hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a)
            (2 / 2)) := by
    have hsum :
        Summable (fun m : ℕ =>
          geometricWeight (s / 2) 2 m *
            maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) :=
      summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) (s := s / 2) hs_half hEll hData
    simpa using hsum
  have hlocal_lambda :
      ∀ R ∈ descendantsAtDepth Q j,
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤ T * L := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hloc :
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
          Real.rpow (3 : ℝ)
              (2 * (s / 2) *
                (Int.toNat (Q.scale - (Q.scale - (j : ℤ))) : ℝ)) *
            L := by
      simpa [L] using
        multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a (s / 2) 2
          (by nlinarith : 0 ≤ s / 2) (by norm_num) hRscale hsum_half
    have htoNat : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
      have hdiff : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
        omega
      rw [hdiff]
      simp
    have hloc' :
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
          Real.rpow (3 : ℝ) (2 * (s / 2) * (j : ℝ)) * L := by
      simpa [htoNat] using hloc
    simpa [T, show 2 * (s / 2) * (j : ℝ) = s * (j : ℝ) by ring] using hloc'
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr hlambda_nonneg
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        A R ≤
          C *
            (cubeBesovPositiveVectorSeminormTwo R s
              (fun x => g x - cubeAverageVec R g)) ^ 2 := by
    intro R hR
    let GR : ℝ :=
      cubeBesovPositiveVectorSeminormTwo R s
        (fun x => g x - cubeAverageVec R g)
    have hcoeff_nonneg :
        0 ≤ 250 * (s⁻¹) ^ 2 * (M * GR) ^ 2 := by
      positivity
    calc
      A R =
          (250 * (s⁻¹) ^ 2 * (M * GR) ^ 2) *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ := by
            dsimp [A, GR]
            ring
      _ ≤
          (250 * (s⁻¹) ^ 2 * (M * GR) ^ 2) * (T * L) := by
            exact mul_le_mul_of_nonneg_left (hlocal_lambda R hR) hcoeff_nonneg
      _ = C * GR ^ 2 := by
            dsimp [C, GR]
            ring
  have hlocal_avg :
      descendantsAverage Q j A ≤
        C * descendantsAverage Q j
          (fun R =>
            (cubeBesovPositiveVectorSeminormTwo R s
              (fun x => g x - cubeAverageVec R g)) ^ 2) := by
    calc
      descendantsAverage Q j A ≤
          descendantsAverage Q j
            (fun R =>
              C *
                (cubeBesovPositiveVectorSeminormTwo R s
                  (fun x => g x - cubeAverageVec R g)) ^ 2) := by
            exact descendantsAverage_le_descendantsAverage Q j hpoint
      _ =
          C * descendantsAverage Q j
            (fun R =>
              (cubeBesovPositiveVectorSeminormTwo R s
                (fun x => g x - cubeAverageVec R g)) ^ 2) := by
            exact descendantsAverage_smul Q j C _
  have hmem_desc :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R) := by
    intro n R hR
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg
  have hlocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) := by
    intro R hR
    exact
      cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
        s g hR hGlobalBdd
  have hcentered_avg :
      descendantsAverage Q j
          (fun R =>
            (cubeBesovPositiveVectorSeminormTwo R s
              (fun x => g x - cubeAverageVec R g)) ^ 2) ≤
        coarsePoincareRHSGlobalForceBound Q g s j := by
    have heq :=
      descendantsAverage_sq_coarsePoincareRHSLocalCenteredForceSeminorm_eq_of_mem
        Q g s j hmem_desc
    have huncentered :=
      descendantsAverage_sq_cubeBesovPositiveVectorSeminormTwo_le_global_scaled
        Q g s j hGlobalBdd hlocalBdd
    calc
      descendantsAverage Q j
          (fun R =>
            (cubeBesovPositiveVectorSeminormTwo R s
              (fun x => g x - cubeAverageVec R g)) ^ 2)
          =
        descendantsAverage Q j
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
          simpa [coarsePoincareRHSLocalCenteredForceSeminorm] using heq
      _ ≤ coarsePoincareRHSGlobalForceBound Q g s j := huncentered
  have hlocal_global :
      descendantsAverage Q j A ≤
        C * coarsePoincareRHSGlobalForceBound Q g s j :=
    hlocal_avg.trans (mul_le_mul_of_nonneg_left hcentered_avg hC_nonneg)
  have hweight_nonneg : 0 ≤ W := by
    dsimp [W]
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hcancel : W * T = 1 := by
    dsimp [W, T]
    unfold coarsePoincareRHSDepthWeight
    calc
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          Real.rpow (3 : ℝ) (s * (j : ℝ))
          = Real.rpow (3 : ℝ) ((-s * (j : ℝ)) + s * (j : ℝ)) := by
            exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
              (-s * (j : ℝ)) (s * (j : ℝ))).symm
      _ = 1 := by
            have hsum : (-s * (j : ℝ)) + s * (j : ℝ) = 0 := by ring
            rw [hsum]
            simp
  have hglobal_le_Gsq :
      coarsePoincareRHSGlobalForceBound Q g s j ≤ G ^ 2 := by
    let T0 : ℝ := Real.rpow (3 : ℝ) (s * (j : ℝ))
    have hT0_pos : 0 < T0 := by
      dsimp [T0]
      exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
    have hT0_ge_one : 1 ≤ T0 := by
      dsimp [T0]
      have hpow := Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3)
        (mul_nonneg hs.le (by positivity : 0 ≤ (j : ℝ)))
      simpa using hpow
    have hT0_sq_ge_one : 1 ≤ T0 ^ 2 := by
      nlinarith [sq_nonneg T0]
    have hinv_le_one : (T0 ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hT0_sq_ge_one
    calc
      coarsePoincareRHSGlobalForceBound Q g s j =
          (T0 ^ 2)⁻¹ * G ^ 2 := by
          dsimp [T0, G]
          rfl
      _ ≤ 1 * G ^ 2 := by
          exact mul_le_mul_of_nonneg_right hinv_le_one (sq_nonneg G)
      _ = G ^ 2 := by ring
  have hcoeff_raw_nonneg : 0 ≤ 250 * (s⁻¹) ^ 2 * L * M ^ 2 := by
    positivity
  have hweighted_raw :
      W * descendantsAverage Q j A ≤
        (250 * (s⁻¹) ^ 2 * L * M ^ 2) *
          coarsePoincareRHSGlobalForceBound Q g s j := by
    have hmul := mul_le_mul_of_nonneg_left hlocal_global hweight_nonneg
    calc
      W * descendantsAverage Q j A ≤
          W * (C * coarsePoincareRHSGlobalForceBound Q g s j) := hmul
      _ =
          (W * T) *
            ((250 * (s⁻¹) ^ 2 * L * M ^ 2) *
              coarsePoincareRHSGlobalForceBound Q g s j) := by
          dsimp [C]
          ring
      _ =
          (250 * (s⁻¹) ^ 2 * L * M ^ 2) *
            coarsePoincareRHSGlobalForceBound Q g s j := by
          rw [hcancel]
          ring
  have hraw :
      W * descendantsAverage Q j A ≤
        (250 * (s⁻¹) ^ 2 * L * M ^ 2) * G ^ 2 :=
    hweighted_raw.trans
      (mul_le_mul_of_nonneg_left hglobal_le_Gsq hcoeff_raw_nonneg)
  have hsqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hN_sq : N ^ 2 = 2 * M ^ 2 := by
    dsimp [N]
    calc
      (M * Real.sqrt 2) ^ 2 = M ^ 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = M ^ 2 * 2 := by rw [hsqrt_two_sq]
      _ = 2 * M ^ 2 := by ring
  have hM_sq_le_N_sq : M ^ 2 ≤ N ^ 2 := by
    rw [hN_sq]
    nlinarith [sq_nonneg M]
  have hcoeff_N_nonneg : 0 ≤ 250 * (s⁻¹) ^ 2 * L * G ^ 2 := by
    positivity
  calc
    coarsePoincareRHSDepthWeight s j *
          descendantsAverage Q j
            (fun R =>
              250 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
                    cubeBesovPositiveVectorSeminormTwo R s
                      (fun x => g x - cubeAverageVec R g))) ^ 2)
        =
      W * descendantsAverage Q j A := by
          apply congrArg (fun F : TriadicCube d → ℝ => W * descendantsAverage Q j F)
          funext R
          dsimp [A, M]
          ring
    _ ≤ (250 * (s⁻¹) ^ 2 * L * M ^ 2) * G ^ 2 := hraw
    _ =
        (250 * (s⁻¹) ^ 2 * L * G ^ 2) * M ^ 2 := by ring
    _ ≤
        (250 * (s⁻¹) ^ 2 * L * G ^ 2) * N ^ 2 := by
          exact mul_le_mul_of_nonneg_left hM_sq_le_N_sq hcoeff_N_nonneg
    _ =
        250 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          ((s⁻¹) ^ 2 *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
          dsimp [N, M, L, G]
          ring

end ZeroTraceDirichletCorrectorData

end

end Homogenization
