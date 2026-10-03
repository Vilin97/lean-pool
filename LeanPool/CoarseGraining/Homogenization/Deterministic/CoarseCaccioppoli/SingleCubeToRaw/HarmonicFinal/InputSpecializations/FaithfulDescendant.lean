/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.CoefficientBounds
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.SolutionInputs
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation
public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity.QOneRoot

/-! # Faithful Descendant -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Descendant version of the coefficient localization displayed after the
single-cube estimate in the notes, for the centered ellipticity product. -/
theorem faithful_centered_descendant_product_le_parent_theta
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) {s t lam Lam : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Real.rpow (3 : ℝ) (-(j : ℝ)) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) ≤
      Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hEllRcube : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEllCube.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hEllRopen : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEllRcube.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
  have hRecR :
      OpenCubeDescendantEllipticRecoveryFamily R a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := R) (a := a) hEllRcube hOrigin
  have hDataR : OpenCubeDescendantDeterministicCoarseData R a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRecR
  have hBsumR_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) a s hs.le hR hBsum_s
  have hSigmaSumR_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) a t ht.le hR hSigmaSum_t
  have hellipticR :
      CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization R a s t :=
    CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization.of_isEllipticFieldOn_of_isSigmaCoarse
      R a hs ht hst hEllRopen hDataR hBsumR_s hSigmaSumR_t
  have hfactor_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-(j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have htoNat : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
    have hdiff : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
      ring
    simp [hdiff]
  have htheta :
      Real.rpow (3 : ℝ) (-(j : ℝ)) *
          Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ) ≤
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) *
          Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
    simpa [htoNat, coarseCaccioppoliSigma] using
      (thetaRatio_boundary_coefficient_le_of_mem_descendantsAtScale
        (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a s t hs.le ht.le
        (mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR)
        hBsum_s hSigmaSum_t)
  calc
    Real.rpow (3 : ℝ) (-(j : ℝ)) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ))
        ≤
      Real.rpow (3 : ℝ) (-(j : ℝ)) *
        Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hellipticR.2 hfactor_nonneg
    _ ≤
      Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := htheta

/-- Variant of `faithful_centered_descendant_product_le_parent_theta` with
`lambdaSq R 1` in the inverse slot.

This is the structural line needed by the average part of the exact centered
coefficient, whose local canonical `A^\circ_1(R)` contains
`lambdaSq R 1`.  Since `1 - s < 1`, the inverse lambda monotonicity upgrades
the `1` slot to the centered `1 - s` slot before applying the usual
descendant theta localization. -/
theorem faithful_centered_descendant_product_one_le_parent_theta
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) {s t lam Lam : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Real.rpow (3 : ℝ) (-(j : ℝ)) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) ≤
      Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hone_sub_pos : 0 < 1 - s := by linarith
  have hEllRcube : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEllCube.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hEllRopen : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEllRcube.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
  have hRecR :
      OpenCubeDescendantEllipticRecoveryFamily R a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := R) (a := a) hEllRcube hOrigin
  have hDataR : OpenCubeDescendantDeterministicCoarseData R a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRecR
  have hSigmaSum_one_sub_s :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hst]) hSigmaSum_t
  have hSigmaSumR_one_sub_s :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) a (1 - s) hone_sub_pos.le hR
      hSigmaSum_one_sub_s
  have hlambda_one :
      Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ) ≤
        Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ) :=
    multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := R) (a := a) (t := 1 - s) (s := (1 : ℝ))
      hone_sub_pos (by linarith) hEllRopen hDataR hSigmaSumR_one_sub_s
  have hLambda_nonneg :
      0 ≤ Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) :=
    Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg R s a hs.le) _
  have hprod_le :
      Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ) ≤
        Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hlambda_one hLambda_nonneg
  have hpow_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-(j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  exact le_trans
    (mul_le_mul_of_nonneg_left hprod_le hpow_nonneg)
    (faithful_centered_descendant_product_le_parent_theta
      (Q := Q) (R := R) (j := j) a hs ht hst hEllCube hR hBsum_s hSigmaSum_t)

/-- Faithful descendant centered coefficient localization, with the harmless
triadic scale constants isolated in `hscaleC`. -/
private theorem faithful_centered_descendant_coeff_le_alpha_of_scale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) {s t C Cwork k ρ₁ ρ₂ lam Lam : ℝ}
    {h : ℝ → ℝ → ℝ}
    (hC : 0 ≤ C) (hCwork : 0 ≤ Cwork)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hlt : ρ₁ < ρ₂)
    (hscaleC :
      C / (s * (1 - s)) * Real.rpow (3 : ℝ) k ≤
        Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hh : h ρ₁ ρ₂ = (j : ℝ)) :
    coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s C k (j : ℝ) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Cwork h ρ₁ ρ₂ := by
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hden_nonneg : 0 ≤ s * (1 - s) :=
    mul_nonneg hs.le (sub_nonneg.mpr hs1.le)
  have hleft_factor_nonneg :
      0 ≤ C / (s * (1 - s)) * Real.rpow (3 : ℝ) k := by
    exact mul_nonneg (div_nonneg hC hden_nonneg)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hright_factor_nonneg :
      0 ≤ Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    exact mul_nonneg (div_nonneg hCwork hden_nonneg)
      (coarseCaccioppoliGapInv_nonneg hlt)
  have hprod :=
    faithful_centered_descendant_product_le_parent_theta
      (Q := Q) (R := R) (j := j) a hs ht hst hEllCube hR hBsum_s hSigmaSum_t
  have hprod_left_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-(j : ℝ)) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) := by
    refine mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _) ?_
    exact mul_nonneg
      (Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg R s a hs.le) _)
      (Real.rpow_nonneg
        (multiscale_ellipticity_lambdaSq_one_nonneg R (1 - s) a
          (sub_nonneg.mpr hs1.le)) _)
  have hscaled :=
    mul_le_mul hscaleC hprod hprod_left_nonneg hright_factor_nonneg
  have hpow_split :
      Real.rpow (3 : ℝ) (k - (j : ℝ)) =
        Real.rpow (3 : ℝ) k * Real.rpow (3 : ℝ) (-(j : ℝ)) := by
    rw [sub_eq_add_neg]
    exact Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
  calc
    coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s C k (j : ℝ)
        =
      (C / (s * (1 - s)) * Real.rpow (3 : ℝ) k) *
        (Real.rpow (3 : ℝ) (-(j : ℝ)) *
          (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
            Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ))) := by
          unfold coarseCaccioppoliSingleCubeBoundaryCenteredCoeff
          rw [hpow_split]
          ring
    _ ≤
      (Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂) *
        (Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) *
          Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)) := hscaled
    _ =
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Cwork h ρ₁ ρ₂ := by
        unfold coarseCaccioppoliBoundaryAlphaOfHeight
        rw [hh]
        ring

/-- Descendant localization for the constant branch ellipticity factor:
`Λ_1(R)^{1/2} ≤ 3^{s j} Λ_s(Q)^{1/2}`. -/
private theorem faithful_constant_descendant_lambda_one_le_parent_lambda_s
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs1 : s < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hEllRcube : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEllCube.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hEllRopen : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEllRcube.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
  have hRecR :
      OpenCubeDescendantEllipticRecoveryFamily R a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := R) (a := a) hEllRcube hOrigin
  have hDataR : OpenCubeDescendantDeterministicCoarseData R a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRecR
  have hBsumR_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) a s hs.le hR hBsum_s
  have hmonoR :
      Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ) ≤
        Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) :=
    multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := R) (a := a) (t := s) (s := (1 : ℝ)) (lam := lam) (Lam := Lam)
      hs hs1 hEllRopen hDataR hBsumR_s
  have hdesc :
      Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) :=
    multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) a s hs.le hR hBsum_s
  exact le_trans hmonoR hdesc

/-- The triadic gap scale absorbs the local factor `3^k` after enlarging the
working constant by the universal factor `81`. -/
private theorem faithful_scale_mul_le_workGap_of_triadicGapScaleChoice
    {C Cwork ρ₁ ρ₂ : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hwork : (81 : ℝ) * C ≤ Cwork)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    C * Real.rpow (3 : ℝ) (k : ℝ) ≤
      Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
  have hpow :
      Real.rpow (3 : ℝ) (k : ℝ) ≤
        81 * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    simpa [Real.rpow_natCast] using
      (coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice
        hchoice hlt)
  have hscaled :=
    mul_le_mul_of_nonneg_left hpow hC
  have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    coarseCaccioppoliGapInv_nonneg hlt
  calc
    C * Real.rpow (3 : ℝ) (k : ℝ)
        ≤ C * (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) := hscaled
    _ = (81 * C) * coarseCaccioppoliGapInv ρ₁ ρ₂ := by ring
    _ ≤ Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ :=
          mul_le_mul_of_nonneg_right hwork hgap_nonneg

/-- Centered-coefficient variant of
`faithful_scale_mul_le_workGap_of_triadicGapScaleChoice`, with the harmless
factor `1 / (s * (1 - s))` carried along. -/
theorem faithful_centered_scale_mul_le_workGap_of_triadicGapScaleChoice
    {s C Cwork ρ₁ ρ₂ : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hwork : (81 : ℝ) * C ≤ Cwork)
    (hs : 0 < s) (hs1 : s < 1)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    C / (s * (1 - s)) * Real.rpow (3 : ℝ) (k : ℝ) ≤
      Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
  have hscale :=
    faithful_scale_mul_le_workGap_of_triadicGapScaleChoice
      (C := C) (Cwork := Cwork) hC hwork hchoice hlt
  have hden_pos : 0 < s * (1 - s) := by nlinarith
  have hinv_nonneg : 0 ≤ (s * (1 - s))⁻¹ :=
    inv_nonneg.mpr hden_pos.le
  have hscaled :=
    mul_le_mul_of_nonneg_left hscale hinv_nonneg
  calc
    C / (s * (1 - s)) * Real.rpow (3 : ℝ) (k : ℝ)
        = (s * (1 - s))⁻¹ * (C * Real.rpow (3 : ℝ) (k : ℝ)) := by
            ring
    _ ≤ (s * (1 - s))⁻¹ * (Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂) := hscaled
    _ = Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
            ring

/-- Constant-branch scale absorption with the extra `3^s` ceiling loss. -/
theorem faithful_scale_mul_rpow_s_le_workGap_of_triadicGapScaleChoice
    {s C Cwork ρ₁ ρ₂ : ℝ} {k : ℕ}
    (hC : 0 ≤ C)
    (hwork : (81 : ℝ) * Real.rpow (3 : ℝ) s * C ≤ Cwork)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    (C * Real.rpow (3 : ℝ) (k : ℝ)) * Real.rpow (3 : ℝ) s ≤
      Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
  have hpow :
      Real.rpow (3 : ℝ) (k : ℝ) ≤
        81 * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    simpa [Real.rpow_natCast] using
      (coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice
        hchoice hlt)
  have hscaled :=
    mul_le_mul_of_nonneg_left hpow hC
  have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    coarseCaccioppoliGapInv_nonneg hlt
  have hpow_s_nonneg : 0 ≤ Real.rpow (3 : ℝ) s :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  calc
    (C * Real.rpow (3 : ℝ) (k : ℝ)) * Real.rpow (3 : ℝ) s
        ≤ (C * (81 * coarseCaccioppoliGapInv ρ₁ ρ₂)) *
            Real.rpow (3 : ℝ) s := by
              exact mul_le_mul_of_nonneg_right hscaled hpow_s_nonneg
    _ = (81 * Real.rpow (3 : ℝ) s * C) *
          coarseCaccioppoliGapInv ρ₁ ρ₂ := by ring
    _ ≤ Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ :=
          mul_le_mul_of_nonneg_right hwork hgap_nonneg

/-- A ceiling estimate for the integerized localized small-cube height. -/
theorem faithful_integerized_height_depth_le_height_add_one
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    {s t C : ℝ} (hs : 0 < s) (k : ℕ) :
    ((coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale
        Q a s t C k : ℕ) : ℝ) ≤
      coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k + 1 := by
  have hheight_nonneg :
      0 ≤ coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k := by
    exact le_trans (div_nonneg (by norm_num : 0 ≤ (4 : ℝ)) hs.le)
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_four_div_s
        Q a s t C k)
  exact le_of_lt (Nat.ceil_lt_add_one hheight_nonneg)

/-- The unit-`L²` cross coefficient times a parent `L²` bound is controlled by
the public cross coefficient.  This is the finite-Cauchy bookkeeping used in
the faithful small-cube proof: local descendant `L²` norms are summed first,
then the parent `L²` size is inserted. -/
theorem boundaryCrossCoeff_one_mul_le_boundaryCrossCoeff_of_cubeLpNorm_le_sqrt
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    {s C uL2Sq ρ₁ ρ₂ U : ℝ} {h : ℝ → ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (hlt : ρ₁ < ρ₂)
    (hU : U ≤ Real.sqrt uL2Sq) :
    coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C 1 h ρ₁ ρ₂ * U ≤
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ := by
  let front : ℝ :=
    C * coarseCaccioppoliGapInv ρ₁ ρ₂ *
      Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) *
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)
  have hfront_nonneg : 0 ≤ front := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (coarseCaccioppoliGapInv_nonneg hlt))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
      (Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le) _)
  have hmul := mul_le_mul_of_nonneg_left hU hfront_nonneg
  simpa [coarseCaccioppoliBoundaryCrossCoeffOfHeight, front, mul_assoc] using hmul

/-- Descendant constant coefficient localization against the real localized
height, with the ceiling loss isolated in `hscaleC`. -/
theorem faithful_constant_descendant_coeff_le_cross_of_scale_height_le_depth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) {s C Cwork k uL2Sq ρ₁ ρ₂ lam Lam : ℝ}
    {h : ℝ → ℝ → ℝ}
    (hC : 0 ≤ C)
    (hs : 0 < s) (hs1 : s < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hscaleC :
      (C * Real.rpow (3 : ℝ) k) * Real.rpow (3 : ℝ) s ≤
        Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hj_le : (j : ℝ) ≤ h ρ₁ ρ₂ + 1) :
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff R a C k uL2Sq ≤
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Cwork uL2Sq h ρ₁ ρ₂ := by
  have hLambda :=
    faithful_constant_descendant_lambda_one_le_parent_lambda_s
      (Q := Q) (R := R) (j := j) a hs hs1 hEllCube hR hBsum_s
  have hleft_factor_nonneg :
      0 ≤ C * Real.rpow (3 : ℝ) k := by
    exact mul_nonneg hC (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hpow_depth :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) ≤
        Real.rpow (3 : ℝ) s * Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
    have hexp_le : s * (j : ℝ) ≤ s + s * h ρ₁ ρ₂ := by
      nlinarith [mul_le_mul_of_nonneg_left hj_le hs.le]
    calc
      Real.rpow (3 : ℝ) (s * (j : ℝ))
          ≤ Real.rpow (3 : ℝ) (s + s * h ρ₁ ρ₂) := by
              exact Real.rpow_le_rpow_of_exponent_le
                (by norm_num : (1 : ℝ) ≤ 3) hexp_le
      _ = Real.rpow (3 : ℝ) s * Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
              simpa using
                (Real.rpow_add (by norm_num : 0 < (3 : ℝ)) s
                  (s * h ρ₁ ρ₂))
  have hcoeff_depth :
      (C * Real.rpow (3 : ℝ) k) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) ≤
        Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
    calc
      (C * Real.rpow (3 : ℝ) k) *
          Real.rpow (3 : ℝ) (s * (j : ℝ))
          ≤ (C * Real.rpow (3 : ℝ) k) *
              (Real.rpow (3 : ℝ) s *
                Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) := by
                exact mul_le_mul_of_nonneg_left hpow_depth hleft_factor_nonneg
      _ = ((C * Real.rpow (3 : ℝ) k) * Real.rpow (3 : ℝ) s) *
            Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by ring
      _ ≤ (Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂) *
            Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
              exact mul_le_mul_of_nonneg_right hscaleC
                (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      _ = Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
            Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by ring
  have hLambda_nonneg :
      0 ≤ Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ) :=
    Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg R 1 a (by norm_num)) _
  have hLambdaQ_nonneg :
      0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) :=
    Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le) _
  have hcoeffLambda :
      (C * Real.rpow (3 : ℝ) k) *
          Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ) ≤
        (Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
    calc
      (C * Real.rpow (3 : ℝ) k) *
          Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ)
          ≤
        (C * Real.rpow (3 : ℝ) k) *
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hLambda hleft_factor_nonneg
      _ =
        ((C * Real.rpow (3 : ℝ) k) *
          Real.rpow (3 : ℝ) (s * (j : ℝ))) *
            Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by ring
      _ ≤
        (Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right hcoeff_depth hLambdaQ_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt uL2Sq := Real.sqrt_nonneg _
  calc
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff R a C k uL2Sq
        =
      ((C * Real.rpow (3 : ℝ) k) *
        Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ)) *
        Real.sqrt uL2Sq := by
          unfold coarseCaccioppoliSingleCubeBoundaryConstantCoeff
          ring
    _ ≤
      ((Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) *
        Real.sqrt uL2Sq := by
          exact mul_le_mul_of_nonneg_right hcoeffLambda hsqrt_nonneg
    _ =
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Cwork uL2Sq h ρ₁ ρ₂ := by
        unfold coarseCaccioppoliBoundaryCrossCoeffOfHeight
        ring

/-- Depth-plus-one version of
`faithful_constant_descendant_coeff_le_cross_of_scale_height_le_depth`.

The arbitrary-center local-patch route takes descendants one generation deeper
than the integerized height.  The constant branch therefore needs one extra
factor `3^s` in the work-constant budget. -/
theorem faithful_constant_descendant_coeff_le_cross_of_scale_height_add_two_le_depth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) {s C Cwork k uL2Sq ρ₁ ρ₂ lam Lam : ℝ}
    {h : ℝ → ℝ → ℝ}
    (hC : 0 ≤ C)
    (hs : 0 < s) (hs1 : s < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hscaleC :
      (C * Real.rpow (3 : ℝ) k) * Real.rpow (3 : ℝ) (2 * s) ≤
        Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hj_le : (j : ℝ) ≤ h ρ₁ ρ₂ + 2) :
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff R a C k uL2Sq ≤
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Cwork uL2Sq h ρ₁ ρ₂ := by
  have hLambda :=
    faithful_constant_descendant_lambda_one_le_parent_lambda_s
      (Q := Q) (R := R) (j := j) a hs hs1 hEllCube hR hBsum_s
  have hleft_factor_nonneg :
      0 ≤ C * Real.rpow (3 : ℝ) k := by
    exact mul_nonneg hC (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hpow_depth :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) ≤
        Real.rpow (3 : ℝ) (2 * s) * Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
    have hexp_le : s * (j : ℝ) ≤ 2 * s + s * h ρ₁ ρ₂ := by
      nlinarith [mul_le_mul_of_nonneg_left hj_le hs.le]
    calc
      Real.rpow (3 : ℝ) (s * (j : ℝ))
          ≤ Real.rpow (3 : ℝ) (2 * s + s * h ρ₁ ρ₂) := by
              exact Real.rpow_le_rpow_of_exponent_le
                (by norm_num : (1 : ℝ) ≤ 3) hexp_le
      _ = Real.rpow (3 : ℝ) (2 * s) * Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
              simpa using
                (Real.rpow_add (by norm_num : 0 < (3 : ℝ)) (2 * s)
                  (s * h ρ₁ ρ₂))
  have hcoeff_depth :
      (C * Real.rpow (3 : ℝ) k) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) ≤
        Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
    calc
      (C * Real.rpow (3 : ℝ) k) *
          Real.rpow (3 : ℝ) (s * (j : ℝ))
          ≤ (C * Real.rpow (3 : ℝ) k) *
              (Real.rpow (3 : ℝ) (2 * s) *
                Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) := by
                exact mul_le_mul_of_nonneg_left hpow_depth hleft_factor_nonneg
      _ = ((C * Real.rpow (3 : ℝ) k) * Real.rpow (3 : ℝ) (2 * s)) *
            Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by ring
      _ ≤ (Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂) *
            Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
              exact mul_le_mul_of_nonneg_right hscaleC
                (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      _ = Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
            Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by ring
  have hLambda_nonneg :
      0 ≤ Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ) :=
    Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg R 1 a (by norm_num)) _
  have hLambdaQ_nonneg :
      0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) :=
    Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le) _
  have hcoeffLambda :
      (C * Real.rpow (3 : ℝ) k) *
          Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ) ≤
        (Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
    calc
      (C * Real.rpow (3 : ℝ) k) *
          Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ)
          ≤
        (C * Real.rpow (3 : ℝ) k) *
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hLambda hleft_factor_nonneg
      _ =
        ((C * Real.rpow (3 : ℝ) k) *
          Real.rpow (3 : ℝ) (s * (j : ℝ))) *
            Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by ring
      _ ≤
        (Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right hcoeff_depth hLambdaQ_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt uL2Sq := Real.sqrt_nonneg _
  calc
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff R a C k uL2Sq
        =
      ((C * Real.rpow (3 : ℝ) k) *
        Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ)) *
        Real.sqrt uL2Sq := by
          unfold coarseCaccioppoliSingleCubeBoundaryConstantCoeff
          ring
    _ ≤
      ((Cwork * coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂)) *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) *
        Real.sqrt uL2Sq := by
          exact mul_le_mul_of_nonneg_right hcoeffLambda hsqrt_nonneg
    _ =
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Cwork uL2Sq h ρ₁ ρ₂ := by
        unfold coarseCaccioppoliBoundaryCrossCoeffOfHeight
        ring

/-- The centered faithful coefficient produced at the integerized depth is
bounded by the parent alpha coefficient at the real localized height. -/
theorem faithful_centered_descendant_coeff_le_alpha_of_scale_height_le_depth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) {s t C Cwork k ρ₁ ρ₂ lam Lam : ℝ}
    {h : ℝ → ℝ → ℝ}
    (hC : 0 ≤ C) (hCwork : 0 ≤ Cwork)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hlt : ρ₁ < ρ₂)
    (hscaleC :
      C / (s * (1 - s)) * Real.rpow (3 : ℝ) k ≤
        Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hh_le : h ρ₁ ρ₂ ≤ (j : ℝ)) :
    coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s C k (j : ℝ) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Cwork h ρ₁ ρ₂ := by
  let hint : ℝ → ℝ → ℝ := fun _ _ => (j : ℝ)
  have hcent_j :
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s C k (j : ℝ) ≤
        coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Cwork hint ρ₁ ρ₂ :=
    faithful_centered_descendant_coeff_le_alpha_of_scale
      (Q := Q) (R := R) (j := j) a hC hCwork hs ht hst hEllCube hR
      hBsum_s hSigmaSum_t hlt hscaleC (by simp [hint])
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hexp_le :
      -coarseCaccioppoliSigma s t * (j : ℝ) ≤
        -coarseCaccioppoliSigma s t * h ρ₁ ρ₂ := by
    nlinarith
  have hpow_le :
      Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) ≤
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp_le
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hden_nonneg : 0 ≤ s * (1 - s) :=
    mul_nonneg hs.le (sub_nonneg.mpr hs1.le)
  have hfront_nonneg :
      0 ≤ Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    exact mul_nonneg (div_nonneg hCwork hden_nonneg)
      (coarseCaccioppoliGapInv_nonneg hlt)
  have htheta_nonneg :
      0 ≤ Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) :=
    Real.rpow_nonneg (thetaRatio_nonneg Q s t a hs.le (by linarith : 0 ≤ t)) _
  have hAlpha_le :
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Cwork hint ρ₁ ρ₂ ≤
        coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Cwork h ρ₁ ρ₂ := by
    calc
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Cwork hint ρ₁ ρ₂
          =
        (Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂) *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) *
          Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
            unfold coarseCaccioppoliBoundaryAlphaOfHeight
            simp [hint]
      _ ≤
        (Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂) *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
          Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow_le hfront_nonneg) htheta_nonneg
      _ =
        coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Cwork h ρ₁ ρ₂ := by
            unfold coarseCaccioppoliBoundaryAlphaOfHeight
            ring
  exact le_trans hcent_j hAlpha_le

end

end Homogenization
