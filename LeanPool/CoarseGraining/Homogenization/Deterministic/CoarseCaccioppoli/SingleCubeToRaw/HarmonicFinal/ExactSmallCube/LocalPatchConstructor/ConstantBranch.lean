/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.LocalPatchConstructor.Factors
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.LocalPatchNoteRawBridge
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.CenteredFactors
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.LocalPatch
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalConstantBranch

/-! # Constant Branch -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Local-patch exact small-cube constant branches

This file contains the constant/cross branch constructors for the
arbitrary-center local-patch exact small-cube coefficient route.
-/

theorem localPatch_centered_fronts_scale_mul_le_workGap_of_triadicGapScaleChoice
    {S Cwork s ρ₁ ρ₂ : ℝ} {k : ℕ}
    (hS : 0 ≤ S)
    (hwork : (81 : ℝ) * S ≤ Cwork / (s * (1 - s)))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    S * Real.rpow (3 : ℝ) (k : ℝ) ≤
      Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
  have hpow :
      Real.rpow (3 : ℝ) (k : ℝ) ≤
        81 * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    simpa [Real.rpow_natCast] using
      (coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice
        hchoice hlt)
  have hscaled := mul_le_mul_of_nonneg_left hpow hS
  have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    coarseCaccioppoliGapInv_nonneg hlt
  calc
    S * Real.rpow (3 : ℝ) (k : ℝ)
        ≤ S * (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) := hscaled
    _ = (81 * S) * coarseCaccioppoliGapInv ρ₁ ρ₂ := by ring
    _ ≤ Cwork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ :=
          mul_le_mul_of_nonneg_right hwork hgap_nonneg

/-- Split constant branch of the local-patch exact-to-parent-raw coefficient
constructor.

The integerized height/depth is governed by `Calpha`, but the constant/cross
coefficient itself is paid for by the independent `Ccross` budget. -/
theorem
    faithfulWorkSmallCubeExactRawConstantBranchSplit_of_closedCubeEllipticity_of_localPatchBufferedCutoffRadiusConst
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (hClocal : 0 ≤ Clocal)
    (hwork_constant_cross :
      (81 : ℝ) * Real.rpow (3 : ℝ) (2 * s) *
          ((Fintype.card (Fin d) : ℝ) * Clocal) ≤
        (Fintype.card (Fin d) : ℝ) * Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤
        (Fintype.card (Fin d) : ℝ) * Clocal) :
    ∀ n : ℕ,
      let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
      let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
      let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
      let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
      let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
      let hheight : ℝ → ℝ → ℝ :=
        coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
          coarseCaccioppoliTriadicGapScale
      let j : ℕ :=
        coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
          CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ + 1
      let ξ : Vec d → Vec d :=
        scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
      let B : ℝ := coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm
      let K : ℝ :=
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
      ∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
            (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  intro n
  let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
  let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let kR : ℝ := (k : ℝ)
  let j0 : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
      CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j : ℕ := j0 + 1
  let ξ : Vec d → Vec d :=
    scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
  let B : ℝ := coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm
  let K : ℝ :=
    coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
  have hρ₁ : (1 / 3 : ℝ) ≤ ρ₁ := by
    simpa [ρ₁] using (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hρ₁_pos : 0 < ρ₁ := by
    exact (show (0 : ℝ) < 1 / 3 by norm_num).trans_le hρ₁
  have hlt : ρ₁ < ρ₂ := by
    simpa [ρ₁, ρ₂] using
      coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ : ρ₂ ≤ 1 := by
    simpa [ρ₂] using (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  have hlt_m : ρ₁ < ρm := by
    simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ := by
    simpa [k, ρ₁, ρ₂] using coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂
  have hjk : k ≤ j0 := by
    simpa [k, j0, CeffAlpha, ρ₁, ρ₂] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice_ge_scaleChoice
        Q a s t CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂)
  have hj0_le_height_add_one : (j0 : ℝ) ≤ hheight ρ₁ ρ₂ + 1 := by
    simpa [hheight, j0, k, CeffAlpha, ρ₁, ρ₂,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      (faithful_integerized_height_depth_le_height_add_one
        (Q := Q) (a := a) (s := s) (t := t) (C := CeffAlpha) hs k)
  have hj_le_height_add_two : (j : ℝ) ≤ hheight ρ₁ ρ₂ + 2 := by
    dsimp [j]
    norm_num
    nlinarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, coarseCaccioppoliLocalPatchCutoffHessianBound]
    exact div_nonneg (quantitativeCubeCutoffHessianConst_nonneg d) (sq_nonneg _)
  have hscale_const :
      (CeffLocal * Real.rpow (3 : ℝ) kR) * Real.rpow (3 : ℝ) (2 * s) ≤
        CeffCross * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    simpa [CeffLocal, CeffCross, kR] using
      (faithful_scale_mul_rpow_s_le_workGap_of_triadicGapScaleChoice
        (s := 2 * s) (C := CeffLocal) (Cwork := CeffCross)
        (mul_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card (Fin d))) hClocal)
        (by simpa [CeffLocal, CeffCross, mul_assoc] using hwork_constant_cross)
        hchoice hlt)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hBsum_s_parent :
      Summable (fun m : ℕ =>
        geometricWeight s 1 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a s hs hEllCube hData
  dsimp
  intro R hR
  have hRj : R ∈ descendantsAtDepth Q j := by
    simpa [j, j0, CeffAlpha, ρ₁, ρ₂] using hR
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEllCube.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hRj)
  have hRecR :
      OpenCubeDescendantEllipticRecoveryFamily R a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := R) (a := a) hEllR hOrigin
  have hDataR : OpenCubeDescendantDeterministicCoarseData R a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRecR
  have hsum_s :
      Summable (fun m : ℕ =>
        geometricWeight s 1 m *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      R a s hs hEllR hDataR
  have hsum_one :
      Summable (fun m : ℕ =>
        geometricWeight (1 : ℝ) 1 m *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a)
            (1 / 2 : ℝ)) := by
    have hs_lt_one : s < 1 := by linarith
    refine summable_geometricWeight_one_of_lt ?_ hs hs_lt_one hsum_s
    intro m
    exact Real.rpow_nonneg
      (maxDescendantBBlockNormAtScale_nonneg R
        (sub_le_self _ (by exact_mod_cast Nat.zero_le m)) a) _
  have hξ :
      cubeLpNorm R ∞
          (scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)) ≤
        coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm := by
    simpa [coarseCaccioppoliLocalPatchCutoffGradientBound] using
      coarseCaccioppoliLocalCanonicalFun_cubeLpNorm_infty_gradientField_le_on_cube
        Q R center hρ₁_pos hlt_m
  have hconstn :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
            (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
            (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
          (B + cubeBesovScaleWeight 1 R *
            coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR := by
    simpa [B, CeffLocal, kR, k, ρm] using
      (coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_mul_localPatch_buffered_cutoff_terms_le_singleCubeBoundaryConstantBaseCoeff_of_descendant_succ
        (Q := Q) (R := R) (a := a) (Ceff := CeffLocal)
        (k := k) (j := j0) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
        (by simpa [j] using hRj) hchoice hlt hjk
        (by simpa [CeffLocal] using hlarge))
  have hlocal :
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R *
            cubeLpNorm R ∞
              (scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm))) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR := by
    have hlocal' :=
      coarseCaccioppoliFluxEnergyExactConstantCoeff_mul_le_singleCubeBoundaryConstantBaseCoeff_of_factor_bounds
        R a
        (scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm))
        j hB_nonneg
        (Ceff := CeffLocal) (kR := kR + (j : ℝ))
        (Aavg := coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (Aflux1 := coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor R a
          (by norm_num : 0 < (1 : ℝ)) hsum_one)
        (by simp [coarseCaccioppoliLambdaFactor])
        hξ
        (by
          simpa [B, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hconstn)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlocal'
  have hbase_le :
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR ≤ K := by
    have hsingle :
        coarseCaccioppoliSingleCubeBoundaryConstantCoeff R a CeffLocal kR 1 ≤ K := by
      simpa [CeffLocal, CeffCross, hheight, ρ₁, ρ₂, kR, j, K] using
        (faithful_constant_descendant_coeff_le_cross_of_scale_height_add_two_le_depth
          (Q := Q) (R := R) (j := j) a
          (s := s) (C := CeffLocal) (Cwork := CeffCross) (k := kR)
          (uL2Sq := 1) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
          (h := hheight)
          (mul_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card (Fin d))) hClocal)
          hs (by nlinarith [ht, hst]) hEllCube hRj
          hBsum_s_parent
          hscale_const hj_le_height_add_two)
    simpa [coarseCaccioppoliSingleCubeBoundaryConstantCoeff,
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff] using hsingle
  exact le_trans
    (by simpa [ξ, B, K] using hlocal)
    hbase_le

/-- All-radii split constant branch of the local-patch exact-to-parent-raw
coefficient constructor.

This is the proof-producing version used by the standard beta-dependent
radius iteration. -/
theorem
    faithfulWorkSmallCubeExactRawConstantBranchSplitAllRadii_of_closedCubeEllipticity_of_localPatchBufferedCutoffRadiusConst
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (hClocal : 0 ≤ Clocal)
    (hwork_constant_cross :
      (81 : ℝ) * Real.rpow (3 : ℝ) (2 * s) *
          ((Fintype.card (Fin d) : ℝ) * Clocal) ≤
        (Fintype.card (Fin d) : ℝ) * Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤
        (Fintype.card (Fin d) : ℝ) * Clocal) :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
      let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
      let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
      let hheight : ℝ → ℝ → ℝ :=
        coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
          coarseCaccioppoliTriadicGapScale
      let j : ℕ :=
        coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
          CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ + 1
      let ξ : Vec d → Vec d :=
        scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
      let B : ℝ := coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm
      let K : ℝ :=
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
      ∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
            (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let kR : ℝ := (k : ℝ)
  let j0 : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
      CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j : ℕ := j0 + 1
  let ξ : Vec d → Vec d :=
    scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
  let B : ℝ := coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm
  let K : ℝ :=
    coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
  have hρ₁_pos : 0 < ρ₁ := by
    exact (show (0 : ℝ) < 1 / 3 by norm_num).trans_le hρ₁
  have hlt_m : ρ₁ < ρm := by
    simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ := by
    simpa [k] using coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂
  have hjk : k ≤ j0 := by
    simpa [k, j0, CeffAlpha] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice_ge_scaleChoice
        Q a s t CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂)
  have hj0_le_height_add_one : (j0 : ℝ) ≤ hheight ρ₁ ρ₂ + 1 := by
    simpa [hheight, j0, k, CeffAlpha,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      (faithful_integerized_height_depth_le_height_add_one
        (Q := Q) (a := a) (s := s) (t := t) (C := CeffAlpha) hs k)
  have hj_le_height_add_two : (j : ℝ) ≤ hheight ρ₁ ρ₂ + 2 := by
    dsimp [j]
    norm_num
    nlinarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, coarseCaccioppoliLocalPatchCutoffHessianBound]
    exact div_nonneg (quantitativeCubeCutoffHessianConst_nonneg d) (sq_nonneg _)
  have hscale_const :
      (CeffLocal * Real.rpow (3 : ℝ) kR) * Real.rpow (3 : ℝ) (2 * s) ≤
        CeffCross * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    simpa [CeffLocal, CeffCross, kR] using
      (faithful_scale_mul_rpow_s_le_workGap_of_triadicGapScaleChoice
        (s := 2 * s) (C := CeffLocal) (Cwork := CeffCross)
        (mul_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card (Fin d))) hClocal)
        (by simpa [CeffLocal, CeffCross, mul_assoc] using hwork_constant_cross)
        hchoice hlt)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hBsum_s_parent :
      Summable (fun m : ℕ =>
        geometricWeight s 1 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a s hs hEllCube hData
  dsimp
  intro R hR
  have hRj : R ∈ descendantsAtDepth Q j := by
    simpa [j, j0, CeffAlpha] using hR
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEllCube.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hRj)
  have hRecR :
      OpenCubeDescendantEllipticRecoveryFamily R a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := R) (a := a) hEllR hOrigin
  have hDataR : OpenCubeDescendantDeterministicCoarseData R a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRecR
  have hsum_s :
      Summable (fun m : ℕ =>
        geometricWeight s 1 m *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      R a s hs hEllR hDataR
  have hsum_one :
      Summable (fun m : ℕ =>
        geometricWeight (1 : ℝ) 1 m *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a)
            (1 / 2 : ℝ)) := by
    have hs_lt_one : s < 1 := by linarith
    refine summable_geometricWeight_one_of_lt ?_ hs hs_lt_one hsum_s
    intro m
    exact Real.rpow_nonneg
      (maxDescendantBBlockNormAtScale_nonneg R
        (sub_le_self _ (by exact_mod_cast Nat.zero_le m)) a) _
  have hξ :
      cubeLpNorm R ∞
          (scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)) ≤
        coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm := by
    simpa [coarseCaccioppoliLocalPatchCutoffGradientBound] using
      coarseCaccioppoliLocalCanonicalFun_cubeLpNorm_infty_gradientField_le_on_cube
        Q R center hρ₁_pos hlt_m
  have hconstn :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
            (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
            (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
          (B + cubeBesovScaleWeight 1 R *
            coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR := by
    simpa [B, CeffLocal, kR, k, ρm] using
      (coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_mul_localPatch_buffered_cutoff_terms_le_singleCubeBoundaryConstantBaseCoeff_of_descendant_succ
        (Q := Q) (R := R) (a := a) (Ceff := CeffLocal)
        (k := k) (j := j0) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
        (by simpa [j] using hRj) hchoice hlt hjk
        (by simpa [CeffLocal] using hlarge))
  have hlocal :
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R *
            cubeLpNorm R ∞
              (scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm))) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR := by
    have hlocal' :=
      coarseCaccioppoliFluxEnergyExactConstantCoeff_mul_le_singleCubeBoundaryConstantBaseCoeff_of_factor_bounds
        R a
        (scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm))
        j hB_nonneg
        (Ceff := CeffLocal) (kR := kR + (j : ℝ))
        (Aavg := coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (Aflux1 := coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor R a
          (by norm_num : 0 < (1 : ℝ)) hsum_one)
        (by simp [coarseCaccioppoliLambdaFactor])
        hξ
        (by
          simpa [B, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hconstn)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlocal'
  have hbase_le :
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR ≤ K := by
    have hsingle :
        coarseCaccioppoliSingleCubeBoundaryConstantCoeff R a CeffLocal kR 1 ≤ K := by
      simpa [CeffLocal, CeffCross, hheight, kR, j, K] using
        (faithful_constant_descendant_coeff_le_cross_of_scale_height_add_two_le_depth
          (Q := Q) (R := R) (j := j) a
          (s := s) (C := CeffLocal) (Cwork := CeffCross) (k := kR)
          (uL2Sq := 1) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
          (h := hheight)
          (mul_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card (Fin d))) hClocal)
          hs (by nlinarith [ht, hst]) hEllCube hRj
          hBsum_s_parent
          hscale_const hj_le_height_add_two)
    simpa [coarseCaccioppoliSingleCubeBoundaryConstantCoeff,
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff] using hsingle
  exact le_trans
    (by simpa [ξ, B, K] using hlocal)
    hbase_le


end

end Homogenization
