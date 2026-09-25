/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalConstantBranch
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.CenteredLocalCoefficient
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Setup

/-! # Centered Fronts -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Local small-cube coefficient package constructors

This sidecar file packages the two local EnergyBridge branch helpers into the
canonical harmonic small-cube local coefficient hypothesis used by the final
single-cube-to-raw bridge.
-/

/-- Split buffered direct exact-raw constant branch calibration.

The descendant depth and explicit height are chosen with `Calpha`, while the
parent cross coefficient is charged only to `Ccross`.  This is the upstream
constant-branch version of the split note-RHS budget. -/
theorem
    faithfulWorkSmallCubeExactRawConstantBranchSplit_of_closedCubeEllipticity_of_bufferedCutoffRadiusConst
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (hClocal : 0 ≤ Clocal) (_hCcross : 0 ≤ Ccross)
    (hwork_constant_cross :
      (81 : ℝ) * Real.rpow (3 : ℝ) s *
          ((Fintype.card (Fin d) : ℝ) * Clocal) ≤
        (Fintype.card (Fin d) : ℝ) * Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤
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
          CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
      let ξ : Vec d → Vec d :=
        scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρm)
      let B : ℝ := coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm
      let K : ℝ :=
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
      ∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
            (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K := by
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCeffLocal_nonneg : 0 ≤ CeffLocal := mul_nonneg hcard_nonneg hClocal
  have hs1 : s < 1 := by nlinarith [ht, hst]
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a s hs hEllCube hData
  intro n
  let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
  let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let kR : ℝ := (k : ℝ)
  let j : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
      CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let ξ : Vec d → Vec d :=
    scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρm)
  let B : ℝ := coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm
  let K : ℝ :=
    coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
  have hρ₁ : (1 / 3 : ℝ) ≤ ρ₁ := by
    simpa [ρ₁] using (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hlt : ρ₁ < ρ₂ := by
    simpa [ρ₁, ρ₂] using
      coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ : ρ₂ ≤ 1 := by
    simpa [ρ₂] using (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  have hlt_m : ρ₁ < ρm := by
    simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  let ηρ : QuantitativeCubeCutoff Q ρ₁ ρm :=
    coarseCaccioppoliCanonicalQuantitativeCutoff Q hρ₁ hlt_m
  have hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ := by
    simpa [k] using coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂
  have hjk : k ≤ j := by
    simpa [k, j, CeffAlpha] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice_ge_scaleChoice
        Q a s t CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂)
  have hj_le_height_add_one : (j : ℝ) ≤ hheight ρ₁ ρ₂ + 1 := by
    simpa [hheight, j, k, CeffAlpha, ρ₁, ρ₂,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      (faithful_integerized_height_depth_le_height_add_one
        (Q := Q) (a := a) (s := s) (t := t) (C := CeffAlpha) hs k)
  have hscale_const :
      (CeffLocal * Real.rpow (3 : ℝ) kR) * Real.rpow (3 : ℝ) s ≤
        CeffCross * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    simpa [CeffLocal, CeffCross, kR] using
      (faithful_scale_mul_rpow_s_le_workGap_of_triadicGapScaleChoice
        (s := s) (C := CeffLocal) (Cwork := CeffCross)
        hCeffLocal_nonneg
        (by simpa [CeffLocal, CeffCross, mul_assoc] using hwork_constant_cross)
        hchoice hlt)
  have hB_nonneg : 0 ≤ B := by
    simpa [B, ρm] using coarseCaccioppoliQuantitativeCutoffHessianBound_nonneg Q ηρ
  have hconstn :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
            (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
            (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
          (B + cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm) ≤
          coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR := by
    intro R hR
    simpa [B, CeffLocal, kR, k, ρm] using
      (coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_mul_parent_buffered_cutoff_terms_le_singleCubeBoundaryConstantBaseCoeff_of_descendant
        (Q := Q) (R := R) (a := a) (Ceff := CeffLocal)
        (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
        hR hchoice hlt hjk (by simpa [CeffLocal] using hlarge))
  dsimp
  intro R hR
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEllCube.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
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
  have hlocal :
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R *
            cubeLpNorm R ∞ (scalarCutoffGradientField ηρ)) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR := by
    have hlocal' :=
      coarseCaccioppoliFluxEnergyExactConstantCoeff_mul_cutoffGradient_le_singleCubeBoundaryConstantBaseCoeff_of_factor_bounds_on_descendant
        (Q := Q) (R := R) (j := j) hR a (η := ηρ) (B := B)
        (Ceff := CeffLocal) (kR := kR + (j : ℝ))
        (Aavg := coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (Aflux1 := coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        hB_nonneg
        (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor R a
          (by norm_num : 0 < (1 : ℝ)) hsum_one)
        (by simp [coarseCaccioppoliLambdaFactor])
        (by
          simpa [B, ρm, coarseCaccioppoliQuantitativeCutoffGradientBound,
            sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hconstn R hR)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlocal'
  have hbase_le :
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR ≤ K := by
    simpa [coarseCaccioppoliSingleCubeBoundaryConstantCoeff,
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff, K] using
      (faithful_constant_descendant_coeff_le_cross_of_scale_height_le_depth
        (Q := Q) (R := R) (j := j) a
        (s := s) (C := CeffLocal) (Cwork := CeffCross) (k := kR)
        (uL2Sq := (1 : ℝ)) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
        (h := hheight)
        hCeffLocal_nonneg hs hs1 hEllCube hR hBsum_s
        hscale_const hj_le_height_add_one)
  exact le_trans
    (by
      simpa [ξ, ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
        QuantitativeCubeCutoff.canonical, B, K, ρm] using hlocal)
    hbase_le

/-- All-radii split buffered direct exact-raw constant branch calibration.

This is the same constant/cross branch as
`faithfulWorkSmallCubeExactRawConstantBranchSplit_of_closedCubeEllipticity_of_bufferedCutoffRadiusConst`,
but with an arbitrary radius pair `1/3 ≤ ρ₁ < ρ₂ ≤ 1`.  It is the
constant-branch input needed by the standard beta-dependent radius iteration. -/
theorem
    faithfulWorkSmallCubeExactRawConstantBranchSplitAllRadii_of_closedCubeEllipticity_of_bufferedCutoffRadiusConst
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (hClocal : 0 ≤ Clocal) (_hCcross : 0 ≤ Ccross)
    (hwork_constant_cross :
      (81 : ℝ) * Real.rpow (3 : ℝ) s *
          ((Fintype.card (Fin d) : ℝ) * Clocal) ≤
        (Fintype.card (Fin d) : ℝ) * Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤
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
          CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
      let ξ : Vec d → Vec d :=
        scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρm)
      let B : ℝ := coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm
      let K : ℝ :=
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
      ∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
            (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K := by
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCeffLocal_nonneg : 0 ≤ CeffLocal := mul_nonneg hcard_nonneg hClocal
  have hs1 : s < 1 := by nlinarith [ht, hst]
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a s hs hEllCube hData
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let kR : ℝ := (k : ℝ)
  let j : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
      CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let ξ : Vec d → Vec d :=
    scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρm)
  let B : ℝ := coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm
  let K : ℝ :=
    coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
  have hlt_m : ρ₁ < ρm := by
    simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  let ηρ : QuantitativeCubeCutoff Q ρ₁ ρm :=
    coarseCaccioppoliCanonicalQuantitativeCutoff Q hρ₁ hlt_m
  have hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ := by
    simpa [k] using coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂
  have hjk : k ≤ j := by
    simpa [k, j, CeffAlpha] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice_ge_scaleChoice
        Q a s t CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂)
  have hj_le_height_add_one : (j : ℝ) ≤ hheight ρ₁ ρ₂ + 1 := by
    simpa [hheight, j, k, CeffAlpha,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      (faithful_integerized_height_depth_le_height_add_one
        (Q := Q) (a := a) (s := s) (t := t) (C := CeffAlpha) hs k)
  have hscale_const :
      (CeffLocal * Real.rpow (3 : ℝ) kR) * Real.rpow (3 : ℝ) s ≤
        CeffCross * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    simpa [CeffLocal, CeffCross, kR] using
      (faithful_scale_mul_rpow_s_le_workGap_of_triadicGapScaleChoice
        (s := s) (C := CeffLocal) (Cwork := CeffCross)
        hCeffLocal_nonneg
        (by simpa [CeffLocal, CeffCross, mul_assoc] using hwork_constant_cross)
        hchoice hlt)
  have hB_nonneg : 0 ≤ B := by
    simpa [B, ρm] using coarseCaccioppoliQuantitativeCutoffHessianBound_nonneg Q ηρ
  have hconstn :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
            (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
            (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
          (B + cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm) ≤
          coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR := by
    intro R hR
    simpa [B, CeffLocal, kR, k, ρm] using
      (coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_mul_parent_buffered_cutoff_terms_le_singleCubeBoundaryConstantBaseCoeff_of_descendant
        (Q := Q) (R := R) (a := a) (Ceff := CeffLocal)
        (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
        hR hchoice hlt hjk (by simpa [CeffLocal] using hlarge))
  dsimp
  intro R hR
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEllCube.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
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
  have hlocal :
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R *
            cubeLpNorm R ∞ (scalarCutoffGradientField ηρ)) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR := by
    have hlocal' :=
      coarseCaccioppoliFluxEnergyExactConstantCoeff_mul_cutoffGradient_le_singleCubeBoundaryConstantBaseCoeff_of_factor_bounds_on_descendant
        (Q := Q) (R := R) (j := j) hR a (η := ηρ) (B := B)
        (Ceff := CeffLocal) (kR := kR + (j : ℝ))
        (Aavg := coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (Aflux1 := coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        hB_nonneg
        (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor R a
          (by norm_num : 0 < (1 : ℝ)) hsum_one)
        (by simp [coarseCaccioppoliLambdaFactor])
        (by
          simpa [B, ρm, coarseCaccioppoliQuantitativeCutoffGradientBound,
            sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hconstn R hR)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlocal'
  have hbase_le :
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a CeffLocal kR ≤ K := by
    simpa [coarseCaccioppoliSingleCubeBoundaryConstantCoeff,
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff, K] using
      (faithful_constant_descendant_coeff_le_cross_of_scale_height_le_depth
        (Q := Q) (R := R) (j := j) a
        (s := s) (C := CeffLocal) (Cwork := CeffCross) (k := kR)
        (uL2Sq := (1 : ℝ)) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
        (h := hheight)
        hCeffLocal_nonneg hs hs1 hEllCube hR hBsum_s
        hscale_const hj_le_height_add_one)
  exact le_trans
    (by
      simpa [ξ, ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
        QuantitativeCubeCutoff.canonical, B, K, ρm] using hlocal)
    hbase_le

/-- Scalar front multiplying the average part of the centered exact
coefficient after inserting the descendant cutoff-gradient estimate. -/
def coarseCaccioppoliCenteredAverageFront (d : ℕ) (s C : ℝ) : ℝ :=
  (d : ℝ) * (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
    ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
    (2 * quantitativeCubeCutoffGradientConst d)

/-- The average part of the centered exact coefficient has the small-cube
cutoff-gradient gain `3^(k-j)` when the canonical `A^\circ_1` factor is kept
on the descendant cube.  This is the first substitution line in the LaTeX
centered single-cube estimate. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localAcircOne_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) {s Ceff : ℝ}
    {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hCeff : 0 ≤ Ceff) (hs : 0 < s)
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) Ceff ≤
      ((d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((2 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) := by
  let cut : ℝ :=
    cubeBesovScaleWeight (-1) R *
      coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂
  let cutBound : ℝ :=
    (2 * quantitativeCubeCutoffGradientConst d) *
      Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))
  let K : ℝ :=
    (d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹))
  let L : ℝ :=
    Real.rpow (LambdaSqFinite R s 1 a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSqFinite R (1 : ℝ) 1 a) (-1 / 2 : ℝ)
  have hcut : cut ≤ cutBound := by
    simpa [cut, cutBound] using
      (cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_le_rpow_sub
        (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt)
  have hdiscS_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hdisc1_pos : 0 < geometricDiscount (1 : ℝ) 1 := by
    exact geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    refine mul_nonneg (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ)) ?_
    refine mul_nonneg ?_ ?_
    · exact mul_nonneg
        (mul_nonneg (by positivity) hCeff)
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    · exact mul_nonneg (inv_nonneg.mpr hdiscS_pos.le)
        (inv_nonneg.mpr hdisc1_pos.le)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    simpa [LambdaSq, lambdaSq] using
      (mul_nonneg
        (Real.rpow_nonneg
          (multiscale_ellipticity_LambdaSq_one_nonneg R s a hs.le) _)
        (Real.rpow_nonneg
          (multiscale_ellipticity_lambdaSq_one_nonneg R (1 : ℝ) a (by norm_num)) _))
  have hmain : K * cut * L ≤ K * cutBound * L := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcut hK_nonneg) hL_nonneg
  have hleft :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) Ceff =
        K * cut * L := by
    dsimp [K, cut, L]
    unfold coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
      coarseCaccioppoliLambdaFactor
      coarseCaccioppoliCanonicalGradientAcircOne
      coarseCaccioppoliCanonicalGradientAcirc
    simp only [LambdaSq, lambdaSq]
    ring_nf
    rw [show LambdaSqFinite R s 1 a ^ (1 / 2 : ℝ) =
        Real.rpow (LambdaSqFinite R s 1 a) (1 / 2 : ℝ) by rfl,
      show lambdaSqFinite R (1 : ℝ) 1 a ^ (-1 / 2 : ℝ) =
        Real.rpow (lambdaSqFinite R (1 : ℝ) 1 a) (-1 / 2 : ℝ) by rfl]
    ac_rfl
  have hright :
      K * cutBound * L =
        ((d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
          ((2 * quantitativeCubeCutoffGradientConst d) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
          (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
            Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) := by
    dsimp [K, cutBound, L]
  calc
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) Ceff
        = K * cut * L := hleft
    _ ≤ K * cutBound * L := hmain
    _ =
      ((d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((2 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) := hright

/-- Buffered version of
`coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localAcircOne_le_rpow_sub`.
The midpoint cutoff doubles the average-branch gradient contribution. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localAcircOne_buffered_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) {s Ceff : ℝ}
    {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hCeff : 0 ≤ Ceff) (hs : 0 < s)
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)) Ceff ≤
      ((d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((4 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) := by
  have hfull :=
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localAcircOne_le_rpow_sub
      (Q := Q) (R := R) (a := a) (s := s) (Ceff := Ceff)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      hCeff hs hR hchoice hlt
  have hleft_eq :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)) Ceff =
        2 * coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) Ceff := by
    rw [coarseCaccioppoliQuantitativeCutoffGradientBound_buffered_eq_two_mul Q hlt]
    unfold coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
      coarseCaccioppoliCanonicalGradientAcircOne
    ring
  calc
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)) Ceff
        =
      2 * coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) Ceff :=
        hleft_eq
    _ ≤
      2 *
        (((d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
          ((2 * quantitativeCubeCutoffGradientConst d) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
          (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
            Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hfull (by norm_num : (0 : ℝ) ≤ 2)
    _ =
      ((d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((4 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) := by
          ring

/-- The average part of the centered exact coefficient localizes directly to
the parent `Alpha` coefficient once the fixed average-branch scalar front is
absorbed into the working constant.

This is the average-term line of the LaTeX small-cube coefficient comparison:
the cutoff gradient gives `3^(k-j)`, the new descendant product lemma turns
`3^{-j} Lambda_s(R)^{1/2} lambda_1(R)^{-1/2}` into the parent theta term, and
the integerized height only improves the final `3^{-sigma h}` decay. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localAcircOne_le_alpha_of_scale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {s t CeffLocal CeffWork : ℝ} {k j : ℕ} {ρ₁ ρ₂ lam Lam : ℝ}
    {hheight : ℝ → ℝ → ℝ}
    (hCeffLocal : 0 ≤ CeffLocal) (hCeffWork : 0 ≤ CeffWork)
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
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂)
    (hscale :
      ((d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        (2 * quantitativeCubeCutoffGradientConst d)) *
          Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hheight_le_j : hheight ρ₁ ρ₂ ≤ (j : ℝ)) :
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) CeffLocal ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
  let A : ℝ :=
    (d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
      (2 * quantitativeCubeCutoffGradientConst d)
  let P : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)
  let Theta : ℝ := Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  let front : ℝ := CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂
  have hsub :=
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localAcircOne_le_rpow_sub
      (Q := Q) (R := R) (a := a) (s := s) (Ceff := CeffLocal)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      hCeffLocal hs hR hchoice hlt
  have hprod :
      Real.rpow (3 : ℝ) (-(j : ℝ)) * P ≤
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) * Theta := by
    simpa [P, Theta] using
      (faithful_centered_descendant_product_one_le_parent_theta
        (Q := Q) (R := R) (j := j) a hs ht hst hEllCube hR hBsum_s hSigmaSum_t)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg R s a hs.le) _)
      (Real.rpow_nonneg
        (multiscale_ellipticity_lambdaSq_one_nonneg R (1 : ℝ) a (by norm_num)) _)
  have hprod_left_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-(j : ℝ)) * P :=
    mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _) hP_nonneg
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hden_nonneg : 0 ≤ s * (1 - s) :=
    mul_nonneg hs.le (sub_nonneg.mpr hs1.le)
  have hfront_nonneg : 0 ≤ front := by
    dsimp [front]
    exact mul_nonneg (div_nonneg hCeffWork hden_nonneg)
      (coarseCaccioppoliGapInv_nonneg hlt)
  have hscaled :=
    mul_le_mul hscale hprod hprod_left_nonneg hfront_nonneg
  have hpow_split :
      Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) =
        Real.rpow (3 : ℝ) (k : ℝ) * Real.rpow (3 : ℝ) (-(j : ℝ)) := by
    rw [sub_eq_add_neg]
    exact Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
  have hsub_rhs_eq :
      ((d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((2 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        P =
        (A * Real.rpow (3 : ℝ) (k : ℝ)) *
          (Real.rpow (3 : ℝ) (-(j : ℝ)) * P) := by
    calc
      ((d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((2 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        P =
        ((d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((2 * quantitativeCubeCutoffGradientConst d) *
          (Real.rpow (3 : ℝ) (k : ℝ) *
            Real.rpow (3 : ℝ) (-(j : ℝ))))) *
        P := by
          rw [hpow_split]
      _ = (A * Real.rpow (3 : ℝ) (k : ℝ)) *
          (Real.rpow (3 : ℝ) (-(j : ℝ)) * P) := by
            dsimp [A]
            ring_nf
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hexp_le :
      -coarseCaccioppoliSigma s t * (j : ℝ) ≤
        -coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂ := by
    nlinarith
  have hpow_height :
      Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) ≤
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (3 : ℝ)) hexp_le
  have hTheta_nonneg : 0 ≤ Theta := by
    dsimp [Theta]
    exact Real.rpow_nonneg (thetaRatio_nonneg Q s t a hs.le ht.le) _
  have hheight_step :
      front * (Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) * Theta) ≤
        front * (Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
          Theta) := by
    refine mul_le_mul_of_nonneg_left ?_ hfront_nonneg
    exact mul_le_mul_of_nonneg_right hpow_height hTheta_nonneg
  calc
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂) CeffLocal
        ≤
      ((d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((2 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        P := hsub
    _ = (A * Real.rpow (3 : ℝ) (k : ℝ)) *
          (Real.rpow (3 : ℝ) (-(j : ℝ)) * P) := hsub_rhs_eq
    _ ≤ front *
        (Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) * Theta) :=
          hscaled
    _ ≤ front *
        (Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
          Theta) := hheight_step
    _ = CeffWork / (s * (1 - s)) *
        coarseCaccioppoliGapInv ρ₁ ρ₂ *
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
          dsimp [front, Theta]
          ring_nf
    _ = coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
          rfl

theorem coarseCaccioppoliCenteredAverageFront_nonneg
    (d : ℕ) {s C : ℝ} (hC : 0 ≤ C) (hs : 0 < s) :
    0 ≤ coarseCaccioppoliCenteredAverageFront d s C := by
  have hdisc_s_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hdisc_one_pos : 0 < geometricDiscount (1 : ℝ) 1 := by
    exact geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hnote_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  unfold coarseCaccioppoliCenteredAverageFront
  refine mul_nonneg ?_ ?_
  · refine mul_nonneg ?_ ?_
    · exact_mod_cast Nat.zero_le d
    · exact mul_nonneg hnote_nonneg
        (mul_nonneg (inv_nonneg.mpr hdisc_s_pos.le)
          (inv_nonneg.mpr hdisc_one_pos.le))
  · exact mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
      (quantitativeCubeCutoffGradientConst_nonneg d)

/-- Multiplicativity of Besov scale weights on a fixed cube. -/
theorem cubeBesovScaleWeight_mul_eq_add {d : ℕ}
    (Q : TriadicCube d) (r q : ℝ) :
    cubeBesovScaleWeight r Q * cubeBesovScaleWeight q Q =
      cubeBesovScaleWeight (r + q) Q := by
  have hpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  unfold cubeBesovScaleWeight
  rw [← Real.rpow_add hpos]
  congr 1
  ring

/-- Scalar front multiplying the Hessian piece of the centered Besov exact
coefficient before the cutoff scale estimate is inserted. -/
def coarseCaccioppoliCenteredBesovHessianBase (d : ℕ) (s C : ℝ) : ℝ :=
  (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s) *
    (geometricDiscount s 1)⁻¹ *
    (2 * (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
      (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        (geometricDiscount (1 : ℝ) 1)⁻¹)))

/-- Scalar front multiplying the gradient piece of the centered Besov exact
coefficient before the cutoff scale estimate is inserted. -/
def coarseCaccioppoliCenteredBesovGradientBase (d : ℕ) (s C : ℝ) : ℝ :=
  (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s) *
    (geometricDiscount s 1)⁻¹ *
    (2 * ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      (1 - (3 : ℝ) ^ (-s))⁻¹) *
      (geometricDiscount (1 - s) 1)⁻¹))

/-- Hessian scalar front after inserting the descendant cutoff estimate. -/
def coarseCaccioppoliCenteredBesovHessianFront (d : ℕ) (s C : ℝ) : ℝ :=
  coarseCaccioppoliCenteredBesovHessianBase d s C *
    (4 * quantitativeCubeCutoffHessianConst d)

/-- Gradient scalar front after inserting the descendant cutoff estimate. -/
def coarseCaccioppoliCenteredBesovGradientFront (d : ℕ) (s C : ℝ) : ℝ :=
  coarseCaccioppoliCenteredBesovGradientBase d s C *
    (2 * quantitativeCubeCutoffGradientConst d)

theorem coarseCaccioppoliCenteredBesovHessianFront_nonneg
    (d : ℕ) {s C : ℝ} (hC : 0 ≤ C) (hs : 0 < s) :
    0 ≤ coarseCaccioppoliCenteredBesovHessianFront d s C := by
  have hdisc_s_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hdisc_one_pos : 0 < geometricDiscount (1 : ℝ) 1 := by
    exact geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hnote_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  unfold coarseCaccioppoliCenteredBesovHessianFront
    coarseCaccioppoliCenteredBesovHessianBase
  refine mul_nonneg ?_ ?_
  · refine mul_nonneg ?_ ?_
    · refine mul_nonneg ?_ (inv_nonneg.mpr hdisc_s_pos.le)
      exact mul_nonneg (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    · refine mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) ?_
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg hnote_nonneg (inv_nonneg.mpr hdisc_one_pos.le))
  · exact mul_nonneg (by norm_num : 0 ≤ (4 : ℝ))
      (quantitativeCubeCutoffHessianConst_nonneg d)

theorem coarseCaccioppoliCenteredBesovGradientFront_nonneg
    (d : ℕ) {s C : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1) :
    0 ≤ coarseCaccioppoliCenteredBesovGradientFront d s C := by
  have hdisc_s_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hdisc_sub_pos : 0 < geometricDiscount (1 - s) 1 := by
    exact geometricDiscount_pos (by nlinarith)
  have hgeomS_nonneg : 0 ≤ (1 - (3 : ℝ) ^ (-s))⁻¹ := by
    have hlt_one : (3 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hlt_one.le)
  have hnote_nonneg :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  unfold coarseCaccioppoliCenteredBesovGradientFront
    coarseCaccioppoliCenteredBesovGradientBase
  refine mul_nonneg ?_ ?_
  · refine mul_nonneg ?_ ?_
    · refine mul_nonneg ?_ (inv_nonneg.mpr hdisc_s_pos.le)
      exact mul_nonneg (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    · refine mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) ?_
      exact mul_nonneg (mul_nonneg hnote_nonneg hgeomS_nonneg)
        (inv_nonneg.mpr hdisc_sub_pos.le)
  · exact mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
      (quantitativeCubeCutoffGradientConst_nonneg d)

end

end Homogenization
