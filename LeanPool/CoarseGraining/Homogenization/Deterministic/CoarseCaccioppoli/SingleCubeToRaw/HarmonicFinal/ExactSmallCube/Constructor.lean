/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.CenteredFactors
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalConstantBranch
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.CenteredLocalCoefficient
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Setup

/-! # Constructor -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Buffered exact centered local coefficient, with descendant-local canonical
`A^\circ` factors, localized directly to the parent `Alpha` coefficient.  The
cutoff radius is the midpoint, while the height and `Alpha` radius pair remain
the full outer pair. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_buffered_localAcirc_le_alpha_of_scale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {s t CeffLocal CeffWork : ℝ} {k j : ℕ} {ρ₁ ρ₂ lam Lam : ℝ}
    {hheight : ℝ → ℝ → ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
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
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j)
    (hscale :
      (2 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
          4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
          2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
          Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hheight_le_j : hheight ρ₁ ρ₂ ≤ (j : ℝ)) :
    let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
    coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s
        (scalarCutoffGradientField η)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
        (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
        CeffLocal ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
  dsimp
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hsumR_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) a s hs.le hR hBsum_s
  have hB_nonneg :
      0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm := by
    simpa [ρm] using coarseCaccioppoliQuantitativeCutoffHessianBound_nonneg Q η
  have hAcirc1_nonneg :
      0 ≤ coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm := by
    simpa using coarseCaccioppoliCanonicalGradientAcircOne_nonneg R a ρ₁ ρm
  have hAcircS_nonneg :
      0 ≤ coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm := by
    simpa using
      coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg R a hs1.le ρ₁ ρm
  have hξ :
      cubeLpNorm R ∞ (scalarCutoffGradientField η) ≤
        coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm := by
    simpa [ρm, coarseCaccioppoliQuantitativeCutoffGradientBound] using
      quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le_on_descendant hR η
  have hcentered :=
    coarseCaccioppoliFluxEnergyExactCenteredFactorBounds_buffered_localAcirc_le_alpha_of_scale
      (Q := Q) (R := R) (a := a) (s := s) (t := t)
      (CeffLocal := CeffLocal) (CeffWork := CeffWork)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      (hheight := hheight) hCeffLocal hCeffWork hs ht hst hEllCube hR
      hBsum_s hSigmaSum_t hchoice hlt hjk hscale hheight_le_j
  exact
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_of_separated_factor_bounds
      R a s CeffLocal (scalarCutoffGradientField η)
      (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
      (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
      hs hCeffLocal hB_nonneg hAcirc1_nonneg hAcircS_nonneg
      (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor R a hs hsumR_s)
      (show
        (geometricDiscount s 1)⁻¹ *
            Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) ≤
          coarseCaccioppoliLambdaFactor R a s by
        simp [coarseCaccioppoliLambdaFactor])
      hξ le_rfl le_rfl le_rfl
      (by simpa [ρm] using hcentered)

private theorem faithful_centered_fronts_scale_mul_le_workGap_of_triadicGapScaleChoice
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

/-- Split buffered exact-to-parent-raw coefficient bounds from closed-cube
ellipticity and separate note budgets.

`Calpha` controls the explicit height and centered absorption coefficient,
while `Ccross` controls only the constant/cross branch. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplit.of_closedCubeEllipticity_of_bufferedCutoffRadiusConst_of_centeredFronts
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (hClocal : 0 ≤ Clocal) (hCalpha : 0 ≤ Calpha) (hCcross : 0 ≤ Ccross)
    (hwork_constant_cross :
      (81 : ℝ) * Real.rpow (3 : ℝ) s *
          ((Fintype.card (Fin d) : ℝ) * Clocal) ≤
        (Fintype.card (Fin d) : ℝ) * Ccross)
    (hwork_centered_fronts_alpha :
      (81 : ℝ) *
          (2 * coarseCaccioppoliCenteredAverageFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal) +
            4 * coarseCaccioppoliCenteredBesovHessianFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal) +
            2 * coarseCaccioppoliCenteredBesovGradientFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal)) ≤
        ((Fintype.card (Fin d) : ℝ) * Calpha) / (s * (1 - s)))
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤
        (Fintype.card (Fin d) : ℝ) * Clocal) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplit
      Q a s t Clocal Calpha Ccross := by
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let Scenter : ℝ :=
    2 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
      4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
      2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCeffLocal_nonneg : 0 ≤ CeffLocal := mul_nonneg hcard_nonneg hClocal
  have hCeffAlpha_nonneg : 0 ≤ CeffAlpha := mul_nonneg hcard_nonneg hCalpha
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hScenter_nonneg : 0 ≤ Scenter := by
    dsimp [Scenter]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (coarseCaccioppoliCenteredAverageFront_nonneg d hCeffLocal_nonneg hs))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
          (coarseCaccioppoliCenteredBesovHessianFront_nonneg d hCeffLocal_nonneg hs)))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (coarseCaccioppoliCenteredBesovGradientFront_nonneg d hCeffLocal_nonneg hs hs1))
  have hcentered_alpha : (81 : ℝ) * Scenter ≤ CeffAlpha / (s * (1 - s)) := by
    simpa [Scenter, CeffLocal, CeffAlpha] using hwork_centered_fronts_alpha
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
  have hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a t ht hEllCube hData
  let hconst :
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
              (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K :=
    faithfulWorkSmallCubeExactRawConstantBranchSplit_of_closedCubeEllipticity_of_bufferedCutoffRadiusConst
      (Q := Q) (a := a) (s := s) (t := t) (Clocal := Clocal)
      (Calpha := Calpha) (Ccross := Ccross)
      hClocal hCcross hwork_constant_cross hs ht hst hEllCube hlarge
  intro n
  let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
  let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
      CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
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
  have hheight_le_j : hheight ρ₁ ρ₂ ≤ (j : ℝ) := by
    simpa [hheight, j, CeffAlpha, ρ₁, ρ₂,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_le_depth
        Q a s t CeffAlpha (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂))
  have hscale :
      Scenter * Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffAlpha / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    faithful_centered_fronts_scale_mul_le_workGap_of_triadicGapScaleChoice
      hScenter_nonneg hcentered_alpha hchoice hlt
  constructor
  · intro R hR
    simpa [CeffAlpha, CeffCross, hheight, ρ₁, ρ₂, ρm, j, ηρ,
      coarseCaccioppoliCanonicalQuantitativeCutoff, QuantitativeCubeCutoff.canonical]
      using hconst n R hR
  · intro R hR
    simpa [CeffLocal, CeffAlpha, hheight, ρ₁, ρ₂, ρm, j, Scenter, ηρ,
      coarseCaccioppoliCanonicalQuantitativeCutoff, QuantitativeCubeCutoff.canonical]
      using
        (coarseCaccioppoliFluxEnergyExactCenteredCoeff_buffered_localAcirc_le_alpha_of_scale
          (Q := Q) (R := R) (a := a) (s := s) (t := t)
          (CeffLocal := CeffLocal) (CeffWork := CeffAlpha)
          (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
          (hheight := hheight) ηρ
        hCeffLocal_nonneg hCeffAlpha_nonneg hs ht hst hEllCube hR
        hBsum_s hSigmaSum_t hchoice hlt hjk
        (by simpa [Scenter] using hscale) hheight_le_j)

/-- All-radii split buffered exact-to-parent-raw coefficient bounds from
closed-cube ellipticity and separate note budgets.

This is the proof-producing coefficient package used by the standard
beta-dependent radius iteration. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplitAllRadii.of_closedCubeEllipticity_of_bufferedCutoffRadiusConst_of_centeredFronts
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (hClocal : 0 ≤ Clocal) (hCalpha : 0 ≤ Calpha) (hCcross : 0 ≤ Ccross)
    (hwork_constant_cross :
      (81 : ℝ) * Real.rpow (3 : ℝ) s *
          ((Fintype.card (Fin d) : ℝ) * Clocal) ≤
        (Fintype.card (Fin d) : ℝ) * Ccross)
    (hwork_centered_fronts_alpha :
      (81 : ℝ) *
          (2 * coarseCaccioppoliCenteredAverageFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal) +
            4 * coarseCaccioppoliCenteredBesovHessianFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal) +
            2 * coarseCaccioppoliCenteredBesovGradientFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal)) ≤
        ((Fintype.card (Fin d) : ℝ) * Calpha) / (s * (1 - s)))
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤
        (Fintype.card (Fin d) : ℝ) * Clocal) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplitAllRadii
      Q a s t Clocal Calpha Ccross := by
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let Scenter : ℝ :=
    2 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
      4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
      2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCeffLocal_nonneg : 0 ≤ CeffLocal := mul_nonneg hcard_nonneg hClocal
  have hCeffAlpha_nonneg : 0 ≤ CeffAlpha := mul_nonneg hcard_nonneg hCalpha
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hScenter_nonneg : 0 ≤ Scenter := by
    dsimp [Scenter]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (coarseCaccioppoliCenteredAverageFront_nonneg d hCeffLocal_nonneg hs))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
          (coarseCaccioppoliCenteredBesovHessianFront_nonneg d hCeffLocal_nonneg hs)))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (coarseCaccioppoliCenteredBesovGradientFront_nonneg d hCeffLocal_nonneg hs hs1))
  have hcentered_alpha : (81 : ℝ) * Scenter ≤ CeffAlpha / (s * (1 - s)) := by
    simpa [Scenter, CeffLocal, CeffAlpha] using hwork_centered_fronts_alpha
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
  have hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a t ht hEllCube hData
  have hconst :=
    faithfulWorkSmallCubeExactRawConstantBranchSplitAllRadii_of_closedCubeEllipticity_of_bufferedCutoffRadiusConst
      (Q := Q) (a := a) (s := s) (t := t) (Clocal := Clocal)
      (Calpha := Calpha) (Ccross := Ccross)
      hClocal hCcross hwork_constant_cross hs ht hst hEllCube hlarge
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
      CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
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
  have hheight_le_j : hheight ρ₁ ρ₂ ≤ (j : ℝ) := by
    simpa [hheight, j, CeffAlpha,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_le_depth
        Q a s t CeffAlpha (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂))
  have hscale :
      Scenter * Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffAlpha / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    faithful_centered_fronts_scale_mul_le_workGap_of_triadicGapScaleChoice
      hScenter_nonneg hcentered_alpha hchoice hlt
  constructor
  · intro R hR
    simpa [CeffAlpha, CeffCross, hheight, ρm, j, ηρ,
      coarseCaccioppoliCanonicalQuantitativeCutoff, QuantitativeCubeCutoff.canonical]
      using hconst hρ₁ hlt hρ₂ R hR
  · intro R hR
    simpa [CeffLocal, CeffAlpha, hheight, ρm, j, Scenter, ηρ,
      coarseCaccioppoliCanonicalQuantitativeCutoff, QuantitativeCubeCutoff.canonical]
      using
        (coarseCaccioppoliFluxEnergyExactCenteredCoeff_buffered_localAcirc_le_alpha_of_scale
          (Q := Q) (R := R) (a := a) (s := s) (t := t)
          (CeffLocal := CeffLocal) (CeffWork := CeffAlpha)
          (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
          (hheight := hheight) ηρ
          hCeffLocal_nonneg hCeffAlpha_nonneg hs ht hst hEllCube hR
          hBsum_s hSigmaSum_t hchoice hlt hjk
          (by simpa [Scenter] using hscale) hheight_le_j)

end

end Homogenization
