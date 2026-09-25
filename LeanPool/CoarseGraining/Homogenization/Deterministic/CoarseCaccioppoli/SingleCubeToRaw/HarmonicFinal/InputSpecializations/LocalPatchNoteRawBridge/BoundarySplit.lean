/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.LocalPatchNoteRawBridge.CoefficientBounds

/-! # Boundary Split -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Local-patch note raw bridge

This sidecar ties the arbitrary-center local-patch descendant summation to the
harmonic weak-testing identity.  It covers the interior-contained local patch
case: the translated cutoff support is required to lie inside the parent open
cube, so the compact-support test function is admissible without a boundary
zero-trace argument.
-/

/-- Boundary local-patch raw bridge for a constant harmonic family with split
note coefficients, once the local weak-testing estimate has been supplied at
every radius. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit.of_constantFamily_localPatchBufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplit_of_testing_of_closedCubeEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (u0 : AHarmonicFunction a (openCubeSet Q))
    (hClocal : 0 ≤ Clocal) (hCcross : 0 ≤ Ccross)
    (hCsol_le : fullVectorPoincareCubeConstant Q ≤ Clocal)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (htesting : ∀ n : ℕ,
      let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
      let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
      let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
      let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a u0 x
      let flux : Vec d → Vec d := fun x => matVecMul (a x) (u0.toH1.grad x)
      let u : Vec d → ℝ := fun x => u0.toH1 x
      let ξ : Vec d → Vec d :=
        scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
      coarseCaccioppoliLocalEnergyRadiusProfile Q center energy ρ₁ ≤
        |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))|)
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplit
        Q center a s t Clocal Calpha Ccross) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit
      Q center a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u0)
      (fun x => scalarVariationEnergyIntegrand a u0 x) := by
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCeffLocal_nonneg : 0 ≤ CeffLocal := by
    exact mul_nonneg hcard_nonneg hClocal
  have hCeffCross_nonneg : 0 ≤ CeffCross := by
    exact mul_nonneg hcard_nonneg hCcross
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEllCube.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a t ht hEllCube hData
  have hSigmaSum_one :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hs, hst]) hSigmaSum_t
  have hSigmaSum_one_sub_s :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hst]) hSigmaSum_t
  intro n
  let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
  let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j0 : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j : ℕ := j0 + 1
  let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a u0 x
  let flux : Vec d → Vec d := fun x => matVecMul (a x) (u0.toH1.grad x)
  let u : Vec d → ℝ := fun x => u0.toH1 x
  let G : Vec d → Vec d := fun x => u0.toH1.grad x
  let ξ : Vec d → Vec d :=
    scalarCutoffGradientField
      (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
  let B : ℝ :=
    quantitativeCubeCutoffHessianConst d / (((ρm - ρ₁) * (cubeRadius Q / 3)) ^ 2)
  let Acirc1 : TriadicCube d → ℝ := fun R =>
    coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm
  let AcircS : TriadicCube d → ℝ := fun R =>
    coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm
  let Alpha : ℝ := coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffAlpha hheight ρ₁ ρ₂
  let Bcross : ℝ :=
    coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross
      (coarseCaccioppoliHarmonicL2Sq Q a u0) hheight ρ₁ ρ₂
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
  have houter : ρm < 1 := by
    have hm_lt : ρm < ρ₂ := by
      simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).2
    have hρ₂_lt : ρ₂ < 1 := by
      simpa [ρ₂] using coarseCaccioppoliRadiusSequence_lt_one (n + 1)
    exact hm_lt.trans hρ₂_lt
  have hρm_le_one : ρm ≤ 1 := houter.le
  have hlt_mid : ρ₁ < ρm := by
    simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ := by
    simpa [k, ρ₁, ρ₂] using coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂
  have hjk : k ≤ j0 := by
    simpa [k, j0, CeffAlpha, ρ₁, ρ₂] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice_ge_scaleChoice
        Q a s t CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂)
  have hfluxEnergyQ :
      CoarseCaccioppoliFluxEnergyControls Q a s flux energy := by
    have hflux :=
      CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
        (Q := Q) (a := a) (s := s) hs hEllCube u0.toCubeSet
    simpa [flux, energy, scalarVariationEnergyIntegrand] using hflux
  have hgradQ : CubeAverageGradientEnergyControl Q a G energy := by
    have hgrad :=
      cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) hEllCube u0.toCubeSet hOrigin
    simpa [G, energy, scalarVariationEnergyIntegrand] using hgrad
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    intro x hx
    have hnonneg :=
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (cubeSet Q) a hEllCube u0.toCubeSet x hx
    simpa [energy, scalarVariationEnergyIntegrand] using hnonneg
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := hfluxEnergyQ.2.1
  have hlowerρ :
      coarseCaccioppoliLocalEnergyRadiusProfile Q center energy ρ₁ ≤
        cubeAverage Q
          (fun x =>
            coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm x * energy x) := by
    simpa [coarseCaccioppoliLocalEnergyRadiusProfile] using
      coarseCaccioppoliLocalEnergyProfile_le_localCanonicalCutoffEnergy_of_integrable
        Q center energy hρ₁_pos hlt_mid henergy_nonneg henergy_int
  have htest :
      coarseCaccioppoliLocalEnergyRadiusProfile Q center energy ρ₁ ≤
        |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| := by
    simpa [ρ₁, ρ₂, ρm, energy, flux, u, ξ] using htesting n
  have hpair_int :
      MeasureTheory.IntegrableOn (fun x => vecDot (flux x) (u x • ξ x))
        (cubeSet Q) MeasureTheory.volume := by
    simpa [flux, u, ξ] using
      integrableOn_vecDot_harmonicFlux_harmonicFunction_localCanonicalCutoff
        Q a center u0 hEllOpen hρ₁_pos hlt_mid
  have huQ : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [u] using memLp_harmonicFunction_normalizedCubeMeasure Q a u0
  have hfluxMem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro R hR
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hR
      (by simpa [flux] using memLp_harmonicFlux_normalizedCubeMeasure Q a u0 hEllOpen)
  have huMem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro R hR
    exact memLp_on_descendant_of_memLp_generic (E := ℝ) hR huQ
  have hGMem : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro R hR i
    exact memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR
      (by simpa [G] using memLp_harmonicGradientComponent_normalizedCubeMeasure Q a u0 i)
  have hfluxEnergyR : ∀ R ∈ descendantsAtDepth Q j,
      CoarseCaccioppoliFluxEnergyControls R a s flux energy := by
    intro R hR
    exact hfluxEnergyQ.restrict_to_descendant hs.le hR
  have hB_nonneg : 0 ≤ B := by
    exact div_nonneg (quantitativeCubeCutoffHessianConst_nonneg d) (sq_nonneg _)
  have hAcirc1_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ Acirc1 R := by
    intro R hR
    simpa [Acirc1] using
      coarseCaccioppoliCanonicalGradientAcircOne_nonneg R a ρ₁ ρm
  have hAcircS_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ AcircS R := by
    intro R hR
    simpa [AcircS] using
      coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg R a hs1.le ρ₁ ρm
  have hBgConst : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤ coarseCaccioppoliConstantCutoffSize R u ξ B := by
    intro R hR
    exact coarseCaccioppoliConstantCutoffSize_nonneg R u ξ hB_nonneg
  have hBgCent : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤ coarseCaccioppoliCenteredCutoffSize R s ξ (Acirc1 R) (AcircS R)
        (Real.sqrt (cubeAverage R energy)) B CeffLocal := by
    intro R hR
    exact
      coarseCaccioppoliCenteredCutoffSize_nonneg R ξ hs
        (hAcirc1_nonneg R hR) (hAcircS_nonneg R hR)
        (Real.sqrt_nonneg _) hB_nonneg hCeffLocal_nonneg
  have hfullFamily :
      CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily Q a Clocal
        (fun _ _ => u0) :=
    (CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily.of_aHarmonicFunction
      Q a (fun _ _ => u0)).mono_C hCsol_le
  have hfull : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R Clocal
        (cubeFluctuation R u) G N := by
    intro R hR N
    simpa [u, G] using
      hfullFamily.vectorPoincare_on_descendant
        hR hρ₁ hlt_mid hρm_le_one N
  have hGcirc1 : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 R * Real.sqrt (cubeAverage R energy) := by
    intro R hR i N
    have henergy_nonneg_R : ∀ x ∈ cubeSet R, 0 ≤ energy x := by
      intro x hx
      exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
    have henergy_int_R :
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume :=
      henergy_int.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hgradR : CubeAverageGradientEnergyControl R a G energy :=
      hgradQ.restrict_to_descendant hR
    have hSigmaSum_one_R :
        Summable (fun n : ℕ =>
          geometricWeight (1 : ℝ) 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) :=
      summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) a (1 : ℝ) (by norm_num) hR hSigmaSum_one
    simpa [G, Acirc1, coarseCaccioppoliCanonicalGradientAcircOne,
      coarseCaccioppoliCanonicalGradientAcirc, energy] using
      cubeBesovCircPartialNorm_component_le_local_canonicalGradientAcirc
        R a (1 : ℝ) (by norm_num)
        henergy_nonneg_R henergy_int_R hgradR hSigmaSum_one_R i N
  have hGcircS : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS R * Real.sqrt (cubeAverage R energy) := by
    intro R hR i N
    have hs_pos : 0 < 1 - s := by linarith
    have henergy_nonneg_R : ∀ x ∈ cubeSet R, 0 ≤ energy x := by
      intro x hx
      exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
    have henergy_int_R :
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume :=
      henergy_int.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hgradR : CubeAverageGradientEnergyControl R a G energy :=
      hgradQ.restrict_to_descendant hR
    have hSigmaSum_one_sub_s_R :
        Summable (fun n : ℕ =>
          geometricWeight (1 - s) 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) :=
      summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) a (1 - s) hs_pos.le hR hSigmaSum_one_sub_s
    simpa [G, AcircS, coarseCaccioppoliCanonicalGradientAcircOneSub,
      coarseCaccioppoliCanonicalGradientAcirc, energy] using
      cubeBesovCircPartialNorm_component_le_local_canonicalGradientAcirc
        R a (1 - s) hs_pos
        henergy_nonneg_R henergy_int_R hgradR hSigmaSum_one_sub_s_R i N
  have hL2n : cubeLpNorm Q (2 : ℝ≥0∞) u ≤
      Real.sqrt (coarseCaccioppoliHarmonicL2Sq Q a u0) := by
    simpa [u, coarseCaccioppoliCanonicalHarmonicL2Profile] using
      CoarseCaccioppoliBoundaryCanonicalHarmonicL2SizeControl.of_constantFamily Q a u0
        hρ₁ hlt hρ₂
  have hK_nonneg : 0 ≤ K := by
    simpa [K] using
      coarseCaccioppoliBoundaryCrossCoeffOfHeight_nonneg
        Q a s CeffCross (1 : ℝ) hheight hCeffCross_nonneg hs hlt
  have hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross := by
    simpa [K, Bcross] using
      boundaryCrossCoeff_one_mul_le_boundaryCrossCoeff_of_cubeLpNorm_le_sqrt
        (Q := Q) (a := a) (s := s) (C := CeffCross)
        (uL2Sq := coarseCaccioppoliHarmonicL2Sq Q a u0)
        (ρ₁ := ρ₁) (ρ₂ := ρ₂) (U := cubeLpNorm Q (2 : ℝ≥0∞) u)
        (h := hheight) hCeffCross_nonneg hs hlt hL2n
  have hbuffer : ∀ R ∈ descendantsAtDepth Q j,
      cubeScaleFactor R ≤ (ρ₂ - ρm) * (cubeRadius Q / 3) := by
    intro R hR
    simpa [j, j0, ρm] using
      cubeScaleFactor_le_local_buffer_of_mem_descendantsAtDepth_succ_of_triadicGapScaleChoice
        (Q := Q) (R := R) (j := j0) (k := k) hR hchoice hjk
  have hrawn :
      (∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
            (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K) ∧
      (∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ (Acirc1 R) (AcircS R)
            B CeffLocal ≤ Alpha) := by
    simpa [
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplit,
      CeffLocal, CeffAlpha, CeffCross, hheight, ρ₁, ρ₂, ρm, j, j0, ξ, B, Acirc1,
      AcircS, K, Alpha]
      using hrawcoeff n
  rcases hrawn with ⟨hconst_raw, hcent_raw⟩
  refine le_trans htest ?_
  have hraw :=
    abs_cubeAverage_vecDot_scalar_smul_le_localPatch_raw_of_localCanonicalCutoff_on_descendants_variableAcirc_of_support_buffer_vectorFullDualFullCirc
      (Q := Q) (center := center) (j := j) (a := a) (s := s)
      (rhoInner := ρ₁) (rhoOuter := ρm) (rho := ρ₂)
      (flux := flux) (u := u) (G := G) (energy := energy)
      (Acirc1 := Acirc1) (AcircS := AcircS) (C := Clocal) (K := K)
      (Alpha := Alpha) (Bcross := Bcross)
      hρ₁_pos hlt_mid hs hs1 hbuffer hpair_int huQ henergy_nonneg henergy_int
      hfluxMem huMem hGMem hfluxEnergyR hB_nonneg hAcirc1_nonneg hAcircS_nonneg
      hBgConst hBgCent hClocal hfull hGcirc1 hGcircS hK_nonneg hKparent
      (by
        intro R hR
        simpa [ξ, B, CeffLocal] using hconst_raw R hR)
      (by
        intro R hR
        simpa [ξ, B, Acirc1, AcircS, CeffLocal] using hcent_raw R hR)
  simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit,
    coarseCaccioppoliLocalEnergyRadiusProfile, CeffAlpha, CeffCross, hheight, ρ₁, ρ₂,
    energy, Alpha, Bcross, flux, u, ξ, B]
    using hraw

/-- All-radii boundary local-patch raw bridge for a constant harmonic family
with split note coefficients, once the local weak-testing estimate has been
supplied at every admissible radius pair. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii.of_constantFamily_localPatchBufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplitAllRadii_of_testing_of_closedCubeEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (u0 : AHarmonicFunction a (openCubeSet Q))
    (hClocal : 0 ≤ Clocal) (hCcross : 0 ≤ Ccross)
    (hCsol_le : fullVectorPoincareCubeConstant Q ≤ Clocal)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (htesting :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
        let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a u0 x
        let flux : Vec d → Vec d := fun x => matVecMul (a x) (u0.toH1.grad x)
        let u : Vec d → ℝ := fun x => u0.toH1 x
        let ξ : Vec d → Vec d :=
          scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
        coarseCaccioppoliLocalEnergyRadiusProfile Q center energy ρ₁ ≤
          |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))|)
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii
        Q center a s t Clocal Calpha Ccross) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii
      Q center a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u0)
      (fun x => scalarVariationEnergyIntegrand a u0 x) := by
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCeffLocal_nonneg : 0 ≤ CeffLocal := by
    exact mul_nonneg hcard_nonneg hClocal
  have hCeffCross_nonneg : 0 ≤ CeffCross := by
    exact mul_nonneg hcard_nonneg hCcross
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEllCube.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a t ht hEllCube hData
  have hSigmaSum_one :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hs, hst]) hSigmaSum_t
  have hSigmaSum_one_sub_s :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hst]) hSigmaSum_t
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j0 : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j : ℕ := j0 + 1
  let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a u0 x
  let flux : Vec d → Vec d := fun x => matVecMul (a x) (u0.toH1.grad x)
  let u : Vec d → ℝ := fun x => u0.toH1 x
  let G : Vec d → Vec d := fun x => u0.toH1.grad x
  let ξ : Vec d → Vec d :=
    scalarCutoffGradientField
      (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
  let B : ℝ :=
    quantitativeCubeCutoffHessianConst d / (((ρm - ρ₁) * (cubeRadius Q / 3)) ^ 2)
  let Acirc1 : TriadicCube d → ℝ := fun R =>
    coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm
  let AcircS : TriadicCube d → ℝ := fun R =>
    coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm
  let Alpha : ℝ := coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffAlpha hheight ρ₁ ρ₂
  let Bcross : ℝ :=
    coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross
      (coarseCaccioppoliHarmonicL2Sq Q a u0) hheight ρ₁ ρ₂
  let K : ℝ :=
    coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
  have hρ₁_pos : 0 < ρ₁ := by
    exact (show (0 : ℝ) < 1 / 3 by norm_num).trans_le hρ₁
  have houter : ρm < 1 := by
    have hm_lt : ρm < ρ₂ := by
      simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).2
    exact hm_lt.trans_le hρ₂
  have hρm_le_one : ρm ≤ 1 := houter.le
  have hlt_mid : ρ₁ < ρm := by
    simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ := by
    simpa [k] using coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂
  have hjk : k ≤ j0 := by
    simpa [k, j0, CeffAlpha] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice_ge_scaleChoice
        Q a s t CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂)
  have hfluxEnergyQ :
      CoarseCaccioppoliFluxEnergyControls Q a s flux energy := by
    have hflux :=
      CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
        (Q := Q) (a := a) (s := s) hs hEllCube u0.toCubeSet
    simpa [flux, energy, scalarVariationEnergyIntegrand] using hflux
  have hgradQ : CubeAverageGradientEnergyControl Q a G energy := by
    have hgrad :=
      cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) hEllCube u0.toCubeSet hOrigin
    simpa [G, energy, scalarVariationEnergyIntegrand] using hgrad
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    intro x hx
    have hnonneg :=
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (cubeSet Q) a hEllCube u0.toCubeSet x hx
    simpa [energy, scalarVariationEnergyIntegrand] using hnonneg
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := hfluxEnergyQ.2.1
  have hlowerρ :
      coarseCaccioppoliLocalEnergyRadiusProfile Q center energy ρ₁ ≤
        cubeAverage Q
          (fun x =>
            coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm x * energy x) := by
    simpa [coarseCaccioppoliLocalEnergyRadiusProfile] using
      coarseCaccioppoliLocalEnergyProfile_le_localCanonicalCutoffEnergy_of_integrable
        Q center energy hρ₁_pos hlt_mid henergy_nonneg henergy_int
  have htest :
      coarseCaccioppoliLocalEnergyRadiusProfile Q center energy ρ₁ ≤
        |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| := by
    simpa [ρm, energy, flux, u, ξ] using htesting hρ₁ hlt hρ₂
  have hpair_int :
      MeasureTheory.IntegrableOn (fun x => vecDot (flux x) (u x • ξ x))
        (cubeSet Q) MeasureTheory.volume := by
    simpa [flux, u, ξ] using
      integrableOn_vecDot_harmonicFlux_harmonicFunction_localCanonicalCutoff
        Q a center u0 hEllOpen hρ₁_pos hlt_mid
  have huQ : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [u] using memLp_harmonicFunction_normalizedCubeMeasure Q a u0
  have hfluxMem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro R hR
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hR
      (by simpa [flux] using memLp_harmonicFlux_normalizedCubeMeasure Q a u0 hEllOpen)
  have huMem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro R hR
    exact memLp_on_descendant_of_memLp_generic (E := ℝ) hR huQ
  have hGMem : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro R hR i
    exact memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR
      (by simpa [G] using memLp_harmonicGradientComponent_normalizedCubeMeasure Q a u0 i)
  have hfluxEnergyR : ∀ R ∈ descendantsAtDepth Q j,
      CoarseCaccioppoliFluxEnergyControls R a s flux energy := by
    intro R hR
    exact hfluxEnergyQ.restrict_to_descendant hs.le hR
  have hB_nonneg : 0 ≤ B := by
    exact div_nonneg (quantitativeCubeCutoffHessianConst_nonneg d) (sq_nonneg _)
  have hAcirc1_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ Acirc1 R := by
    intro R hR
    simpa [Acirc1] using
      coarseCaccioppoliCanonicalGradientAcircOne_nonneg R a ρ₁ ρm
  have hAcircS_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ AcircS R := by
    intro R hR
    simpa [AcircS] using
      coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg R a hs1.le ρ₁ ρm
  have hBgConst : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤ coarseCaccioppoliConstantCutoffSize R u ξ B := by
    intro R hR
    exact coarseCaccioppoliConstantCutoffSize_nonneg R u ξ hB_nonneg
  have hBgCent : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤ coarseCaccioppoliCenteredCutoffSize R s ξ (Acirc1 R) (AcircS R)
        (Real.sqrt (cubeAverage R energy)) B CeffLocal := by
    intro R hR
    exact
      coarseCaccioppoliCenteredCutoffSize_nonneg R ξ hs
        (hAcirc1_nonneg R hR) (hAcircS_nonneg R hR)
        (Real.sqrt_nonneg _) hB_nonneg hCeffLocal_nonneg
  have hfullFamily :
      CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily Q a Clocal
        (fun _ _ => u0) :=
    (CoarseCaccioppoliBoundaryCanonicalGradientFullDualPoincareVectorFamily.of_aHarmonicFunction
      Q a (fun _ _ => u0)).mono_C hCsol_le
  have hfull : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R Clocal
        (cubeFluctuation R u) G N := by
    intro R hR N
    simpa [u, G] using
      hfullFamily.vectorPoincare_on_descendant
        hR hρ₁ hlt_mid hρm_le_one N
  have hGcirc1 : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 R * Real.sqrt (cubeAverage R energy) := by
    intro R hR i N
    have henergy_nonneg_R : ∀ x ∈ cubeSet R, 0 ≤ energy x := by
      intro x hx
      exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
    have henergy_int_R :
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume :=
      henergy_int.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hgradR : CubeAverageGradientEnergyControl R a G energy :=
      hgradQ.restrict_to_descendant hR
    have hSigmaSum_one_R :
        Summable (fun n : ℕ =>
          geometricWeight (1 : ℝ) 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) :=
      summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) a (1 : ℝ) (by norm_num) hR hSigmaSum_one
    simpa [G, Acirc1, coarseCaccioppoliCanonicalGradientAcircOne,
      coarseCaccioppoliCanonicalGradientAcirc, energy] using
      cubeBesovCircPartialNorm_component_le_local_canonicalGradientAcirc
        R a (1 : ℝ) (by norm_num)
        henergy_nonneg_R henergy_int_R hgradR hSigmaSum_one_R i N
  have hGcircS : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS R * Real.sqrt (cubeAverage R energy) := by
    intro R hR i N
    have hs_pos : 0 < 1 - s := by linarith
    have henergy_nonneg_R : ∀ x ∈ cubeSet R, 0 ≤ energy x := by
      intro x hx
      exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
    have henergy_int_R :
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume :=
      henergy_int.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hgradR : CubeAverageGradientEnergyControl R a G energy :=
      hgradQ.restrict_to_descendant hR
    have hSigmaSum_one_sub_s_R :
        Summable (fun n : ℕ =>
          geometricWeight (1 - s) 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) :=
      summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) a (1 - s) hs_pos.le hR hSigmaSum_one_sub_s
    simpa [G, AcircS, coarseCaccioppoliCanonicalGradientAcircOneSub,
      coarseCaccioppoliCanonicalGradientAcirc, energy] using
      cubeBesovCircPartialNorm_component_le_local_canonicalGradientAcirc
        R a (1 - s) hs_pos
        henergy_nonneg_R henergy_int_R hgradR hSigmaSum_one_sub_s_R i N
  have hL2n : cubeLpNorm Q (2 : ℝ≥0∞) u ≤
      Real.sqrt (coarseCaccioppoliHarmonicL2Sq Q a u0) := by
    simpa [u, coarseCaccioppoliCanonicalHarmonicL2Profile] using
      CoarseCaccioppoliBoundaryCanonicalHarmonicL2SizeControl.of_constantFamily Q a u0
        hρ₁ hlt hρ₂
  have hK_nonneg : 0 ≤ K := by
    simpa [K] using
      coarseCaccioppoliBoundaryCrossCoeffOfHeight_nonneg
        Q a s CeffCross (1 : ℝ) hheight hCeffCross_nonneg hs hlt
  have hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross := by
    simpa [K, Bcross] using
      boundaryCrossCoeff_one_mul_le_boundaryCrossCoeff_of_cubeLpNorm_le_sqrt
        (Q := Q) (a := a) (s := s) (C := CeffCross)
        (uL2Sq := coarseCaccioppoliHarmonicL2Sq Q a u0)
        (ρ₁ := ρ₁) (ρ₂ := ρ₂) (U := cubeLpNorm Q (2 : ℝ≥0∞) u)
        (h := hheight) hCeffCross_nonneg hs hlt hL2n
  have hbuffer : ∀ R ∈ descendantsAtDepth Q j,
      cubeScaleFactor R ≤ (ρ₂ - ρm) * (cubeRadius Q / 3) := by
    intro R hR
    simpa [j, j0, ρm] using
      cubeScaleFactor_le_local_buffer_of_mem_descendantsAtDepth_succ_of_triadicGapScaleChoice
        (Q := Q) (R := R) (j := j0) (k := k) hR hchoice hjk
  have hrawn :
      (∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
            (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K) ∧
      (∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ (Acirc1 R) (AcircS R)
            B CeffLocal ≤ Alpha) := by
    simpa [
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii,
      CeffLocal, CeffAlpha, CeffCross, hheight, ρm, j, j0, ξ, B, Acirc1,
      AcircS, K, Alpha, coarseCaccioppoliLocalPatchCutoffHessianBound]
      using hrawcoeff hρ₁ hlt hρ₂
  rcases hrawn with ⟨hconst_raw, hcent_raw⟩
  refine le_trans htest ?_
  have hraw :=
    abs_cubeAverage_vecDot_scalar_smul_le_localPatch_raw_of_localCanonicalCutoff_on_descendants_variableAcirc_of_support_buffer_vectorFullDualFullCirc
      (Q := Q) (center := center) (j := j) (a := a) (s := s)
      (rhoInner := ρ₁) (rhoOuter := ρm) (rho := ρ₂)
      (flux := flux) (u := u) (G := G) (energy := energy)
      (Acirc1 := Acirc1) (AcircS := AcircS) (C := Clocal) (K := K)
      (Alpha := Alpha) (Bcross := Bcross)
      hρ₁_pos hlt_mid hs hs1 hbuffer hpair_int huQ henergy_nonneg henergy_int
      hfluxMem huMem hGMem hfluxEnergyR hB_nonneg hAcirc1_nonneg hAcircS_nonneg
      hBgConst hBgCent hClocal hfull hGcirc1 hGcircS hK_nonneg hKparent
      (by
        intro R hR
        simpa [ξ, B, CeffLocal] using hconst_raw R hR)
      (by
        intro R hR
        simpa [ξ, B, Acirc1, AcircS, CeffLocal] using hcent_raw R hR)
  simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii,
    coarseCaccioppoliLocalEnergyRadiusProfile, CeffAlpha, CeffCross, hheight,
    energy, Alpha, Bcross, flux, u, ξ, B]
    using hraw

end

end Homogenization
