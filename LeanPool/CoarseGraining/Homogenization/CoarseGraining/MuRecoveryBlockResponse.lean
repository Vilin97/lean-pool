/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Equalities
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery

/-! # Mu Recovery Block Response -/

namespace Homogenization

noncomputable section

/-!
Direct convex-domain bridges from recovered fields to block-response pair-half
representations and scalar-response splitting identities.
-/

/-- Hodge-packaged direct recovery-to-half-pair bridge for the pure-flux
slice. This is the generic form of the convex-domain wrapper below. -/
theorem MuCorrectionSpaceRecoveryData.exists_blockResponsePairHalfState_ae_eq_recoveredField_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q : Vec d) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U]
          fun x => (R.recoveredField system (0, q)).eval x := by
  have hResp :
      BlockResponseSpace a U (R.recoveredField system (0, q)) :=
    R.recoveredField_mem_responseSpace_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
      system hU hEll hHodge hvol q
  have hLower :
      IsPotentialOn U
        (fun x =>
          (blockMatVecMul (blockCoeffField a x)
            ((R.recoveredField system (0, q)).eval x)).2) :=
    R.recoveredField_lowerImage_isPotential_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
      system hEll hHodge hvol q
  exact
    exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
      (a := a) hU.1 hResp hLower hEll

/-- Hodge-packaged direct recovery-to-half-pair bridge for a general block
datum. This is the generic form of the convex-domain wrapper below. -/
theorem MuCorrectionSpaceRecoveryData.exists_blockResponsePairHalfState_ae_eq_recoveredField_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U]
          fun x => (R.recoveredField system P).eval x := by
  have hResp :
      BlockResponseSpace a U (R.recoveredField system P) :=
    R.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_hodgeConverseCriterion
      system hU hEll hHodge hvol P
  have hLower :
      IsPotentialOn U
        (fun x =>
          (blockMatVecMul (blockCoeffField a x)
            ((R.recoveredField system P).eval x)).2) :=
    R.recoveredField_lowerImage_isPotential_of_isEllipticFieldOn_of_hodgeConverseCriterion
      system hEll hHodge hvol P
  exact
    exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
      (a := a) hU.1 hResp hLower hEll

/-- Recovery-to-response bridge for the pure-flux slice, proved without any
coarse-matrix package. This is the sigma-free theorem needed before the
canonical `sigma_*^{-1}` positivity layer. -/
theorem MuCorrectionSpaceRecoveryData.mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (q0 : Vec d) :
    Mu U (0, q0) a = ResponseJ U 0 q0 a := by
  let Xrec : BlockState d := R.recoveredField system (0, q0)
  rcases
      R.exists_blockResponsePairHalfState_ae_eq_recoveredField_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
        system hU hEll hHodge hvol q0 with
    ⟨u, v, hEq⟩
  have hAdm : IsBlockMuAdmissible U (0, q0) Xrec := by
    simpa [Xrec] using R.recoveredField_admissible system (0, q0)
  have hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a 0 q0 u w) = 0 := by
    simpa [Xrec] using
      scalarFirstVariation_zero_right_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
        (a := a) (U := U) (hU := hU.1) hEll q0 u v Xrec hEq hAdm
  have hEnergyRec :
      blockEnergyAverage U a Xrec = Mu U (0, q0) a := by
    simpa [Xrec] using
      R.recoveredField_blockEnergyAverage_eq_mu system mu_eq_muCandidate (0, q0)
  let Xpair : BlockState d := blockResponsePairHalfState a u v
  have hEnergyEq :
      blockEnergyAverage U a Xpair = blockEnergyAverage U a Xrec := by
    unfold blockEnergyAverage volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, blockEnergyDensity] using
      congrArg
        (fun z =>
          (1 / 2 : ℝ) * blockVecDot z (blockMatVecMul (blockCoeffField a x) z))
        hx
  have hPairEq :
      volumeAverage U
          (fun x => vecDot (Xpair.potential x) (Xpair.flux x)) =
        volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) := by
    unfold volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, BlockState.eval] using
      congrArg (fun z : BlockVec d => vecDot z.1 z.2) hx
  have hpotZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).potential x i
          ∂MeasureTheory.volume) = 0 := by
    intro P
    let Y := R.recoveredCorrectionField system P
    exact IsPotentialZeroTraceOn.integral_eq_zero
      Y.isPotentialZeroTrace
  have hfluxZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).flux x i
          ∂MeasureTheory.volume) = 0 := by
    intro P
    let Y := R.recoveredCorrectionField system P
    exact IsSolenoidalZeroNormalTraceOn.integral_eq_zero hU
      Y.isSolenoidalZeroNormalTrace
  have hPairRec :
      volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) = 0 := by
    simpa [Xrec, vecDot_zero_left] using
      R.recoveredField_average_pairing_of_integral_eq_zero
        system hpotZero hfluxZero hvol (0, q0)
  have hPair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = 0 := by
    simpa [Xpair] using hPairEq.trans hPairRec
  have hCouple :
      blockEnergyAverage U a Xpair = ResponseJ U 0 q0 a := by
    simpa [Xpair] using
      blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_zero_of_pairingAverage_eq_zero_of_firstVariation_eq_zero
        (a := a) hU.1 hEll q0 u v hPair hfirst
  calc
    Mu U (0, q0) a = blockEnergyAverage U a Xrec := hEnergyRec.symm
    _ = blockEnergyAverage U a Xpair := hEnergyEq.symm
    _ = ResponseJ U 0 q0 a := hCouple

/-- Packaged pure-flux recovery/response bridge on a Hodge domain. -/
theorem PotentialSolenoidalL2RecoveryData.mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (q0 : Vec d) :
    Mu U (0, q0) a = ResponseJ U 0 q0 a := by
  let Rc : MuCorrectionSpaceRecoveryData U := R.toMuCorrectionSpaceRecoveryData
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  exact
    Rc.mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn_of_hodgeConverseCriterion
        system hU hEll hHodge hvol.ne' compat.mu_eq_muCandidate q0

/-- Preferred convex-domain wrapper for the packaged pure-flux
recovery/response bridge. -/
theorem PotentialSolenoidalL2RecoveryData.mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (q0 : Vec d) :
    Mu U (0, q0) a = ResponseJ U 0 q0 a :=
  R.mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn_of_hodgeConverseCriterion
    hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat q0

/-- Convex-domain direct recovery-to-half-pair bridge for the pure-flux slice.
This packages the response-space and lower-image-potential promotion into a
single theorem, so downstream users can recover the scalar primal/adjoint pair
without mentioning any Hodge or response-space intermediate hypotheses. -/
theorem MuCorrectionSpaceRecoveryData.exists_blockResponsePairHalfState_ae_eq_recoveredField_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q : Vec d) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U]
          fun x => (R.recoveredField system (0, q)).eval x := by
  have hU : IsSobolevRegularDomain U := hConv.isSobolevRegularDomain
  have hResp :
      BlockResponseSpace a U (R.recoveredField system (0, q)) :=
    R.recoveredField_mem_responseSpace_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol q
  have hLower :
      IsPotentialOn U
        (fun x =>
          (blockMatVecMul (blockCoeffField a x)
            ((R.recoveredField system (0, q)).eval x)).2) :=
    R.recoveredField_lowerImage_isPotential_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol q
  exact
    exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
      (a := a) hU.1 hResp hLower hEll

/-- Convex-domain direct recovery-to-half-pair bridge for a general block
datum. -/
theorem MuCorrectionSpaceRecoveryData.exists_blockResponsePairHalfState_ae_eq_recoveredField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        (fun x => (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn U]
          fun x => (R.recoveredField system P).eval x := by
  have hU : IsSobolevRegularDomain U := hConv.isSobolevRegularDomain
  have hResp :
      BlockResponseSpace a U (R.recoveredField system P) :=
    R.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol P
  have hLower :
      IsPotentialOn U
        (fun x =>
          (blockMatVecMul (blockCoeffField a x)
            ((R.recoveredField system P).eval x)).2) :=
    R.recoveredField_lowerImage_isPotential_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol P
  exact
    exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
      (a := a) hU.1 hResp hLower hEll

/-- Recovery-to-response bridge for the pure-gradient slice, proved without any
coarse-matrix package. -/
theorem MuCorrectionSpaceRecoveryData.mu_left_zero_eq_responseJ_zero_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (p0 : Vec d) :
    Mu U (p0, 0) a = ResponseJ U p0 0 a := by
  let Xrec : BlockState d := R.recoveredField system (p0, 0)
  rcases
      R.exists_blockResponsePairHalfState_ae_eq_recoveredField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        system hConv hEll hvol (p0, 0) with
    ⟨u, v, hEq⟩
  have hAdm : IsBlockMuAdmissible U (p0, 0) Xrec := by
    simpa [Xrec] using R.recoveredField_admissible system (p0, 0)
  have hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a (-p0) 0 u w) = 0 := by
    simpa [Xrec] using
      scalarFirstVariation_neg_left_zero_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
        (a := a) (U := U) (hU := hConv.isOpen.measurableSet) hEll p0 u v Xrec hEq hAdm
  have hEnergyRec :
      blockEnergyAverage U a Xrec = Mu U (p0, 0) a := by
    simpa [Xrec] using
      R.recoveredField_blockEnergyAverage_eq_mu system mu_eq_muCandidate (p0, 0)
  let Xpair : BlockState d := blockResponsePairHalfState a u v
  have hEnergyEq :
      blockEnergyAverage U a Xpair = blockEnergyAverage U a Xrec := by
    unfold blockEnergyAverage volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, blockEnergyDensity] using
      congrArg
        (fun z =>
          (1 / 2 : ℝ) * blockVecDot z (blockMatVecMul (blockCoeffField a x) z))
        hx
  have hPairEq :
      volumeAverage U
          (fun x => vecDot (Xpair.potential x) (Xpair.flux x)) =
        volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) := by
    unfold volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, BlockState.eval] using
      congrArg (fun z : BlockVec d => vecDot z.1 z.2) hx
  have hpotZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).potential x i
          ∂MeasureTheory.volume) = 0 := by
    intro P
    let Y := R.recoveredCorrectionField system P
    exact IsPotentialZeroTraceOn.integral_eq_zero
      Y.isPotentialZeroTrace
  have hfluxZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).flux x i
          ∂MeasureTheory.volume) = 0 := by
    intro P
    let Y := R.recoveredCorrectionField system P
    exact IsSolenoidalZeroNormalTraceOn.integral_eq_zero hConv.isSobolevRegularDomain
      Y.isSolenoidalZeroNormalTrace
  have hPairRec :
      volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) = 0 := by
    simpa [Xrec, vecDot_zero_right] using
      R.recoveredField_average_pairing_of_integral_eq_zero
        system hpotZero hfluxZero hvol (p0, 0)
  have hPair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = 0 := by
    simpa [Xpair] using hPairEq.trans hPairRec
  have hCouple :
      blockEnergyAverage U a Xpair = ResponseJ U p0 0 a := by
    simpa [Xpair] using
      blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_left_zero_of_pairingAverage_eq_zero_of_firstVariation_neg_left_zero
        (a := a) hEll p0 u v hPair hfirst
  calc
    Mu U (p0, 0) a = blockEnergyAverage U a Xrec := hEnergyRec.symm
    _ = blockEnergyAverage U a Xpair := hEnergyEq.symm
    _ = ResponseJ U p0 0 a := hCouple

/-- Packaged pure-gradient recovery/response bridge on a bounded open convex
domain. -/
theorem PotentialSolenoidalL2RecoveryData.mu_left_zero_eq_responseJ_zero_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (p0 : Vec d) :
    Mu U (p0, 0) a = ResponseJ U p0 0 a := by
  let Rc : MuCorrectionSpaceRecoveryData U := R.toMuCorrectionSpaceRecoveryData
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  exact
    Rc.mu_left_zero_eq_responseJ_zero_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol.ne' compat.mu_eq_muCandidate p0

/-- Recovery-to-response bridge for the full mixed slice, proved without any
coarse-matrix package. -/
theorem MuCorrectionSpaceRecoveryData.responseJ_eq_mu_neg_left_sub_vecDot_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (p0 q0 : Vec d) :
    ResponseJ U p0 q0 a = Mu U (-p0, q0) a - vecDot p0 q0 := by
  let Xrec : BlockState d := R.recoveredField system (-p0, q0)
  rcases
      R.exists_blockResponsePairHalfState_ae_eq_recoveredField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        system hConv hEll hvol (-p0, q0) with
    ⟨u, v, hEq⟩
  have hAdm : IsBlockMuAdmissible U (-p0, q0) Xrec := by
    simpa [Xrec] using R.recoveredField_admissible system (-p0, q0)
  have hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a p0 q0 u w) = 0 := by
    simpa [Xrec] using
      scalarFirstVariation_neg_left_right_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
        (a := a) (U := U) (hU := hConv.isOpen.measurableSet) hEll (-p0) q0 u v Xrec hEq hAdm
  have hEnergyRec :
      blockEnergyAverage U a Xrec = Mu U (-p0, q0) a := by
    simpa [Xrec] using
      R.recoveredField_blockEnergyAverage_eq_mu system mu_eq_muCandidate (-p0, q0)
  let Xpair : BlockState d := blockResponsePairHalfState a u v
  have hEnergyEq :
      blockEnergyAverage U a Xpair = blockEnergyAverage U a Xrec := by
    unfold blockEnergyAverage volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, blockEnergyDensity] using
      congrArg
        (fun z =>
          (1 / 2 : ℝ) * blockVecDot z (blockMatVecMul (blockCoeffField a x) z))
        hx
  have hPairEq :
      volumeAverage U
          (fun x => vecDot (Xpair.potential x) (Xpair.flux x)) =
        volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) := by
    unfold volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, BlockState.eval] using
      congrArg (fun z : BlockVec d => vecDot z.1 z.2) hx
  have hpotZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).potential x i
          ∂MeasureTheory.volume) = 0 := by
    intro P
    let Y := R.recoveredCorrectionField system P
    exact IsPotentialZeroTraceOn.integral_eq_zero
      Y.isPotentialZeroTrace
  have hfluxZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).flux x i
          ∂MeasureTheory.volume) = 0 := by
    intro P
    let Y := R.recoveredCorrectionField system P
    exact IsSolenoidalZeroNormalTraceOn.integral_eq_zero hConv.isSobolevRegularDomain
      Y.isSolenoidalZeroNormalTrace
  have hPairRec :
      volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) = -vecDot p0 q0 := by
    simpa [Xrec, vecDot_neg_left] using
      R.recoveredField_average_pairing_of_integral_eq_zero
        system hpotZero hfluxZero hvol (-p0, q0)
  have hPair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = -vecDot p0 q0 := by
    simpa [Xpair] using hPairEq.trans hPairRec
  have hCouple :
      blockEnergyAverage U a Xpair = ResponseJ U p0 q0 a - (-vecDot p0 q0) := by
    simpa [Xpair] using
      blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_sub_pairing_of_pairingAverage_eq_of_firstVariation_eq_zero
        (a := a) hEll p0 q0 u v (-vecDot p0 q0) hPair hfirst
  have hMu :
      Mu U (-p0, q0) a = ResponseJ U p0 q0 a + vecDot p0 q0 := by
    calc
      Mu U (-p0, q0) a = blockEnergyAverage U a Xrec := hEnergyRec.symm
      _ = blockEnergyAverage U a Xpair := hEnergyEq.symm
      _ = ResponseJ U p0 q0 a - (-vecDot p0 q0) := hCouple
      _ = ResponseJ U p0 q0 a + vecDot p0 q0 := by ring
  linarith

/-- Packaged full mixed recovery/response bridge on a bounded open convex
domain. -/
theorem PotentialSolenoidalL2RecoveryData.responseJ_eq_mu_neg_left_sub_vecDot_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (p0 q0 : Vec d) :
    ResponseJ U p0 q0 a = Mu U (-p0, q0) a - vecDot p0 q0 := by
  let Rc : MuCorrectionSpaceRecoveryData U := R.toMuCorrectionSpaceRecoveryData
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  exact
    Rc.responseJ_eq_mu_neg_left_sub_vecDot_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol.ne' compat.mu_eq_muCandidate p0 q0

/-- Convex-domain direct scalar-response splitting for the pure-flux recovered
field. This is the note-facing form of the previous bridge. -/
theorem MuCorrectionSpaceRecoveryData.volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_recoveredField_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q0 p pStar q qStar : Vec d) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        volumeAverage U
            (blockResponseIntegrand a (p, q) (qStar, pStar)
              (R.recoveredField system (0, q0))) =
          (1 / 2 : ℝ) * volumeAverage U
              (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
            (1 / 2 : ℝ) *
              volumeAverage U
                (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q) v) := by
  have hU : IsSobolevRegularDomain U := hConv.isSobolevRegularDomain
  have hResp :
      BlockResponseSpace a U (R.recoveredField system (0, q0)) :=
    R.recoveredField_mem_responseSpace_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol q0
  have hLower :
      IsPotentialOn U
        (fun x =>
          (blockMatVecMul (blockCoeffField a x)
            ((R.recoveredField system (0, q0)).eval x)).2) :=
    R.recoveredField_lowerImage_isPotential_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol q0
  exact
    volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
      (a := a) hU.1 hResp hLower hEll p pStar q qStar

/-- Convex-domain direct scalar-response splitting for a general recovered
block datum. -/
theorem MuCorrectionSpaceRecoveryData.volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_recoveredField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) (p pStar q qStar : Vec d) :
    ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (Homogenization.adjointCoeffField a) U,
        volumeAverage U
            (blockResponseIntegrand a (p, q) (qStar, pStar)
              (R.recoveredField system P)) =
          (1 / 2 : ℝ) * volumeAverage U
              (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
            (1 / 2 : ℝ) *
              volumeAverage U
                (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q) v) := by
  have hU : IsSobolevRegularDomain U := hConv.isSobolevRegularDomain
  have hResp :
      BlockResponseSpace a U (R.recoveredField system P) :=
    R.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol P
  have hLower :
      IsPotentialOn U
        (fun x =>
          (blockMatVecMul (blockCoeffField a x)
            ((R.recoveredField system P).eval x)).2) :=
    R.recoveredField_lowerImage_isPotential_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEll hvol P
  exact
    volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
      (a := a) hU.1 hResp hLower hEll p pStar q qStar

end

end Homogenization
