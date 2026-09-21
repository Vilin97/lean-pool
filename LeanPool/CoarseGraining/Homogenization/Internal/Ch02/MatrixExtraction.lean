/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixExtraction
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Existence
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Adapters
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecoveryBlockResponse
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticWrappers
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaStarPosDef
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.QuadraticMu
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Realization
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-! # Matrix Extraction -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

theorem domain_volume_pos {d : ℕ} (U : Domain d) :
    0 < (MeasureTheory.volume (U : Set (Vec d))).toReal := by
  have hpos : 0 < MeasureTheory.volume (U : Set (Vec d)) :=
    U.isOpen.measure_pos MeasureTheory.volume U.nonempty
  have htop : MeasureTheory.volume (U : Set (Vec d)) ≠ ⊤ :=
    ne_of_lt U.isDomain.volume_lt_top
  exact ENNReal.toReal_pos hpos.ne' htop

/-- On a bounded open convex domain, the canonical closure-based recovery data
realizes the Hilbert minimizer value `muCandidate`. -/
theorem exists_recoveryData_of_mu_eq_muCandidate_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ∃ R : PotentialSolenoidalL2RecoveryData U,
      ∀ P : BlockVec d,
        Mu U P a =
          ((R.toMuHilbertRealization
            (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)).muCandidate P) := by
  let hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hConv
  let R : PotentialSolenoidalL2RecoveryData U :=
    potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
      (U := U) hRealize
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  refine ⟨R, ?_⟩
  intro P
  have hCandidateLe :
      ∀ X : BlockState d, IsBlockMuAdmissible U P X →
        (R.toMuHilbertRealization system).muCandidate P ≤ blockEnergyAverage U a X := by
    intro X hX
    let Y : CorrectionFieldData U := hX.toCorrectionFieldDataOfAdmissible
    have hXmemBlock : MemBlockL2 U X.eval := hX.memBlockL2_eval
    have hcorr :
        Y.toHilbertBlockL2 ∈ R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.correctionSpace := by
      exact
        R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.mem_correctionSpace
          Y.potential_memL2 Y.flux_memL2 Y.isPotentialZeroTrace Y.isSolenoidalZeroNormalTrace
    have hconst_add :
        toHilbertBlockL2OfBlockField (U := U) hXmemBlock =
          blockVecToHilbertBlockL2Const (U := U) P + Y.toHilbertBlockL2 := by
      simpa [Y] using hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    have hcorr_mem :
        toHilbertBlockL2OfBlockField (U := U) hXmemBlock -
            (R.toMuHilbertRealization system).constantField P ∈
          (R.toMuHilbertRealization system).correctionSpace.correctionSpace := by
      rw [hconst_add]
      simpa [R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        MuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcorr
    have hMin :
        (R.toMuHilbertRealization system).muCandidate P ≤
          quadraticEnergy
            (energyBilinOfOperator system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (U := U) hXmemBlock) := by
      simpa [R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        MuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        (R.toMuHilbertRealization system).muCandidate_le_quadraticEnergy P
          (toHilbertBlockL2OfBlockField (U := U) hXmemBlock) hcorr_mem
    calc
      (R.toMuHilbertRealization system).muCandidate P ≤
          quadraticEnergy
            (energyBilinOfOperator system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (U := U) hXmemBlock) := hMin
      _ = blockEnergyAverage U a X := by
            exact
              system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                (X := X) hXmemBlock
  have hrecEnergy :
      blockEnergyAverage U a ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P) =
        (R.toMuHilbertRealization system).muCandidate P := by
    let H : MuHilbertRealization U a := R.toMuHilbertRealization system
    have hminim :
        toHilbertBlockL2OfBlockField (U := U)
            ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P) =
          H.minimizerMap P := by
      simpa [H, R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization] using!
        (R.toMuCorrectionSpaceRecoveryData).recoveredField_minimizer_eq system P
    calc
      blockEnergyAverage U a ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P)
          = quadraticEnergy
              (energyBilinOfOperator system.toMuOperatorRealization.operator)
              (toHilbertBlockL2OfBlockField (U := U)
                ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P)) := by
                symm
                exact
                  system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                    (X := (R.toMuCorrectionSpaceRecoveryData).recoveredField system P)
                    ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P)
      _ = quadraticEnergy H.energyBilin (H.minimizerMap P) := by
            rw [hminim]
            rfl
      _ = H.muCandidate P := by
            rfl
      _ = (R.toMuHilbertRealization system).muCandidate P := by
            rfl
  have hBddBelow : BddBelow (muValueSet U P a) := by
    refine ⟨vecDot P.1 P.2, ?_⟩
    intro m hm
    rcases hm with ⟨X, hX, rfl⟩
    exact
      hX.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
        (a := a)
        (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn (a := a) hEll)
        hEll
        (by
          simpa [sub_eq_add_neg] using
            (IsPotentialZeroTraceOn.integral_eq_zero hX.isPotentialZeroTrace))
        (by
          simpa [sub_eq_add_neg] using
            (IsSolenoidalZeroNormalTraceOn.integral_eq_zero hConv.isSobolevRegularDomain
              hX.isSolenoidalZeroNormalTrace))
        hvol.ne'
  have hUpper :
      Mu U P a ≤ (R.toMuHilbertRealization system).muCandidate P := by
    let Xrec : BlockState d := (R.toMuCorrectionSpaceRecoveryData).recoveredField system P
    have hAdm : IsBlockMuAdmissible U P Xrec := by
      simpa [Xrec] using (R.toMuCorrectionSpaceRecoveryData).recoveredField_admissible system P
    calc
      Mu U P a ≤ blockEnergyAverage U a Xrec := by
        exact csInf_le hBddBelow (muValueSet_mem hAdm)
      _ = (R.toMuHilbertRealization system).muCandidate P := hrecEnergy
  have hLower :
      (R.toMuHilbertRealization system).muCandidate P ≤ Mu U P a := by
    apply le_Mu_of_forall_isBlockMuAdmissible
    intro X hX
    exact hCandidateLe X hX
  exact le_antisymm hUpper hLower

/-- Internal package of old coarse-matrix data, with all recovery and
compatibility witnesses hidden behind bounded-open-convex domain hypotheses. -/
theorem exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ∃ R : PotentialSolenoidalL2RecoveryData U,
      ∃ sigma0 : Mat d,
        ∃ _compat :
        PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
            (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol),
          IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a) ∧
            IsSigmaStarInvCoarse U a (sigmaStarInvCoarse U a) ∧
            IsSigmaStarCoarse U a (sigmaStarCoarse U a) ∧
            IsKappaCoarse U a (sigmaStarCoarse U a) (kappaCoarse U a) ∧
            IsSigmaCoarse U a sigma0 (sigmaStarCoarse U a) (kappaCoarse U a) ∧
            IsSigmaCanonicalCoarse U a (sigmaCoarse U a) := by
  rcases
      exists_recoveryData_of_mu_eq_muCandidate_of_isOpenBoundedConvexDomain
        (U := U) hConv hEll hvol with
    ⟨R, hMuEq⟩
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  have compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R system := by
    simpa [system] using!
      R.muRecoveryCompatibilityData_of_isEllipticFieldOn_of_mu_eq_muCandidate
        hEll hvol hMuEq
  have hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
    R.exists_coarseBlockMatrixOfIsEllipticFieldOn hEll hvol compat
  have hAcoarse : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex
  have hMuRespQ :
      ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a := by
    intro q
    exact R.mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      hConv hEll hvol compat q
  have hMuRespP :
      ∀ p : Vec d, Mu U (p, 0) a = ResponseJ U p 0 a := by
    intro p
    exact R.mu_left_zero_eq_responseJ_zero_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      hConv hEll hvol compat p
  have hResp :
      ∀ p q : Vec d, ResponseJ U p q a = Mu U (-p, q) a - vecDot p q := by
    intro p q
    exact R.responseJ_eq_mu_neg_left_sub_vecDot_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      hConv hEll hvol compat p q
  have hSInvLower :
      IsSigmaStarInvCoarse U a (coarseBlockMatrix U a).lowerRight :=
    isSigmaStarInvCoarse_coarseBlockMatrix_lowerRight_of_mu_zero_right_eq_responseJ_zero
      (U := U) (a := a) hex hMuRespQ
  have hSInv : IsSigmaStarInvCoarse U a (sigmaStarInvCoarse U a) :=
    isSigmaStarInvCoarse_sigmaStarInvCoarse
      ⟨(coarseBlockMatrix U a).lowerRight, hSInvLower⟩
  have hMlower :
      IsSigmaStarInvKappaCoarse U a (-(coarseBlockMatrix U a).lowerLeft) :=
    isSigmaStarInvKappaCoarse_neg_coarseBlockMatrix_lowerLeft_of_exact_slices
      (U := U) (a := a) hex hMuRespQ hMuRespP hResp
  have hM : IsSigmaStarInvKappaCoarse U a (sigmaStarInvKappaCoarse U a) :=
    isSigmaStarInvKappaCoarse_sigmaStarInvKappaCoarse
      ⟨-(coarseBlockMatrix U a).lowerLeft, hMlower⟩
  have hdetInv : IsUnit (sigmaStarInvCoarse U a).det := by
    have hPos : (sigmaStarInvCoarse U a).PosDef :=
      sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        R hConv hEll hvol compat
    exact (Matrix.isUnit_iff_isUnit_det (A := sigmaStarInvCoarse U a)).mp hPos.isUnit
  have hS : IsSigmaStarCoarse U a (sigmaStarCoarse U a) :=
    isSigmaStarCoarse_sigmaStarCoarse_of_isSigmaStarInvCoarse hSInv hdetInv
  have hK : IsKappaCoarse U a (sigmaStarCoarse U a) (kappaCoarse U a) :=
    isKappaCoarse_kappaCoarse_of_isSigmaStarInvKappaCoarse_of_isUnit_det_sigmaStarInvCoarse
      hM hdetInv
  let sigma0 : Mat d :=
    (coarseBlockMatrix U a).upperLeft -
      (matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a * kappaCoarse U a
  have hSigma0 :
      IsSigmaCoarse U a sigma0 (sigmaStarCoarse U a) (kappaCoarse U a) := by
    refine ⟨?_, ?_⟩
    · have hUpperSymm : ((coarseBlockMatrix U a).upperLeft).IsSymm := by
        rw [Matrix.IsSymm.ext_iff]
        intro i j
        simpa [blockMatEntry] using (hAcoarse.1 (Sum.inl i) (Sum.inl j)).symm
      have hCorrSymm :
          (((matTranspose (kappaCoarse U a)) * sigmaStarInvCoarse U a *
              kappaCoarse U a)).IsSymm :=
        transpose_mul_symm_mul_isSymm (kappaCoarse U a) (sigmaStarInvCoarse U a) hSInv.1
      rw [Matrix.IsSymm.ext_iff]
      intro i j
      simp [sigma0, hUpperSymm.apply i j, hCorrSymm.apply i j]
    · intro p
      have hRespP :
          ResponseJ U p 0 a =
            (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
        calc
          ResponseJ U p 0 a = Mu U (p, 0) a := (hMuRespP p).symm
          _ =
            (1 / 2 : ℝ) * blockVecDot (p, 0)
              (blockMatVecMul (coarseBlockMatrix U a) (p, 0)) := by
                simpa using hAcoarse.2 (p, 0)
          _ =
            (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
                simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left]
      have hInvEq : (sigmaStarCoarse U a)⁻¹ = sigmaStarInvCoarse U a := by
        rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
      rw [hRespP, hInvEq]
      simp [sigma0, sub_eq_add_neg, add_matVecMul, neg_matVecMul, vecDot_add_right,
        vecDot_neg_right, matVecMul_mul, Matrix.mul_assoc]
      ring_nf
  have hdetS : IsUnit (sigmaStarCoarse U a).det := by
    unfold sigmaStarCoarse
    exact Matrix.isUnit_nonsing_inv_det (A := sigmaStarInvCoarse U a) hdetInv
  have hLower :
      (coarseBlockMatrix U a).lowerLeft =
        -((sigmaStarCoarse U a)⁻¹ * kappaCoarse U a) := by
    calc
      (coarseBlockMatrix U a).lowerLeft = -(sigmaStarInvKappaCoarse U a) := by
        have hEq :
            -(coarseBlockMatrix U a).lowerLeft = sigmaStarInvKappaCoarse U a :=
          eq_sigmaStarInvKappaCoarse_of_isSigmaStarInvKappaCoarse hMlower
        simpa using congrArg Neg.neg hEq
      _ = -((sigmaStarCoarse U a)⁻¹ * kappaCoarse U a) := by
        rw [sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse hK]
  have hUpper :
      (coarseBlockMatrix U a).upperRight =
        -((matTranspose (kappaCoarse U a)) * (sigmaStarCoarse U a)⁻¹) := by
    have hUpperSymm :
        (coarseBlockMatrix U a).upperRight =
          matTranspose (coarseBlockMatrix U a).lowerLeft := by
      ext i j
      simpa [blockMatEntry, matTranspose] using hAcoarse.1 (Sum.inl i) (Sum.inr j)
    calc
      (coarseBlockMatrix U a).upperRight =
          matTranspose (coarseBlockMatrix U a).lowerLeft := hUpperSymm
      _ = matTranspose (-((sigmaStarCoarse U a)⁻¹ * kappaCoarse U a)) := by
            rw [hLower]
      _ = -((matTranspose (kappaCoarse U a)) * (sigmaStarCoarse U a)⁻¹) := by
            change Matrix.transpose (-((sigmaStarCoarse U a)⁻¹ * kappaCoarse U a)) =
              -((matTranspose (kappaCoarse U a)) * (sigmaStarCoarse U a)⁻¹)
            rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
            rw [show Matrix.transpose (sigmaStarCoarse U a) = sigmaStarCoarse U a by
                  simpa [matTranspose] using hS.1.eq]
            simp [matTranspose]
  have hLowerRight :
      (coarseBlockMatrix U a).lowerRight = sigmaStarInvCoarse U a := by
    exact
      coarseBlockMatrix_lowerRight_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero
        (U := U) (a := a) hex hMuRespQ
  have hBlockEq :
      blockMatrixOfDeterministicData sigma0 (sigmaStarCoarse U a) (kappaCoarse U a) =
        coarseBlockMatrix U a := by
    refine blockMat_ext ?_ ?_ ?_ ?_
    · simp [blockMatrixOfDeterministicData, bCoarse, sigma0,
        sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
    · simpa [blockMatrixOfDeterministicData] using hUpper.symm
    · simpa [blockMatrixOfDeterministicData] using hLower.symm
    · calc
        (sigmaStarCoarse U a)⁻¹ = sigmaStarInvCoarse U a := by
          rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
        _ = (coarseBlockMatrix U a).lowerRight := hLowerRight.symm
  have hAblock :
      IsCoarseBlockMatrix U a
        (blockMatrixOfDeterministicData sigma0 (sigmaStarCoarse U a) (kappaCoarse U a)) := by
    rw [hBlockEq]
    exact hAcoarse
  have hAdet :
      IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a) := by
    rw [deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS hK hSigma0 hdetS]
    exact hAblock
  have hSigmaCanonical0 : IsSigmaCanonicalCoarse U a sigma0 :=
    isSigmaCanonicalCoarse_of_isSigmaCoarse hS hK hSigma0 hdetS
  have hSigmaCanonical : IsSigmaCanonicalCoarse U a (sigmaCoarse U a) :=
    isSigmaCanonicalCoarse_sigmaCoarse ⟨sigma0, hSigmaCanonical0⟩
  exact ⟨R, sigma0, compat, hAdet, hSInv, hS, hK, hSigma0, hSigmaCanonical⟩

private theorem responseJ_zero_zero_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseJ (U : Set (Vec d)) 0 0 a.toCoeffField = 0 := by
  have hmax0 :
      Homogenization.IsResponseMaximizer (U : Set (Vec d)) 0 0 a.toCoeffField
        (0 : AHarmonicFunction a.toCoeffField (U : Set (Vec d))) := by
    apply isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
      (U : Set (Vec d)) a.toCoeffField hEll
    intro w
    rw [show
        scalarFirstVariationIntegrand (U : Set (Vec d)) a.toCoeffField 0 0
            (0 : AHarmonicFunction a.toCoeffField (U : Set (Vec d))) w = 0 by
          funext x
          simp [scalarFirstVariationIntegrand, matVecMul_zero, vecDot_zero_left,
            vecDot_zero_right]]
    exact volumeAverage_zero (U : Set (Vec d))
  have hJ :=
    responseJ_eq_of_isResponseMaximizer (U : Set (Vec d)) 0 0 a.toCoeffField hmax0
  rw [hJ]
  simp [scalarResponseIntegrand_zero]

private theorem responseJ_zero_zero {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    responseJ U a 0 0 = 0 := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hb : responseJ U b 0 0 = 0 := by
    rw [book_responseJ_eq_ResponseJ U b 0 0]
    exact responseJ_zero_zero_of_isEllipticFieldOn U b
      (by simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a)
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  calc
    responseJ U a 0 0 = responseJ U b 0 0 := (responseJ_eq_ofAEEq hba 0 0).symm
    _ = 0 := hb

private theorem canonicalResponseMatrixIdentities_zero_dim
    (U : Domain 0) (a : CoeffOn U) :
    CanonicalResponseMatrixIdentities U a := by
  have hJ00 : responseJ U a 0 0 = 0 := responseJ_zero_zero U a
  refine
    { sigma_symm := coarseMatrices_sigma_isSymm U a
      sigmaStarInv_symm := coarseMatrices_sigmaStarInv_isSymm U a
      sigmaStarInv_response := ?_
      kappa_response := ?_
      sigma_response := ?_
      full_response := ?_ }
  · intro q
    have hq : q = 0 := Subsingleton.elim q 0
    subst q
    change responseJ U a (0 : Vec 0) (0 : Vec 0) =
      (1 / 2 : ℝ) * vecDot (0 : Vec 0)
        (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) (0 : Vec 0))
    simpa [vecDot, matVecMul] using hJ00
  · intro p q
    have hp : p = 0 := Subsingleton.elim p 0
    have hq : q = 0 := Subsingleton.elim q 0
    subst p
    subst q
    change Book.Ch02.mixedResponse U a (0 : Vec 0) (0 : Vec 0) =
      vecDot (0 : Vec 0)
        (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
          (matVecMul (Book.Ch02.kappaCoarse U a) (0 : Vec 0)))
    simpa [Book.Ch02.mixedResponse, vecDot, matVecMul] using hJ00
  · intro p
    have hp : p = 0 := Subsingleton.elim p 0
    subst p
    change Book.Ch02.sigmaCorrectedResponse U a (coarseMatrices U a) (0 : Vec 0) =
      (1 / 2 : ℝ) * vecDot (0 : Vec 0)
        (matVecMul (Book.Ch02.sigmaCoarse U a) (0 : Vec 0))
    simpa [Book.Ch02.sigmaCorrectedResponse, vecDot, matVecMul] using hJ00
  · intro p q
    have hp : p = 0 := Subsingleton.elim p 0
    have hq : q = 0 := Subsingleton.elim q 0
    subst p
    subst q
    change responseJ U a (0 : Vec 0) (0 : Vec 0) =
      (1 / 2 : ℝ) * vecDot (0 : Vec 0)
          (matVecMul (Book.Ch02.sigmaCoarse U a) (0 : Vec 0)) +
        (1 / 2 : ℝ) *
          vecDot ((0 : Vec 0) + matVecMul (Book.Ch02.kappaCoarse U a) (0 : Vec 0))
            (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
              ((0 : Vec 0) + matVecMul (Book.Ch02.kappaCoarse U a) (0 : Vec 0))) -
        vecDot (0 : Vec 0) (0 : Vec 0)
    simpa [vecDot, matVecMul] using hJ00

theorem canonicalResponseMatrixIdentities_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    CanonicalResponseMatrixIdentities U a := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨R, sigma0, compat, _hA, hSInv, hS, hK, hSigma, hSigmaCanonical⟩
  refine
    { sigma_symm := coarseMatrices_sigma_isSymm U a
      sigmaStarInv_symm := coarseMatrices_sigmaStarInv_isSymm U a
      sigmaStarInv_response := ?_
      kappa_response := ?_
      sigma_response := ?_
      full_response := ?_ }
  · intro q
    calc
      responseJ U a 0 q =
          ResponseJ (U : Set (Vec d)) 0 q a.toCoeffField :=
        book_responseJ_eq_ResponseJ U a 0 q
      _ = (1 / 2 : ℝ) * vecDot q
            (matVecMul (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField) q) :=
        hSInv.2 q
      _ = (1 / 2 : ℝ) * vecDot q
            (matVecMul (coarseMatrices U a).sigmaStarInv q) := by
        rw [← book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a]
        rfl
  · intro p q
    calc
      mixedResponse U a p q =
          ResponseJ (U : Set (Vec d)) p q a.toCoeffField -
            ResponseJ (U : Set (Vec d)) p 0 a.toCoeffField -
            ResponseJ (U : Set (Vec d)) 0 q a.toCoeffField + vecDot p q := by
        simp [mixedResponse, book_responseJ_eq_ResponseJ]
      _ =
          vecDot q
            (matVecMul
              ((Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)⁻¹)
              (matVecMul (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)) :=
        hK p q
      _ =
          vecDot q
            (matVecMul
              (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField)
              (matVecMul (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)) := by
        rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
      _ =
          vecDot q
            (matVecMul (coarseMatrices U a).sigmaStarInv
              (matVecMul (coarseMatrices U a).kappa p)) := by
        rw [← book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a,
          ← book_kappaCoarse_eq_kappaCoarse U a]
        rfl
  · intro p
    calc
      Book.Ch02.sigmaCorrectedResponse U a (coarseMatrices U a) p =
          Homogenization.sigmaCorrectedResponse (U : Set (Vec d)) a.toCoeffField p := by
        rw [Book.Ch02.sigmaCorrectedResponse_coarseMatrices]
        exact book_canonicalSigmaCorrectedResponse_eq_sigmaCorrectedResponse U a p
      _ =
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField) p) :=
        hSigmaCanonical.2 p
      _ =
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (coarseMatrices U a).sigma p) := by
        rw [← book_sigmaCoarse_eq_sigmaCoarse U a]
        rfl
  · intro p q
    have hOld :
        ResponseJ (U : Set (Vec d)) p q a.toCoeffField =
          Homogenization.sigmaCorrectedResponse (U : Set (Vec d)) a.toCoeffField p -
            vecDot p q +
            (1 / 2 : ℝ) *
              vecDot
                (q + matVecMul (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)
                (matVecMul
                  (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField)
                  (q + matVecMul
                    (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)) :=
      magic_identity_responseJ_completed_square_canonical_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        R U.isDomain hEll hvol compat hS hK hSigma p q
    calc
      responseJ U a p q =
          ResponseJ (U : Set (Vec d)) p q a.toCoeffField :=
        book_responseJ_eq_ResponseJ U a p q
      _ =
          (1 / 2 : ℝ) * vecDot p
              (matVecMul (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField) p) +
            (1 / 2 : ℝ) *
              vecDot
                (q + matVecMul (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)
                (matVecMul
                  (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField)
                  (q + matVecMul
                    (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p)) -
            vecDot p q := by
        rw [hOld, hSigmaCanonical.2 p]
        ring
      _ =
          (1 / 2 : ℝ) * vecDot p (matVecMul (coarseMatrices U a).sigma p) +
            (1 / 2 : ℝ) *
              vecDot (q + matVecMul (coarseMatrices U a).kappa p)
                (matVecMul (coarseMatrices U a).sigmaStarInv
                  (q + matVecMul (coarseMatrices U a).kappa p)) -
            vecDot p q := by
        rw [← book_sigmaCoarse_eq_sigmaCoarse U a,
          ← book_kappaCoarse_eq_kappaCoarse U a,
          ← book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a]
        rfl

theorem canonicalResponseMatrixIdentities_of_neZero
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U) :
    CanonicalResponseMatrixIdentities U a := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hb : CanonicalResponseMatrixIdentities U b :=
    canonicalResponseMatrixIdentities_of_isEllipticFieldOn U b
      (by simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a)
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  exact CanonicalResponseMatrixIdentities.ofAEEq hba hb

theorem canonicalResponseMatrixIdentities
    {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    CanonicalResponseMatrixIdentities U a := by
  by_cases hd : d = 0
  · subst d
    exact canonicalResponseMatrixIdentities_zero_dim U a
  · let : NeZero d := ⟨hd⟩
    exact canonicalResponseMatrixIdentities_of_neZero U a

end BookCh02

end

end Ch02
end Internal
end Homogenization
