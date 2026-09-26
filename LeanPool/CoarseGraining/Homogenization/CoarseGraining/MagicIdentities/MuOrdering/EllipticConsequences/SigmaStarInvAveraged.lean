/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.BCoarseAveraged

/-! # Sigma Star Inv Averaged -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- sigmaStarInvCoarse averaged-blockmatrix bounds

`sigmaStarInvCoarse_le_average_blockMatrixOfCoeff_lowerRight_…` and the two
elliptic-bridge wrappers establishing the harmonic-mean-style upper bound
`sigmaStarInvCoarse U a ≤ volumeAverage U (symmPart (a x))⁻¹` under
`HodgeConverseCriterion` / `IsOpenBoundedConvexDomain`.
-/

theorem sigmaStarInvCoarse_le_average_blockMatrixOfCoeff_lowerRight_of_mu_zero_right_eq_responseJ_zero
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d}
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hMuResp : ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a)
    (q : Vec d) :
    vecDot q (matVecMul (sigmaStarInvCoarse U a) q) ≤
      volumeAverage U
        (fun x => vecDot q (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) q)) := by
  let P : BlockVec d := (0, q)
  let X : BlockState d :=
    { potential := fun _ => 0
      flux := fun _ => q }
  have hX : IsBlockMuAdmissible U P X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hzero : (fun x => X.potential x - P.1) = (0 : Vec d → Vec d) := by
        funext x
        simp [X, P]
      rw [hzero]
      exact MeasureTheory.MemLp.zero
    · have hzero : (fun x => X.potential x - P.1) = (0 : Vec d → Vec d) := by
        funext x
        simp [X, P]
      rw [hzero]
      exact isPotentialZeroTraceOn_zero (U := U)
    · have hzero : (fun x => X.flux x - P.2) = (0 : Vec d → Vec d) := by
        funext x
        simp [X, P]
      rw [hzero]
      exact MeasureTheory.MemLp.zero
    · have hzero : (fun x => X.flux x - P.2) = (0 : Vec d → Vec d) := by
        funext x
        simp [X, P]
      rw [hzero]
      exact isSolenoidalZeroNormalTraceOn_zero (U := U)
  have hBddBelow : BddBelow (muValueSet U P a) := by
    refine ⟨0, ?_⟩
    intro m hm
    rcases hm with ⟨Y, hY, rfl⟩
    have hLower :
        vecDot P.1 P.2 ≤ blockEnergyAverage U a Y := by
      exact
        hY.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
          (a := a)
          (hY.toBlockMuIntegrabilityDataOfIsEllipticFieldOn (a := a) hEll)
          hEll
          (by
            simpa [sub_eq_add_neg] using
              (IsPotentialZeroTraceOn.integral_eq_zero hY.isPotentialZeroTrace))
          (by
            simpa [sub_eq_add_neg] using
              (IsSolenoidalZeroNormalTraceOn.integral_eq_zero hU hY.isSolenoidalZeroNormalTrace))
          hvol
    have hLower' : 0 ≤ blockEnergyAverage U a Y := by
      simpa [P, vecDot_zero_left] using hLower
    simpa [blockEnergyAverage] using hLower'
  have hMuLe :
      Mu U P a ≤ volumeAverage U (blockEnergyDensity a X) := by
    unfold Mu
    exact csInf_le hBddBelow (muValueSet_mem hX)
  have hAc : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex
  have hMuEq :
      Mu U P a =
        (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
    calc
      Mu U P a =
          (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) := by
            rw [hAc.2 P]
      _ =
          (1 / 2 : ℝ) *
            vecDot q (matVecMul ((coarseBlockMatrix U a).lowerRight) q) := by
            simp [P, blockVecDot, matVecMul_zero, vecDot_zero_left]
      _ =
          (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
            rw [coarseBlockMatrix_lowerRight_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero
              (U := U) (a := a) hex hMuResp]
  have hEnergy :
      blockEnergyDensity a X =
        fun x =>
          (1 / 2 : ℝ) * vecDot q (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) q) := by
    funext x
    simp [X, blockEnergyDensity, BlockState.eval, blockCoeffField, blockVecDot, blockMatVecMul,
      matVecMul_zero, vecDot_zero_left]
  rw [hMuEq, hEnergy] at hMuLe
  have hAvgHalf :
      volumeAverage U (fun x => (1 / 2 : ℝ) * vecDot q (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) q)) =
        (1 / 2 : ℝ) *
          volumeAverage U (fun x => vecDot q (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) q)) := by
    simpa [smul_eq_mul] using!
      (volumeAverage_smul U (1 / 2 : ℝ)
        (fun x => vecDot q (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) q)))
  rw [hAvgHalf] at hMuLe
  nlinarith

theorem sigmaStarInvCoarse_le_averaged_symmPart_inv_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (q : Vec d) :
    vecDot q (matVecMul (sigmaStarInvCoarse U a) q) ≤
      volumeAverage U
        (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q)) := by
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  let Rc : MuCorrectionSpaceRecoveryData U := R.toMuCorrectionSpaceRecoveryData
  have hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
    R.exists_coarseBlockMatrixOfIsEllipticFieldOn hEll hvol compat
  have hMuResp :
      ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a := by
    intro q
    exact
      Rc.mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn_of_hodgeConverseCriterion
        system hU hEll hHodge hvol.ne' compat.mu_eq_muCandidate q
  simpa [blockMatrixOfCoeff] using
    sigmaStarInvCoarse_le_average_blockMatrixOfCoeff_lowerRight_of_mu_zero_right_eq_responseJ_zero
      (U := U) (a := a) hU hEll hex hvol.ne' hMuResp q

theorem sigmaStarInvCoarse_le_averaged_symmPart_inv_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (q : Vec d) :
    vecDot q (matVecMul (sigmaStarInvCoarse U a) q) ≤
      volumeAverage U
        (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q)) := by
  exact
    sigmaStarInvCoarse_le_averaged_symmPart_inv_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat q

end

end Homogenization
