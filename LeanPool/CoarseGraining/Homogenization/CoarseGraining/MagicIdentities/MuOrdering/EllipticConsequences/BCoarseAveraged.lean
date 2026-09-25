/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaLeBCoarse

/-! # BCoarse Averaged -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- bCoarse averaged-blockmatrix bounds

`bCoarse_le_average_blockMatrixOfCoeff_upperLeft_…` plus the three
`bCoarse_le_averaged_symmPart_plus_correction_…` wrappers. These reach back to
the Mu/blockEnergy variational lower bound and show the canonical `bCoarse`
matrix is dominated by the volume-average of `(blockMatrixOfCoeff (a x)).upperLeft`,
i.e., the symmetric part plus the (skew⊤ · symm⁻¹ · skew) Schur correction.
-/

theorem bCoarse_le_average_blockMatrixOfCoeff_upperLeft_of_isEllipticFieldOn_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d) :
    vecDot p (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) ≤
      volumeAverage U
        (fun x => vecDot p (matVecMul ((blockMatrixOfCoeff (a x)).upperLeft) p)) := by
  let P : BlockVec d := (p, 0)
  let X : BlockState d :=
    { potential := fun _ => p
      flux := fun _ => 0 }
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
      simpa [P, vecDot_zero_right] using hLower
    simpa [blockEnergyAverage] using hLower'
  have hMuLe :
      Mu U P a ≤ volumeAverage U (blockEnergyDensity a X) := by
    unfold Mu
    exact csInf_le hBddBelow (muValueSet_mem hX)
  have hAc : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix
      ⟨deterministicCoarseBlockMatrix U a, hA⟩
  have hMuEq :
      Mu U P a =
        (1 / 2 : ℝ) *
          vecDot p
            (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) := by
    calc
      Mu U P a =
          (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) := by
            rw [hAc.2 P]
      _ =
          (1 / 2 : ℝ) *
            vecDot p (matVecMul ((coarseBlockMatrix U a).upperLeft) p) := by
            simp [P, blockVecDot, matVecMul_zero, vecDot_zero_left]
      _ =
          (1 / 2 : ℝ) *
            vecDot p
              (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) := by
            rw [coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix
              hA hS hK hSigma hdet]
            simp [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
              eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
              sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet]
  have hEnergy :
      blockEnergyDensity a X =
        fun x =>
          (1 / 2 : ℝ) * vecDot p (matVecMul ((blockMatrixOfCoeff (a x)).upperLeft) p) := by
    funext x
    simp [X, blockEnergyDensity, BlockState.eval, blockCoeffField, blockVecDot, blockMatVecMul,
      matVecMul_zero, vecDot_zero_left]
  rw [hMuEq, hEnergy] at hMuLe
  have hAvgHalf :
      volumeAverage U (fun x => (1 / 2 : ℝ) * vecDot p (matVecMul ((blockMatrixOfCoeff (a x)).upperLeft) p)) =
        (1 / 2 : ℝ) *
          volumeAverage U (fun x => vecDot p (matVecMul ((blockMatrixOfCoeff (a x)).upperLeft) p)) := by
    simpa [smul_eq_mul] using!
      (volumeAverage_smul U (1 / 2 : ℝ)
        (fun x => vecDot p (matVecMul ((blockMatrixOfCoeff (a x)).upperLeft) p)))
  rw [hAvgHalf] at hMuLe
  nlinarith

theorem bCoarse_le_averaged_symmPart_plus_correction_of_isEllipticFieldOn_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d) :
    vecDot p (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) ≤
      volumeAverage U
        (fun x =>
          vecDot p
            (matVecMul
              (symmPart (a x) +
                matTranspose (skewPart (a x)) * (symmPart (a x))⁻¹ * skewPart (a x))
              p)) := by
  simpa [blockMatrixOfCoeff] using
    bCoarse_le_average_blockMatrixOfCoeff_upperLeft_of_isEllipticFieldOn_of_isSobolevRegularDomain
      (U := U) (a := a) hU hEll hvol hA hS hK hSigma hdet p

theorem bCoarse_le_averaged_symmPart_plus_correction_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (p : Vec d) :
    vecDot p (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) ≤
      volumeAverage U
        (fun x =>
          vecDot p
            (matVecMul
              (symmPart (a x) +
                matTranspose (skewPart (a x)) * (symmPart (a x))⁻¹ * skewPart (a x))
              p)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact
    bCoarse_le_averaged_symmPart_plus_correction_of_isEllipticFieldOn_of_isSobolevRegularDomain
      (U := U) (a := a) hU hEll hvol.ne' hA hS hK hSigma hdet p

theorem bCoarse_le_averaged_symmPart_plus_correction_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (p : Vec d) :
    vecDot p (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p) ≤
      volumeAverage U
        (fun x =>
          vecDot p
            (matVecMul
              (symmPart (a x) +
                matTranspose (skewPart (a x)) * (symmPart (a x))⁻¹ * skewPart (a x))
              p)) := by
  exact
    bCoarse_le_averaged_symmPart_plus_correction_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat hA hS hK hSigma p

end

end Homogenization
