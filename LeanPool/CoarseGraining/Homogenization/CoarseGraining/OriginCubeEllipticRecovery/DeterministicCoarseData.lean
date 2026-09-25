/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.HarmonicMean
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.UpperLeftAverage
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.MuGeVecDot

/-!
# Origin-cube elliptic recovery -- deterministic coarse data output

Adjoint-free sigma_* <= sigma and sigma <= b orderings on the centered open
cube, the packaged openCubeDeterministicCoarseData_of_triadicCube and its
descendant-family variant. These are the outputs consumed by the Chapter-3
coarse Poincare wrappers.
-/

@[expose] public section

namespace Homogenization


/--
Adjoint-free deterministic ordering `σ_*(U; a) ≤ σ(U; a)` on the centered
open cube, packaged directly from deterministic recovery-plus-ellipticity
data.
-/
theorem sigmaStarCoarse_le_sigmaCoarse_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa)
    (p : Vec d) :
    vecDot p (matVecMul (sigmaStarCoarse (openCubeSet (originCube d n)) a) p) ≤
      vecDot p (matVecMul (sigmaCoarse (openCubeSet (originCube d n)) a) p) := by
  rcases hData with ⟨hEll, hCompat⟩
  exact
    sigmaStarCoarse_le_sigmaCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))
      hEll (volume_openCubeSet_originCube_toReal_pos (d := d) n)
      hCompat hA hS hK hSigma p

/--
Deterministic ordering `σ(U; a) ≤ b(U; a)` on the centered open cube,
packaged directly from deterministic recovery-plus-ellipticity data.
-/
theorem sigmaCoarse_le_bCoarse_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa) :
    MatLoewnerLE
      (sigmaCoarse (openCubeSet (originCube d n)) a)
      (bCoarse
        (sigmaCoarse (openCubeSet (originCube d n)) a)
        (sigmaStarCoarse (openCubeSet (originCube d n)) a)
        (kappaCoarse (openCubeSet (originCube d n)) a)) := by
  rcases hData with ⟨hEll, hCompat⟩
  exact
    sigmaCoarse_le_bCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))
      hEll (volume_openCubeSet_originCube_toReal_pos (d := d) n)
      hCompat hS hK hSigma

/--
Deterministic upper bound
`b(U; a) ≤ average(symmPart(a) + k(a)ᵀ symmPart(a)⁻¹ k(a))`
on the centered open cube, packaged directly from deterministic
recovery-plus-ellipticity data.
-/
theorem bCoarse_le_averaged_symmPart_plus_correction_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa)
    (p : Vec d) :
    vecDot p
        (matVecMul
          (bCoarse
            (sigmaCoarse (openCubeSet (originCube d n)) a)
            (sigmaStarCoarse (openCubeSet (originCube d n)) a)
            (kappaCoarse (openCubeSet (originCube d n)) a)) p) ≤
      volumeAverage (openCubeSet (originCube d n))
        (fun x =>
          vecDot p
            (matVecMul
              (symmPart (a x) +
                matTranspose (skewPart (a x)) * (symmPart (a x))⁻¹ * skewPart (a x)) p)) := by
  rcases hData with ⟨hEll, hCompat⟩
  exact
    bCoarse_le_averaged_symmPart_plus_correction_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))
      hEll (volume_openCubeSet_originCube_toReal_pos (d := d) n)
      hCompat hA hS hK hSigma p

/--
Deterministic upper-left matrix-order bound
`b(U; a) ≤ average(symmPart(a) + k(a)ᵀ symmPart(a)⁻¹ k(a))`
on the centered open cube, packaged directly from deterministic
recovery-plus-ellipticity data.
-/
theorem bCoarse_le_averagedSymmPartPlusCorrection_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa) :
    MatLoewnerLE
      (bCoarse
        (sigmaCoarse (openCubeSet (originCube d n)) a)
        (sigmaStarCoarse (openCubeSet (originCube d n)) a)
        (kappaCoarse (openCubeSet (originCube d n)) a))
      (averagedSymmPartPlusCorrection (openCubeSet (originCube d n)) a) := by
  rcases hData with ⟨hEll, hCompat⟩
  exact
    bCoarse_le_averagedSymmPartPlusCorrection_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))
      hEll (volume_openCubeSet_originCube_toReal_pos (d := d) n)
      hCompat hA hS hK hSigma

/--
Deterministic inverse-side harmonic-mean upper bound
`σ_*^{-1}(U; a) ≤ average(symmPart(a)⁻¹)`
on the centered open cube, packaged directly from deterministic
recovery-plus-ellipticity data.
-/
theorem sigmaStarInvCoarse_le_averaged_symmPart_inv_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (q : Vec d) :
    vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet (originCube d n)) a) q) ≤
      volumeAverage (openCubeSet (originCube d n))
        (fun x => vecDot q (matVecMul ((symmPart (a x))⁻¹) q)) := by
  rcases hData with ⟨hEll, hCompat⟩
  exact
    sigmaStarInvCoarse_le_averaged_symmPart_inv_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))
      hEll (volume_openCubeSet_originCube_toReal_pos (d := d) n)
      hCompat q

/--
Deterministic inverse-side harmonic-mean matrix bound
`σ_*^{-1}(U; a) ≤ average(symmPart(a)^{-1})`
on the centered open cube, packaged directly from deterministic
recovery-plus-ellipticity data.
-/
theorem sigmaStarInvCoarse_le_averagedSymmPartInv_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a) :
    MatLoewnerLE
      (sigmaStarInvCoarse (openCubeSet (originCube d n)) a)
      (averagedSymmPartInv (openCubeSet (originCube d n)) a) := by
  rcases hData with ⟨hEll, hCompat⟩
  exact
    sigmaStarInvCoarse_le_averagedSymmPartInv_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))
      hEll (volume_openCubeSet_originCube_toReal_pos (d := d) n) hCompat

/--
Deterministic harmonic-mean lower bound
`(average(symmPart(a)^{-1}))^{-1} ≤ σ_*(U; a)` on the centered open cube,
packaged directly from deterministic recovery-plus-ellipticity data.
-/
theorem harmonicMeanSymmPart_le_sigmaStarCoarse_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a) :
    MatLoewnerLE
      ((averagedSymmPartInv (openCubeSet (originCube d n)) a)⁻¹)
      (sigmaStarCoarse (openCubeSet (originCube d n)) a) := by
  rcases hData with ⟨hEll, hCompat⟩
  exact
    harmonicMeanSymmPart_le_sigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d n)) (a := a) R
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))
      hEll (volume_openCubeSet_originCube_toReal_pos (d := d) n) hCompat

/--
Minimal one-cube deterministic coarse-data constructor from translated
origin-cube recovery data.

This is the exact upstream theorem needed to start removing the remaining
`OpenCubeDescendantDeterministicCoarseData` burden from the note-facing Chapter
3 coarse Poincare wrappers.
-/
theorem openCubeDeterministicCoarseData_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hRec :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a)) :
    OpenCubeDeterministicCoarseData Q a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  let U0 : Set (Vec d) := openCubeSet (originCube d Q.scale)
  let a0 : CoeffField d := translateCoeffField z a
  let : Fact (MeasureTheory.volume U0 < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) Q.scale⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U0) := by
    simpa [volumeMeasureOn, U0] using
      (isOpenBoundedConvexDomain_openCubeSet (originCube d Q.scale)).isFiniteMeasure_restrict_volume
  have hEll : IsEllipticFieldOn lam Lam U0 a0 := Classical.choose hRec
  let system : MuOperatorSystemData U0 a0 :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) Q.scale)
  have hCompat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData
        (a := a0) R system := by
    simpa [U0, a0, system] using Classical.choose_spec hRec
  have hex0 :
      ∃ Abar : BlockMat d, IsCoarseBlockMatrix U0 a0 Abar := by
    simpa [U0, a0] using
      exists_coarseBlockMatrix_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
        (R := R) (a := a0) hRec
  have hA0coarse : IsCoarseBlockMatrix U0 a0 (coarseBlockMatrix U0 a0) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex0
  have hMuRespQ0 :
      ∀ q : Vec d, Mu U0 (0, q) a0 = ResponseJ U0 0 q a0 := by
    intro q
    simpa [U0, a0] using
      mu_zero_right_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
        (R := R) (a := a0) hRec q
  have hMuRespP0 :
      ∀ p : Vec d, Mu U0 (p, 0) a0 = ResponseJ U0 p 0 a0 := by
    intro p
    simpa [U0, a0] using
      mu_left_zero_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
        (R := R) (a := a0) hRec p
  have hResp0 :
      ∀ p q : Vec d,
        ResponseJ U0 p q a0 = Mu U0 (-p, q) a0 - vecDot p q := by
    intro p q
    simpa [U0, a0] using
      responseJ_eq_mu_neg_left_sub_vecDot_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
        (R := R) (a := a0) hRec p q
  have hSInvLower :
      IsSigmaStarInvCoarse U0 a0 (coarseBlockMatrix U0 a0).lowerRight := by
    exact
      isSigmaStarInvCoarse_coarseBlockMatrix_lowerRight_of_mu_zero_right_eq_responseJ_zero
        (U := U0) (a := a0) hex0 hMuRespQ0
  have hSInv0 : IsSigmaStarInvCoarse U0 a0 (sigmaStarInvCoarse U0 a0) := by
    exact isSigmaStarInvCoarse_sigmaStarInvCoarse
      ⟨(coarseBlockMatrix U0 a0).lowerRight, hSInvLower⟩
  have hMlower :
      IsSigmaStarInvKappaCoarse U0 a0 (-(coarseBlockMatrix U0 a0).lowerLeft) := by
    exact
      isSigmaStarInvKappaCoarse_neg_coarseBlockMatrix_lowerLeft_of_exact_slices
        (U := U0) (a := a0) hex0 hMuRespQ0 hMuRespP0 hResp0
  have hM0 : IsSigmaStarInvKappaCoarse U0 a0 (sigmaStarInvKappaCoarse U0 a0) := by
    exact isSigmaStarInvKappaCoarse_sigmaStarInvKappaCoarse
      ⟨-(coarseBlockMatrix U0 a0).lowerLeft, hMlower⟩
  have hdetInv0 : IsUnit (sigmaStarInvCoarse U0 a0).det := by
    have hzeroMem : (0 : Vec d) ∈ U0 := by
      have hpow : 0 < (3 : ℝ) ^ Q.scale := by
        positivity
      change (0 : Vec d) ∈ openCubeSet (originCube d Q.scale)
      rw [mem_openCubeSet_originCube_iff]
      intro i
      have hhalfpow : 0 < (1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale := by
        positivity
      constructor
      · have hneg : -((1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale) < 0 := by
          linarith
        simpa [neg_mul] using hneg
      · simpa using hhalfpow
    have hlam_pos : 0 < lam := (hEll.2 0 hzeroMem).1
    have hden_pos : 0 < 1 + 2 * Lam ^ 2 := by
      nlinarith [sq_nonneg Lam]
    have hcoeff_pos : 0 < lam / (1 + 2 * Lam ^ 2) := by
      exact div_pos hlam_pos hden_pos
    have hcoeff_half_pos : 0 < lam / (2 * (1 + 2 * Lam ^ 2)) := by
      have hden2_pos : 0 < 2 * (1 + 2 * Lam ^ 2) := by
        positivity
      exact div_pos hlam_pos hden2_pos
    have hcoeff_half_nonneg : 0 ≤ lam / (2 * (1 + 2 * Lam ^ 2)) := by
      positivity
    have hquad_pos :
        ∀ q : Vec d, q ≠ 0 → 0 < vecDot q (matVecMul (sigmaStarInvCoarse U0 a0) q) := by
      intro q hq
      let Xq : BlockState d := (R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q)
      have hAdm : IsBlockMuAdmissible U0 (0, q) Xq := by
        simpa [U0, system, Xq] using
          (R.toMuCorrectionSpaceRecoveryData).recoveredField_admissible system (0, q)
      have hFluxDiff : MemVectorL2 U0 (fun x => Xq.flux x - q) :=
        hAdm.fluxCorrection_memL2
      have hFlux : MemVectorL2 U0 Xq.flux := by
        have hconst : MemVectorL2 U0 (fun _ : Vec d => q) :=
          MeasureTheory.memLp_const (μ := volumeMeasureOn U0) (p := (2 : ENNReal)) (c := q)
        have hsum :
            MemVectorL2 U0 ((fun x => Xq.flux x - q) + fun _ : Vec d => q) :=
          hFluxDiff.add hconst
        have hEq :
            ((fun x => Xq.flux x - q) + fun _ : Vec d => q) = Xq.flux := by
          funext x
          simp [Xq, sub_eq_add_neg, add_comm]
        rw [hEq] at hsum
        exact hsum
      have hFluxSqInt : MeasureTheory.IntegrableOn (fun x => vecNormSq (Xq.flux x)) U0 := by
        simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hFlux hFlux
      have hEnergyInt :
          MeasureTheory.IntegrableOn (blockEnergyDensity a0 Xq) U0 := by
        exact blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn
          ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system (0, q)) hEll
      have hFluxAvg :
          (fun i => volumeAverage U0 (fun x => Xq.flux x i)) = q := by
        simpa [U0, Xq] using
          congrArg Prod.snd
            ((R.toMuCorrectionSpaceRecoveryData).recoveredField_average_state_openCubeSet_originCube
              system (0, q))
      have hJensen :
          vecNormSq q ≤ volumeAverage U0 (fun x => vecNormSq (Xq.flux x)) := by
        have hraw :=
          vecNormSq_volumeAverage_le_volumeAverage_vecNormSq
            (U := U0)
            (hU := measurableSet_openCubeSet (originCube d Q.scale))
            (hvol := (volume_openCubeSet_originCube_toReal_pos (d := d) Q.scale).ne')
            hFlux
        rw [hFluxAvg] at hraw
        exact hraw
      have hpoint :
          ∀ x ∈ U0,
            (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq (Xq.flux x) ≤
              blockEnergyDensity a0 Xq x := by
        intro x hx
        have hcoer :=
          blockMatrixOfCoeff_coercive_of_isEllipticMatrix (hEll.2 x hx) (Xq.eval x)
        have hcoeff_nonneg : 0 ≤ lam / (1 + 2 * Lam ^ 2) := by
          positivity
        have hflux_le_block :
            vecNormSq (Xq.flux x) ≤ blockVecDot (Xq.eval x) (Xq.eval x) := by
          change vecNormSq (Xq.flux x) ≤
            vecNormSq (Xq.potential x) + vecNormSq (Xq.flux x)
          exact le_add_of_nonneg_left (vecNormSq_nonneg (Xq.potential x))
        have hflux_scaled :
            (lam / (1 + 2 * Lam ^ 2)) * vecNormSq (Xq.flux x) ≤
              (lam / (1 + 2 * Lam ^ 2)) * blockVecDot (Xq.eval x) (Xq.eval x) := by
          exact mul_le_mul_of_nonneg_left hflux_le_block hcoeff_nonneg
        have hcoer' :
            (lam / (1 + 2 * Lam ^ 2)) * blockVecDot (Xq.eval x) (Xq.eval x) ≤
              2 * blockEnergyDensity a0 Xq x := by
          simpa [blockEnergyDensity, Xq] using! hcoer
        have hchain :
            (lam / (1 + 2 * Lam ^ 2)) * vecNormSq (Xq.flux x) ≤
              2 * blockEnergyDensity a0 Xq x := le_trans hflux_scaled hcoer'
        have hhalf :=
          mul_le_mul_of_nonneg_left hchain (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        have hleft :
            (1 / 2 : ℝ) * ((lam / (1 + 2 * Lam ^ 2)) * vecNormSq (Xq.flux x)) =
              (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq (Xq.flux x) := by
          field_simp [hden_pos.ne']
        have hright :
            (1 / 2 : ℝ) * (2 * blockEnergyDensity a0 Xq x) = blockEnergyDensity a0 Xq x := by
          ring
        rw [hleft, hright] at hhalf
        exact hhalf
      have hEnergyLower :
          (lam / (2 * (1 + 2 * Lam ^ 2))) *
              volumeAverage U0 (fun x => vecNormSq (Xq.flux x)) ≤
            blockEnergyAverage U0 a0 Xq := by
        calc
          (lam / (2 * (1 + 2 * Lam ^ 2))) *
              volumeAverage U0 (fun x => vecNormSq (Xq.flux x))
              =
            volumeAverage U0 (fun x =>
              (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq (Xq.flux x)) := by
                symm
                simpa [smul_eq_mul] using!
                  (volumeAverage_smul U0 (lam / (2 * (1 + 2 * Lam ^ 2)))
                    (fun x => vecNormSq (Xq.flux x)))
          _ ≤ volumeAverage U0 (blockEnergyDensity a0 Xq) := by
            exact volumeAverage_le_volumeAverage_of_le_on
              (U := U0)
              (hU := measurableSet_openCubeSet (originCube d Q.scale))
              (hf := by
                simpa [smul_eq_mul] using!
                  hFluxSqInt.smul (lam / (2 * (1 + 2 * Lam ^ 2))))
              (hg := hEnergyInt)
              hpoint
          _ = blockEnergyAverage U0 a0 Xq := rfl
      have hEnergyRec :
          blockEnergyAverage U0 a0 Xq = Mu U0 (0, q) a0 := by
        simpa [U0, system, Xq] using
          (R.toMuCorrectionSpaceRecoveryData).recoveredField_blockEnergyAverage_eq_mu
            system hCompat.mu_eq_muCandidate (0, q)
      have hMain :
          (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq q ≤
            (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U0 a0) q) := by
        have hscaledJensen :
            (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq q ≤
              (lam / (2 * (1 + 2 * Lam ^ 2))) *
                volumeAverage U0 (fun x => vecNormSq (Xq.flux x)) := by
          exact mul_le_mul_of_nonneg_left hJensen hcoeff_half_nonneg
        calc
          (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq q
              ≤
            (lam / (2 * (1 + 2 * Lam ^ 2))) *
              volumeAverage U0 (fun x => vecNormSq (Xq.flux x)) := hscaledJensen
          _ ≤ blockEnergyAverage U0 a0 Xq := hEnergyLower
          _ = Mu U0 (0, q) a0 := hEnergyRec
          _ = ResponseJ U0 0 q a0 := hMuRespQ0 q
          _ = (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U0 a0) q) := hSInv0.2 q
      have hqnorm_ne : vecNormSq q ≠ 0 := by
        intro hqnorm
        exact hq (vecNormSq_eq_zero hqnorm)
      have hqnorm_pos : 0 < vecNormSq q := by
        exact lt_of_le_of_ne (vecNormSq_nonneg q) (by simpa [eq_comm] using hqnorm_ne)
      have hhalf_pos :
          0 < (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U0 a0) q) :=
        lt_of_lt_of_le (mul_pos hcoeff_half_pos hqnorm_pos) hMain
      nlinarith
    have hPosDef : (sigmaStarInvCoarse U0 a0).PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
      · simpa [Matrix.IsHermitian, Matrix.IsSymm] using hSInv0.1
      · intro q hq
        simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hquad_pos q hq
    exact (Matrix.isUnit_iff_isUnit_det (A := sigmaStarInvCoarse U0 a0)).mp hPosDef.isUnit
  have hS0 : IsSigmaStarCoarse U0 a0 (sigmaStarCoarse U0 a0) := by
    exact isSigmaStarCoarse_sigmaStarCoarse_of_isSigmaStarInvCoarse hSInv0 hdetInv0
  have hK0 :
      IsKappaCoarse U0 a0 (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0) := by
    exact
      isKappaCoarse_kappaCoarse_of_isSigmaStarInvKappaCoarse_of_isUnit_det_sigmaStarInvCoarse
        hM0 hdetInv0
  let sigma0 : Mat d :=
    (coarseBlockMatrix U0 a0).upperLeft -
      (matTranspose (kappaCoarse U0 a0)) * sigmaStarInvCoarse U0 a0 * kappaCoarse U0 a0
  have hSigma0 :
      IsSigmaCoarse U0 a0 sigma0 (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0) := by
    refine ⟨?_, ?_⟩
    · have hUpperSymm : ((coarseBlockMatrix U0 a0).upperLeft).IsSymm := by
        rw [Matrix.IsSymm.ext_iff]
        intro i j
        simpa [blockMatEntry] using (hA0coarse.1 (Sum.inl i) (Sum.inl j)).symm
      have hCorrSymm :
          (((matTranspose (kappaCoarse U0 a0)) * sigmaStarInvCoarse U0 a0 *
              kappaCoarse U0 a0)).IsSymm :=
        transpose_mul_symm_mul_isSymm (kappaCoarse U0 a0) (sigmaStarInvCoarse U0 a0) hSInv0.1
      rw [Matrix.IsSymm.ext_iff]
      intro i j
      simp [sigma0, hUpperSymm.apply i j, hCorrSymm.apply i j]
    · intro p
      have hRespP :
          ResponseJ U0 p 0 a0 =
            (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U0 a0).upperLeft p) := by
        calc
          ResponseJ U0 p 0 a0 = Mu U0 (p, 0) a0 := (hMuRespP0 p).symm
          _ =
            (1 / 2 : ℝ) * blockVecDot (p, 0)
              (blockMatVecMul (coarseBlockMatrix U0 a0) (p, 0)) := by
                simpa using hA0coarse.2 (p, 0)
          _ =
            (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U0 a0).upperLeft p) := by
                simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left]
      have hInvEq : (sigmaStarCoarse U0 a0)⁻¹ = sigmaStarInvCoarse U0 a0 := by
        rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS0]
      rw [hRespP, hInvEq]
      simp [sigma0, sub_eq_add_neg, add_matVecMul, neg_matVecMul, vecDot_add_right,
        vecDot_neg_right, matVecMul_mul, Matrix.mul_assoc]
      ring_nf
  have hdet0 : IsUnit (sigmaStarCoarse U0 a0).det := by
    unfold sigmaStarCoarse
    exact Matrix.isUnit_nonsing_inv_det (A := sigmaStarInvCoarse U0 a0) hdetInv0
  have hLower0 :
      (coarseBlockMatrix U0 a0).lowerLeft =
        -((sigmaStarCoarse U0 a0)⁻¹ * kappaCoarse U0 a0) := by
    calc
      (coarseBlockMatrix U0 a0).lowerLeft = -(sigmaStarInvKappaCoarse U0 a0) := by
        have hEq :
            -(coarseBlockMatrix U0 a0).lowerLeft = sigmaStarInvKappaCoarse U0 a0 :=
          eq_sigmaStarInvKappaCoarse_of_isSigmaStarInvKappaCoarse hMlower
        simpa using congrArg Neg.neg hEq
      _ = -((sigmaStarCoarse U0 a0)⁻¹ * kappaCoarse U0 a0) := by
        rw [sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse hK0]
  have hUpper0 :
      (coarseBlockMatrix U0 a0).upperRight =
        -((matTranspose (kappaCoarse U0 a0)) * (sigmaStarCoarse U0 a0)⁻¹) := by
    have hUpperSymm :
        (coarseBlockMatrix U0 a0).upperRight =
          matTranspose (coarseBlockMatrix U0 a0).lowerLeft := by
      ext i j
      simpa [blockMatEntry, matTranspose] using hA0coarse.1 (Sum.inl i) (Sum.inr j)
    calc
      (coarseBlockMatrix U0 a0).upperRight =
          matTranspose (coarseBlockMatrix U0 a0).lowerLeft := hUpperSymm
      _ = matTranspose (-((sigmaStarCoarse U0 a0)⁻¹ * kappaCoarse U0 a0)) := by
            rw [hLower0]
      _ = -((matTranspose (kappaCoarse U0 a0)) * (sigmaStarCoarse U0 a0)⁻¹) := by
            change Matrix.transpose (-((sigmaStarCoarse U0 a0)⁻¹ * kappaCoarse U0 a0)) =
              -((matTranspose (kappaCoarse U0 a0)) * (sigmaStarCoarse U0 a0)⁻¹)
            rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
            rw [show Matrix.transpose (sigmaStarCoarse U0 a0) = sigmaStarCoarse U0 a0 by
                  simpa [matTranspose] using hS0.1.eq]
            simp [matTranspose]
  have hLowerRight0 :
      (coarseBlockMatrix U0 a0).lowerRight = sigmaStarInvCoarse U0 a0 := by
    exact
      coarseBlockMatrix_lowerRight_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero
        (U := U0) (a := a0) hex0 hMuRespQ0
  have hBlockEq0 :
      blockMatrixOfDeterministicData sigma0 (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0) =
        coarseBlockMatrix U0 a0 := by
    refine blockMat_ext ?_ ?_ ?_ ?_
    · simp [blockMatrixOfDeterministicData, bCoarse, sigma0,
        sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS0]
    · simpa [blockMatrixOfDeterministicData] using hUpper0.symm
    · simpa [blockMatrixOfDeterministicData] using hLower0.symm
    · calc
        (sigmaStarCoarse U0 a0)⁻¹ = sigmaStarInvCoarse U0 a0 := by
          rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS0]
        _ = (coarseBlockMatrix U0 a0).lowerRight := hLowerRight0.symm
  have hAblock0 :
      IsCoarseBlockMatrix U0 a0
        (blockMatrixOfDeterministicData sigma0 (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0)) := by
    rw [hBlockEq0]
    exact hA0coarse
  have hSQ :
      IsSigmaStarCoarse (openCubeSet Q) a (sigmaStarCoarse U0 a0) := by
    have htrans :=
      (isSigmaStarCoarse_translateSet_iff z U0 a (sigmaStarCoarse U0 a0)).2 hS0
    simpa [z, U0, a0, openCubeSet_eq_translateSet_originCube_of_triadicCube Q] using! htrans
  have hKQ :
      IsKappaCoarse (openCubeSet Q) a (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0) := by
    have htrans :=
      (isKappaCoarse_translateSet_iff z U0 a (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0)).2 hK0
    simpa [z, U0, a0, openCubeSet_eq_translateSet_originCube_of_triadicCube Q] using! htrans
  have hSigmaQ :
      IsSigmaCoarse (openCubeSet Q) a sigma0 (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0) := by
    have htrans :=
      (isSigmaCoarse_translateSet_iff z U0 a sigma0
        (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0)).2 hSigma0
    simpa [z, U0, a0, openCubeSet_eq_translateSet_originCube_of_triadicCube Q] using! htrans
  have hAblockQ :
      IsCoarseBlockMatrix (openCubeSet Q) a
        (blockMatrixOfDeterministicData sigma0 (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0)) := by
    have htrans :=
      (isCoarseBlockMatrix_translateSet_iff z U0 a
        (blockMatrixOfDeterministicData sigma0 (sigmaStarCoarse U0 a0) (kappaCoarse U0 a0))).2
        hAblock0
    simpa [z, U0, a0, openCubeSet_eq_translateSet_originCube_of_triadicCube Q] using! htrans
  have hAQ :
      IsCoarseBlockMatrix (openCubeSet Q) a
        (deterministicCoarseBlockMatrix (openCubeSet Q) a) := by
    rw [deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hSQ hKQ hSigmaQ hdet0]
    exact hAblockQ
  exact
    ⟨sigma0, sigmaStarCoarse U0 a0, kappaCoarse U0 a0,
      hAQ, hSQ, hKQ, hSigmaQ, hdet0⟩

/--
If the coefficient field is self-adjoint, then the canonical coarse
`\kappa(openCubeSet Q; a)` vanishes on any triadic open cube once translated
origin-cube elliptic recovery data is available.
-/
theorem kappaCoarse_eq_zero_openCubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData_of_adjointCoeffField_eq
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d Q.scale)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hRec :
      HasOpenCubeEllipticRecoveryData (d := d) Q.scale R
        (lam := lam) (Lam := Lam)
        (translateCoeffField (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) a))
    (hAdj : adjointCoeffField a = a) :
    kappaCoarse (openCubeSet Q) a = 0 := by
  rcases
      openCubeDeterministicCoarseData_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
        Q R hRec with
    ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact
    kappaCoarse_eq_zero_of_adjointCoeffField_eq_of_isCoarseBlockMatrix
      (U := openCubeSet Q) (a := a) hA hAdj

/--
Descendant deterministic coarse data from a descendant family of translated
origin-cube recovery witnesses.

This is the packaged upstream theorem that would directly discharge the last
honest Chapter-2 burden still visible in the top harmonic Chapter-3
coarse-Poincare wrappers.
-/
theorem openCubeDescendantDeterministicCoarseData_of_recoveryFamily
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    OpenCubeDescendantDeterministicCoarseData Q a := by
  intro l hl R hR
  rcases hRec l hl R hR with ⟨RR, hRR⟩
  exact openCubeDeterministicCoarseData_of_triadicCube_of_hasOpenCubeEllipticRecoveryData
    (Q := R) RR hRR

end Homogenization
