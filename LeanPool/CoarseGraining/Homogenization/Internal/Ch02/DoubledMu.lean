/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledMuDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.GradientUniqueness
public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.PotentialSolenoidal
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.RecoveryPackages
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixExtraction
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.DoubledResponse.ScalarMaximizers
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives

/-! # Doubled Mu -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem potentialZeroTraceFieldOn_of_isPotentialZeroTraceOn {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn U f) :
    Book.Ch01.PotentialZeroTraceFieldOn U f := by
  rcases hf with ⟨φ, rfl⟩
  exact Book.Ch01.potentialZeroTraceFieldOn_of_h10 φ

private theorem isBlockMuAdmissible_of_isDoubledMuAdmissible {d : ℕ}
    {U : Domain d} {P : BlockVec d} {X : DoubledField d}
    (hX : IsDoubledMuAdmissible U P X) :
    IsBlockMuAdmissible (U : Set (Vec d)) P (blockStateOfDoubled X) := by
  refine ⟨hX.1.1, ?_, hX.2.1, hX.2.2⟩
  exact isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn hX.1

private theorem isDoubledMuAdmissible_of_isBlockMuAdmissible {d : ℕ}
    {U : Domain d} {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible (U : Set (Vec d)) P X) :
    IsDoubledMuAdmissible U P (doubledFieldOfBlockState X) := by
  refine ⟨?_, ?_⟩
  · exact potentialZeroTraceFieldOn_of_isPotentialZeroTraceOn hX.isPotentialZeroTrace
  · exact ⟨hX.fluxCorrection_memL2, hX.isSolenoidalZeroNormalTrace⟩

private theorem book_doubledMuValue_eq_blockEnergyAverage {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (X : DoubledField d) :
    doubledMuValue U a X =
      blockEnergyAverage (U : Set (Vec d)) a.toCoeffField (blockStateOfDoubled X) := by
  rfl

private theorem book_doubledMuValue_ofBlockState_eq_blockEnergyAverage {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (X : BlockState d) :
    doubledMuValue U a (doubledFieldOfBlockState X) =
      blockEnergyAverage (U : Set (Vec d)) a.toCoeffField X := by
  rfl

private theorem book_doubledBlockPairingIntegrand_eq_blockPairingIntegrand {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (Y X : DoubledField d) :
    doubledBlockPairingIntegrand U a Y X =
      blockPairingIntegrand a.toCoeffField (blockStateOfDoubled Y) (blockStateOfDoubled X) := by
  rfl

private theorem book_doubledMuValueSet_eq_muValueSet {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (P : BlockVec d) :
    doubledMuValueSet U a P =
      muValueSet (U : Set (Vec d)) P a.toCoeffField := by
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨blockStateOfDoubled X, isBlockMuAdmissible_of_isDoubledMuAdmissible hX, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨doubledFieldOfBlockState X, isDoubledMuAdmissible_of_isBlockMuAdmissible hX, rfl⟩

theorem book_doubledMu_eq_Mu {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (P : BlockVec d) :
    doubledMu U a P = Mu (U : Set (Vec d)) P a.toCoeffField := by
  unfold doubledMu Mu
  rw [book_doubledMuValueSet_eq_muValueSet U a P]

private theorem muValueSet_bddBelow_of_isEllipticFieldOn_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) (P : BlockVec d) :
    BddBelow (muValueSet U P a) := by
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
          (IsSolenoidalZeroNormalTraceOn.integral_eq_zero hU
            hX.isSolenoidalZeroNormalTrace))
      hvol

/-- Internal bridge identifying the public coarse block matrix with the old
coarse-block matrix once the old deterministic coarse data have been produced. -/
theorem book_coarseBlockMatrix_eq_old_coarseBlockMatrix_of_data {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    {sigma sigmaStar kappa : Mat d}
    (hA :
      IsCoarseBlockMatrix (U : Set (Vec d)) a.toCoeffField
        (deterministicCoarseBlockMatrix (U : Set (Vec d)) a.toCoeffField))
    (hS : IsSigmaStarCoarse (U : Set (Vec d)) a.toCoeffField sigmaStar)
    (hK : IsKappaCoarse (U : Set (Vec d)) a.toCoeffField sigmaStar kappa)
    (hSigma : IsSigmaCoarse (U : Set (Vec d)) a.toCoeffField sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    Book.Ch02.coarseBlockMatrix U a =
      Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField := by
  have hSigmaStarEq :
      Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField = sigmaStar :=
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet
  have hKappaEq :
      Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField = kappa :=
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet
  have hSigmaEq :
      Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField = sigma :=
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet
  have hSCanon :
      IsSigmaStarCoarse (U : Set (Vec d)) a.toCoeffField
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) := by
    simpa [hSigmaStarEq] using hS
  have hKCanon :
      IsKappaCoarse (U : Set (Vec d)) a.toCoeffField
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) := by
    simpa [hSigmaStarEq, hKappaEq] using hK
  have hSigmaCanon :
      IsSigmaCoarse (U : Set (Vec d)) a.toCoeffField
        (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) := by
    simpa [hSigmaEq, hSigmaStarEq, hKappaEq] using hSigma
  have hdetCanon :
      IsUnit
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).det := by
    simpa [hSigmaStarEq] using hdet
  have hBook :
      Book.Ch02.coarseBlockMatrix U a =
        blockMatrixOfDeterministicData
          (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
          (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
          (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) := by
    refine blockMat_ext ?_ ?_ ?_ ?_
    · simpa [Book.Ch02.coarseBlockMatrix, Book.Ch02.blockMatrixOfCoarseMatrices,
        blockMatrixOfDeterministicData] using
        book_coarseMatrices_b_eq_bCoarse_of_isSigmaStarCoarse U a hSCanon
    · simp [Book.Ch02.coarseBlockMatrix, Book.Ch02.blockMatrixOfCoarseMatrices,
        blockMatrixOfDeterministicData,
        book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a,
        book_kappaCoarse_eq_kappaCoarse U a,
        sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hSCanon]
    · simp [Book.Ch02.coarseBlockMatrix, Book.Ch02.blockMatrixOfCoarseMatrices,
        blockMatrixOfDeterministicData,
        book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a,
        book_kappaCoarse_eq_kappaCoarse U a,
        sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hSCanon]
    · simp [Book.Ch02.coarseBlockMatrix, Book.Ch02.blockMatrixOfCoarseMatrices,
        blockMatrixOfDeterministicData,
        book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a,
        sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hSCanon]
  calc
    Book.Ch02.coarseBlockMatrix U a =
        blockMatrixOfDeterministicData
          (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
          (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
          (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) := hBook
    _ = deterministicCoarseBlockMatrix (U : Set (Vec d)) a.toCoeffField := by
        exact
          (deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
            (U := (U : Set (Vec d))) (a := a.toCoeffField)
            hSCanon hKCanon hSigmaCanon hdetCanon).symm
    _ = Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField :=
        eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA

private theorem isDoubledMuMinimizer_recoveredField {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal)
    (R : PotentialSolenoidalL2RecoveryData (U : Set (Vec d)))
    (system : MuOperatorSystemData (U : Set (Vec d)) a.toCoeffField)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData
        (a := a.toCoeffField) R system)
    (P : BlockVec d) :
    IsDoubledMuMinimizer U a P
      (doubledFieldOfBlockState
        ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P)) := by
  let Rc := R.toMuCorrectionSpaceRecoveryData
  let Xrec : BlockState d := Rc.recoveredField system P
  have hAdmOld : IsBlockMuAdmissible (U : Set (Vec d)) P Xrec := by
    simpa [Rc, Xrec] using Rc.recoveredField_admissible system P
  refine ⟨isDoubledMuAdmissible_of_isBlockMuAdmissible hAdmOld, ?_⟩
  intro Y hY
  have hYOld :
      IsBlockMuAdmissible (U : Set (Vec d)) P (blockStateOfDoubled Y) :=
    isBlockMuAdmissible_of_isDoubledMuAdmissible hY
  have hBdd :
      BddBelow (muValueSet (U : Set (Vec d)) P a.toCoeffField) :=
    muValueSet_bddBelow_of_isEllipticFieldOn_of_isSobolevRegularDomain
      U.isDomain.isSobolevRegularDomain hEll hvol.ne' P
  have hMuLeY :
      Mu (U : Set (Vec d)) P a.toCoeffField ≤
        blockEnergyAverage (U : Set (Vec d)) a.toCoeffField (blockStateOfDoubled Y) :=
    csInf_le hBdd (muValueSet_mem hYOld)
  have hRecEnergy :
      blockEnergyAverage (U : Set (Vec d)) a.toCoeffField Xrec =
        Mu (U : Set (Vec d)) P a.toCoeffField := by
    simpa [Rc, Xrec] using
      Rc.recoveredField_blockEnergyAverage_eq_mu system compat.mu_eq_muCandidate P
  calc
    doubledMuValue U a (doubledFieldOfBlockState Xrec) =
        blockEnergyAverage (U : Set (Vec d)) a.toCoeffField Xrec :=
      book_doubledMuValue_ofBlockState_eq_blockEnergyAverage U a Xrec
    _ = Mu (U : Set (Vec d)) P a.toCoeffField := hRecEnergy
    _ ≤ blockEnergyAverage (U : Set (Vec d)) a.toCoeffField (blockStateOfDoubled Y) :=
      hMuLeY
    _ = doubledMuValue U a Y :=
      (book_doubledMuValue_eq_blockEnergyAverage U a Y).symm

private theorem hilbert_eq_minimizerMap_of_isDoubledMuMinimizer {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (R : PotentialSolenoidalL2RecoveryData (U : Set (Vec d)))
    (system : MuOperatorSystemData (U : Set (Vec d)) a.toCoeffField)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData
        (a := a.toCoeffField) R system)
    (P : BlockVec d) {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a P X) :
    toHilbertBlockL2OfBlockField
      (isBlockMuAdmissible_of_isDoubledMuAdmissible hX.1).memBlockL2_eval =
        (R.toMuHilbertRealization system).minimizerMap P := by
  let Xold : BlockState d := blockStateOfDoubled X
  let hXOld : IsBlockMuAdmissible (U : Set (Vec d)) P Xold :=
    isBlockMuAdmissible_of_isDoubledMuAdmissible hX.1
  let HX : HilbertBlockL2 (U : Set (Vec d)) :=
    toHilbertBlockL2OfBlockField hXOld.memBlockL2_eval
  let H : MuHilbertRealization (U : Set (Vec d)) a.toCoeffField :=
    R.toMuHilbertRealization system
  have hcorr :
      HX - H.constantField P ∈ H.correctionSpace.correctionSpace := by
    let Y : CorrectionFieldData (U : Set (Vec d)) :=
      hXOld.toCorrectionFieldDataOfAdmissible
    have hYmem :
        Y.toHilbertBlockL2 ∈
          R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.correctionSpace := by
      exact
        R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.mem_correctionSpace
          Y.potential_memL2 Y.flux_memL2
          Y.isPotentialZeroTrace Y.isSolenoidalZeroNormalTrace
    have hsplit :
        HX =
          blockVecToHilbertBlockL2Const (U := (U : Set (Vec d))) P +
            Y.toHilbertBlockL2 := by
      simpa [HX, Y] using
        hXOld.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    rw [hsplit]
    change
      blockVecToHilbertBlockL2Const (U := (U : Set (Vec d))) P +
          Y.toHilbertBlockL2 -
            blockVecToHilbertBlockL2Const (U := (U : Set (Vec d))) P ∈
        R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.correctionSpace
    convert hYmem using 1
    abel
  let Rc := R.toMuCorrectionSpaceRecoveryData
  let Xrec : BlockState d := Rc.recoveredField system P
  have hRecAdmOld : IsBlockMuAdmissible (U : Set (Vec d)) P Xrec := by
    simpa [Rc, Xrec] using Rc.recoveredField_admissible system P
  have hMinLeRec :
      doubledMuValue U a X ≤
        doubledMuValue U a (doubledFieldOfBlockState Xrec) :=
    hX.2 (doubledFieldOfBlockState Xrec)
      (isDoubledMuAdmissible_of_isBlockMuAdmissible hRecAdmOld)
  have hRecEnergy :
      blockEnergyAverage (U : Set (Vec d)) a.toCoeffField Xrec =
        Mu (U : Set (Vec d)) P a.toCoeffField := by
    simpa [Rc, Xrec] using
      Rc.recoveredField_blockEnergyAverage_eq_mu system compat.mu_eq_muCandidate P
  have hBlockLeCandidate :
      blockEnergyAverage (U : Set (Vec d)) a.toCoeffField Xold ≤
        H.muCandidate P := by
    calc
      blockEnergyAverage (U : Set (Vec d)) a.toCoeffField Xold =
          doubledMuValue U a X :=
        (book_doubledMuValue_eq_blockEnergyAverage U a X).symm
      _ ≤ doubledMuValue U a (doubledFieldOfBlockState Xrec) := hMinLeRec
      _ = blockEnergyAverage (U : Set (Vec d)) a.toCoeffField Xrec :=
        book_doubledMuValue_ofBlockState_eq_blockEnergyAverage U a Xrec
      _ = Mu (U : Set (Vec d)) P a.toCoeffField := hRecEnergy
      _ = H.muCandidate P := by
        simpa [H] using compat.mu_eq_muCandidate P
  have hQuadEq :
      quadraticEnergy H.energyBilin HX =
        blockEnergyAverage (U : Set (Vec d)) a.toCoeffField Xold := by
    change
      quadraticEnergy (energyBilinOfOperator system.toMuOperatorRealization.operator) HX =
        blockEnergyAverage (U : Set (Vec d)) a.toCoeffField Xold
    simpa [HX, Xold] using
      system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        (X := Xold) (hX := hXOld.memBlockL2_eval)
  have hQuadLe : quadraticEnergy H.energyBilin HX ≤ H.muCandidate P := by
    simpa [hQuadEq] using hBlockLeCandidate
  have hEq : HX = H.minimizerMap P :=
    H.eq_minimizerMap_of_quadraticEnergy_le_muCandidate P HX hcorr hQuadLe
  simpa [HX, H, hXOld, Xold] using hEq

private theorem sameAE_of_hilbertBlockL2_eq {d : ℕ}
    {U : Domain d} {P : BlockVec d} {X Y : DoubledField d}
    (hX : IsBlockMuAdmissible (U : Set (Vec d)) P (blockStateOfDoubled X))
    (hY : IsBlockMuAdmissible (U : Set (Vec d)) P (blockStateOfDoubled Y))
    (hEq :
      toHilbertBlockL2OfBlockField hX.memBlockL2_eval =
        toHilbertBlockL2OfBlockField hY.memBlockL2_eval) :
    DoubledField.SameAE (U := U) X Y := by
  have hBlockL2 :
      toBlockL2 hX.memBlockL2_eval = toBlockL2 hY.memBlockL2_eval := by
    calc
      toBlockL2 hX.memBlockL2_eval =
          hilbertBlockL2ToBlockL2
            (toHilbertBlockL2OfBlockField hX.memBlockL2_eval) := by
        symm
        exact hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField hX.memBlockL2_eval
      _ =
          hilbertBlockL2ToBlockL2
            (toHilbertBlockL2OfBlockField hY.memBlockL2_eval) := by
        rw [hEq]
      _ = toBlockL2 hY.memBlockL2_eval :=
        hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField hY.memBlockL2_eval
  have hAE :
      (blockStateOfDoubled X).eval
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
          (blockStateOfDoubled Y).eval :=
    (toBlockL2_eq_toBlockL2_iff hX.memBlockL2_eval hY.memBlockL2_eval).mp
      hBlockL2
  constructor
  · filter_upwards [hAE] with x hx
    exact congrArg Prod.fst hx
  · filter_upwards [hAE] with x hx
    exact congrArg Prod.snd hx

private theorem sameAE_of_isDoubledMuMinimizers {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (R : PotentialSolenoidalL2RecoveryData (U : Set (Vec d)))
    (system : MuOperatorSystemData (U : Set (Vec d)) a.toCoeffField)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData
        (a := a.toCoeffField) R system)
    (P : BlockVec d) {X Y : DoubledField d}
    (hX : IsDoubledMuMinimizer U a P X)
    (hY : IsDoubledMuMinimizer U a P Y) :
    DoubledField.SameAE (U := U) X Y := by
  let hXOld : IsBlockMuAdmissible (U : Set (Vec d)) P (blockStateOfDoubled X) :=
    isBlockMuAdmissible_of_isDoubledMuAdmissible hX.1
  let hYOld : IsBlockMuAdmissible (U : Set (Vec d)) P (blockStateOfDoubled Y) :=
    isBlockMuAdmissible_of_isDoubledMuAdmissible hY.1
  have hXEq :=
    hilbert_eq_minimizerMap_of_isDoubledMuMinimizer U a R system compat P hX
  have hYEq :=
    hilbert_eq_minimizerMap_of_isDoubledMuMinimizer U a R system compat P hY
  exact sameAE_of_hilbertBlockL2_eq hXOld hYOld (hXEq.trans hYEq.symm)

private theorem doubledBlockPairingIntegrand_ae_eq_of_sameAE_right {d : ℕ}
    {U : Domain d} (a : CoeffOn U) (Y X Z : DoubledField d)
    (hXZ : DoubledField.SameAE (U := U) X Z) :
    doubledBlockPairingIntegrand U a Y X
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        doubledBlockPairingIntegrand U a Y Z := by
  filter_upwards [hXZ.1, hXZ.2] with x hpot hflux
  simp [doubledBlockPairingIntegrand, DoubledField.eval, hpot, hflux]

private theorem firstVariation_recoveredField {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (R : PotentialSolenoidalL2RecoveryData (U : Set (Vec d)))
    (system : MuOperatorSystemData (U : Set (Vec d)) a.toCoeffField)
    (P : BlockVec d) (Y : DoubledField d)
    (hY : IsDoubledTestField U Y)
    (hvol : (MeasureTheory.volume (U : Set (Vec d))).toReal ≠ 0) :
    ∫ x in (U : Set (Vec d)),
        doubledBlockPairingIntegrand U a Y
          (doubledFieldOfBlockState
            ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P)) x
          ∂MeasureTheory.volume = 0 := by
  let Rc := R.toMuCorrectionSpaceRecoveryData
  have hpot : IsPotentialZeroTraceOn (U : Set (Vec d)) Y.potential :=
    isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn hY.1
  have hOld :=
    Rc.integral_blockPairingIntegrand_correction_eq_zero
      system P hY.1.1 hY.2.1 hpot hY.2.2 hvol
  simpa [Rc, doubledFieldOfBlockState, blockStateOfDoubled,
    book_doubledBlockPairingIntegrand_eq_blockPairingIntegrand U a Y
      (doubledFieldOfBlockState (Rc.recoveredField system P))] using! hOld

private theorem doubledMuTheory_zero_dim (U : Domain 0) (a : CoeffOn U) :
    DoubledMuTheory U a := by
  have hAdm : ∀ P : BlockVec 0, ∀ X : DoubledField 0,
      IsDoubledMuAdmissible U P X := by
    intro P X
    have hpotZero :
        (fun x => X.potential x - P.1) = (0 : Vec 0 → Vec 0) := by
      funext x
      exact Subsingleton.elim _ _
    have hfluxZero :
        (fun x => X.flux x - P.2) = (0 : Vec 0 → Vec 0) := by
      funext x
      exact Subsingleton.elim _ _
    refine ⟨?_, ?_⟩
    · rw [hpotZero]
      exact Book.Ch01.potentialZeroTraceFieldOn_of_h10
        (0 : H10Function (U : Set (Vec 0)))
    · rw [hfluxZero]
      refine ⟨MeasureTheory.MemLp.zero, ?_⟩
      intro φ
      simp [vecDot]
  have hValueZero : ∀ X : DoubledField 0, doubledMuValue U a X = 0 := by
    intro X
    unfold doubledMuValue average blockEnergyDensityAt
    have hfun :
        (fun x : Vec 0 =>
            (1 / 2 : ℝ) *
              blockVecDot (X.eval x) (blockMatVecMul (blockMatrixField a x) (X.eval x))) =
            0 := by
        funext x
        simp [blockVecDot, vecDot]
    rw [hfun]
    simp
  have hMuZero : ∀ P : BlockVec 0, doubledMu U a P = 0 := by
    intro P
    have hset : doubledMuValueSet U a P = {0} := by
      ext m
      constructor
      · rintro ⟨X, _hX, rfl⟩
        simp [hValueZero X]
      · intro hm
        rw [Set.mem_singleton_iff] at hm
        subst m
        exact ⟨0, hAdm P 0, by simp [hValueZero 0]⟩
    unfold doubledMu
    rw [hset]
    simp
  refine
    { minimizer_exists := ?_
      minimizer_unique_ae := ?_
      mu_quadratic := ?_
      minimizer_first_variation := ?_ }
  · intro P
    refine ⟨0, ?_⟩
    refine ⟨hAdm P 0, ?_⟩
    intro Y hY
    simp [hValueZero]
  · intro P X Y hX hY
    constructor
    · exact Filter.Eventually.of_forall fun x => Subsingleton.elim _ _
    · exact Filter.Eventually.of_forall fun x => Subsingleton.elim _ _
  · intro P
    have hP : P = 0 := Subsingleton.elim P 0
    subst P
    simp [hMuZero, blockVecDot, vecDot]
  · intro P X hX Y hY
    have hfun :
        doubledBlockPairingIntegrand U a Y X = 0 := by
      funext x
      simp [doubledBlockPairingIntegrand, DoubledField.eval, blockVecDot, vecDot,
        matVecMul]
    rw [hfun]
    simp

private theorem doubledMuTheory_of_isEllipticFieldOn {d : ℕ} [NeZero d]
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    DoubledMuTheory U a := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨R, _sigma0, compat, hA, _hSInv, hS, hK, hSigma, _hSigmaCanonical⟩
  let system : MuOperatorSystemData (U : Set (Vec d)) a.toCoeffField :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  have hdet : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).det := by
      exact
        isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
          (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol
          compat (sigmaStar := Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) hS
  have hBlockEq :
      Book.Ch02.coarseBlockMatrix U a =
        Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField :=
    book_coarseBlockMatrix_eq_old_coarseBlockMatrix_of_data U a hA hS hK hSigma hdet
  refine
    { minimizer_exists := ?_
      minimizer_unique_ae := ?_
      mu_quadratic := ?_
      minimizer_first_variation := ?_ }
  · intro P
    exact
      ⟨doubledFieldOfBlockState
          ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P),
        isDoubledMuMinimizer_recoveredField U a hEll hvol R system compat P⟩
  · intro P X Y hX hY
    exact sameAE_of_isDoubledMuMinimizers U a R system compat P hX hY
  · intro P
    have hMuOld :=
      R.mu_eq_half_blockVecDot_coarseBlockMatrixOfIsEllipticFieldOn
        (a := a.toCoeffField) hEll hvol compat P
    calc
      doubledMu U a P = Mu (U : Set (Vec d)) P a.toCoeffField :=
        book_doubledMu_eq_Mu U a P
      _ =
          (1 / 2 : ℝ) *
            blockVecDot P
              (blockMatVecMul
                (Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField) P) :=
        hMuOld
      _ =
          (1 / 2 : ℝ) *
            blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) := by
        rw [hBlockEq]
  · intro P X hX Y hY
    let Xrec : DoubledField d :=
      doubledFieldOfBlockState
        ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P)
    have hRecMin : IsDoubledMuMinimizer U a P Xrec :=
      isDoubledMuMinimizer_recoveredField U a hEll hvol R system compat P
    have hSame : DoubledField.SameAE (U := U) X Xrec :=
      sameAE_of_isDoubledMuMinimizers U a R system compat P hX hRecMin
    have hFirstRec :=
      firstVariation_recoveredField U a R system P Y hY hvol.ne'
    calc
      ∫ x in (U : Set (Vec d)),
          doubledBlockPairingIntegrand U a Y X x ∂MeasureTheory.volume =
        ∫ x in (U : Set (Vec d)),
          doubledBlockPairingIntegrand U a Y Xrec x ∂MeasureTheory.volume := by
          exact MeasureTheory.integral_congr_ae
            (doubledBlockPairingIntegrand_ae_eq_of_sameAE_right a Y X Xrec hSame)
      _ = 0 := by
        simpa [Xrec] using hFirstRec

private theorem doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p q : Vec d) {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a (-p, q) X) :
    (fun x =>
        X.potential x +
          (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x =>
      (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨R, _sigma0, compat, _hA, _hSInv, _hS, _hK, _hSigma, _hSigmaCanonical⟩
  let system : MuOperatorSystemData (U : Set (Vec d)) a.toCoeffField :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  let Rc : MuCorrectionSpaceRecoveryData (U : Set (Vec d)) :=
    R.toMuCorrectionSpaceRecoveryData
  let XrecState : BlockState d := Rc.recoveredField system (-p, q)
  let Xrec : DoubledField d := doubledFieldOfBlockState XrecState
  have hRecMin : IsDoubledMuMinimizer U a (-p, q) Xrec :=
    isDoubledMuMinimizer_recoveredField U a hEll hvol R system compat (-p, q)
  have hSame : DoubledField.SameAE (U := U) X Xrec :=
    sameAE_of_isDoubledMuMinimizers U a R system compat (-p, q) hX hRecMin
  rcases
      Rc.exists_blockResponsePairHalfState_ae_eq_recoveredField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        system U.isDomain hEll hvol.ne' (-p, q) with
    ⟨u, v, hPairRec⟩
  have hAdm : IsBlockMuAdmissible (U : Set (Vec d)) (-p, q) XrecState := by
    simpa [XrecState, Rc] using Rc.recoveredField_admissible system (-p, q)
  have hfirst :
      ∀ w : AHarmonicFunction a.toCoeffField (U : Set (Vec d)),
        volumeAverage (U : Set (Vec d))
          (scalarFirstVariationIntegrand (U : Set (Vec d)) a.toCoeffField p q u w) = 0 := by
    intro w
    simpa [XrecState, Rc] using
      scalarFirstVariation_neg_left_right_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
        (a := a.toCoeffField) (U := (U : Set (Vec d))) (hU := U.measurableSet)
        hEll (-p) q u v XrecState hPairRec hAdm w
  have hOldMax :
      Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q a.toCoeffField u :=
    isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hEll p q u hfirst
  have hMax : Book.Ch02.IsResponseMaximizer U a p q u :=
    public_isResponseMaximizer_of_old U a p q u hOldMax
  have hCanonical :
      (fun x => u.toH1.grad x)
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x =>
        (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x :=
    (canonicalMaximizer_sameGradientAE_of_isResponseMaximizer hMax).symm
  have hLowerPair :
      (fun x =>
          (blockMatVecMul (blockCoeffField a.toCoeffField x)
            ((blockResponsePairHalfState a.toCoeffField u v).eval x)).2)
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x) :=
    blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
      (a := a.toCoeffField) hEll u v
  have hPairExtract :
      (fun x =>
          (blockResponsePairHalfState a.toCoeffField u v).potential x +
            (blockMatVecMul (blockCoeffField a.toCoeffField x)
              ((blockResponsePairHalfState a.toCoeffField u v).eval x)).2)
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => u.toH1.grad x := by
    filter_upwards [hLowerPair] with x hLower
    rw [hLower]
    change ((1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x) +
        (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x)) = u.toH1.grad x
    ext i
    simp [sub_eq_add_neg]
    ring_nf
  have hXExtract_eq_pair :
      (fun x =>
          X.potential x +
            (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2)
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x =>
          (blockResponsePairHalfState a.toCoeffField u v).potential x +
            (blockMatVecMul (blockCoeffField a.toCoeffField x)
              ((blockResponsePairHalfState a.toCoeffField u v).eval x)).2 := by
    filter_upwards [hSame.1, hSame.2, hPairRec] with x hPot hFlux hPair
    have hPairPot :
        (blockResponsePairHalfState a.toCoeffField u v).potential x =
          XrecState.potential x := congrArg Prod.fst hPair
    have hPairFlux :
        (blockResponsePairHalfState a.toCoeffField u v).flux x =
          XrecState.flux x := congrArg Prod.snd hPair
    have hPotPair :
        X.potential x = (blockResponsePairHalfState a.toCoeffField u v).potential x := by
      simpa [Xrec, XrecState, doubledFieldOfBlockState] using hPot.trans hPairPot.symm
    have hFluxPair :
        X.flux x = (blockResponsePairHalfState a.toCoeffField u v).flux x := by
      simpa [Xrec, XrecState, doubledFieldOfBlockState] using hFlux.trans hPairFlux.symm
    have hEval :
        X.eval x = (blockResponsePairHalfState a.toCoeffField u v).eval x := by
      exact Prod.ext hPotPair hFluxPair
    rw [hPotPair, hEval]
  exact hXExtract_eq_pair.trans (hPairExtract.trans hCanonical)

private theorem doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p q : Vec d) {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a (-p, q) X) :
    (fun x =>
        X.flux x +
          (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).1)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x =>
      matVecMul (a.toCoeffField x)
        ((canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x) := by
  have hGrad :=
    doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient_of_isEllipticFieldOn
      U a hEll p q hX
  filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet, hGrad] with x hx hgrad
  have hAlg :=
    upper_add_flux_eq_matVecMul_potential_add_lowerImage_of_isEllipticFieldOn
      (a := a.toCoeffField) hEll (X := blockStateOfDoubled X) hx
  calc
    X.flux x + (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).1 =
        (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).1 + X.flux x := by
          abel
    _ =
        matVecMul (a.toCoeffField x)
          (X.potential x +
            (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2) := by
          simpa [blockStateOfDoubled] using! hAlg
    _ =
        matVecMul (a.toCoeffField x)
          ((canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x) := by
          rw [hgrad]

theorem doubledMuTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    DoubledMuTheory U a := by
  by_cases hd : d = 0
  · subst d
    exact doubledMuTheory_zero_dim U a
  · let : NeZero d := ⟨hd⟩
    let b : CoeffOn U := pointwiseCoeffOn U a
    have hb : DoubledMuTheory U b :=
      doubledMuTheory_of_isEllipticFieldOn U b
        (by simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a)
    have hba : CoeffOn.AEEq b a := by
      simpa [b] using pointwiseCoeffOn_ae_eq U a
    exact DoubledMuTheory.ofAEEq hba hb

theorem doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient
    {d : ℕ} (U : Domain d) (a : CoeffOn U) (p q : Vec d)
    {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a (-p, q) X) :
    (fun x =>
        X.potential x +
          (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x =>
      (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x := by
  by_cases hd : d = 0
  · subst d
    exact Filter.Eventually.of_forall fun x => Subsingleton.elim _ _
  · let : NeZero d := ⟨hd⟩
    let b : CoeffOn U := pointwiseCoeffOn U a
    have hba : CoeffOn.AEEq b a := by
      simpa [b] using pointwiseCoeffOn_ae_eq U a
    have hXb : IsDoubledMuMinimizer U b (-p, q) X :=
      hX.ofAEEq hba.symm
    have hCoeff : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField :=
      hba
    have hLeft :
        (fun x =>
            X.potential x +
              (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2)
          =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x =>
            X.potential x +
              (blockMatVecMul (blockCoeffField b.toCoeffField x) (X.eval x)).2 := by
      filter_upwards [hCoeff] with x hx
      simp [blockCoeffField, hx]
    have hExtractB :=
      doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient_of_isEllipticFieldOn
        U b (by simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a) p q hXb
    have hCanonical :
        (fun x =>
          (canonicalMaximizer (responseExistenceTheory U b) p q).toSolution.toH1.grad x)
          =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x =>
          (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x := by
      simpa [Solution.SameGradientAE] using
        (canonicalMaximizer_sameGradientAE_ofAEEq hba p q)
    exact hLeft.trans (hExtractB.trans hCanonical)

theorem doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux
    {d : ℕ} (U : Domain d) (a : CoeffOn U) (p q : Vec d)
    {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a (-p, q) X) :
    (fun x =>
        X.flux x +
          (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).1)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x =>
      matVecMul (a.toCoeffField x)
        ((canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x) := by
  by_cases hd : d = 0
  · subst d
    exact Filter.Eventually.of_forall fun x => Subsingleton.elim _ _
  · let : NeZero d := ⟨hd⟩
    let b : CoeffOn U := pointwiseCoeffOn U a
    have hba : CoeffOn.AEEq b a := by
      simpa [b] using pointwiseCoeffOn_ae_eq U a
    have hXb : IsDoubledMuMinimizer U b (-p, q) X :=
      hX.ofAEEq hba.symm
    have hCoeff : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField :=
      hba
    have hLeft :
        (fun x =>
            X.flux x +
              (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).1)
          =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x =>
            X.flux x +
              (blockMatVecMul (blockCoeffField b.toCoeffField x) (X.eval x)).1 := by
      filter_upwards [hCoeff] with x hx
      simp [blockCoeffField, hx]
    have hExtractB :=
      doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux_of_isEllipticFieldOn
        U b (by simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a) p q hXb
    have hCanonical :
        (fun x =>
          matVecMul (b.toCoeffField x)
            ((canonicalMaximizer (responseExistenceTheory U b) p q).toSolution.toH1.grad x))
          =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x =>
          matVecMul (a.toCoeffField x)
            ((canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x) := by
      have hGrad :
          (fun x =>
            (canonicalMaximizer (responseExistenceTheory U b) p q).toSolution.toH1.grad x)
            =ᵐ[volumeMeasureOn (U : Set (Vec d))]
          fun x =>
            (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution.toH1.grad x := by
        simpa [Solution.SameGradientAE] using
          (canonicalMaximizer_sameGradientAE_ofAEEq hba p q)
      filter_upwards [hCoeff, hGrad] with x hcoeff hgrad
      rw [hcoeff, hgrad]
    exact hLeft.trans (hExtractB.trans hCanonical)

end BookCh02

end

end Ch02
end Internal
end Homogenization
