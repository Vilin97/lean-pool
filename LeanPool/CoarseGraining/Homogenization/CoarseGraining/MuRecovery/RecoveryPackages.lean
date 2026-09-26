/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy

/-! # Recovery Packages -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Mu recovery -- Minimizer and PotentialSolenoidalL2 package APIs

MuMinimizerRecoveryData namespace (ofCorrectionSpaceRecovery and the
hasQuadraticMu / exists_coarseBlockMatrix / mu_eq_half_blockVecDot
bridges) plus the PotentialSolenoidalL2RecoveryData API used by the
origin-cube recovery layer.
-/

namespace MuMinimizerRecoveryData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- Convert recovery data for Hilbert minimizers into the note-faithful linear
family of pointwise doubled minimizers. -/
noncomputable def toLinearMuMinimizerFamily (M : MuMinimizerRecoveryData U a) :
    LinearMuMinimizerFamily U a where
  field := M.field
  map_add := M.map_add
  map_smul := M.map_smul
  admissible := M.admissible
  pairingIntegrable := M.pairingIntegrable
  realizes := by
    intro P
    have hquad :
        quadraticEnergy
            (energyBilinOfOperator M.system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (M.mem_blockL2 P)) =
          blockEnergyAverage U a (M.field P) :=
      M.system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        (X := M.field P)
        (hX := M.mem_blockL2 P)
    rw [M.mu_eq_muCandidate P]
    show
      quadraticEnergy
          (energyBilinOfOperator M.system.toMuOperatorRealization.operator)
          (M.system.toMuHilbertRealization.minimizerMap P) =
        blockEnergyAverage U a (M.field P)
    rw [← M.minimizer_eq P]
    exact hquad

theorem hasQuadraticMu (M : MuMinimizerRecoveryData U a) :
    HasQuadraticMu U a :=
  M.toLinearMuMinimizerFamily.hasQuadraticMu

theorem exists_coarseBlockMatrix (M : MuMinimizerRecoveryData U a) :
    ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
  M.toLinearMuMinimizerFamily.exists_coarseBlockMatrix

theorem existsUnique_coarseBlockMatrix (M : MuMinimizerRecoveryData U a) :
    ∃! Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
  M.toLinearMuMinimizerFamily.existsUnique_coarseBlockMatrix

theorem mu_eq_half_blockVecDot_coarseBlockMatrix
    (M : MuMinimizerRecoveryData U a) (P : BlockVec d) :
    Mu U P a = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) :=
  Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu M.hasQuadraticMu P

/-- Build minimizer recovery data from a recovered correction space, leaving
pairing integrability as the only remaining auxiliary input. -/
noncomputable def ofCorrectionSpaceRecovery
    (system : MuOperatorSystemData U a)
    (R : MuCorrectionSpaceRecoveryData U)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q)) U)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P) :
    MuMinimizerRecoveryData U a where
  system := system.withCorrectionSpace R.toMuCorrectionSpaceData
  field := R.recoveredField system
  map_add := R.recoveredField_add system
  map_smul := R.recoveredField_smul system
  mem_blockL2 := R.recoveredField_memBlockL2 system
  minimizer_eq := R.recoveredField_minimizer_eq system
  admissible := R.recoveredField_admissible system
  pairingIntegrable := pairingIntegrable
  mu_eq_muCandidate := mu_eq_muCandidate

end MuMinimizerRecoveryData

namespace PotentialSolenoidalL2RecoveryData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- The Hilbert-space realization associated with the block-side recovery data
and a concrete doubled operator system. -/
noncomputable def toMuHilbertRealization
    (R : PotentialSolenoidalL2RecoveryData U)
    (system : MuOperatorSystemData U a) :
    MuHilbertRealization U a :=
  system.toMuOperatorRealization.toMuHilbertRealization
    R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData

/-- The remaining recovery-side hypotheses needed to convert the Hilbert
minimization package into the note-faithful pointwise minimizer family. -/
structure MuRecoveryCompatibilityData
    (R : PotentialSolenoidalL2RecoveryData U)
    (system : MuOperatorSystemData U a) where
  pairingIntegrable :
    ∀ P Q : BlockVec d,
      MeasureTheory.IntegrableOn
        (blockPairingIntegrand a
          ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P)
          ((R.toMuCorrectionSpaceRecoveryData).recoveredField system Q)) U
  mu_eq_muCandidate :
    ∀ P : BlockVec d,
      Mu U P a = (R.toMuHilbertRealization system).muCandidate P

/-- Under ellipticity, the only non-formal field of
`MuRecoveryCompatibilityData` is the identification of `Mu` with the Hilbert
minimizer value. Pairing integrability follows automatically from the `L²`
control of recovered fields. -/
theorem muRecoveryCompatibilityData_of_isEllipticFieldOn_of_mu_eq_muCandidate
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          ((R.toMuHilbertRealization
            (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)).muCandidate P)) :
    MuRecoveryCompatibilityData (a := a) R
      (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol) := by
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  refine ⟨?_, ?_⟩
  · intro P Q
    exact
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P)
        ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system Q)
        hEll
  · simpa [system] using mu_eq_muCandidate

/-- The linear minimizer family produced directly from block-side recovery data
and a concrete doubled operator system. -/
noncomputable def toLinearMuMinimizerFamily
    (R : PotentialSolenoidalL2RecoveryData U)
    (system : MuOperatorSystemData U a)
    (compat : MuRecoveryCompatibilityData (a := a) R system) :
    LinearMuMinimizerFamily U a :=
  (MuMinimizerRecoveryData.ofCorrectionSpaceRecovery
    (system := system)
    (R := R.toMuCorrectionSpaceRecoveryData)
    compat.pairingIntegrable
    compat.mu_eq_muCandidate).toLinearMuMinimizerFamily

/-- Build minimizer recovery data directly from block-side recovery data
`\Lpoto(U) × \Lsolo(U)` and a concrete doubled operator system. -/
noncomputable def toMuMinimizerRecoveryData
    (R : PotentialSolenoidalL2RecoveryData U)
    (system : MuOperatorSystemData U a)
    (compat : MuRecoveryCompatibilityData (a := a) R system) :
    MuMinimizerRecoveryData U a :=
  MuMinimizerRecoveryData.ofCorrectionSpaceRecovery
    (system := system)
    (R := R.toMuCorrectionSpaceRecoveryData)
    compat.pairingIntegrable
    compat.mu_eq_muCandidate

theorem hasQuadraticMu
    (R : PotentialSolenoidalL2RecoveryData U)
    (system : MuOperatorSystemData U a)
    (compat : MuRecoveryCompatibilityData (a := a) R system) :
    HasQuadraticMu U a :=
  (R.toLinearMuMinimizerFamily system compat).hasQuadraticMu

theorem exists_coarseBlockMatrix
    (R : PotentialSolenoidalL2RecoveryData U)
    (system : MuOperatorSystemData U a)
    (compat : MuRecoveryCompatibilityData (a := a) R system) :
    ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
  (R.toLinearMuMinimizerFamily system compat).exists_coarseBlockMatrix

theorem existsUnique_coarseBlockMatrix
    (R : PotentialSolenoidalL2RecoveryData U)
    (system : MuOperatorSystemData U a)
    (compat : MuRecoveryCompatibilityData (a := a) R system) :
    ∃! Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
  (R.toLinearMuMinimizerFamily system compat).existsUnique_coarseBlockMatrix

theorem mu_eq_half_blockVecDot_coarseBlockMatrix
    (R : PotentialSolenoidalL2RecoveryData U)
    (system : MuOperatorSystemData U a)
    (compat : MuRecoveryCompatibilityData (a := a) R system)
    (P : BlockVec d) :
    Mu U P a = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) :=
  (R.toLinearMuMinimizerFamily system compat).mu_eq_half_blockVecDot_coarseBlockMatrix P

/-- The deterministic doubled operator system built from raw ellipticity and
the packaged block-side correction space. -/
noncomputable def toMuOperatorSystemDataOfIsEllipticFieldOn
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    MuOperatorSystemData U a :=
  R.toPotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol

/-- Build minimizer recovery data directly from block-side recovery data and
raw ellipticity assumptions. -/
noncomputable def toMuMinimizerRecoveryDataOfIsEllipticFieldOn
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    MuMinimizerRecoveryData U a :=
  R.toMuMinimizerRecoveryData
    (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol) compat

theorem hasQuadraticMuOfIsEllipticFieldOn
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    HasQuadraticMu U a :=
  (R.toMuMinimizerRecoveryDataOfIsEllipticFieldOn hEll hvol compat).hasQuadraticMu

theorem exists_coarseBlockMatrixOfIsEllipticFieldOn
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
  (R.toMuMinimizerRecoveryDataOfIsEllipticFieldOn hEll hvol compat).exists_coarseBlockMatrix

theorem existsUnique_coarseBlockMatrixOfIsEllipticFieldOn
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    ∃! Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
  (R.toMuMinimizerRecoveryDataOfIsEllipticFieldOn hEll hvol compat).existsUnique_coarseBlockMatrix

theorem mu_eq_half_blockVecDot_coarseBlockMatrixOfIsEllipticFieldOn
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (P : BlockVec d) :
    Mu U P a = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) :=
  MuMinimizerRecoveryData.mu_eq_half_blockVecDot_coarseBlockMatrix
    (R.toMuMinimizerRecoveryDataOfIsEllipticFieldOn hEll hvol compat) P

/-- Under the deterministic coarse-data package, the recovery-side quadratic
representation of `\mu` identifies its pure-flux slice with the scalar
response slice `\mathcal J(U; 0, q, a)`. -/
theorem mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn_of_isSigmaCoarse
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (q : Vec d) :
    Mu U (0, q) a = ResponseJ U 0 q a := by
  have hMu :=
    R.mu_eq_half_blockVecDot_coarseBlockMatrixOfIsEllipticFieldOn
      (a := a) hEll hvol compat (0, q)
  have hResp :=
    basic_cg_identities_responseJ_formula_coarseBlockMatrix_of_isSigmaCoarse
      U a hA hS hK hSigma hdet 0 q
  calc
    Mu U (0, q) a =
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) := by
          simpa [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left] using hMu
    _ = ResponseJ U 0 q a := by
          symm
          simpa [vecDot_zero_left, vecDot_zero_right, matVecMul_zero] using hResp

/-- Under the deterministic coarse-data package, the recovery-side quadratic
representation of `\mu` identifies its pure-gradient slice with the scalar
response slice `\mathcal J(U; p, 0, a)`. -/
theorem mu_left_zero_eq_responseJ_zero_of_isEllipticFieldOn_of_isSigmaCoarse
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (p : Vec d) :
    Mu U (p, 0) a = ResponseJ U p 0 a := by
  have hMu :=
    R.mu_eq_half_blockVecDot_coarseBlockMatrixOfIsEllipticFieldOn
      (a := a) hEll hvol compat (p, 0)
  have hResp :=
    basic_cg_identities_responseJ_zero_formula_coarseBlockMatrix_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p
  calc
    Mu U (p, 0) a =
        (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
          simpa [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left] using hMu
    _ = ResponseJ U p 0 a := by
          symm
          simpa using hResp

/-- If the pure-flux slice of `\mu` matches the pure-flux slice of
`\mathcal J`, then the lower-right block of `\mathbf A(U; a)` is the canonical
`\sigma_*^{-1}(U; a)`, packaged directly from recovery data and ellipticity. -/
theorem coarseBlockMatrix_lowerRight_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (hMuResp : ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a) :
    (coarseBlockMatrix U a).lowerRight = sigmaStarInvCoarse U a :=
  coarseBlockMatrix_lowerRight_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero
    (U := U) (a := a)
    (R.exists_coarseBlockMatrixOfIsEllipticFieldOn hEll hvol compat) hMuResp

/-- If the pure-flux slice of `\mu` matches the pure-flux slice of
`\mathcal J`, then the upper-left block of `\mathbf A_*^{-1}(U; a)` is the
canonical `\sigma_*^{-1}(U; a)`, packaged directly from recovery data and
ellipticity. -/
theorem coarseStarredBlockMatrixInv_upperLeft_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (hMuResp : ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a) :
    (coarseStarredBlockMatrixInv U a).upperLeft = sigmaStarInvCoarse U a :=
  coarseStarredBlockMatrixInv_upperLeft_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero
    (U := U) (a := a)
    (R.exists_coarseBlockMatrixOfIsEllipticFieldOn hEll hvol compat) hMuResp

theorem mu_ge_vecDot_of_isEllipticFieldOn
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤ Mu U P a := by
  let system := R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  have hpotZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U,
          ((R.toMuCorrectionSpaceRecoveryData).recoveredCorrectionField system P).potential x i
            ∂MeasureTheory.volume) = 0 := by
    intro P
    let Y := (R.toMuCorrectionSpaceRecoveryData).recoveredCorrectionField system P
    simpa [Y] using IsPotentialZeroTraceOn.integral_eq_zero Y.isPotentialZeroTrace
  have hfluxZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U,
          ((R.toMuCorrectionSpaceRecoveryData).recoveredCorrectionField system P).flux x i
            ∂MeasureTheory.volume) = 0 := by
    intro P
    let Y := (R.toMuCorrectionSpaceRecoveryData).recoveredCorrectionField system P
    simpa [Y] using
      IsSolenoidalZeroNormalTraceOn.integral_eq_zero hU Y.isSolenoidalZeroNormalTrace
  have hvol_ne : (MeasureTheory.volume U).toReal ≠ 0 := hvol.ne'
  simpa [system] using
    ((R.toMuCorrectionSpaceRecoveryData).mu_ge_vecDot_of_isEllipticFieldOn_of_integral_eq_zero
      system hEll compat.pairingIntegrable hpotZero hfluxZero hvol_ne compat.mu_eq_muCandidate P)

theorem mu_ge_vecDot_openCubeSet_originCubeOfIsEllipticFieldOn
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
          (volume_openCubeSet_originCube_toReal_pos_recovery (d := d) n)))
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤ Mu (openCubeSet (originCube d n)) P a := by
  let system :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos_recovery (d := d) n)
  simpa [system] using
    (R.toMuCorrectionSpaceRecoveryData.mu_ge_vecDot_openCubeSet_originCube
      system hEll compat.pairingIntegrable compat.mu_eq_muCandidate P)

theorem mu_ge_vecDot_cubeSet_originCubeOfIsEllipticFieldOn
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (cubeSet (originCube d n)))
    {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a)
    (compat :
      MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
          (volume_cubeSet_originCube_toReal_pos_recovery (d := d) n)))
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤ Mu (cubeSet (originCube d n)) P a := by
  let system :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_cubeSet_originCube_toReal_pos_recovery (d := d) n)
  simpa [system] using
    (R.toMuCorrectionSpaceRecoveryData.mu_ge_vecDot_cubeSet_originCube
      system hEll compat.pairingIntegrable compat.mu_eq_muCandidate P)

end PotentialSolenoidalL2RecoveryData

end

end Homogenization
