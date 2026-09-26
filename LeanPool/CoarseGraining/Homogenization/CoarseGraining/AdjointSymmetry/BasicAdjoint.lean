/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockMatrixProperties
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery
public import LeanPool.CoarseGraining.Homogenization.Probability.RandomField
public import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidal

/-! # Basic Adjoint -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Adjoint symmetry -- basic adjoint-coefficient-field equalities

blockVecFlipFlux / blockMatFlipFlux, muValueSet_adjointCoeffField_flipFlux,
Mu_adjointCoeffField_flipFlux, and the coarseBlockMatrix /
coarseStarredBlockMatrixInv adjointCoeffField equalities (including the
component variants for upperLeft / upperRight / lowerLeft / lowerRight).
-/

/--
Flip the flux component of a doubled block vector.
-/
def blockVecFlipFlux {d : ℕ} (P : BlockVec d) : BlockVec d :=
  (P.1, -P.2)

/--
Flip the off-diagonal flux signs of a doubled block matrix.
-/
def blockMatFlipFlux {d : ℕ} (A : BlockMat d) : BlockMat d :=
  { upperLeft := A.upperLeft
    upperRight := -A.upperRight
    lowerLeft := -A.lowerLeft
    lowerRight := A.lowerRight }

@[simp] theorem blockVecFlipFlux_flipFlux {d : ℕ} (P : BlockVec d) :
    blockVecFlipFlux (blockVecFlipFlux P) = P := by
  rcases P with ⟨p, q⟩
  simp [blockVecFlipFlux]

@[simp] theorem blockState_flipFlux_flipFlux {d : ℕ} (X : BlockState d) :
    X.flipFlux.flipFlux = X := by
  cases X
  apply BlockState.ext
  · rfl
  · funext x
    simp [BlockState.flipFlux]

@[simp] theorem adjointCoeffField_adjointCoeffField {d : ℕ} (a : CoeffField d) :
    adjointCoeffField (adjointCoeffField a) = a := by
  funext x
  simp [adjointCoeffField, matTranspose]

@[simp] theorem blockMatVecMul_blockMatFlipFlux {d : ℕ}
    (A : BlockMat d) (P : BlockVec d) :
    blockMatVecMul (blockMatFlipFlux A) P =
      blockVecFlipFlux (blockMatVecMul A (blockVecFlipFlux P)) := by
  rcases A with ⟨ul, ur, ll, lr⟩
  rcases P with ⟨p, q⟩
  apply Prod.ext
  · simp [blockMatFlipFlux, blockVecFlipFlux, blockMatVecMul, neg_matVecMul, matVecMul_neg]
  · simp [blockMatFlipFlux, blockVecFlipFlux, blockMatVecMul, neg_matVecMul, matVecMul_neg,
      add_comm]

theorem blockVecDot_blockVecFlipFlux_right {d : ℕ} (P Q : BlockVec d) :
    blockVecDot P (blockVecFlipFlux Q) = blockVecDot (blockVecFlipFlux P) Q := by
  rcases P with ⟨p, q⟩
  rcases Q with ⟨u, v⟩
  simp [blockVecFlipFlux, blockVecDot, vecDot_neg_left, vecDot_neg_right]

private theorem isSymmetricBlockMat_blockMatFlipFlux {d : ℕ} {Abar : BlockMat d}
    (hA : IsSymmetricBlockMat Abar) :
    IsSymmetricBlockMat (blockMatFlipFlux Abar) := by
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [blockMatFlipFlux, blockMatEntry] using hA (Sum.inl i) (Sum.inl j)
      | inr j =>
          simpa [blockMatFlipFlux, blockMatEntry] using congrArg Neg.neg (hA (Sum.inl i) (Sum.inr j))
  | inr i =>
      cases β with
      | inl j =>
          simpa [blockMatFlipFlux, blockMatEntry] using congrArg Neg.neg (hA (Sum.inr i) (Sum.inl j))
      | inr j =>
          simpa [blockMatFlipFlux, blockMatEntry] using hA (Sum.inr i) (Sum.inr j)

@[simp] theorem blockReflect_blockMatFlipFlux {d : ℕ} (A : BlockMat d) :
    blockReflect (blockMatFlipFlux A) = blockMatFlipFlux (blockReflect A) :=
  rfl

theorem isBlockMuAdmissible_flipFlux {d : ℕ} {U : Set (Vec d)} {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible U P X) :
    IsBlockMuAdmissible U (blockVecFlipFlux P) X.flipFlux := by
  rcases hX with ⟨hpotL2, hpot, hsolL2, hsol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [BlockState.flipFlux] using! hpotL2
  · simpa [IsBlockMuAdmissible, blockVecFlipFlux, BlockState.flipFlux] using hpot
  · convert hsolL2.neg using 1
    funext x
    simp [BlockState.flipFlux, blockVecFlipFlux, sub_eq_add_neg, add_comm]
  · convert isSolenoidalZeroNormalTraceOn_smul hsol (-1 : ℝ) using 1
    funext x
    simp [blockVecFlipFlux, BlockState.flipFlux, sub_eq_add_neg, add_comm]

theorem blockEnergyDensity_adjointCoeffField_flipFlux {d : ℕ}
    (a : CoeffField d) (X : BlockState d) (x : Vec d) :
    blockEnergyDensity (adjointCoeffField a) X.flipFlux x =
      blockEnergyDensity a X x := by
  simpa [adjointCoeffField] using!
    blockEnergyDensity_matTranspose_flipFlux (a := a) (X := X) (x := x)

theorem volumeAverage_blockEnergyDensity_adjointCoeffField_flipFlux {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (X : BlockState d) :
    volumeAverage U (blockEnergyDensity (adjointCoeffField a) X.flipFlux) =
      volumeAverage U (blockEnergyDensity a X) := by
  unfold volumeAverage
  rw [show (∫ x in U, blockEnergyDensity (adjointCoeffField a) X.flipFlux x ∂MeasureTheory.volume) =
      ∫ x in U, blockEnergyDensity a X x ∂MeasureTheory.volume by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        exact blockEnergyDensity_adjointCoeffField_flipFlux a X x]

theorem muValueSet_adjointCoeffField_flipFlux {d : ℕ}
    (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) :
    muValueSet U (blockVecFlipFlux P) (adjointCoeffField a) = muValueSet U P a := by
  ext m
  constructor
  · rintro ⟨X, hX, hm⟩
    refine ⟨X.flipFlux, ?_, ?_⟩
    · simpa using isBlockMuAdmissible_flipFlux
        (U := U) (P := blockVecFlipFlux P) (X := X) hX
    · calc
        m = volumeAverage U (blockEnergyDensity (adjointCoeffField a) X) := hm
        _ = volumeAverage U
              (blockEnergyDensity (adjointCoeffField (adjointCoeffField a)) X.flipFlux) := by
              symm
              exact volumeAverage_blockEnergyDensity_adjointCoeffField_flipFlux
                U (adjointCoeffField a) X
        _ = volumeAverage U (blockEnergyDensity a X.flipFlux) := by simp
  · rintro ⟨X, hX, hm⟩
    refine ⟨X.flipFlux, isBlockMuAdmissible_flipFlux (U := U) (P := P) (X := X) hX, ?_⟩
    calc
      m = volumeAverage U (blockEnergyDensity a X) := hm
      _ = volumeAverage U (blockEnergyDensity (adjointCoeffField a) X.flipFlux) := by
            symm
            exact volumeAverage_blockEnergyDensity_adjointCoeffField_flipFlux U a X

theorem Mu_adjointCoeffField_flipFlux {d : ℕ}
    (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) :
    Mu U (blockVecFlipFlux P) (adjointCoeffField a) = Mu U P a := by
  rw [Mu, Mu, muValueSet_adjointCoeffField_flipFlux U P a]

/-- The full-coordinate linear map flipping the flux half of a block vector. -/
def fullBlockVecFlipFluxLinearMap {d : ℕ} :
    FullBlockVec d →ₗ[ℝ] FullBlockVec d where
  toFun x
    | Sum.inl i => x (Sum.inl i)
    | Sum.inr i => -x (Sum.inr i)
  map_add' x y := by
    funext α
    cases α <;> simp [add_comm]
  map_smul' c x := by
    funext α
    cases α <;> simp

@[simp] theorem fullBlockVecFlipFluxLinearMap_toFullBlockVec {d : ℕ} (P : BlockVec d) :
    fullBlockVecFlipFluxLinearMap (d := d) (toFullBlockVec P) =
      toFullBlockVec (blockVecFlipFlux P) := by
  funext α
  cases α <;> rfl

theorem hasQuadraticMu_adjointCoeffField {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hquad : HasQuadraticMu U a) :
    HasQuadraticMu U (adjointCoeffField a) := by
  rcases hquad with ⟨Q, hQ⟩
  refine ⟨Q.comp (fullBlockVecFlipFluxLinearMap (d := d)), ?_⟩
  intro P
  calc
    Mu U P (adjointCoeffField a)
        = Mu U (blockVecFlipFlux P) a := by
            simpa using Mu_adjointCoeffField_flipFlux U (blockVecFlipFlux P) a
    _ = (1 / 2 : ℝ) * Q (toFullBlockVec (blockVecFlipFlux P)) := hQ (blockVecFlipFlux P)
    _ = (1 / 2 : ℝ) *
          (Q.comp (fullBlockVecFlipFluxLinearMap (d := d))) (toFullBlockVec P) := by
            simp

namespace IsCoarseBlockMatrix

theorem adjointCoeffField_symm {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {Abar : BlockMat d}
    (hA : IsCoarseBlockMatrix U a Abar) :
    IsCoarseBlockMatrix U (Homogenization.adjointCoeffField a) (blockMatFlipFlux Abar) := by
  rcases hA with ⟨hsymm, hmu⟩
  refine ⟨isSymmetricBlockMat_blockMatFlipFlux hsymm, ?_⟩
  intro P
  have hMuP :
      Mu U P (Homogenization.adjointCoeffField a) = Mu U (blockVecFlipFlux P) a := by
    simpa using (Mu_adjointCoeffField_flipFlux U (blockVecFlipFlux P) a)
  have hdot :
      blockVecDot P (blockMatVecMul (blockMatFlipFlux Abar) P) =
        blockVecDot (blockVecFlipFlux P) (blockMatVecMul Abar (blockVecFlipFlux P)) := by
    rw [blockMatVecMul_blockMatFlipFlux]
    exact blockVecDot_blockVecFlipFlux_right P (blockMatVecMul Abar (blockVecFlipFlux P))
  calc
    Mu U P (Homogenization.adjointCoeffField a)
        = Mu U (blockVecFlipFlux P) a := hMuP
    _ = (1 / 2 : ℝ) * blockVecDot (blockVecFlipFlux P)
          (blockMatVecMul Abar (blockVecFlipFlux P)) := hmu _
    _ = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (blockMatFlipFlux Abar) P) := by
          rw [hdot]

end IsCoarseBlockMatrix

theorem coarseBlockMatrix_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    coarseBlockMatrix U (Homogenization.adjointCoeffField a) =
      blockMatFlipFlux (coarseBlockMatrix U a) := by
  rcases hex with ⟨Abar, hA⟩
  have hAadj := IsCoarseBlockMatrix.adjointCoeffField_symm (U := U) hA
  calc
    coarseBlockMatrix U (Homogenization.adjointCoeffField a) = blockMatFlipFlux Abar := by
      symm
      exact eq_coarseBlockMatrix_of_isCoarseBlockMatrix hAadj
    _ = blockMatFlipFlux (coarseBlockMatrix U a) := by
      rw [eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA]

theorem coarseBlockMatrix_lowerLeft_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    (coarseBlockMatrix U (adjointCoeffField a)).lowerLeft =
      -((coarseBlockMatrix U a).lowerLeft) := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.lowerLeft (coarseBlockMatrix_adjointCoeffField_of_exists (U := U) hex)

theorem coarseBlockMatrix_upperLeft_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    (coarseBlockMatrix U (adjointCoeffField a)).upperLeft =
      (coarseBlockMatrix U a).upperLeft := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.upperLeft (coarseBlockMatrix_adjointCoeffField_of_exists (U := U) hex)

theorem coarseBlockMatrix_upperRight_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    (coarseBlockMatrix U (adjointCoeffField a)).upperRight =
      -((coarseBlockMatrix U a).upperRight) := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.upperRight (coarseBlockMatrix_adjointCoeffField_of_exists (U := U) hex)

theorem coarseBlockMatrix_lowerRight_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    (coarseBlockMatrix U (adjointCoeffField a)).lowerRight =
      (coarseBlockMatrix U a).lowerRight := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.lowerRight (coarseBlockMatrix_adjointCoeffField_of_exists (U := U) hex)

theorem coarseStarredBlockMatrixInv_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    coarseStarredBlockMatrixInv U (adjointCoeffField a) =
      blockMatFlipFlux (coarseStarredBlockMatrixInv U a) := by
  rw [coarseStarredBlockMatrixInv_eq_blockReflect,
    coarseBlockMatrix_adjointCoeffField_of_exists (U := U) (a := a) hex,
    blockReflect_blockMatFlipFlux, coarseStarredBlockMatrixInv_eq_blockReflect]

theorem coarseStarredBlockMatrixInv_upperLeft_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    (coarseStarredBlockMatrixInv U (adjointCoeffField a)).upperLeft =
      (coarseStarredBlockMatrixInv U a).upperLeft := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.upperLeft
      (coarseStarredBlockMatrixInv_adjointCoeffField_of_exists (U := U) (a := a) hex)

theorem coarseStarredBlockMatrixInv_upperRight_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    (coarseStarredBlockMatrixInv U (adjointCoeffField a)).upperRight =
      -((coarseStarredBlockMatrixInv U a).upperRight) := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.upperRight
      (coarseStarredBlockMatrixInv_adjointCoeffField_of_exists (U := U) (a := a) hex)

theorem coarseStarredBlockMatrixInv_lowerLeft_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    (coarseStarredBlockMatrixInv U (adjointCoeffField a)).lowerLeft =
      -((coarseStarredBlockMatrixInv U a).lowerLeft) := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.lowerLeft
      (coarseStarredBlockMatrixInv_adjointCoeffField_of_exists (U := U) (a := a) hex)

theorem coarseStarredBlockMatrixInv_lowerRight_adjointCoeffField_of_exists {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar) :
    (coarseStarredBlockMatrixInv U (adjointCoeffField a)).lowerRight =
      (coarseStarredBlockMatrixInv U a).lowerRight := by
  simpa [blockMatFlipFlux] using
    congrArg BlockMat.lowerRight
      (coarseStarredBlockMatrixInv_adjointCoeffField_of_exists (U := U) (a := a) hex)

/-- Generic-domain note-facing transpose compatibility for the canonical coarse
block matrix `\mathbf A(U; a)` packaged from recovery data and ellipticity. -/
theorem coarseBlockMatrix_adjointCoeffField_eq_blockMatFlipFlux_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    coarseBlockMatrix U (Homogenization.adjointCoeffField a) =
      blockMatFlipFlux (coarseBlockMatrix U a) := by
  exact coarseBlockMatrix_adjointCoeffField_of_exists (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

/-- Generic-domain note-facing transpose compatibility for the upper-left block
of `\mathbf A(U; a)` packaged from recovery data and ellipticity. -/
theorem coarseBlockMatrix_upperLeft_adjointCoeffField_eq_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (coarseBlockMatrix U (adjointCoeffField a)).upperLeft =
      (coarseBlockMatrix U a).upperLeft := by
  exact coarseBlockMatrix_upperLeft_adjointCoeffField_of_exists (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

/-- Generic-domain note-facing transpose compatibility for the upper-right block
of `\mathbf A(U; a)` packaged from recovery data and ellipticity. -/
theorem coarseBlockMatrix_upperRight_adjointCoeffField_of_exists_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (coarseBlockMatrix U (adjointCoeffField a)).upperRight =
      -((coarseBlockMatrix U a).upperRight) := by
  exact coarseBlockMatrix_upperRight_adjointCoeffField_of_exists (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

/-- Generic-domain note-facing transpose compatibility for the lower-left block
of `\mathbf A(U; a)` packaged from recovery data and ellipticity. -/
theorem coarseBlockMatrix_lowerLeft_adjointCoeffField_of_exists_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (coarseBlockMatrix U (adjointCoeffField a)).lowerLeft =
      -((coarseBlockMatrix U a).lowerLeft) := by
  exact coarseBlockMatrix_lowerLeft_adjointCoeffField_of_exists (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

/-- Generic-domain note-facing transpose compatibility for the lower-right block
of `\mathbf A(U; a)` packaged from recovery data and ellipticity. -/
theorem coarseBlockMatrix_lowerRight_adjointCoeffField_eq_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (coarseBlockMatrix U (adjointCoeffField a)).lowerRight =
      (coarseBlockMatrix U a).lowerRight := by
  exact coarseBlockMatrix_lowerRight_adjointCoeffField_of_exists (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

/-- Generic-domain note-facing transpose compatibility for the canonical
starred inverse block matrix `\mathbf A_*^{-1}(U; a)` packaged from recovery
data and ellipticity. -/
theorem coarseStarredBlockMatrixInv_adjointCoeffField_of_exists_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    coarseStarredBlockMatrixInv U (adjointCoeffField a) =
      blockMatFlipFlux (coarseStarredBlockMatrixInv U a) := by
  exact coarseStarredBlockMatrixInv_adjointCoeffField_of_exists
    (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

/-- Generic-domain note-facing transpose compatibility for the upper-left block
of `\mathbf A_*^{-1}(U; a)` packaged from recovery data and ellipticity. -/
theorem coarseStarredBlockMatrixInv_upperLeft_adjointCoeffField_eq_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (coarseStarredBlockMatrixInv U (adjointCoeffField a)).upperLeft =
      (coarseStarredBlockMatrixInv U a).upperLeft := by
  exact coarseStarredBlockMatrixInv_upperLeft_adjointCoeffField_of_exists (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

/-- Generic-domain note-facing transpose compatibility for the upper-right
block of `\mathbf A_*^{-1}(U; a)` packaged from recovery data and ellipticity. -/
theorem coarseStarredBlockMatrixInv_upperRight_adjointCoeffField_of_exists_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (coarseStarredBlockMatrixInv U (adjointCoeffField a)).upperRight =
      -((coarseStarredBlockMatrixInv U a).upperRight) := by
  exact coarseStarredBlockMatrixInv_upperRight_adjointCoeffField_of_exists (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

/-- Generic-domain note-facing transpose compatibility for the lower-left block
of `\mathbf A_*^{-1}(U; a)` packaged from recovery data and ellipticity. -/
theorem coarseStarredBlockMatrixInv_lowerLeft_adjointCoeffField_of_exists_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (coarseStarredBlockMatrixInv U (adjointCoeffField a)).lowerLeft =
      -((coarseStarredBlockMatrixInv U a).lowerLeft) := by
  exact coarseStarredBlockMatrixInv_lowerLeft_adjointCoeffField_of_exists (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

/-- Generic-domain note-facing transpose compatibility for the lower-right
block of `\mathbf A_*^{-1}(U; a)` packaged from recovery data and ellipticity. -/
theorem coarseStarredBlockMatrixInv_lowerRight_adjointCoeffField_eq_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (coarseStarredBlockMatrixInv U (adjointCoeffField a)).lowerRight =
      (coarseStarredBlockMatrixInv U a).lowerRight := by
  exact coarseStarredBlockMatrixInv_lowerRight_adjointCoeffField_of_exists (U := U) (a := a)
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) hEll hvol compat)

theorem sigmaStarInvCoarse_adjointCoeffField_eq_of_isSigmaStarCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar) :
    sigmaStarInvCoarse U (adjointCoeffField a) = sigmaStarInvCoarse U a := by
  rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hSAdj,
    sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]

/-- Note-facing transpose compatibility for `\sigma_*^{-1}(U; a)` from primal
and adjoint `\sigma_*` witness data. -/
theorem sigmaStarInvCoarse_adjointCoeffField_eq_of_isSigmaStarData
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar) :
    sigmaStarInvCoarse U (adjointCoeffField a) = sigmaStarInvCoarse U a :=
  sigmaStarInvCoarse_adjointCoeffField_eq_of_isSigmaStarCoarse
    (U := U) (a := a) hS hSAdj

theorem sigmaStarCoarse_adjointCoeffField_eq_of_isSigmaStarCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSAdj : IsSigmaStarCoarse U (adjointCoeffField a) sigmaStar)
    (hdet : IsUnit sigmaStar.det) :
    sigmaStarCoarse U (adjointCoeffField a) = sigmaStarCoarse U a := by
  rw [eq_sigmaStarCoarse_of_isSigmaStarCoarse hSAdj hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet]

/-- If the coefficient field is self-adjoint, then the lower-left block of the
canonical coarse block matrix vanishes. -/
theorem coarseBlockMatrix_lowerLeft_eq_zero_of_adjointCoeffField_eq_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (hAdj : adjointCoeffField a = a) :
    (coarseBlockMatrix U a).lowerLeft = 0 := by
  have hLower :
      (coarseBlockMatrix U a).lowerLeft = -((coarseBlockMatrix U a).lowerLeft) := by
    simpa [hAdj] using
      coarseBlockMatrix_lowerLeft_adjointCoeffField_of_exists_of_isEllipticFieldOn
        (U := U) (a := a) R hEll hvol compat
  ext i j
  have hij : (coarseBlockMatrix U a).lowerLeft i j = -((coarseBlockMatrix U a).lowerLeft i j) := by
    exact congrFun (congrFun hLower i) j
  simpa using (CharZero.eq_neg_self_iff.mp hij)

/-- If the coefficient field is self-adjoint, then the upper-right block of the
canonical coarse block matrix vanishes. -/
theorem coarseBlockMatrix_upperRight_eq_zero_of_adjointCoeffField_eq_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    (hAdj : adjointCoeffField a = a) :
    (coarseBlockMatrix U a).upperRight = 0 := by
  have hUpper :
      (coarseBlockMatrix U a).upperRight = -((coarseBlockMatrix U a).upperRight) := by
    simpa [hAdj] using
      coarseBlockMatrix_upperRight_adjointCoeffField_of_exists_of_isEllipticFieldOn
        (U := U) (a := a) R hEll hvol compat
  ext i j
  have hij : (coarseBlockMatrix U a).upperRight i j = -((coarseBlockMatrix U a).upperRight i j) := by
    exact congrFun (congrFun hUpper i) j
  simpa using (CharZero.eq_neg_self_iff.mp hij)


end

end Homogenization
