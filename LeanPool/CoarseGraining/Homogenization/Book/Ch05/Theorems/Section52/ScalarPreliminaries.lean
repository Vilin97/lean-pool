/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.P4Integrability

/-! # Scalar Preliminaries -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: ScalarPreliminaries

Scalar monotonicity, response identities, and tau nonnegativity.
-/

/-- Scalar contrast monotonicity in Ch5 notation.  The only inputs are the
note-level integrability facts used to take expectations. -/
theorem thetaAtScale_mono_of_integrable_diagonalBlockNorms
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {n m : ℤ} (hn_nonneg : 0 ≤ n) (hnm : n ≤ m)
    (hParentBInt :
      Integrable (fun a : RegCoeffField d => coarseBBlockNorm (originCube d m) a) P)
    (hParentStarInt :
      Integrable
        (fun a : RegCoeffField d => coarseSigmaStarInvBlockNorm (originCube d m) a) P)
    (hDescBInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (fun a : RegCoeffField d => coarseBBlockNorm R a) P)
    (hDescStarInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (fun a : RegCoeffField d => coarseSigmaStarInvBlockNorm R a) P)
    (hChildBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P) :
    thetaAtScale hP hStruct m ≤
      thetaAtScale hP hStruct n := by
  have hParentInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d m)) P :=
    hP.integrable_coarseFullBlockMatrixAtCube_of_integrable_diagonalBlockNorms
      (originCube d m) hParentBInt hParentStarInt
  have hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact hP.integrable_coarseFullBlockMatrixAtCube_of_integrable_diagonalBlockNorms
      R (hDescBInt R hR) (hDescStarInt R hR)
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  let hPrim_m := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct m
  let hPrim_n := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n
  have hStar_m_nonneg : 0 ≤ hPrim_m.barSigmaStarInv :=
    (Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube hP
      hPrim_m hParentInt).le
  have hB_n_nonneg : 0 ≤ hPrim_n.barB :=
    Ch04.RestrictionLawCarrier.Internal.barB_nonneg_of_integrable_coarseFullBlockMatrixAtCube hP
      hPrim_n hChildBlockInt
  simpa [thetaAtScale, scalarization, hPrim_m, hPrim_n,
    Ch04.Internal.thetaAtScale_eq_scalarization_contrast] using
    Ch04.RestrictionLawCarrier.Internal.scalar_contrast_le_of_primitive_of_integrable_coarseFullBlockMatrixAtCube hP
      hStruct.stationary hn_nonneg hnm scalarization hPrim_m hPrim_n
      hParentInt hDescInt hStar_m_nonneg hB_n_nonneg

/-- Scalar contrast monotonicity in Ch5 notation, with full coarse-block
integrability as the only analytic input. -/
theorem thetaAtScale_mono_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {n m : ℤ} (hn_nonneg : 0 ≤ n) (hnm : n ≤ m)
    (hParentBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d m)) P)
    (hChildBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P)
    (hDescBlockInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P) :
    thetaAtScale hP hStruct m ≤
      thetaAtScale hP hStruct n := by
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  let hPrim_m := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct m
  let hPrim_n := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n
  have hStar_m_nonneg : 0 ≤ hPrim_m.barSigmaStarInv :=
    (Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube hP
      hPrim_m hParentBlockInt).le
  have hB_n_nonneg : 0 ≤ hPrim_n.barB :=
    Ch04.RestrictionLawCarrier.Internal.barB_nonneg_of_integrable_coarseFullBlockMatrixAtCube hP
      hPrim_n hChildBlockInt
  simpa [thetaAtScale, scalarization, hPrim_m, hPrim_n,
    Ch04.Internal.thetaAtScale_eq_scalarization_contrast] using
    Ch04.RestrictionLawCarrier.Internal.scalar_contrast_le_of_primitive_of_integrable_coarseFullBlockMatrixAtCube hP
      hStruct.stationary hn_nonneg hnm scalarization hPrim_m hPrim_n
      hParentBlockInt hDescBlockInt hStar_m_nonneg hB_n_nonneg

theorem tauAtScale_nonneg_of_integrable_restrictionResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k n : ℤ} (hk_nonneg : 0 ≤ k) (hkn : k ≤ n)
    (p q : Vec d)
    (hParentInt :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q) P)
    (hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d n) k →
        Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    0 ≤ tauAtScale P n k p q := by
  have hle :
      Ch04.annealedResponseJAtScale P n p q ≤
        Ch04.annealedResponseJAtScale P k p q :=
    hP.annealedResponseJAtScale_le hstat hk_nonneg hkn p q hParentInt hDescInt
  dsimp [tauAtScale]
  linarith

/-- Nonnegativity of the annealed additivity defect, with response
integrability derived from full coarse-block integrability. -/
theorem tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k n : ℤ} (hk_nonneg : 0 ≤ k) (hkn : k ≤ n)
    (p q : Vec d)
    (hParentBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P)
    (hDescBlockInt :
      ∀ R, R ∈ descendantsAtScale (originCube d n) k →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P) :
    0 ≤ tauAtScale P n k p q := by
  exact tauAtScale_nonneg_of_integrable_restrictionResponseJObservableCubeSet hP hstat
    hk_nonneg hkn p q
    (hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (originCube d n) p q hParentBlockInt)
    (fun R hR =>
      hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        R p q (hDescBlockInt R hR))

private theorem annealedResponseJAtScale_eq_expectedJScalarFormula_of_primitive
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P) {n : ℤ}
    (primitive : Ch04.Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (p q : Vec d)
    (hBlock : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P) :
    Ch04.annealedResponseJAtScale P n p q =
      expectedJScalarFormula hP hStruct n p q := by
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  have hLowerLeftZero :
      (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).lowerLeft = 0 := by
    have h := primitive.sigmaStarInvKappaMean_eq_zero
    simpa [Ch04.annealedSigmaStarInvKappaMeanAtScale,
      Ch04.annealedSigmaStarInvKappaMean] using congrArg Neg.neg h
  have hStar :
      (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).lowerRight =
        primitive.barSigmaStarInv • (1 : Mat d) := by
    simpa [Ch04.annealedSigmaStarInvAtScale, Ch04.annealedSigmaStarInv] using
      primitive.sigmaStarInv_eq
  have hB :
      (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).upperLeft =
        primitive.barB • (1 : Mat d) := by
    simpa [Ch04.annealedBAtScale, Ch04.annealedB] using primitive.b_eq
  have hOneQ : matVecMul (1 : Mat d) q = q := by
    change (1 : Matrix (Fin d) (Fin d) ℝ).mulVec q = q
    exact Matrix.one_mulVec q
  have hOneP : matVecMul (1 : Mat d) p = p := by
    change (1 : Matrix (Fin d) (Fin d) ℝ).mulVec p = p
    exact Matrix.one_mulVec p
  have hZeroP : matVecMul (0 : Mat d) p = 0 := by
    funext i
    simp [matVecMul]
  have hSource :=
    hP.integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
      (originCube d n) p q hBlock
  calc
    Ch04.annealedResponseJAtScale P n p q =
        ∫ a, Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q a ∂P := rfl
    _ = (1 / 2 : ℝ) * vecDot q
          (matVecMul (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).upperLeft p) :=
      hSource
    _ = expectedJScalarFormula hP hStruct n p q := by
        rw [hLowerLeftZero, hStar, hB]
        simp [expectedJScalarFormula,
          Ch04.RestrictionLawCarrier.barSigmaAtScale, Ch04.RestrictionLawCarrier.barSigmaStarAtScale,
          Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigma_eq_barB scalarization primitive,
          Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigmaStar_eq_inv_barSigmaStarInv
            scalarization primitive,
          smul_matVecMul, hOneQ, hOneP, hZeroP, vecDot_smul_right, vecDot_zero_right]

private theorem tauAtScale_eq_tauScalarFormula_of_primitive
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P) {n k : ℤ}
    (primitive_n : Ch04.Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (primitive_k : Ch04.Internal.AnnealedPrimitiveScalarizationData (d := d) P k)
    (p q : Vec d)
    (hBlock_n : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P)
    (hBlock_k : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d k)) P) :
    tauAtScale P n k p q =
      tauScalarFormula hP hStruct n k p q := by
  calc
    tauAtScale P n k p q =
        Ch04.annealedResponseJAtScale P k p q -
          Ch04.annealedResponseJAtScale P n p q := rfl
    _ =
        expectedJScalarFormula hP hStruct k p q -
          expectedJScalarFormula hP hStruct n p q := by
        rw [annealedResponseJAtScale_eq_expectedJScalarFormula_of_primitive
            hP hStruct primitive_k p q hBlock_k,
          annealedResponseJAtScale_eq_expectedJScalarFormula_of_primitive
            hP hStruct primitive_n p q hBlock_n]
    _ = tauScalarFormula hP hStruct n k p q := by
        simp [expectedJScalarFormula, tauScalarFormula, vecDot_smul_right]
        ring_nf

/-- Note-facing scalar response formula under the Chapter 4 law and structural
assumptions. -/
theorem annealedResponseJAtScale_eq_expectedJScalarFormula
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (n : ℤ) (p q : Vec d)
    (hBlock : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P) :
    Ch04.annealedResponseJAtScale P n p q =
      expectedJScalarFormula hP hStruct n p q :=
  annealedResponseJAtScale_eq_expectedJScalarFormula_of_primitive hP
    hStruct
    (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n) p q hBlock

/-- Note-facing scalar formula for `τ_{n,k}`. -/
theorem tauAtScale_eq_tauScalarFormula
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (n k : ℤ) (p q : Vec d)
    (hBlock_n : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P)
    (hBlock_k : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d k)) P) :
    tauAtScale P n k p q =
      tauScalarFormula hP hStruct n k p q :=
  tauAtScale_eq_tauScalarFormula_of_primitive hP
    hStruct
    (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n)
    (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct k)
    p q hBlock_n hBlock_k

/-- Manuscript Lemma `l.scalar.preliminaries.homogenization.scale`.

All integrability needed for scalar monotonicity, response identities, and
moment-factor comparison is derived internally from the law carrier, structural
law, and `(P4)` hypotheses. -/
theorem scalarPreliminaries_homogenizationScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (n m k : ℕ) (hnm : n ≤ m) (hkn : k ≤ n) (p q : Vec d) :
    1 ≤ thetaAtScale hP hStruct (m : ℤ) ∧
      thetaAtScale hP hStruct (m : ℤ) ≤
        thetaAtScale hP hStruct (n : ℤ) ∧
      thetaAtScale hP hStruct (n : ℤ) ≤
        widetildeThetaAtScale P (n : ℤ) hP4 ∧
      Ch04.annealedResponseJAtScale P (n : ℤ) p q =
        expectedJScalarFormula hP hStruct (n : ℤ) p q ∧
      tauAtScale P (n : ℤ) (k : ℤ) p q =
        tauScalarFormula hP hStruct (n : ℤ) (k : ℤ) p q ∧
      0 ≤ tauAtScale P (n : ℤ) (k : ℤ) p q := by
  have hn_nonneg : 0 ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hk_nonneg : 0 ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hnm_int : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast hnm
  have hkn_int : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hkn
  have hOriginBlockInt :
      ∀ l : ℕ,
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (l : ℤ))) P :=
    fun l => originBlockIntegrableAtScale_from_P4 hP hStruct hP4 l
  have hUpperPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (Ch04.LambdaSqCoeffField (originCube d (l : ℤ)) hP4.sUpper (.finite 1) a) ^
              hP4.xi) P :=
    fun l => upperFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l
  have hLowerPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((Ch04.lambdaSqCoeffField (originCube d (l : ℤ)) hP4.sLower (.finite 1) a)⁻¹) ^
              hP4.xi) P :=
    fun l => lowerFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l
  have hDescBlockInt_mn :
      ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hStruct.stationary hn_nonneg hnm_int hR (hOriginBlockInt n)
  have hDescBlockInt_nk :
      ∀ R, R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ) →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hStruct.stationary hk_nonneg hkn_int hR (hOriginBlockInt k)
  constructor
  · exact
      one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
        hP hStruct (m : ℤ) (hOriginBlockInt m)
  constructor
  · exact
      thetaAtScale_mono_of_integrable_coarseFullBlockMatrixAtCube
        hP hStruct hn_nonneg hnm_int
        (hOriginBlockInt m) (hOriginBlockInt n) hDescBlockInt_mn
  constructor
  · exact
      thetaAtScale_le_widetildeThetaAtScale_of_integrable_factor_observables
        hP hStruct hP4 hOriginBlockInt hUpperPowInt hLowerPowInt n
  constructor
  · exact
      annealedResponseJAtScale_eq_expectedJScalarFormula
        hP hStruct (n : ℤ) p q (hOriginBlockInt n)
  constructor
  · exact
      tauAtScale_eq_tauScalarFormula
        hP hStruct (n : ℤ) (k : ℤ) p q (hOriginBlockInt n) (hOriginBlockInt k)
  · exact
      tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
        hP hStruct.stationary hk_nonneg hkn_int p q
        (hOriginBlockInt n) hDescBlockInt_nk

end

end Section52
end Ch05
end Book
end Homogenization
