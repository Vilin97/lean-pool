/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.CoarseAverages
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.P4Integrability

/-! # Fluctuation Integrability -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem memLp_two_of_nonneg_pow_integrable
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} {X : RegCoeffField d → ℝ}
    (hξ : 2 ≤ ξ) (hX_meas : AEMeasurable X P)
    (hX_nonneg : ∀ᵐ a ∂P, 0 ≤ X a)
    (hXpow_int : Integrable (fun a => X a ^ ξ) P) :
    MemLp X (2 : ENNReal) P := by
  have hξ_ne : ξ ≠ 0 := by omega
  have hnormpow_int : Integrable (fun a => ‖X a‖ ^ ξ) P := by
    refine hXpow_int.congr ?_
    filter_upwards [hX_nonneg] with a ha
    simp [Real.norm_eq_abs, abs_of_nonneg ha]
  have hmem_ξ : MemLp X (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hX_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa using hnormpow_int
  exact hmem_ξ.mono_exponent (by exact_mod_cast hξ)

private theorem integrable_abs_sq_of_ae_abs_le_nonneg_memLp_two
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d}
    {X Y : RegCoeffField d → ℝ}
    (hX_meas : AEMeasurable X P)
    (hY_nonneg : ∀ a, 0 ≤ Y a)
    (hXY : ∀ᵐ a ∂P, |X a| ≤ Y a)
    (hY_mem : MemLp Y (2 : ENNReal) P) :
    Integrable (fun a => |X a| ^ 2) P := by
  have hY_int : Integrable (fun a => |Y a| ^ 2) P := by
    simpa [Real.norm_eq_abs] using hY_mem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  refine Integrable.mono' hY_int
    ((hX_meas.norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [hXY] with a ha
  have hpow : |X a| ^ 2 ≤ Y a ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg (X a)) ha 2
  have hleft : ‖|X a| ^ 2‖ = |X a| ^ 2 := by
    simp [Real.norm_eq_abs]
  have hright : |Y a| ^ 2 = Y a ^ 2 := by
    rw [abs_of_nonneg (hY_nonneg a)]
  simpa [hleft, hright] using hpow

private theorem blockMatVecMul_sub'
    {d : ℕ} (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  have hneg : blockMatVecMul A (-Y) = -blockMatVecMul A Y := by
    simpa using blockMatVecMul_smul A (-1) Y
  rw [sub_eq_add_neg, blockMatVecMul_add, hneg]
  rfl

private theorem blockVecDot_sub_left'
    {d : ℕ} (X Y Z : BlockVec d) :
    blockVecDot (X - Y) Z = blockVecDot X Z - blockVecDot Y Z := by
  have hneg : blockVecDot (-Y) Z = -blockVecDot Y Z := by
    simpa using blockVecDot_smul_left (-1) Y Z
  rw [sub_eq_add_neg, blockVecDot_add_left, hneg]
  rfl

private theorem blockBasis_sub_pairing'
    {d : ℕ} (A : BlockMat d) (α β : BlockCoord d) :
    blockVecDot (blockBasis α - blockBasis β)
        (blockMatVecMul A (blockBasis α - blockBasis β)) =
      blockMatEntry A α α - blockMatEntry A α β -
        blockMatEntry A β α + blockMatEntry A β β := by
  rw [blockMatVecMul_sub', blockVecDot_sub_left']
  rw [blockVecDot_sub_right]
  rw [blockVecDot_sub_right]
  rw [blockBasis_pairing, blockBasis_pairing, blockBasis_pairing, blockBasis_pairing]
  ring

private theorem aemeasurable_blockMatEntry_coarseBlockMatrix_cubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q : TriadicCube d)
    (α β : BlockCoord d) :
    AEMeasurable
      (fun a : RegCoeffField d => blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) α β) P := by
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [blockMatEntry] using
            hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j
      | inr j =>
          simpa [blockMatEntry] using
            hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet Q i j
  | inr i =>
      cases β with
      | inl j =>
          simpa [blockMatEntry] using
            hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j
      | inr j =>
          simpa [blockMatEntry] using
            hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j

private theorem blockBasis_add_ne_zero'
    {d : ℕ} {α β : BlockCoord d} (hαβ : α ≠ β) :
    blockBasis α + blockBasis β ≠ (0 : BlockVec d) := by
  intro hzero
  have hcoord := congrArg (fun X : BlockVec d => toFullBlockVec X α) hzero
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord
      | inr j =>
          simp [blockBasis, toFullBlockVec] at hcoord
  | inr i =>
      cases β with
      | inl j =>
          simp [blockBasis, toFullBlockVec] at hcoord
      | inr j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord

private theorem blockBasis_sub_ne_zero'
    {d : ℕ} {α β : BlockCoord d} (hαβ : α ≠ β) :
    blockBasis α - blockBasis β ≠ (0 : BlockVec d) := by
  intro hzero
  have hcoord := congrArg (fun X : BlockVec d => toFullBlockVec X α) hzero
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord
      | inr j =>
          simp [blockBasis, toFullBlockVec] at hcoord
  | inr i =>
      cases β with
      | inl j =>
          simp [blockBasis, toFullBlockVec] at hcoord
      | inr j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord

private theorem abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef'
    {d : ℕ} {A : BlockMat d} (hSymm : IsSymmetricBlockMat A)
    (hPos : Ch02.BlockPosDef A) {α β : BlockCoord d} (hαβ : α ≠ β) :
    |blockMatEntry A α β| ≤
      (1 / 2 : ℝ) * (blockMatEntry A α α + blockMatEntry A β β) := by
  have hplus_pos :=
    hPos (blockBasis α + blockBasis β) (blockBasis_add_ne_zero' hαβ)
  have hminus_pos :=
    hPos (blockBasis α - blockBasis β) (blockBasis_sub_ne_zero' hαβ)
  have hplus :
      0 <
        blockMatEntry A α α + blockMatEntry A α β +
          blockMatEntry A β α + blockMatEntry A β β := by
    simpa [blockBasis_sum_pairing] using hplus_pos
  have hminus :
      0 <
        blockMatEntry A α α - blockMatEntry A α β -
          blockMatEntry A β α + blockMatEntry A β β := by
    simpa [blockBasis_sub_pairing'] using hminus_pos
  have hsymm : blockMatEntry A β α = blockMatEntry A α β := (hSymm α β).symm
  rw [abs_le]
  constructor <;> nlinarith

private theorem blockMatEntry_abs_le_factor_sum_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q : TriadicCube d)
    {sUpper sLower : ℝ} (hsUpper : 0 < sUpper) (hsLower : 0 < sLower)
    (α β : BlockCoord d) :
    (fun a : RegCoeffField d =>
        |blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) α β|) ≤ᵐ[P]
      fun a =>
        Ch04.LambdaSqCoeffField Q sUpper (.finite 1) a +
          (Ch04.lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹ := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hSymm : IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) := by
    rw [hEq]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hPos : Ch02.BlockPosDef (coarseBlockMatrix (cubeSet Q) a.toFun) := by
    rw [hEq]
    exact
      (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q)
        (F.coeffOn Q)).block_matrix_posDef
  have hUpperEntry : ∀ i j : Fin d,
      |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j| ≤
        Ch04.LambdaSqCoeffField Q sUpper (.finite 1) a := by
    intro i j
    calc
      |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j|
          = |(Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).upperLeft i j| := by
            rw [hEq]
      _ ≤ Ch02.coarseBMatrixNorm Q F := by
            simpa [Ch02.coarseBMatrixNorm, Ch02.matrixNorm_eq_matrixOperatorNorm] using
              Ch02.abs_entry_le_matrixOperatorNorm
                ((Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).upperLeft) i j
      _ ≤ Ch02.LambdaSq Q sUpper (.finite 1) F :=
            Ch02.oneCube_b_le_LambdaSq_finite Q F hsUpper
              (by norm_num : (1 : ℝ) ≤ 1)
      _ = Ch04.LambdaSqCoeffField Q sUpper (.finite 1) a := by
          simp [Ch04.LambdaSqCoeffField, ha, F]
  have hLowerEntry : ∀ i j : Fin d,
      |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j| ≤
        (Ch04.lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹ := by
    intro i j
    calc
      |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j|
          = |(Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).lowerRight i j| := by
            rw [hEq]
      _ ≤ Ch02.coarseSigmaStarInvMatrixNorm Q F := by
            simpa [Ch02.coarseSigmaStarInvMatrixNorm, Ch02.matrixNorm_eq_matrixOperatorNorm] using
              Ch02.abs_entry_le_matrixOperatorNorm
                ((Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).lowerRight) i j
      _ ≤ (Ch02.lambdaSq Q sLower (.finite 1) F)⁻¹ :=
            Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q F hsLower
              (by norm_num : (1 : ℝ) ≤ 1)
      _ = (Ch04.lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹ := by
          simp [Ch04.lambdaSqCoeffField, ha, F]
  have hX_nonneg :
      0 ≤ Ch04.LambdaSqCoeffField Q sUpper (.finite 1) a :=
    Ch04.LambdaSqCoeffField_finite_nonneg Q a hsUpper (by norm_num : (1 : ℝ) ≤ 1)
  have hY_nonneg :
      0 ≤ (Ch04.lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹ :=
    inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg Q a hsLower (by norm_num : (1 : ℝ) ≤ 1))
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          exact (hUpperEntry i j).trans (by linarith)
      | inr j =>
          have hcross :
              |blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl i) (Sum.inr j)| ≤
                (1 / 2 : ℝ) *
                  (blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl i) (Sum.inl i) +
                    blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr j) (Sum.inr j)) :=
            abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef' hSymm hPos
              (by intro h; cases h)
          have hUL :
              blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl i) (Sum.inl i) ≤
                Ch04.LambdaSqCoeffField Q sUpper (.finite 1) a := by
            exact (le_abs_self _).trans (by simpa [blockMatEntry] using hUpperEntry i i)
          have hLR :
              blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr j) (Sum.inr j) ≤
                (Ch04.lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹ := by
            exact (le_abs_self _).trans (by simpa [blockMatEntry] using hLowerEntry j j)
          linarith
  | inr i =>
      cases β with
      | inl j =>
          have hcross :
              |blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr i) (Sum.inl j)| ≤
                (1 / 2 : ℝ) *
                  (blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr i) (Sum.inr i) +
                    blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl j) (Sum.inl j)) :=
            abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef' hSymm hPos
              (by intro h; cases h)
          have hLR :
              blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr i) (Sum.inr i) ≤
                (Ch04.lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹ := by
            exact (le_abs_self _).trans (by simpa [blockMatEntry] using hLowerEntry i i)
          have hUL :
              blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl j) (Sum.inl j) ≤
                Ch04.LambdaSqCoeffField Q sUpper (.finite 1) a := by
            exact (le_abs_self _).trans (by simpa [blockMatEntry] using hUpperEntry j j)
          linarith
      | inr j =>
          exact (hLowerEntry i j).trans (by linarith)

private theorem memLp_two_blockMatEntry_coarseBlockMatrix_cubeSet_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (n : ℕ) (α β : BlockCoord d) :
    MemLp
      (fun a : RegCoeffField d =>
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ))) a.toFun) α β)
      (2 : ENNReal) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d (n : ℤ)
  let X : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a
  let Y : RegCoeffField d → ℝ :=
    fun a => (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹
  have hX_meas : AEMeasurable X P := by
    simpa [X, Q] using
      hP.aemeasurable_LambdaSqCoeffField_finite_one (originCube d (n : ℤ)) hP4.sUpper_pos
  have hY_meas : AEMeasurable Y P := by
    exact (hP.aemeasurable_lambdaSqCoeffField_finite_one
      (originCube d (n : ℤ)) hP4.sLower_pos).inv
  have hX_nonneg : ∀ᵐ a ∂P, 0 ≤ X a :=
    Filter.Eventually.of_forall fun a =>
      Ch04.LambdaSqCoeffField_finite_nonneg Q a hP4.sUpper_pos
        (by norm_num : (1 : ℝ) ≤ 1)
  have hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a :=
    Filter.Eventually.of_forall fun a =>
      inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg Q a hP4.sLower_pos
          (by norm_num : (1 : ℝ) ≤ 1))
  have hX_mem2 : MemLp X (2 : ENNReal) P :=
    memLp_two_of_nonneg_pow_integrable hP4.two_le_xi hX_meas hX_nonneg
      (by
        simpa [X, Q] using
          Section52.upperFactorPowerIntegrableAtScale_from_P4
            hP hStruct hP4 n)
  have hY_mem2 : MemLp Y (2 : ENNReal) P :=
    memLp_two_of_nonneg_pow_integrable hP4.two_le_xi hY_meas hY_nonneg
      (by
        simpa [Y, Q] using
          Section52.lowerFactorPowerIntegrableAtScale_from_P4
            hP hStruct hP4 n)
  have hXY_mem2 : MemLp (fun a => X a + Y a) (2 : ENNReal) P :=
    hX_mem2.add hY_mem2
  have hEntry_meas :
      AEMeasurable
        (fun a : RegCoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) α β) P := by
    simpa [Q] using
      aemeasurable_blockMatEntry_coarseBlockMatrix_cubeSet
        hP (originCube d (n : ℤ)) α β
  have hXY_nonneg : ∀ a, 0 ≤ X a + Y a := by
    intro a
    exact add_nonneg
      (Ch04.LambdaSqCoeffField_finite_nonneg Q a hP4.sUpper_pos
        (by norm_num : (1 : ℝ) ≤ 1))
      (inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg Q a hP4.sLower_pos
          (by norm_num : (1 : ℝ) ≤ 1)))
  have hEntry_bound :
      ∀ᵐ a ∂P,
        |blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) α β| ≤
          X a + Y a := by
    simpa [X, Y, Q] using!
      blockMatEntry_abs_le_factor_sum_ae
        hP (originCube d (n : ℤ)) hP4.sUpper_pos hP4.sLower_pos α β
  have hEntry_abs_sq :
      Integrable
        (fun a : RegCoeffField d =>
          |blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) α β| ^ 2) P :=
    integrable_abs_sq_of_ae_abs_le_nonneg_memLp_two
      hEntry_meas hXY_nonneg hEntry_bound hXY_mem2
  rw [← MeasureTheory.integrable_norm_rpow_iff hEntry_meas.aestronglyMeasurable
    (by norm_num : (2 : ENNReal) ≠ 0) (by simp)]
  simpa [Real.norm_eq_abs] using hEntry_abs_sq

theorem memLp_two_restrictionResponseJObservableCubeSet_originCube_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ) (p q : Vec d) :
    MemLp
      (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p q)
      (2 : ENNReal) P := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d (k : ℤ)
  let M : RegCoeffField d → BlockMat d := fun a => coarseBlockMatrix (cubeSet Q) a.toFun
  let quad : RegCoeffField d → ℝ :=
    fun a =>
      (1 / 2 : ℝ) * vecDot q (matVecMul (M a).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (M a).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (M a).upperLeft p)
  have hLR_entry :
      ∀ i j : Fin d,
        MemLp (fun a : RegCoeffField d => (M a).lowerRight i j)
          (2 : ENNReal) P := by
    intro i j
    simpa [M, Q, blockMatEntry] using
      memLp_two_blockMatEntry_coarseBlockMatrix_cubeSet_from_P4
        hP hStruct hP4 k (Sum.inr i) (Sum.inr j)
  have hLL_entry :
      ∀ i j : Fin d,
        MemLp (fun a : RegCoeffField d => (M a).lowerLeft i j)
          (2 : ENNReal) P := by
    intro i j
    simpa [M, Q, blockMatEntry] using
      memLp_two_blockMatEntry_coarseBlockMatrix_cubeSet_from_P4
        hP hStruct hP4 k (Sum.inr i) (Sum.inl j)
  have hUL_entry :
      ∀ i j : Fin d,
        MemLp (fun a : RegCoeffField d => (M a).upperLeft i j)
          (2 : ENNReal) P := by
    intro i j
    simpa [M, Q, blockMatEntry] using
      memLp_two_blockMatEntry_coarseBlockMatrix_cubeSet_from_P4
        hP hStruct hP4 k (Sum.inl i) (Sum.inl j)
  have hLR :
      MemLp (fun a : RegCoeffField d => vecDot q (matVecMul (M a).lowerRight q))
        (2 : ENNReal) P := by
    simp [vecDot, matVecMul]
    refine memLp_finsetSum (s := (Finset.univ : Finset (Fin d))) ?_
    intro i _hi
    have hinner :
        MemLp (fun a : RegCoeffField d => ∑ j : Fin d, (M a).lowerRight i j * q j)
          (2 : ENNReal) P := by
      refine memLp_finsetSum (s := (Finset.univ : Finset (Fin d))) ?_
      intro j _hj
      simpa [mul_comm] using (hLR_entry i j).const_mul (q j)
    exact hinner.const_mul (q i)
  have hLL :
      MemLp (fun a : RegCoeffField d => vecDot q (matVecMul (M a).lowerLeft p))
        (2 : ENNReal) P := by
    simp [vecDot, matVecMul]
    refine memLp_finsetSum (s := (Finset.univ : Finset (Fin d))) ?_
    intro i _hi
    have hinner :
        MemLp (fun a : RegCoeffField d => ∑ j : Fin d, (M a).lowerLeft i j * p j)
          (2 : ENNReal) P := by
      refine memLp_finsetSum (s := (Finset.univ : Finset (Fin d))) ?_
      intro j _hj
      simpa [mul_comm] using (hLL_entry i j).const_mul (p j)
    exact hinner.const_mul (q i)
  have hUL :
      MemLp (fun a : RegCoeffField d => vecDot p (matVecMul (M a).upperLeft p))
        (2 : ENNReal) P := by
    simp [vecDot, matVecMul]
    refine memLp_finsetSum (s := (Finset.univ : Finset (Fin d))) ?_
    intro i _hi
    have hinner :
        MemLp (fun a : RegCoeffField d => ∑ j : Fin d, (M a).upperLeft i j * p j)
          (2 : ENNReal) P := by
      refine memLp_finsetSum (s := (Finset.univ : Finset (Fin d))) ?_
      intro j _hj
      simpa [mul_comm] using (hUL_entry i j).const_mul (p j)
    exact hinner.const_mul (p i)
  have hquad :
      MemLp quad (2 : ENNReal) P := by
    simpa [quad] using!
      (((hLR.const_mul (1 / 2 : ℝ)).sub
          (memLp_const (c := vecDot p q) (μ := P) (p := (2 : ENNReal)))).sub hLL).add
        (hUL.const_mul (1 / 2 : ℝ))
  have hformula :
      (fun a : RegCoeffField d =>
        Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p q a) =ᵐ[P]
        quad := by
    simpa [quad, M, Q] using
      Ch04.restrictionResponseJObservableCubeSet_ae_eq_quadratic_coarseBlockMatrix_of_lawCarrier
        hP (originCube d (k : ℤ)) p q
  exact MemLp.ae_eq hformula.symm hquad

theorem memLp_two_restrictionResponseJObservableCubeSet_cubeSet_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale) (p q : Vec d) :
    MemLp (Ch04.restrictionResponseJObservableCubeSet R p q) (2 : ENNReal) P := by
  let n : ℕ := Int.toNat R.scale
  let z : Fin d → ℤ := Ch04.scaleTranslationShift R.scale R
  let X : RegCoeffField d → ℝ :=
    fun a => ResponseJ (cubeSet (originCube d R.scale)) p q a.toFun
  have hOrigin :
      MemLp X (2 : ENNReal) P := by
    have hbase :=
      memLp_two_restrictionResponseJObservableCubeSet_originCube_from_P4
        hP hStruct hP4 n p q
    have hn : ((n : ℕ) : ℤ) = R.scale := by
      simpa [n] using Int.toNat_of_nonneg hR_nonneg
    simpa [X, Ch04.restrictionResponseJObservableCubeSet, hn] using! hbase
  have hOrigin_map :
      MemLp X (2 : ENNReal) (Measure.map (translateReg (intVecToRealVec z)) P) := by
    simpa [hstat z] using hOrigin
  have hComp : MemLp (X ∘ translateReg (intVecToRealVec z)) (2 : ENNReal) P :=
    hOrigin_map.comp_of_map (measurable_translateReg (intVecToRealVec z)).aemeasurable
  have hshift :
      cubeSet R =
        translateSet (intVecToRealVec z) (cubeSet (originCube d R.scale)) := by
    simpa [z] using
      Ch04.cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  have hEq :
      Ch04.restrictionResponseJObservableCubeSet R p q =ᵐ[P] X ∘ translateReg (intVecToRealVec z) := by
    filter_upwards with a
    dsimp [X, Ch04.restrictionResponseJObservableCubeSet, Function.comp]
    rw [hshift, Ch04.translateReg_toFun]
    exact Ch04.responseJCubeSet_translation_covariant p q
      (cubeSet (originCube d R.scale)) z a.toFun
  exact MemLp.ae_eq hEq.symm hComp

theorem memLp_zeta_restrictionResponseJObservableCubeSet_cubeSet_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale) (p q : Vec d) :
    MemLp (Ch04.restrictionResponseJObservableCubeSet R p q)
      (ENNReal.ofReal (section53CoarseFluctuationZeta hP4)) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let ζ := section53CoarseFluctuationZeta hP4
  have hζ_le_two : ENNReal.ofReal ζ ≤ (2 : ENNReal) := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [ζ] using section53CoarseFluctuationZeta_le_two hP4)
  exact
    (memLp_two_restrictionResponseJObservableCubeSet_cubeSet_from_P4_of_stationary
      hP hstat hStruct hP4 R hR_nonneg p q).mono_exponent hζ_le_two

theorem memLp_zeta_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    (p q : Vec d) :
    MemLp
      (fun a : RegCoeffField d =>
        descendantsAverage (originCube d m) (Int.toNat (m - k))
          (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a))
      (ENNReal.ofReal (section53CoarseFluctuationZeta hP4)) P := by
  refine Ch04.memLp_descendantsAverage_restrictionResponseJObservableCubeSet ?_
  intro R hR
  have hRscaleMem : R ∈ descendantsAtScale (originCube d m) k := by
    simpa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm] using! hR
  have hRscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hRscaleMem
  exact
    memLp_zeta_restrictionResponseJObservableCubeSet_cubeSet_from_P4_of_stationary
      hP hstat hStruct hP4 R (by simpa [hRscale] using hk_nonneg) p q

private theorem restrictionResponseJObservableCubeSet_rpow_translation_covariant
    {d : ℕ} (ζ : ℝ) (p q : Vec d) :
    Ch04.IsRestrictionTranslationCovariant
      (fun U : Set (Vec d) => fun a : RegCoeffField d =>
        Real.rpow (ResponseJ U p q a.toFun) ζ) := by
  have hraw : IsTranslationCovariant
      (fun U : Set (Vec d) => fun a : CoeffField d =>
        Real.rpow (ResponseJ U p q a) ζ) := by
    intro U z a
    exact congrArg (fun x : ℝ => Real.rpow x ζ)
      (Ch04.responseJCubeSet_translation_covariant p q U z a)
  exact Ch04.isRestrictionTranslationCovariant_comp_toFun hraw

theorem integral_rpow_restrictionResponseJObservableCubeSet_cubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale)
    {ζ : ℝ} (hζ_nonneg : 0 ≤ ζ) (p q : Vec d) :
    ∫ a,
        Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ ∂P =
      ∫ a,
        Real.rpow
          (Ch04.restrictionResponseJObservableCubeSet (originCube d R.scale) p q a) ζ ∂P := by
  have hshift :=
    Ch04.cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  calc
    ∫ a, Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ ∂P
        =
      ∫ a, Real.rpow (ResponseJ (cubeSet R) p q a.toFun) ζ ∂P := by
        rfl
    _ =
      ∫ a,
        Real.rpow
          (ResponseJ
            (translateSet (intVecToRealVec (Ch04.scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale))) p q a) ζ ∂P := by
          rw [hshift]
    _ =
      ∫ a, Real.rpow (ResponseJ (cubeSet (originCube d R.scale)) p q a.toFun) ζ ∂P := by
        exact
          Ch04.integral_eq_of_isRestrictionTranslationCovariant_of_stationary_aestronglyMeasurable
            (P := P) hstat
            (U := cubeSet (originCube d R.scale))
            (by
              exact
                ((Real.continuous_rpow_const hζ_nonneg).measurable.comp_aemeasurable
                  (by
                    simpa [Ch04.restrictionResponseJObservableCubeSet] using!
                      hP.aemeasurable_restrictionResponseJObservableCubeSet
                        (originCube d R.scale) p q)).aestronglyMeasurable)
            (restrictionResponseJObservableCubeSet_rpow_translation_covariant ζ p q)
            (Ch04.scaleTranslationShift R.scale R)
    _ =
      ∫ a,
        Real.rpow
          (Ch04.restrictionResponseJObservableCubeSet (originCube d R.scale) p q a) ζ ∂P := by
        rfl

private theorem rpow_descendantsAverage_le_descendantsAverage_rpow
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) {ζ : ℝ}
    (hζ : 1 ≤ ζ) {F : TriadicCube d → ℝ}
    (hF_nonneg : ∀ R, R ∈ descendantsAtDepth Q j → 0 ≤ F R) :
    Real.rpow (descendantsAverage Q j F) ζ ≤
      descendantsAverage Q j (fun R => Real.rpow (F R) ζ) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let w : TriadicCube d → ℝ := fun _ => (D.card : ℝ)⁻¹
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_ne : ((D.card : ℝ) ≠ 0) := by
    exact_mod_cast Finset.card_ne_zero.mpr hD_nonempty
  have hcard_pos : 0 < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD_nonempty
  have hw_nonneg : ∀ R ∈ D, 0 ≤ w R := by
    intro R hR
    dsimp [w]
    exact inv_nonneg.mpr hcard_pos.le
  have hw_sum : ∑ R ∈ D, w R = 1 := by
    simp [w, Finset.sum_const, nsmul_eq_mul, hcard_ne]
  have hmem : ∀ R ∈ D, F R ∈ Set.Ici (0 : ℝ) := by
    intro R hR
    exact hF_nonneg R (by simpa [D] using hR)
  have hJensen :=
    (convexOn_rpow hζ).map_sum_le
      (t := D) (w := w) (p := F) hw_nonneg hw_sum hmem
  have hleft :
      (fun x : ℝ => x ^ ζ) (∑ R ∈ D, w R • F R) =
        Real.rpow (descendantsAverage Q j F) ζ := by
    congr 1
    simp only [descendantsAverage, D, w, smul_eq_mul]
    rw [Finset.mul_sum]
  have hright :
      (∑ R ∈ D, w R • (fun x : ℝ => x ^ ζ) (F R)) =
        descendantsAverage Q j (fun R => Real.rpow (F R) ζ) := by
    simp only [descendantsAverage, D, w, smul_eq_mul, Real.rpow_eq_pow]
    rw [Finset.mul_sum]
  calc
    Real.rpow (descendantsAverage Q j F) ζ
        = (fun x : ℝ => x ^ ζ) (∑ R ∈ D, w R • F R) := hleft.symm
    _ ≤ ∑ R ∈ D, w R • (fun x : ℝ => x ^ ζ) (F R) := hJensen
    _ = descendantsAverage Q j (fun R => Real.rpow (F R) ζ) := hright

theorem integral_rpow_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_le_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m) (p q : Vec d) :
    let ζ := section53CoarseFluctuationZeta hP4
    ∫ a,
        Real.rpow
          (descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)) ζ ∂P
      ≤
        ∫ a,
          Real.rpow
            (Ch04.restrictionResponseJObservableCubeSet (originCube d k) p q a) ζ ∂P := by
  dsimp only
  let : IsProbabilityMeasure P := hP.isProbability
  let ζ := section53CoarseFluctuationZeta hP4
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - k)
  let childAvg : RegCoeffField d → ℝ :=
    fun a =>
      descendantsAverage Q j
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)
  have hζ_pos : 0 < ζ := by
    simpa [ζ] using section53CoarseFluctuationZeta_pos hP4
  have hζ_one : 1 ≤ ζ := by
    exact (one_lt_section53CoarseFluctuationZeta hP4).le
  have hchild_mem :
      MemLp childAvg (ENNReal.ofReal ζ) P := by
    simpa [childAvg, Q, j, ζ] using
      memLp_zeta_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm p q
  have hchild_int :
      Integrable (fun a : RegCoeffField d => Real.rpow (childAvg a) ζ) P := by
    have hζ_ne_zero : ENNReal.ofReal ζ ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le.mpr hζ_pos]
    have hζ_ne_top : ENNReal.ofReal ζ ≠ ⊤ := by simp
    have hint :
        Integrable
          (fun a : RegCoeffField d => ‖childAvg a‖ ^ (ENNReal.ofReal ζ).toReal) P :=
      hchild_mem.integrable_norm_rpow hζ_ne_zero hζ_ne_top
    refine hint.congr ?_
    filter_upwards with a
    have hnonneg : 0 ≤ childAvg a := by
      dsimp [childAvg]
      exact descendantsAverage_nonneg Q j
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)
        (fun R hR => Ch04.restrictionResponseJObservableCubeSet_nonneg R p q a)
    rw [ENNReal.toReal_ofReal hζ_pos.le, Real.norm_of_nonneg hnonneg,
      Real.rpow_eq_pow]
  have horigin_int :
      Integrable
        (fun a : RegCoeffField d =>
          Real.rpow (Ch04.restrictionResponseJObservableCubeSet (originCube d k) p q a) ζ) P := by
    have hknat : ((Int.toNat k : ℕ) : ℤ) = k :=
      Int.toNat_of_nonneg hk_nonneg
    let J : RegCoeffField d → ℝ :=
      Ch04.restrictionResponseJObservableCubeSet (originCube d k) p q
    have hζ_le_two : ENNReal.ofReal ζ ≤ (2 : ENNReal) := by
      rw [← ENNReal.ofReal_ofNat]
      exact ENNReal.ofReal_le_ofReal (by
        simpa [ζ] using section53CoarseFluctuationZeta_le_two hP4)
    have hJ_mem2 : MemLp J (2 : ENNReal) P := by
      have hbase :=
        memLp_two_restrictionResponseJObservableCubeSet_originCube_from_P4
          hP hStruct hP4 (Int.toNat k) p q
      simpa [J, hknat] using hbase
    have hJ_memζ : MemLp J (ENNReal.ofReal ζ) P :=
      hJ_mem2.mono_exponent hζ_le_two
    have hζ_ne_zero : ENNReal.ofReal ζ ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le.mpr hζ_pos]
    have hζ_ne_top : ENNReal.ofReal ζ ≠ ⊤ := by
      simp
    have hint :
        Integrable (fun a : RegCoeffField d => ‖J a‖ ^ (ENNReal.ofReal ζ).toReal) P :=
      hJ_memζ.integrable_norm_rpow hζ_ne_zero hζ_ne_top
    refine hint.congr ?_
    filter_upwards with a
    have hJ_nonneg : 0 ≤ J a := by
      simpa [J] using Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d k) p q a
    rw [ENNReal.toReal_ofReal hζ_pos.le, Real.norm_of_nonneg hJ_nonneg,
      Real.rpow_eq_pow]
  have hpoint :
      (fun a : RegCoeffField d => Real.rpow (childAvg a) ζ) ≤ᵐ[P]
        fun a => descendantsAverage Q j
          (fun R => Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ) := by
    filter_upwards with a
    dsimp [childAvg]
    exact
      rpow_descendantsAverage_le_descendantsAverage_rpow Q j hζ_one
        (fun R hR => Ch04.restrictionResponseJObservableCubeSet_nonneg R p q a)
  have hdesc_int :
      Integrable
        (fun a : RegCoeffField d =>
          descendantsAverage Q j
            (fun R => Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ)) P := by
    refine Ch04.integrable_descendantsAverage ?_
    intro R hR
    have hRscaleMem : R ∈ descendantsAtScale (originCube d m) k := by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm] using! hR
    have hRscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hRscaleMem
    have hstat_eq :=
      integral_rpow_restrictionResponseJObservableCubeSet_cubeSet_eq_originCube_of_stationary
        hP hstat R (by simpa [hRscale] using hk_nonneg) hζ_pos.le p q
    have hR_mem :
        MemLp (Ch04.restrictionResponseJObservableCubeSet R p q)
          (ENNReal.ofReal ζ) P := by
      simpa [ζ] using
        memLp_zeta_restrictionResponseJObservableCubeSet_cubeSet_from_P4_of_stationary
          hP hstat hStruct hP4 R (by simpa [hRscale] using hk_nonneg) p q
    have hζ_ne_zero : ENNReal.ofReal ζ ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le.mpr hζ_pos]
    have hζ_ne_top : ENNReal.ofReal ζ ≠ ⊤ := by simp
    have hint :
        Integrable
          (fun a : RegCoeffField d =>
            ‖Ch04.restrictionResponseJObservableCubeSet R p q a‖ ^
              (ENNReal.ofReal ζ).toReal) P :=
      hR_mem.integrable_norm_rpow hζ_ne_zero hζ_ne_top
    refine hint.congr ?_
    filter_upwards with a
    have hnonneg : 0 ≤ Ch04.restrictionResponseJObservableCubeSet R p q a :=
      Ch04.restrictionResponseJObservableCubeSet_nonneg R p q a
    rw [ENNReal.toReal_ofReal hζ_pos.le, Real.norm_of_nonneg hnonneg,
      Real.rpow_eq_pow]
  have hmono :
      ∫ a, Real.rpow (childAvg a) ζ ∂P ≤
        ∫ a,
          descendantsAverage Q j
            (fun R => Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ) ∂P :=
    integral_mono_ae hchild_int hdesc_int hpoint
  have hdesc_eq :
      ∫ a,
          descendantsAverage Q j
            (fun R => Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ) ∂P =
        ∫ a,
          Real.rpow
            (Ch04.restrictionResponseJObservableCubeSet (originCube d k) p q a) ζ ∂P := by
    classical
    let D : Finset (TriadicCube d) := descendantsAtDepth Q j
    have hFint :
        ∀ R, R ∈ descendantsAtDepth Q j →
          Integrable
            (fun a : RegCoeffField d =>
              Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ) P := by
      intro R hR
      have hRscaleMem : R ∈ descendantsAtScale (originCube d m) k := by
        simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm] using! hR
      have hRscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hRscaleMem
      have hR_mem :
          MemLp (Ch04.restrictionResponseJObservableCubeSet R p q)
            (ENNReal.ofReal ζ) P := by
        simpa [ζ] using
          memLp_zeta_restrictionResponseJObservableCubeSet_cubeSet_from_P4_of_stationary
            hP hstat hStruct hP4 R (by simpa [hRscale] using hk_nonneg) p q
      have hζ_ne_zero : ENNReal.ofReal ζ ≠ 0 := by
        simp [ENNReal.ofReal_eq_zero, not_le.mpr hζ_pos]
      have hζ_ne_top : ENNReal.ofReal ζ ≠ ⊤ := by simp
      have hint :
          Integrable
            (fun a : RegCoeffField d =>
              ‖Ch04.restrictionResponseJObservableCubeSet R p q a‖ ^
                (ENNReal.ofReal ζ).toReal) P :=
        hR_mem.integrable_norm_rpow hζ_ne_zero hζ_ne_top
      refine hint.congr ?_
      filter_upwards with a
      have hnonneg : 0 ≤ Ch04.restrictionResponseJObservableCubeSet R p q a :=
        Ch04.restrictionResponseJObservableCubeSet_nonneg R p q a
      rw [ENNReal.toReal_ofReal hζ_pos.le, Real.norm_of_nonneg hnonneg,
        Real.rpow_eq_pow]
    calc
      ∫ a,
          descendantsAverage Q j
            (fun R => Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ) ∂P
          =
        descendantsAverage Q j
          (fun R => ∫ a,
            Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ ∂P) :=
          Ch04.integral_descendantsAverage_eq_descendantsAverage_integral
            (P := P) (Q := Q) (j := j)
            (F := fun R a =>
              Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ) hFint
      _ =
        descendantsAverage Q j
          (fun _R => ∫ a,
            Real.rpow
              (Ch04.restrictionResponseJObservableCubeSet (originCube d k) p q a) ζ ∂P) := by
          unfold descendantsAverage
          refine congrArg (fun t : ℝ => ((D.card : ℝ)⁻¹) * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          have hRscaleMem : R ∈ descendantsAtScale (originCube d m) k := by
            simpa [Q, j, D, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm] using! hR
          have hRscale : R.scale = k := scale_eq_of_mem_descendantsAtScale hRscaleMem
          have hR_nonneg : 0 ≤ R.scale := by simpa [hRscale] using hk_nonneg
          calc
            ∫ a, Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ ∂P
                =
              ∫ a,
                Real.rpow
                  (Ch04.restrictionResponseJObservableCubeSet (originCube d R.scale) p q a) ζ ∂P :=
                integral_rpow_restrictionResponseJObservableCubeSet_cubeSet_eq_originCube_of_stationary
                  hP hstat R hR_nonneg hζ_pos.le p q
            _ =
              ∫ a,
                Real.rpow
                  (Ch04.restrictionResponseJObservableCubeSet (originCube d k) p q a) ζ ∂P := by
                rw [hRscale]
      _ =
        ∫ a,
          Real.rpow
            (Ch04.restrictionResponseJObservableCubeSet (originCube d k) p q a) ζ ∂P := by
          simp [descendantsAverage_const, Q, j]
  calc
    ∫ a,
        Real.rpow
          (descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)) ζ ∂P
        =
      ∫ a, Real.rpow (childAvg a) ζ ∂P := rfl
    _ ≤
      ∫ a,
        descendantsAverage Q j
          (fun R => Real.rpow (Ch04.restrictionResponseJObservableCubeSet R p q a) ζ) ∂P := hmono
    _ =
      ∫ a,
        Real.rpow
          (Ch04.restrictionResponseJObservableCubeSet (originCube d k) p q a) ζ ∂P := hdesc_eq


end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
