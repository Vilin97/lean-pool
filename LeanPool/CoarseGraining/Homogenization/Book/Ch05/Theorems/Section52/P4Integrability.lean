/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessLowerAndIntegrability.LowerVariants
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessLowerAndIntegrability.PowIntegrable
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessLowerAndIntegrability.UnitDescendantSup

/-! # P4Integrability -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: P4Integrability

Origin-block integrability consequences of P4.
-/

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

private theorem norm_toEuclideanCLM_le_sum_abs_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M‖ ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, |M i j| := by
  classical
  let S : ℝ := ∑ i : ι, ∑ j : ι, |M i j|
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg _) hS_nonneg) ?_
  intro x
  have hcoord :
      ∀ i : ι,
        ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖ ≤
          S * ‖x‖ := by
    intro i
    calc
      ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖
          = |∑ j : ι, M i j * x.ofLp j| := by
              simp [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
      _ ≤ ∑ j : ι, |M i j * x.ofLp j| :=
            Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun j => M i j * x.ofLp j)
      _ = ∑ j : ι, |M i j| * ‖x.ofLp j‖ := by
            simp [abs_mul, Real.norm_eq_abs]
      _ ≤ ∑ j : ι, |M i j| * ‖x‖ := by
            exact Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (abs_nonneg _)
      _ = (∑ j : ι, |M i j|) * ‖x‖ := by
            rw [Finset.sum_mul]
      _ ≤ S * ‖x‖ := by
            exact mul_le_mul_of_nonneg_right
              (Finset.single_le_sum
                (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (M k j))
                (Finset.mem_univ i))
              (norm_nonneg x)
  have hnorm_sq :
      ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x‖ ^ 2 ≤
        (((Fintype.card ι : ℝ) * S) * ‖x‖) ^ 2 := by
    calc
      ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x‖ ^ 2
          = ∑ i : ι,
              ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖ ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq]
      _ ≤ ∑ i : ι, (S * ‖x‖) ^ 2 := by
            exact Finset.sum_le_sum fun i _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
      _ ≤ (∑ _i : ι, S * ‖x‖) ^ 2 := by
            exact Finset.sum_sq_le_sq_sum_of_nonneg
              (fun _ _ => mul_nonneg hS_nonneg (norm_nonneg x))
      _ = (((Fintype.card ι : ℝ) * S) * ‖x‖) ^ 2 := by
            simp [Finset.sum_const]
            ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hS_nonneg) (norm_nonneg x))).mp hnorm_sq

private theorem norm_toEuclideanCLM_sq_integrable_of_entry_memLp_two
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {Z : RegCoeffField d → FullBlockMat d}
    (hZ_aemeas : AEMeasurable Z P)
    (hZ_entry : ∀ α β : BlockCoord d, MemLp (fun a => Z a α β) (2 : ENNReal) P) :
    Integrable
      (fun a : RegCoeffField d =>
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (Z a)‖ ^ 2) P := by
  classical
  let S : RegCoeffField d → ℝ := fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d, |Z a α β|
  have hS_mem : MemLp S (2 : ENNReal) P := by
    dsimp [S]
    refine memLp_finsetSum _ ?_
    intro α _hα
    refine memLp_finsetSum _ ?_
    intro β _hβ
    simpa [Real.norm_eq_abs] using (hZ_entry α β).norm
  have hS_sq_int : Integrable (fun a => S a ^ 2) P := by
    simpa [Real.norm_eq_abs, S] using
      hS_mem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  let C : ℝ := Fintype.card (BlockCoord d)
  let L :
      FullBlockMat d →ₗ[ℝ]
        (EuclideanSpace ℝ (BlockCoord d) →L[ℝ] EuclideanSpace ℝ (BlockCoord d)) := {
    toFun := fun M => Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M
    map_add' := by
      intro A B
      exact map_add (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) A B
    map_smul' := by
      intro r A
      exact map_smul (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) r A
  }
  have hCS_sq_int : Integrable (fun a => (C * S a) ^ 2) P := by
    convert hS_sq_int.const_mul (C * C) using 1
    ext a
    ring
  refine Integrable.mono' hCS_sq_int ?_ ?_
  · exact ((continuous_norm.measurable.comp_aemeasurable
        (L.continuous_of_finiteDimensional.measurable.comp_aemeasurable hZ_aemeas)).pow_const 2).aestronglyMeasurable
  · filter_upwards with a
    have hnorm :=
      norm_toEuclideanCLM_le_sum_abs_entries (Z a)
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    simpa [S, C, Real.norm_eq_abs] using hpow

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

theorem originBlockIntegrableAtScale_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
  hP.integrable_coarseFullBlockMatrixAtCube_of_integrable_factor_observables
    (originCube d (m : ℤ))
    hP4.sUpper_pos hP4.sLower_pos (Nat.succ_le_of_lt hP4.xi_pos)
    (upperFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 m)
    (lowerFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 m)

theorem memLp_two_blockMatEntry_coarseBlockMatrix_cubeSet_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (n : ℕ) (α β : BlockCoord d) :
    MemLp
      (fun a : RegCoeffField d =>
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ))) a) α β)
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
    simpa [Y, Q] using!
      hP.aemeasurable_lambdaSqCoeffField_finite_one
        (originCube d (n : ℤ)) hP4.sLower_pos
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
          upperFactorPowerIntegrableAtScale_from_P4
            hP hStruct hP4 n)
  have hY_mem2 : MemLp Y (2 : ENNReal) P :=
    memLp_two_of_nonneg_pow_integrable hP4.two_le_xi hY_meas hY_nonneg
      (by
        simpa [Y, Q] using
          lowerFactorPowerIntegrableAtScale_from_P4
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

theorem integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_originCube_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℤ) (n : ℕ) :
    Integrable
      (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct m (originCube d (n : ℤ))) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d (n : ℤ)
  let b := hP.barSigmaAtScale hStruct m
  let c := hP.barSigmaStarAtScale hStruct m
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let Abar : BlockMat d := Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct m
  let Z : RegCoeffField d → FullBlockMat d :=
    fun a => D * (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) - toFullBlockMat Abar) * D
  have hZ_entry : ∀ α β : BlockCoord d, MemLp (fun a => Z a α β) (2 : ENNReal) P := by
    intro α β
    dsimp [Z]
    have hsum :
        MemLp
          (fun a : RegCoeffField d =>
            ∑ γ : BlockCoord d,
              (∑ δ : BlockCoord d,
                D α δ *
                  (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) δ γ -
                    toFullBlockMat Abar δ γ)) *
                D γ β)
          (2 : ENNReal) P := by
      refine memLp_finsetSum (s := (Finset.univ : Finset (BlockCoord d)))
        (p := (2 : ENNReal)) ?_
      intro γ _hγ
      have hinner :
          MemLp
            (fun a : RegCoeffField d =>
              ∑ δ : BlockCoord d,
                D α δ *
                  (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) δ γ -
                    toFullBlockMat Abar δ γ))
            (2 : ENNReal) P := by
        refine memLp_finsetSum (s := (Finset.univ : Finset (BlockCoord d)))
          (p := (2 : ENNReal)) ?_
        intro δ _hδ
        have hbase :
            MemLp
                (fun a : RegCoeffField d =>
                toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) δ γ -
                  toFullBlockMat Abar δ γ)
              (2 : ENNReal) P := by
          have hentry :
              MemLp
                (fun a : RegCoeffField d =>
                  toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) δ γ)
                (2 : ENNReal) P := by
            simpa [Q, toFullBlockMat, blockMatEntry] using
              memLp_two_blockMatEntry_coarseBlockMatrix_cubeSet_from_P4
                hP hStruct hP4 n δ γ
          exact hentry.sub
            (memLp_const
              (c := toFullBlockMat Abar δ γ) (μ := P) (p := (2 : ENNReal)))
        exact hbase.const_mul (D α δ)
      simpa [mul_comm] using hinner.const_mul (D γ β)
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun a => by
      simp [Matrix.mul_apply]) hsum
  have hZ_aemeas : AEMeasurable Z P := by
    refine aemeasurable_pi_lambda Z ?_
    intro α
    refine aemeasurable_pi_lambda (fun a => Z a α) ?_
    intro β
    exact (hZ_entry α β).aestronglyMeasurable.aemeasurable
  change
    Integrable
      (fun a : RegCoeffField d =>
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (D * (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) - toFullBlockMat Abar) * D)‖ ^ 2)
      P
  exact norm_toEuclideanCLM_sq_integrable_of_entry_memLp_two hZ_aemeas hZ_entry

end

end Section52
end Ch05
end Book
end Homogenization
