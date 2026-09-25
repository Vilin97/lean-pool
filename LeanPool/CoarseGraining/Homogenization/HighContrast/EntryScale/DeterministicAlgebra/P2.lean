/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.ScalarPreliminaries
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.GoodScale.ScalarBounds
public import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.Inputs
public import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.DeterministicAlgebra.P1

/-! # P2 -/

@[expose] public section

open scoped BigOperators Matrix.Norms.Elementwise
open scoped Matrix.Norms.L2Operator

namespace Homogenization.HighContrast.EntryScale

/--
Source label `e.drift.general`: if both scalar ratios are at least one, then
each diagonal drift entry is bounded by the product excess `a b - 1`.
-/
theorem abs_sub_one_le_mul_sub_one_of_one_le {a b : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |a - 1| ≤ a * b - 1 ∧ |b - 1| ≤ a * b - 1 := by
  have ha_nonneg : 0 ≤ a := le_trans zero_le_one ha
  have hb_nonneg : 0 ≤ b := le_trans zero_le_one hb
  have ha_sub_nonneg : 0 ≤ a - 1 := sub_nonneg.mpr ha
  have hb_sub_nonneg : 0 ≤ b - 1 := sub_nonneg.mpr hb
  have ha_le_mul : a ≤ a * b := by
    have h := mul_le_mul_of_nonneg_left hb ha_nonneg
    simpa using h
  have hb_le_mul : b ≤ a * b := by
    have h := mul_le_mul_of_nonneg_right ha hb_nonneg
    simpa [one_mul] using h
  constructor
  · rw [abs_of_nonneg ha_sub_nonneg]
    linarith
  · rw [abs_of_nonneg hb_sub_nonneg]
    linarith

/--
Euclidean/L2 operator norm of a full block matrix.  This is the matrix norm
used by the full `Ahom_m^{-1/2} (...) Ahom_m^{-1/2}` observable in source
label `l.union.bound`.
-/
noncomputable def fullBlockOperatorNorm {d : ℕ}
    (A : Homogenization.FullBlockMat d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ) A‖

theorem fullBlockOperatorNorm_eq_l2_opNorm {d : ℕ}
    (A : Homogenization.FullBlockMat d) :
    fullBlockOperatorNorm A = ‖A‖ := by
  exact Matrix.l2_opNorm_toEuclideanCLM
    (n := Homogenization.BlockCoord d) (𝕜 := ℝ) A

theorem fullBlockOperatorNorm_nonneg {d : ℕ}
    (A : Homogenization.FullBlockMat d) :
    0 ≤ fullBlockOperatorNorm A := by
  exact norm_nonneg _

theorem fullBlockOperatorNorm_mul_le {d : ℕ}
    (A B : Homogenization.FullBlockMat d) :
    fullBlockOperatorNorm (A * B) ≤
      fullBlockOperatorNorm A * fullBlockOperatorNorm B := by
  calc
    fullBlockOperatorNorm (A * B)
        = ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
            (𝕜 := ℝ) (A * B)‖ := rfl
    _ = ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) A *
          Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) B‖ := by
        rw [map_mul]
    _ ≤ ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) A‖ *
          ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) B‖ := norm_mul_le _ _
    _ = fullBlockOperatorNorm A * fullBlockOperatorNorm B := rfl

/--
Source label `l.S.and.J`: squared triangle inequality for the full-block
operator norm, in the form used to split
`A(cu_j) - Ahom_m = (A(cu_j) - Ahom_j) + (Ahom_j - Ahom_m)`.
-/
theorem fullBlockOperatorNorm_add_sq_le_two_mul_add {d : ℕ}
    (A B : Homogenization.FullBlockMat d) :
    fullBlockOperatorNorm (A + B) ^ 2 ≤
      2 * fullBlockOperatorNorm A ^ 2 + 2 * fullBlockOperatorNorm B ^ 2 := by
  let a := fullBlockOperatorNorm A
  let b := fullBlockOperatorNorm B
  have hnorm : fullBlockOperatorNorm (A + B) ≤ a + b := by
    calc
      fullBlockOperatorNorm (A + B)
          = ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
              (𝕜 := ℝ) (A + B)‖ := rfl
      _ = ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
              (𝕜 := ℝ) A +
            Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
              (𝕜 := ℝ) B‖ := by
          rw [map_add]
      _ ≤ ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
              (𝕜 := ℝ) A‖ +
            ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
              (𝕜 := ℝ) B‖ :=
          norm_add_le _ _
      _ = a + b := rfl
  have hleft_nonneg : 0 ≤ fullBlockOperatorNorm (A + B) :=
    fullBlockOperatorNorm_nonneg (A + B)
  have hright_nonneg : 0 ≤ a + b := by
    exact add_nonneg (fullBlockOperatorNorm_nonneg A) (fullBlockOperatorNorm_nonneg B)
  have hsquare :
      fullBlockOperatorNorm (A + B) ^ 2 ≤ (a + b) ^ 2 :=
    (sq_le_sq₀ hleft_nonneg hright_nonneg).2 hnorm
  nlinarith [sq_nonneg (a - b)]

theorem fullBlockOperatorNorm_diagonal {d : ℕ}
    (v : Homogenization.BlockCoord d → ℝ) :
    fullBlockOperatorNorm (Matrix.diagonal v : Homogenization.FullBlockMat d) =
      ‖v‖ := by
  rw [fullBlockOperatorNorm_eq_l2_opNorm]
  exact Matrix.l2_opNorm_diagonal (𝕜 := ℝ) v

theorem fullBlockOperatorNorm_diagonal_le_of_forall_norm_le {d : ℕ}
    {v : Homogenization.BlockCoord d → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hv : ∀ α, ‖v α‖ ≤ R) :
    fullBlockOperatorNorm (Matrix.diagonal v : Homogenization.FullBlockMat d) ≤ R := by
  rw [fullBlockOperatorNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hR).mpr hv

theorem fullBlockOperatorNorm_diagonal_le_of_forall_abs_le {d : ℕ}
    {v : Homogenization.BlockCoord d → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hv : ∀ α, |v α| ≤ R) :
    fullBlockOperatorNorm (Matrix.diagonal v : Homogenization.FullBlockMat d) ≤ R := by
  exact fullBlockOperatorNorm_diagonal_le_of_forall_norm_le hR
    (fun α => by simpa [Real.norm_eq_abs] using hv α)

/--
Source label `l.union.bound`: full-block operator-norm bridge for changing
both sides of the terminal normalization.  Once the two diagonal change
matrices have norm bounds, this converts them into the corresponding bound for
the full centered block observable.
-/
theorem fullBlockOperatorNorm_two_sided_mul_le {d : ℕ}
    (L X R : Homogenization.FullBlockMat d) {CL CR : ℝ}
    (hCL_nonneg : 0 ≤ CL)
    (hL : fullBlockOperatorNorm L ≤ CL)
    (hR : fullBlockOperatorNorm R ≤ CR) :
    fullBlockOperatorNorm (L * X * R) ≤
      CL * CR * fullBlockOperatorNorm X := by
  have hX_nonneg : 0 ≤ fullBlockOperatorNorm X :=
    fullBlockOperatorNorm_nonneg X
  have hR_nonneg : 0 ≤ fullBlockOperatorNorm R :=
    fullBlockOperatorNorm_nonneg R
  have hLX :
      fullBlockOperatorNorm (L * X) ≤
        fullBlockOperatorNorm L * fullBlockOperatorNorm X :=
    fullBlockOperatorNorm_mul_le L X
  have hLX_bound :
      fullBlockOperatorNorm (L * X) ≤
        CL * fullBlockOperatorNorm X :=
    hLX.trans (mul_le_mul_of_nonneg_right hL hX_nonneg)
  have hmain :
      fullBlockOperatorNorm (L * X) * fullBlockOperatorNorm R ≤
        (CL * fullBlockOperatorNorm X) * CR :=
    mul_le_mul hLX_bound hR hR_nonneg (mul_nonneg hCL_nonneg hX_nonneg)
  calc
    fullBlockOperatorNorm (L * X * R)
        ≤ fullBlockOperatorNorm (L * X) * fullBlockOperatorNorm R :=
          fullBlockOperatorNorm_mul_le (L * X) R
    _ ≤ (CL * fullBlockOperatorNorm X) * CR := hmain
    _ = CL * CR * fullBlockOperatorNorm X := by ring

/--
Source label `l.union.bound`: diagonal entries of the full-block
terminal/intermediate normalization-change matrix, written in terms of the two
scalar ratios
`barSigma_j / barSigma_m` and
`barSigmaStar_j^{-1} / barSigmaStar_m^{-1}`.
-/
noncomputable def terminalNormalizerChangeDiag {d : ℕ}
    (upperRatio invStarRatio : ℝ) :
    Homogenization.BlockCoord d → ℝ
  | Sum.inl _ => Real.sqrt upperRatio
  | Sum.inr _ => Real.sqrt invStarRatio

/--
Source label `l.union.bound`: concrete diagonal entries of
`Ahom_m^{-1/2} Ahom_j^{1/2}` in the scalar-block coordinates.
-/
noncomputable def terminalNormalizerChangeDiagAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (j m : ℕ) :
    Homogenization.BlockCoord d → ℝ :=
  terminalNormalizerChangeDiag
    (d := d)
    (hP.barSigmaAtScale hStruct (j : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ))
    ((hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)

/--
Source label `l.union.bound`: concrete full-block diagonal matrix for
`Ahom_m^{-1/2} Ahom_j^{1/2}`.
-/
noncomputable def terminalNormalizerChangeMatrixAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (j m : ℕ) : Homogenization.FullBlockMat d :=
  Matrix.diagonal (terminalNormalizerChangeDiagAtScales hP hStruct j m)

/--
Source label `l.union.bound`: the library's scalar full-block normalizer at one scale,
as the diagonal matrix `Ahom_n^{-1/2}`.
-/
noncomputable def scalarFullBlockNormalizerMatrixAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (n : ℕ) : Homogenization.FullBlockMat d :=
  Matrix.diagonal
    (Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag
      (d := d)
      (hP.barSigmaAtScale hStruct (n : ℤ))
      (hP.barSigmaStarAtScale hStruct (n : ℤ)))

/--
Source label `l.union.bound`: full-block matrix centered by the scalar
annealed block at scale `center`.
-/
noncomputable def scalarCenteredFullBlockMatrixAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (center : ℕ) (Y : Homogenization.FullBlockMat d) :
    Homogenization.FullBlockMat d :=
  Y - Homogenization.toFullBlockMat
    (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
      hP hStruct (center : ℤ))

/--
Source label `e.drift.general`: diagonal entries of the terminal-normalized
annealed drift `Ahom_m^{-1/2} (Ahom_j - Ahom_m) Ahom_m^{-1/2}`.
-/
noncomputable def terminalAnnealedFullBlockDriftDiagAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (j m : ℕ) :
    Homogenization.BlockCoord d → ℝ
  | Sum.inl _ =>
      hP.barSigmaAtScale hStruct (j : ℤ) /
          hP.barSigmaAtScale hStruct (m : ℤ) - 1
  | Sum.inr _ =>
      (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ - 1

/--
Source label `e.drift.general`: the deterministic annealed-drift matrix is
exactly diagonal after terminal scalar normalization.
-/
theorem terminalAnnealedFullBlockDriftMatrix_eq_diagonal
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (j m : ℕ) :
    scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        (Homogenization.toFullBlockMat
            (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
              hP hStruct (j : ℤ)) -
          Homogenization.toFullBlockMat
            (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
              hP hStruct (m : ℤ))) *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m =
      Matrix.diagonal
        (terminalAnnealedFullBlockDriftDiagAtScales hP hStruct j m) := by
  classical
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let bj := hP.barSigmaAtScale hStruct (j : ℤ)
  let cj := hP.barSigmaStarAtScale hStruct (j : ℤ)
  have hbm_pos : 0 < bm := by
    simpa [bm] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m
  have hcm_pos : 0 < cm := by
    simpa [cm] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  have hcj_pos : 0 < cj := by
    simpa [cj] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 j
  have hbm_sqrt_ne : Real.sqrt bm ≠ 0 :=
    (Real.sqrt_ne_zero').2 hbm_pos
  have hcm_sqrt_ne : Real.sqrt cm ≠ 0 :=
    (Real.sqrt_ne_zero').2 hcm_pos
  have hcm_ne : cm ≠ 0 := ne_of_gt hcm_pos
  have hcj_ne : cj ≠ 0 := ne_of_gt hcj_pos
  have hcm_inv_ne : cm⁻¹ ≠ 0 := inv_ne_zero hcm_ne
  ext α β
  by_cases hαβ : α = β
  · subst β
    cases α with
    | inl i =>
        simp [scalarFullBlockNormalizerMatrixAtScale,
          terminalAnnealedFullBlockDriftDiagAtScales,
          Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
          Homogenization.Book.Ch02.blockDiag,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          Homogenization.toFullBlockMat, Matrix.mul_apply, Matrix.diagonal]
        field_simp [hbm_sqrt_ne]
        rw [Real.sq_sqrt hbm_pos.le]
        change (bj - bm) / bm = bj / bm - 1
        field_simp [ne_of_gt hbm_pos]
    | inr i =>
        simp [scalarFullBlockNormalizerMatrixAtScale,
          terminalAnnealedFullBlockDriftDiagAtScales,
          Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
          Homogenization.Book.Ch02.blockDiag,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          Homogenization.toFullBlockMat, Matrix.mul_apply, Matrix.diagonal]
        field_simp [hcm_sqrt_ne, hcm_ne, hcm_inv_ne]
        rw [Real.sq_sqrt hcm_pos.le]
        change cm * (1 / cj - 1 / cm) = cm / cj - 1
        field_simp [hcm_ne, hcj_ne]
  · cases α with
    | inl i =>
        cases β with
        | inl i' =>
            have hii' : i ≠ i' := by
              intro hii'
              exact hαβ (by simp [hii'])
            simp [scalarFullBlockNormalizerMatrixAtScale,
              terminalAnnealedFullBlockDriftDiagAtScales,
              Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
              Homogenization.Book.Ch02.blockDiag,
              Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
              Homogenization.toFullBlockMat, Matrix.mul_apply, Matrix.diagonal, hii']
        | inr i' =>
            simp [scalarFullBlockNormalizerMatrixAtScale,
              terminalAnnealedFullBlockDriftDiagAtScales,
              Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
              Homogenization.Book.Ch02.blockDiag,
              Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
              Homogenization.toFullBlockMat, Matrix.mul_apply, Matrix.diagonal]
    | inr i =>
        cases β with
        | inl i' =>
            simp [scalarFullBlockNormalizerMatrixAtScale,
              terminalAnnealedFullBlockDriftDiagAtScales,
              Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
              Homogenization.Book.Ch02.blockDiag,
              Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
              Homogenization.toFullBlockMat, Matrix.mul_apply, Matrix.diagonal]
        | inr i' =>
            have hii' : i ≠ i' := by
              intro hii'
              exact hαβ (by simp [hii'])
            simp [scalarFullBlockNormalizerMatrixAtScale,
              terminalAnnealedFullBlockDriftDiagAtScales,
              Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
              Homogenization.Book.Ch02.blockDiag,
              Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
              Homogenization.toFullBlockMat, Matrix.mul_apply, Matrix.diagonal, hii']

/--
Source label `e.drift.general`: deterministic annealed-drift norm
`D_{j,m}` from the source proof.
-/
noncomputable def terminalAnnealedFullBlockDriftAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (j m : ℕ) : ℝ :=
  fullBlockOperatorNorm
    (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
      (Homogenization.toFullBlockMat
          (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
            hP hStruct (j : ℤ)) -
        Homogenization.toFullBlockMat
          (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
            hP hStruct (m : ℤ))) *
      scalarFullBlockNormalizerMatrixAtScale hP hStruct m)

/-- Source label `e.drift.general`: `D_{j,m}` is nonnegative. -/
theorem terminalAnnealedFullBlockDriftAtScales_nonneg
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (j m : ℕ) :
    0 ≤ terminalAnnealedFullBlockDriftAtScales hP hStruct j m :=
  fullBlockOperatorNorm_nonneg _

/--
Source label `e.drift.general`: bound `D_{j,m}` by uniform bounds on the two
scalar diagonal entries.
-/
theorem terminalAnnealedFullBlockDriftAtScales_le_of_diag_bounds
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (j m : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (hdiag :
      ∀ α, |terminalAnnealedFullBlockDriftDiagAtScales hP hStruct j m α| ≤ R) :
    terminalAnnealedFullBlockDriftAtScales hP hStruct j m ≤ R := by
  unfold terminalAnnealedFullBlockDriftAtScales
  rw [terminalAnnealedFullBlockDriftMatrix_eq_diagonal hP hStruct hP4 j m]
  exact fullBlockOperatorNorm_diagonal_le_of_forall_abs_le hR hdiag

/--
Source label `e.drift.general`: source-facing scalar-ratio form of the
pointwise deterministic drift bound.
-/
theorem terminalAnnealedFullBlockDriftAtScales_le_of_scalar_ratio_bounds
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (j m : ℕ) {R : ℝ}
    (hR : 0 ≤ R)
    (hupper :
      |hP.barSigmaAtScale hStruct (j : ℤ) /
          hP.barSigmaAtScale hStruct (m : ℤ) - 1| ≤ R)
    (hlower :
      |(hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ - 1| ≤ R) :
    terminalAnnealedFullBlockDriftAtScales hP hStruct j m ≤ R := by
  refine terminalAnnealedFullBlockDriftAtScales_le_of_diag_bounds
    hP hStruct hP4 j m hR ?_
  intro α
  cases α with
  | inl i =>
      simpa [terminalAnnealedFullBlockDriftDiagAtScales] using hupper
  | inr i =>
      simpa [terminalAnnealedFullBlockDriftDiagAtScales] using hlower

/--
Source label `e.drift.general`: the pointwise deterministic drift is bounded
by the product excess of the two scalar terminal ratios.
-/
theorem terminalAnnealedFullBlockDriftAtScales_le_scalar_ratio_product_sub_one
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (j m : ℕ)
    (hupper_one :
      1 ≤ hP.barSigmaAtScale hStruct (j : ℤ) /
        hP.barSigmaAtScale hStruct (m : ℤ))
    (hlower_one :
      1 ≤ (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) :
    terminalAnnealedFullBlockDriftAtScales hP hStruct j m ≤
      (hP.barSigmaAtScale hStruct (j : ℤ) /
          hP.barSigmaAtScale hStruct (m : ℤ)) *
        ((hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) -
      1 := by
  let upper :=
    hP.barSigmaAtScale hStruct (j : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ)
  let lower :=
    (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  have hbounds : |upper - 1| ≤ upper * lower - 1 ∧
      |lower - 1| ≤ upper * lower - 1 :=
    abs_sub_one_le_mul_sub_one_of_one_le
      (by simpa [upper] using hupper_one)
      (by simpa [lower] using hlower_one)
  have hproduct_one : 1 ≤ upper * lower := by
    have hupper_ge_one : 1 ≤ upper := by simpa [upper] using hupper_one
    have hlower_ge_one : 1 ≤ lower := by simpa [lower] using hlower_one
    have hupper_nonneg : 0 ≤ upper := le_trans zero_le_one hupper_ge_one
    have hmul : (1 : ℝ) * 1 ≤ upper * lower :=
      mul_le_mul hupper_ge_one hlower_ge_one (by norm_num) hupper_nonneg
    simpa using hmul
  have hR_nonneg : 0 ≤ upper * lower - 1 := sub_nonneg.mpr hproduct_one
  refine terminalAnnealedFullBlockDriftAtScales_le_of_scalar_ratio_bounds
    hP hStruct hP4 j m (by simpa [upper, lower] using hR_nonneg) ?_ ?_
  · simpa [upper, lower] using hbounds.1
  · simpa [upper, lower] using hbounds.2

/--
Source label `e.drift.general`: under `(P4)` and `j <= m`, the scalar-chain
monotonicity supplies the hypotheses for the product-excess drift bound.
-/
theorem terminalAnnealedFullBlockDriftAtScales_le_scalar_ratio_product_sub_one_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (hjm : j ≤ m) :
    terminalAnnealedFullBlockDriftAtScales hP hStruct j m ≤
      (hP.barSigmaAtScale hStruct (j : ℤ) /
          hP.barSigmaAtScale hStruct (m : ℤ)) *
        ((hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) -
      1 := by
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hjm
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4
      hP hStruct hP4 m
  have hupper_one :
      1 ≤ hP.barSigmaAtScale hStruct (j : ℤ) /
        hP.barSigmaAtScale hStruct (m : ℤ) := by
    rw [le_div_iff₀ hbm_pos]
    simpa using hchain.2.2
  have hlower_one :
      1 ≤ (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := by
    rw [le_div_iff₀ hcm_inv_pos]
    simpa using hchain.2.1
  exact
    terminalAnnealedFullBlockDriftAtScales_le_scalar_ratio_product_sub_one
      hP hStruct hP4 j m hupper_one hlower_one

/--
Source label `e.drift.general`: library-facing pointwise drift bound in the
paper's scalar excess notation `F_n = Theta_n - 1`.
-/
theorem terminalAnnealedFullBlockDriftAtScales_le_contrastExcess_drop_div_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (hjm : j ≤ m) :
    terminalAnnealedFullBlockDriftAtScales hP hStruct j m ≤
      (contrastExcessAtScale hP hStruct j -
          contrastExcessAtScale hP hStruct m) /
        (1 + contrastExcessAtScale hP hStruct m) := by
  let theta_j := Homogenization.Book.Ch05.thetaAtScale hP hStruct (j : ℤ)
  let theta_m := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  have htheta_m_one : 1 ≤ theta_m := by
    simpa [theta_m] using
      Homogenization.Book.Ch05.Section54.GoodScale.one_le_thetaAtScale_of_P4
        hP hStruct hP4 m
  have htheta_m_pos : 0 < theta_m := by linarith
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcj_pos :
      0 < hP.barSigmaStarAtScale hStruct (j : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 j
  have hcm_pos :
      0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hprod_eq :
      (hP.barSigmaAtScale hStruct (j : ℤ) /
          hP.barSigmaAtScale hStruct (m : ℤ)) *
        ((hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) =
        theta_j / theta_m := by
    rw [terminalScalarRatioProduct_eq_theta_ratio
      (ne_of_gt hbm_pos) (ne_of_gt hcj_pos) (ne_of_gt hcm_pos)]
    rfl
  have hD :=
    terminalAnnealedFullBlockDriftAtScales_le_scalar_ratio_product_sub_one_of_P4
      hP hStruct hP4 hjm
  calc
    terminalAnnealedFullBlockDriftAtScales hP hStruct j m
        ≤
          (hP.barSigmaAtScale hStruct (j : ℤ) /
              hP.barSigmaAtScale hStruct (m : ℤ)) *
            ((hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
              (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) -
          1 := hD
    _ = theta_j / theta_m - 1 := by rw [hprod_eq]
    _ = (theta_j - theta_m) / theta_m := by
          field_simp [ne_of_gt htheta_m_pos]
    _ =
        (contrastExcessAtScale hP hStruct j -
            contrastExcessAtScale hP hStruct m) /
          (1 + contrastExcessAtScale hP hStruct m) := by
          dsimp [contrastExcessAtScale, theta_j, theta_m]
          ring

/--
Source label `e.tau.sum.absorb`: on a no-drop window `[k,m]`, every
intermediate contrast drop is bounded by the endpoint no-drop budget.
-/
theorem contrastExcess_drop_le_noDrop_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {rho : ℝ} {k j m : ℕ}
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hkj : k ≤ j) :
    contrastExcessAtScale hP hStruct j -
        contrastExcessAtScale hP hStruct m ≤
      rho * contrastExcessAtScale hP hStruct m := by
  have htheta_jk :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (j : ℤ) ≤
        Homogenization.Book.Ch05.thetaAtScale hP hStruct (k : ℤ) :=
    Homogenization.Book.Ch05.Section54.GoodScale.thetaAtScale_mono_of_P4
      hP hStruct hP4 (n := k) (m := j) hkj
  have hdrop_le :
      contrastExcessAtScale hP hStruct j -
          contrastExcessAtScale hP hStruct m ≤
        contrastExcessAtScale hP hStruct k -
          contrastExcessAtScale hP hStruct m := by
    change
      (Homogenization.Book.Ch05.thetaAtScale hP hStruct (j : ℤ) - 1) -
          (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1) ≤
        (Homogenization.Book.Ch05.thetaAtScale hP hStruct (k : ℤ) - 1) -
          (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1)
    linarith
  exact hdrop_le.trans hno

/--
Source label `e.drift.general`: on a no-drop window, the pointwise drift
bound becomes the paper's no-drop form with `F_m = Theta_m - 1`.
-/
theorem terminalAnnealedFullBlockDriftAtScales_le_noDrop_contrastExcess_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {rho : ℝ} {k j m : ℕ}
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hkj : k ≤ j) (hjm : j ≤ m) :
    terminalAnnealedFullBlockDriftAtScales hP hStruct j m ≤
      rho * contrastExcessAtScale hP hStruct m /
        (1 + contrastExcessAtScale hP hStruct m) := by
  have hD :=
    terminalAnnealedFullBlockDriftAtScales_le_contrastExcess_drop_div_of_P4
      hP hStruct hP4 hjm
  have htheta_jk :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (j : ℤ) ≤
        Homogenization.Book.Ch05.thetaAtScale hP hStruct (k : ℤ) :=
    Homogenization.Book.Ch05.Section54.GoodScale.thetaAtScale_mono_of_P4
      hP hStruct hP4 (n := k) (m := j) hkj
  have hdrop_le :
      contrastExcessAtScale hP hStruct j -
          contrastExcessAtScale hP hStruct m ≤
        contrastExcessAtScale hP hStruct k -
          contrastExcessAtScale hP hStruct m := by
    change
      (Homogenization.Book.Ch05.thetaAtScale hP hStruct (j : ℤ) - 1) -
          (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1) ≤
        (Homogenization.Book.Ch05.thetaAtScale hP hStruct (k : ℤ) - 1) -
          (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1)
    linarith
  have hdrop_no :
      contrastExcessAtScale hP hStruct j -
          contrastExcessAtScale hP hStruct m ≤
        rho * contrastExcessAtScale hP hStruct m :=
    hdrop_le.trans hno
  have hden_pos : 0 < 1 + contrastExcessAtScale hP hStruct m := by
    have htheta_one :
        1 ≤ Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) :=
      Homogenization.Book.Ch05.Section54.GoodScale.one_le_thetaAtScale_of_P4
        hP hStruct hP4 m
    change 0 < 1 + (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1)
    linarith
  exact hD.trans
    (div_le_div_of_nonneg_right hdrop_no (le_of_lt hden_pos))

private theorem sqrt_div_mul_inv_sqrt_eq_inv_sqrt {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) * (Real.sqrt a)⁻¹ = (Real.sqrt b)⁻¹ := by
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_ne_zero').2 ha
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_ne_zero').2 hb
  rw [Real.sqrt_div ha.le b]
  field_simp [hsa, hsb]

private theorem sqrt_inv_mul_mul_sqrt_eq_sqrt {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a⁻¹ * b) * Real.sqrt a = Real.sqrt b := by
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_ne_zero').2 ha
  have hratio : a⁻¹ * b = b / a := by
    field_simp [ha.ne']
  rw [hratio, Real.sqrt_div hb.le a]
  field_simp [hsa]

theorem terminalNormalizerChangeMatrixAtScales_mul_scalarFullBlockNormalizerMatrixAtScale_eq
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (j m : ℕ) :
    terminalNormalizerChangeMatrixAtScales hP hStruct j m *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct j =
      scalarFullBlockNormalizerMatrixAtScale hP hStruct m := by
  have hbj_pos :
      0 < hP.barSigmaAtScale hStruct (j : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 j
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcj_pos :
      0 < hP.barSigmaStarAtScale hStruct (j : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 j
  have hcm_pos :
      0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  unfold terminalNormalizerChangeMatrixAtScales
  unfold scalarFullBlockNormalizerMatrixAtScale
  rw [Matrix.diagonal_mul_diagonal]
  ext α β
  by_cases hαβ : α = β
  · subst β
    cases α with
    | inl i =>
        simp [terminalNormalizerChangeDiagAtScales, terminalNormalizerChangeDiag,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          sqrt_div_mul_inv_sqrt_eq_inv_sqrt hbj_pos hbm_pos]
    | inr i =>
        simp [terminalNormalizerChangeDiagAtScales, terminalNormalizerChangeDiag,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          sqrt_inv_mul_mul_sqrt_eq_sqrt hcj_pos hcm_pos]
  · simp [Matrix.diagonal, hαβ]

theorem scalarFullBlockNormalizerMatrixAtScale_mul_terminalNormalizerChangeMatrixAtScales_eq
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (j m : ℕ) :
    scalarFullBlockNormalizerMatrixAtScale hP hStruct j *
        terminalNormalizerChangeMatrixAtScales hP hStruct j m =
      scalarFullBlockNormalizerMatrixAtScale hP hStruct m := by
  have hbj_pos :
      0 < hP.barSigmaAtScale hStruct (j : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 j
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcj_pos :
      0 < hP.barSigmaStarAtScale hStruct (j : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 j
  have hcm_pos :
      0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  unfold terminalNormalizerChangeMatrixAtScales
  unfold scalarFullBlockNormalizerMatrixAtScale
  rw [Matrix.diagonal_mul_diagonal]
  ext α β
  by_cases hαβ : α = β
  · subst β
    cases α with
    | inl i =>
        simpa [terminalNormalizerChangeDiagAtScales, terminalNormalizerChangeDiag,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag, mul_comm] using
          sqrt_div_mul_inv_sqrt_eq_inv_sqrt hbj_pos hbm_pos
    | inr i =>
        simpa [terminalNormalizerChangeDiagAtScales, terminalNormalizerChangeDiag,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag, mul_comm] using
          sqrt_inv_mul_mul_sqrt_eq_sqrt hcj_pos hcm_pos
  · simp [Matrix.diagonal, hαβ]

theorem fullBlockOperatorNorm_terminalNormalizerChangeDiag_le_sqrt_of_bounds
    {d : ℕ} {upperRatio invStarRatio T : ℝ}
    (hupper : upperRatio ≤ T)
    (hinvStar : invStarRatio ≤ T) :
    fullBlockOperatorNorm
        (Matrix.diagonal
          (terminalNormalizerChangeDiag (d := d) upperRatio invStarRatio) :
          Homogenization.FullBlockMat d) ≤
      Real.sqrt T := by
  rw [fullBlockOperatorNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg T)).mpr ?_
  intro α
  cases α with
  | inl i =>
      simpa [terminalNormalizerChangeDiag, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg upperRatio)] using
        Real.sqrt_le_sqrt hupper
  | inr i =>
      simpa [terminalNormalizerChangeDiag, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg invStarRatio)] using
        Real.sqrt_le_sqrt hinvStar

/--
Source label `l.union.bound`: the concrete terminal/intermediate diagonal
normalization-change matrix has full-block operator norm at most
`sqrt widetildeTheta_0`.
-/
theorem fullBlockOperatorNorm_terminalNormalizerChangeMatrixAtScales_le_sqrt_initialWidetildeTheta_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (hjm : j ≤ m) :
    fullBlockOperatorNorm
        (terminalNormalizerChangeMatrixAtScales hP hStruct j m) ≤
      Real.sqrt
        (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) := by
  unfold terminalNormalizerChangeMatrixAtScales
  unfold terminalNormalizerChangeDiagAtScales
  exact
    fullBlockOperatorNorm_terminalNormalizerChangeDiag_le_sqrt_of_bounds
      (terminalUpperScalarRatio_le_initialWidetildeTheta_of_P4
        hP hStruct hP4 hjm)
      (terminalInvStarScalarRatio_le_initialWidetildeTheta_of_P4
        hP hStruct hP4 hjm)

/--
Source label `l.union.bound`: changing both sides of a full-block observable
from intermediate scale `j` to terminal scale `m` costs at most the corrected
initial contrast budget `T = widetildeTheta_0`.
-/
theorem fullBlockOperatorNorm_terminalNormalizerChange_two_sided_le_initialWidetildeTheta_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (hjm : j ≤ m) (X : Homogenization.FullBlockMat d) :
    fullBlockOperatorNorm
        (terminalNormalizerChangeMatrixAtScales hP hStruct j m * X *
          terminalNormalizerChangeMatrixAtScales hP hStruct j m) ≤
      Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 *
        fullBlockOperatorNorm X := by
  let T := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  let D : Homogenization.FullBlockMat d :=
    terminalNormalizerChangeMatrixAtScales hP hStruct j m
  have hD : fullBlockOperatorNorm D ≤ Real.sqrt T := by
    simpa [D, T] using
      fullBlockOperatorNorm_terminalNormalizerChangeMatrixAtScales_le_sqrt_initialWidetildeTheta_of_P4
        hP hStruct hP4 hjm
  have hsqrt_nonneg : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have htwo :=
    fullBlockOperatorNorm_two_sided_mul_le
      (L := D) (X := X) (R := D)
      (CL := Real.sqrt T) (CR := Real.sqrt T)
      hsqrt_nonneg hD hD
  have hT_nonneg : 0 ≤ T := by
    have hT_one : 1 ≤ T := by
      simpa [T] using one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
    linarith
  calc
    fullBlockOperatorNorm
        (terminalNormalizerChangeMatrixAtScales hP hStruct j m * X *
          terminalNormalizerChangeMatrixAtScales hP hStruct j m)
        = fullBlockOperatorNorm (D * X * D) := by rfl
    _ ≤ Real.sqrt T * Real.sqrt T * fullBlockOperatorNorm X := htwo
    _ = T * fullBlockOperatorNorm X := by
          rw [← pow_two, Real.sq_sqrt hT_nonneg]

/--
Source label `l.union.bound`: terminal normalization of a block centered at
scale `j` costs at most `T = widetildeTheta_0` times the same centered block
with its intermediate-scale normalization.
-/
theorem fullBlockOperatorNorm_terminalNormalizedCenteredFullBlock_le_initialWidetildeTheta_mul_intermediate_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (hjm : j ≤ m) (Y : Homogenization.FullBlockMat d) :
    fullBlockOperatorNorm
        (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
          scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
          scalarFullBlockNormalizerMatrixAtScale hP hStruct m) ≤
      Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 *
        fullBlockOperatorNorm
          (scalarFullBlockNormalizerMatrixAtScale hP hStruct j *
            scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
            scalarFullBlockNormalizerMatrixAtScale hP hStruct j) := by
  let T := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  let E : Homogenization.FullBlockMat d :=
    terminalNormalizerChangeMatrixAtScales hP hStruct j m
  let Dj : Homogenization.FullBlockMat d :=
    scalarFullBlockNormalizerMatrixAtScale hP hStruct j
  let Dm : Homogenization.FullBlockMat d :=
    scalarFullBlockNormalizerMatrixAtScale hP hStruct m
  let C : Homogenization.FullBlockMat d :=
    scalarCenteredFullBlockMatrixAtScale hP hStruct j Y
  have hleft : E * Dj = Dm := by
    simpa [E, Dj, Dm] using
      terminalNormalizerChangeMatrixAtScales_mul_scalarFullBlockNormalizerMatrixAtScale_eq
        hP hStruct hP4 j m
  have hright : Dj * E = Dm := by
    simpa [E, Dj, Dm] using
      scalarFullBlockNormalizerMatrixAtScale_mul_terminalNormalizerChangeMatrixAtScales_eq
        hP hStruct hP4 j m
  have hfactor :
      Dm * C * Dm = E * (Dj * C * Dj) * E := by
    calc
      Dm * C * Dm = (E * Dj) * C * (Dj * E) := by
        rw [hleft, hright]
      _ = E * (Dj * C * Dj) * E := by
        simp [mul_assoc]
  have hnorm :=
    fullBlockOperatorNorm_terminalNormalizerChange_two_sided_le_initialWidetildeTheta_of_P4
      hP hStruct hP4 hjm (Dj * C * Dj)
  calc
    fullBlockOperatorNorm
        (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
          scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
          scalarFullBlockNormalizerMatrixAtScale hP hStruct m)
        = fullBlockOperatorNorm (Dm * C * Dm) := by rfl
    _ = fullBlockOperatorNorm (E * (Dj * C * Dj) * E) := by rw [hfactor]
    _ ≤ T * fullBlockOperatorNorm (Dj * C * Dj) := by
          simpa [T, E] using hnorm
    _ =
        Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 *
          fullBlockOperatorNorm
            (scalarFullBlockNormalizerMatrixAtScale hP hStruct j *
              scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
              scalarFullBlockNormalizerMatrixAtScale hP hStruct j) := by
          rfl

end Homogenization.HighContrast.EntryScale
