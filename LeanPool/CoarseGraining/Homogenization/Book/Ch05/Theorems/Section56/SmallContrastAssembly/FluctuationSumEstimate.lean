/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.TraceAverageEstimate
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.WeightedGeometricSummation
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.NormalizedStatements

/-! # Fluctuation Sum Estimate -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAssembly

open Section53.JUpperBoundCoarseFluctuations
open Section54.VarianceBoundGoodScale

/-!
# The unconditional fluctuation-sum estimate for Section 5.6

This file proves the analytic estimate which feeds the final constant
selection in `FinalAssembly.lean`: the `m`-centered full-block fluctuation sum
is bounded by the bottom-scale geometric decay and the square of the
small-contrast excess at scale `ell`.
-/

/-- Parameter-only version of the trace-`J` geometric constant. -/
noncomputable def normalizedTraceJAverageGeometricConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  8 * (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
    normalizedMatrixAverageGeometricConstParams params

@[simp]
theorem normalizedTraceJAverageGeometricConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    normalizedTraceJAverageGeometricConstParams hP4.params =
      normalizedTraceJAverageGeometricConst hP4 := rfl

theorem normalizedMatrixAverageGeometricConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ normalizedMatrixAverageGeometricConst hP4 := by
  unfold normalizedMatrixAverageGeometricConst
  have hcard : 0 ≤ (Fintype.card (BlockCoord d) : ℝ) ^ (6 : ℕ) :=
    pow_nonneg (Nat.cast_nonneg _) _
  exact mul_nonneg
    (mul_nonneg hcard (by norm_num))
    (normalizedQuadraticProbeAverageUniformRootSqConst_nonneg hP4)

theorem normalizedTraceJAverageGeometricConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ normalizedTraceJAverageGeometricConst hP4 := by
  unfold normalizedTraceJAverageGeometricConst
  nlinarith [sq_nonneg (Fintype.card (BlockCoord d) : ℝ),
    normalizedMatrixAverageGeometricConst_nonneg hP4]

theorem normalizedTraceJAverageThetaConst_nonneg (d : ℕ) :
    0 ≤ normalizedTraceJAverageThetaConst d := by
  unfold normalizedTraceJAverageThetaConst
  nlinarith [sq_nonneg (Fintype.card (BlockCoord d) : ℝ)]

private theorem fullBlock_diagonal_conj_operatorNormSq_le_sixteen
    {d : ℕ} (r : BlockCoord d → ℝ) (M : FullBlockMat d)
    (hr : ∀ α, |r α| ≤ (2 : ℝ)) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (Matrix.diagonal r * M * Matrix.diagonal r)‖ ^ (2 : ℕ) ≤
      16 *
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^
          (2 : ℕ) := by
  let D : FullBlockMat d := Matrix.diagonal r
  let LM :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M
  let LD :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) D
  have hD_norm_le : ‖LD‖ ≤ (2 : ℝ) := by
    have hrnorm : ‖r‖ ≤ (2 : ℝ) := by
      refine (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr ?_
      intro α
      simpa [Real.norm_eq_abs] using hr α
    calc
      ‖LD‖ = ‖(Matrix.diagonal r : FullBlockMat d)‖ := rfl
      _ = ‖r‖ := Matrix.l2_opNorm_diagonal r
      _ ≤ (2 : ℝ) := hrnorm
  have hnorm :
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Matrix.diagonal r * M * Matrix.diagonal r)‖ ≤
        (2 : ℝ) * ‖LM‖ * (2 : ℝ) := by
    calc
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Matrix.diagonal r * M * Matrix.diagonal r)‖
          = ‖LD * LM * LD‖ := by
              dsimp [LD, LM, D]
              rw [map_mul, map_mul]
      _ ≤ ‖LD * LM‖ * ‖LD‖ := norm_mul_le _ _
      _ ≤ (‖LD‖ * ‖LM‖) * ‖LD‖ := by
            exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((2 : ℝ) * ‖LM‖) * 2 := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right hD_norm_le (norm_nonneg _))
              hD_norm_le (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))
      _ = (2 : ℝ) * ‖LM‖ * 2 := by ring
  have hsq :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_nonneg ‖LM‖]

private theorem diagonal_gap_operatorNormSq_le_thetaSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {ell j m : ℕ} (hellj : ell ≤ j) (hjm : j ≤ m) :
    let bm := hP.barSigmaAtScale hStruct (m : ℤ)
    let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
    let Dm : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm)
    let Aell : FullBlockMat d :=
      toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (ell : ℤ))
    let Am : FullBlockMat d :=
      toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (m : ℤ))
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (Dm * (Aell - Am) * Dm)‖ ^ (2 : ℕ) ≤
      (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
  classical
  dsimp only
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let bell := hP.barSigmaAtScale hStruct (ell : ℤ)
  let cell := hP.barSigmaStarAtScale hStruct (ell : ℤ)
  let Dm : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm)
  let Aell : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (ell : ℤ))
  let Am : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (m : ℤ))
  let gapDiag : BlockCoord d → ℝ := fun α =>
    match α with
    | Sum.inl _ => bell * bm⁻¹ - 1
    | Sum.inr _ => cm * cell⁻¹ - 1
  have hbm_pos : 0 < bm := by
    simpa [bm] using Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_pos : 0 < cm := by
    simpa [cm] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hbell_pos : 0 < bell := by
    simpa [bell] using Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 ell
  have hcell_pos : 0 < cell := by
    simpa [cell] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 ell
  have hchain_ell_m :=
    Section54.Pigeonhole.scalarChain_of_P4 hP hStruct hP4
      (n := ell) (m := m) (hellj.trans hjm)
  have hcell_le_cm : cell ≤ cm := by simpa [cell, cm] using hchain_ell_m.1
  have hbm_le_bell : bm ≤ bell := by simpa [bm, bell] using hchain_ell_m.2.2
  have hcm_le_bm : cm ≤ bm := by
    simpa [bm, cm] using
      Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 m
  have htheta_two :
      thetaAtScale hP hStruct (ell : ℤ) ≤ 2 :=
    thetaAtScale_le_two_of_widetildeThetaAtScale_zero_le_two
      hP hStruct hP4 hsmall ell
  have htheta_one :
      1 ≤ thetaAtScale hP hStruct (ell : ℤ) :=
    Section54.GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 ell
  have hupper_le_theta :
      bell * bm⁻¹ ≤ thetaAtScale hP hStruct (ell : ℤ) := by
    have hcell_le_bm : cell ≤ bm := hcell_le_cm.trans hcm_le_bm
    have hinv : bm⁻¹ ≤ cell⁻¹ := (inv_le_inv₀ hbm_pos hcell_pos).2 hcell_le_bm
    calc
      bell * bm⁻¹ ≤ bell * cell⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hbell_pos.le
      _ = thetaAtScale hP hStruct (ell : ℤ) := by
        simp [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, bell, cell]
  have hlower_le_theta :
      cm * cell⁻¹ ≤ thetaAtScale hP hStruct (ell : ℤ) := by
    calc
      cm * cell⁻¹ ≤ bell * cell⁻¹ :=
        mul_le_mul_of_nonneg_right (hcm_le_bm.trans hbm_le_bell)
          (inv_nonneg.mpr hcell_pos.le)
      _ = thetaAtScale hP hStruct (ell : ℤ) := by
        simp [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, bell, cell]
  have hupper_one : 1 ≤ bell * bm⁻¹ := by
    calc
      1 = bm * bm⁻¹ := by field_simp [hbm_pos.ne']
      _ ≤ bell * bm⁻¹ :=
        mul_le_mul_of_nonneg_right hbm_le_bell (inv_nonneg.mpr hbm_pos.le)
  have hlower_one : 1 ≤ cm * cell⁻¹ := by
    calc
      1 = cell * cell⁻¹ := by field_simp [hcell_pos.ne']
      _ ≤ cm * cell⁻¹ :=
        mul_le_mul_of_nonneg_right hcell_le_cm (inv_nonneg.mpr hcell_pos.le)
  have hdiag_bound : ∀ α, |gapDiag α| ≤ thetaAtScale hP hStruct (ell : ℤ) - 1 := by
    intro α
    cases α with
    | inl i =>
        have hnonneg : 0 ≤ bell * bm⁻¹ - 1 := by linarith
        rw [abs_of_nonneg hnonneg]
        linarith
    | inr i =>
        have hnonneg : 0 ≤ cm * cell⁻¹ - 1 := by linarith
        rw [abs_of_nonneg hnonneg]
        linarith
  have hmat :
      Dm * (Aell - Am) * Dm = Matrix.diagonal gapDiag := by
    have hell_diag :=
      Section54.VarianceBoundGoodScale.normalizedScalarAnnealedBlockMatrix_eq_diagonal
        hP hStruct (m : ℤ) (ell : ℤ)
    have hm_self :=
      Section54.VarianceBoundGoodScale.normalizedScalarAnnealedBlockMatrix_self_eq_one
        hP hStruct hP4 m
    dsimp only at hell_diag hm_self
    change Dm * (Aell - Am) * Dm = Matrix.diagonal gapDiag
    have hsplit : Dm * (Aell - Am) * Dm = Dm * Aell * Dm - Dm * Am * Dm := by
      noncomm_ring
    rw [hsplit]
    have hAm : Dm * Am * Dm = 1 := by
      simpa [Dm, Am, bm, cm] using hm_self
    have hAell :
        Dm * Aell * Dm =
          Matrix.diagonal (fun α : BlockCoord d =>
            match α with
            | Sum.inl _ => (Real.sqrt bm)⁻¹ * bell * (Real.sqrt bm)⁻¹
            | Sum.inr _ => Real.sqrt cm * cell⁻¹ * Real.sqrt cm) := by
      simpa [Dm, Aell, bm, cm, bell, cell] using! hell_diag
    rw [hAell, hAm]
    ext α β
    by_cases hαβ : α = β
    · subst β
      cases α with
      | inl i =>
          simp [Matrix.diagonal, gapDiag]
          field_simp [hbm_pos.ne', (Real.sqrt_pos.mpr hbm_pos).ne']
          rw [Real.sq_sqrt hbm_pos.le]
      | inr i =>
          simp [Matrix.diagonal, gapDiag]
          field_simp [hcell_pos.ne', hcm_pos.ne', (Real.sqrt_pos.mpr hcm_pos).ne']
          rw [Real.sq_sqrt hcm_pos.le]
    · simp [Matrix.diagonal, hαβ]
  have hnorm_le :
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Dm * (Aell - Am) * Dm)‖ ≤
        thetaAtScale hP hStruct (ell : ℤ) - 1 := by
    rw [hmat]
    have hdiag_norm :
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
            (Matrix.diagonal gapDiag : FullBlockMat d)‖ = ‖gapDiag‖ := by
      calc
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
            (Matrix.diagonal gapDiag : FullBlockMat d)‖ =
            ‖(Matrix.diagonal gapDiag : FullBlockMat d)‖ := rfl
        _ = ‖gapDiag‖ := Matrix.l2_opNorm_diagonal gapDiag
    rw [hdiag_norm]
    exact (pi_norm_le_iff_of_nonneg (by linarith)).mpr
      (fun α => by simpa [Real.norm_eq_abs] using hdiag_bound α)
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2

private theorem normalizer_ratio_abs_le_two
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {ell m : ℕ} (hellm : ell ≤ m) :
    let bm := hP.barSigmaAtScale hStruct (m : ℤ)
    let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
    let bell := hP.barSigmaAtScale hStruct (ell : ℤ)
    let cell := hP.barSigmaStarAtScale hStruct (ell : ℤ)
    let r : BlockCoord d → ℝ := fun α =>
      match α with
      | Sum.inl _ => Real.sqrt bell * (Real.sqrt bm)⁻¹
      | Sum.inr _ => Real.sqrt cm * (Real.sqrt cell)⁻¹
    ∀ α, |r α| ≤ (2 : ℝ) := by
  dsimp only
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let bell := hP.barSigmaAtScale hStruct (ell : ℤ)
  let cell := hP.barSigmaStarAtScale hStruct (ell : ℤ)
  let θell := thetaAtScale hP hStruct (ell : ℤ)
  have hbm_pos : 0 < bm := by
    simpa [bm] using Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_pos : 0 < cm := by
    simpa [cm] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hbell_pos : 0 < bell := by
    simpa [bell] using Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 ell
  have hcell_pos : 0 < cell := by
    simpa [cell] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 ell
  have hchain_ell_m :=
    Section54.Pigeonhole.scalarChain_of_P4 hP hStruct hP4
      (n := ell) (m := m) hellm
  have hcell_le_cm : cell ≤ cm := by simpa [cell, cm] using hchain_ell_m.1
  have hbm_le_bell : bm ≤ bell := by simpa [bm, bell] using hchain_ell_m.2.2
  have hcm_le_bm : cm ≤ bm := by
    simpa [bm, cm] using
      Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 m
  have htheta_two : θell ≤ 2 := by
    simpa [θell] using
      thetaAtScale_le_two_of_widetildeThetaAtScale_zero_le_two
        hP hStruct hP4 hsmall ell
  have hupper_ratio :
      bell * bm⁻¹ ≤ θell := by
    have hcell_le_bm : cell ≤ bm := hcell_le_cm.trans hcm_le_bm
    have hinv : bm⁻¹ ≤ cell⁻¹ := (inv_le_inv₀ hbm_pos hcell_pos).2 hcell_le_bm
    calc
      bell * bm⁻¹ ≤ bell * cell⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hbell_pos.le
      _ = θell := by
        simp [θell, Ch04.RestrictionLawCarrier.thetaAtScale, bell, cell]
  have hlower_ratio :
      cm * cell⁻¹ ≤ θell := by
    calc
      cm * cell⁻¹ ≤ bell * cell⁻¹ :=
        mul_le_mul_of_nonneg_right (hcm_le_bm.trans hbm_le_bell)
          (inv_nonneg.mpr hcell_pos.le)
      _ = θell := by
        simp [θell, Ch04.RestrictionLawCarrier.thetaAtScale, bell, cell]
  intro α
  cases α with
  | inl i =>
      let x : ℝ := Real.sqrt bell * (Real.sqrt bm)⁻¹
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        exact mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
      have hx_sq : x ^ (2 : ℕ) = bell * bm⁻¹ := by
        dsimp [x]
        field_simp [(Real.sqrt_pos.mpr hbm_pos).ne']
        rw [Real.sq_sqrt hbell_pos.le, Real.sq_sqrt hbm_pos.le]
        ring
      have hx_sq_le_four : x ^ (2 : ℕ) ≤ (2 : ℝ) ^ (2 : ℕ) := by
        rw [hx_sq]
        calc
          bell * bm⁻¹ ≤ θell := hupper_ratio
          _ ≤ (2 : ℝ) := htheta_two
          _ ≤ (2 : ℝ) ^ (2 : ℕ) := by norm_num
      have hx_le_two : x ≤ (2 : ℝ) :=
        (sq_le_sq₀ hx_nonneg (by norm_num : (0 : ℝ) ≤ 2)).1 hx_sq_le_four
      have habs : |Real.sqrt bell * (Real.sqrt bm)⁻¹| ≤ (2 : ℝ) := by
        rw [abs_of_nonneg hx_nonneg]
        exact hx_le_two
      simpa [bm, bell, x] using habs
  | inr i =>
      let x : ℝ := Real.sqrt cm * (Real.sqrt cell)⁻¹
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        exact mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
      have hx_sq : x ^ (2 : ℕ) = cm * cell⁻¹ := by
        dsimp [x]
        field_simp [(Real.sqrt_pos.mpr hcell_pos).ne']
        rw [Real.sq_sqrt hcm_pos.le, Real.sq_sqrt hcell_pos.le]
        ring
      have hx_sq_le_four : x ^ (2 : ℕ) ≤ (2 : ℝ) ^ (2 : ℕ) := by
        rw [hx_sq]
        calc
          cm * cell⁻¹ ≤ θell := hlower_ratio
          _ ≤ (2 : ℝ) := htheta_two
          _ ≤ (2 : ℝ) ^ (2 : ℕ) := by norm_num
      have hx_le_two : x ≤ (2 : ℝ) :=
        (sq_le_sq₀ hx_nonneg (by norm_num : (0 : ℝ) ≤ 2)).1 hx_sq_le_four
      have habs : |Real.sqrt cm * (Real.sqrt cell)⁻¹| ≤ (2 : ℝ) := by
        rw [abs_of_nonneg hx_nonneg]
        exact hx_le_two
      simpa [cm, cell, x] using habs

private theorem normalizer_change_operatorNormSq_le_sixteen
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {ell m : ℕ} (hellm : ell ≤ m) (M : FullBlockMat d) :
    let bm := hP.barSigmaAtScale hStruct (m : ℤ)
    let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
    let bell := hP.barSigmaAtScale hStruct (ell : ℤ)
    let cell := hP.barSigmaStarAtScale hStruct (ell : ℤ)
    let Dm : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm)
    let Dell : FullBlockMat d :=
      Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bell cell)
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (Dm * M * Dm)‖ ^
        (2 : ℕ) ≤
      16 *
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Dell * M * Dell)‖ ^ (2 : ℕ) := by
  classical
  dsimp only
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let bell := hP.barSigmaAtScale hStruct (ell : ℤ)
  let cell := hP.barSigmaStarAtScale hStruct (ell : ℤ)
  let Dm : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm)
  let Dell : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bell cell)
  let r : BlockCoord d → ℝ := fun α =>
    match α with
    | Sum.inl _ => Real.sqrt bell * (Real.sqrt bm)⁻¹
    | Sum.inr _ => Real.sqrt cm * (Real.sqrt cell)⁻¹
  let R : FullBlockMat d := Matrix.diagonal r
  have hbm_pos : 0 < bm := by
    simpa [bm] using Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_pos : 0 < cm := by
    simpa [cm] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hbell_pos : 0 < bell := by
    simpa [bell] using Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 ell
  have hcell_pos : 0 < cell := by
    simpa [cell] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 ell
  have hdiag_left :
      (fun α : BlockCoord d =>
          r α * Ch04.scalarFullBlockInvSqrtDiag bell cell α) =
        Ch04.scalarFullBlockInvSqrtDiag bm cm := by
    funext α
    cases α with
    | inl i =>
        simp [r, Ch04.scalarFullBlockInvSqrtDiag]
        field_simp [(Real.sqrt_pos.mpr hbell_pos).ne',
          (Real.sqrt_pos.mpr hbm_pos).ne']
    | inr i =>
        simp [r, Ch04.scalarFullBlockInvSqrtDiag]
        field_simp [(Real.sqrt_pos.mpr hcell_pos).ne']
  have hdiag_right :
      (fun α : BlockCoord d =>
          Ch04.scalarFullBlockInvSqrtDiag bell cell α * r α) =
        Ch04.scalarFullBlockInvSqrtDiag bm cm := by
    funext α
    rw [mul_comm]
    exact congr_fun hdiag_left α
  have hDm_left : Dm = R * Dell := by
    dsimp [Dm, R, Dell]
    rw [Matrix.diagonal_mul_diagonal, hdiag_left]
  have hDm_right : Dm = Dell * R := by
    dsimp [Dm, R, Dell]
    rw [Matrix.diagonal_mul_diagonal, hdiag_right]
  have hrewrite :
      Dm * M * Dm = R * (Dell * M * Dell) * R := by
    calc
      Dm * M * Dm = (R * Dell) * M * (Dell * R) := by
        nth_rewrite 1 [hDm_left]
        nth_rewrite 1 [hDm_right]
        rfl
      _ = R * (Dell * M * Dell) * R := by
        noncomm_ring
  rw [hrewrite]
  exact fullBlock_diagonal_conj_operatorNormSq_le_sixteen
    r (Dell * M * Dell)
    (by
      simpa [r, bm, cm, bell, cell] using
        normalizer_ratio_abs_le_two hP hStruct hP4 hsmall hellm)

theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_center_ell
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {ell m : ℕ} (hellm : ell ≤ m) (Q : TriadicCube d) (a : RegCoeffField d) :
    Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct (m : ℤ) Q a ≤
      32 *
          Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct (ell : ℤ) Q a +
        2 * (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let bell := hP.barSigmaAtScale hStruct (ell : ℤ)
  let cell := hP.barSigmaStarAtScale hStruct (ell : ℤ)
  let Dm : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bm cm)
  let Dell : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag bell cell)
  let A : FullBlockMat d := toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)
  let Aell : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (ell : ℤ))
  let Am : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (m : ℤ))
  let X : FullBlockMat d := Dm * (A - Am) * Dm
  let Y : FullBlockMat d := Dm * (A - Aell) * Dm
  let Z : FullBlockMat d := Dm * (Aell - Am) * Dm
  let LX :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X
  let LY :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) Y
  let LZ :=
    Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) Z
  have hX : X = Y + Z := by
    dsimp [X, Y, Z]
    noncomm_ring
  have hLX : LX = LY + LZ := by
    dsimp [LX, LY, LZ]
    rw [hX, map_add]
  have htriangle :
      ‖LX‖ ^ (2 : ℕ) ≤
        2 * ‖LY‖ ^ (2 : ℕ) + 2 * ‖LZ‖ ^ (2 : ℕ) := by
    rw [hLX]
    exact norm_add_sq_le_two_sq_add_two_sq LY LZ
  have hY :
      ‖LY‖ ^ (2 : ℕ) ≤
        16 *
          Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct (ell : ℤ) Q a := by
    have hcomp :=
      normalizer_change_operatorNormSq_le_sixteen
        hP hStruct hP4 hsmall hellm (A - Aell)
    simpa [LY, Y, Dell, bell, cell, Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale,
      Ch04.fullBlockNormalizedFluctuationOperatorNormSq, A, Aell]
      using hcomp
  have hZ :
      ‖LZ‖ ^ (2 : ℕ) ≤
        (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
    have hgap :=
      diagonal_gap_operatorNormSq_le_thetaSq
        hP hStruct hP4 hsmall (ell := ell) (j := ell) (m := m)
        le_rfl hellm
    simpa [LZ, Z, Dm, bm, cm, Aell, Am] using hgap
  have hmain :
      ‖LX‖ ^ (2 : ℕ) ≤
        32 *
            Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (ell : ℤ) Q a +
          2 * (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
    calc
      ‖LX‖ ^ (2 : ℕ) ≤ 2 * ‖LY‖ ^ (2 : ℕ) + 2 * ‖LZ‖ ^ (2 : ℕ) :=
        htriangle
      _ ≤
          2 *
              (16 *
                Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
                  hP hStruct (ell : ℤ) Q a) +
            2 * (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hY (by norm_num : (0 : ℝ) ≤ 2))
            (mul_le_mul_of_nonneg_left hZ (by norm_num : (0 : ℝ) ≤ 2))
      _ =
          32 *
              Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct (ell : ℤ) Q a +
            2 * (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
          ring
  simpa [LX, X, Dm, bm, cm, A, Am,
    Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale,
    Ch04.fullBlockNormalizedFluctuationOperatorNormSq] using hmain

/-- The geometric coefficient in the one-scale fluctuation estimate. -/
noncomputable def fluctuationOneScaleGeometricConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  32 * (2 * normalizedMatrixAverageGeometricConst hP4 +
    8 * normalizedTraceJAverageGeometricConst hP4)

/-- The contrast-square coefficient in the one-scale fluctuation estimate. -/
noncomputable def fluctuationOneScaleThetaConst (d : ℕ) : ℝ :=
  32 * (8 * normalizedTraceJAverageThetaConst d) + 2

theorem fluctuationOneScaleGeometricConst_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ fluctuationOneScaleGeometricConst hP4 := by
  unfold fluctuationOneScaleGeometricConst
  nlinarith [normalizedMatrixAverageGeometricConst_nonneg hP4,
    normalizedTraceJAverageGeometricConst_nonneg hP4]

theorem fluctuationOneScaleThetaConst_nonneg (d : ℕ) :
    0 ≤ fluctuationOneScaleThetaConst d := by
  unfold fluctuationOneScaleThetaConst
  nlinarith [normalizedTraceJAverageThetaConst_nonneg d]

theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_geometric_add_theta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {ell j m : ℕ} (hellj : ell ≤ j) (hjm : j ≤ m) :
    ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P ≤
      fluctuationOneScaleGeometricConst hP4 *
          Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) +
        fluctuationOneScaleThetaConst d *
          (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d (j : ℤ)
  let Fm : RegCoeffField d → ℝ :=
    fun a =>
      Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct (m : ℤ) Q a
  let Fell : RegCoeffField d → ℝ :=
    fun a =>
      Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct (ell : ℤ) Q a
  let thetaSq : ℝ := (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ)
  let geom : ℝ :=
    Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ))
  have hellm : ell ≤ m := hellj.trans hjm
  have hFellInt : Integrable Fell P := by
    simpa [Fell, Q] using
      Section54.VarianceBoundGoodScale.integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4
        hP hStruct hP4 (ell : ℤ) j
  have hRhsInt :
      Integrable (fun a : RegCoeffField d => 32 * Fell a + 2 * thetaSq) P :=
    (hFellInt.const_mul (32 : ℝ)).add (integrable_const (2 * thetaSq))
  have hpoint :
      Fm ≤ᵐ[P] fun a : RegCoeffField d => 32 * Fell a + 2 * thetaSq := by
    filter_upwards with a
    simpa [Fm, Fell, Q, thetaSq] using
      fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_center_ell
        hP hStruct hP4 hsmall hellm Q a
  have hmono :
      ∫ a, Fm a ∂P ≤ ∫ a, 32 * Fell a + 2 * thetaSq ∂P := by
    refine integral_mono_of_nonneg ?_ hRhsInt hpoint
    filter_upwards with a
    exact
      Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg
        hP hStruct (m : ℤ) Q a
  have hcenter_eval :
      ∫ a, 32 * Fell a + 2 * thetaSq ∂P =
        32 * ∫ a, Fell a ∂P + 2 * thetaSq := by
    rw [integral_add (hFellInt.const_mul (32 : ℝ))
      (integrable_const (2 * thetaSq))]
    rw [integral_const_mul]
    rw [integral_const]
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  have hvar :
      ∫ a, Fell a ∂P ≤
        2 *
          ∫ a,
            descendantsAverageNormalizedFluctuationOperatorNormSq
              hP hStruct (ell : ℤ) (originCube d (j : ℤ)) (j - ell) a ∂P +
        8 *
          ∫ a,
            normalizedBlockJTraceAverageSq hP hStruct (ell : ℤ)
              (originCube d (j : ℤ)) (j - ell) a ∂P := by
    simpa [Fell, Q] using
      fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_two_descendantsAverageNormalized_add_eight_JTraceAverageSq
        hP hStruct hP4 ell j ell hellj
  have hdesc :
      ∫ a,
          descendantsAverageNormalizedFluctuationOperatorNormSq
            hP hStruct (ell : ℤ) (originCube d (j : ℤ)) (j - ell) a ∂P ≤
        normalizedMatrixAverageGeometricConst hP4 * geom := by
    simpa [geom] using
      descendantsAverageNormalizedFluctuationOperatorNormSq_integral_le_geometric_of_smallContrast
        hP hStruct hP4 hsmall hellj
  have htrace :
      ∫ a,
          normalizedBlockJTraceAverageSq hP hStruct (ell : ℤ)
            (originCube d (j : ℤ)) (j - ell) a ∂P ≤
        normalizedTraceJAverageGeometricConst hP4 * geom +
          normalizedTraceJAverageThetaConst d * thetaSq := by
    simpa [geom, thetaSq] using
      normalizedBlockJTraceAverageSq_integral_le_geometric_add_thetaSq_of_smallContrast
        hP hStruct hP4 hsmall hellj
  have hFell_bound :
      ∫ a, Fell a ∂P ≤
        (2 * normalizedMatrixAverageGeometricConst hP4 +
            8 * normalizedTraceJAverageGeometricConst hP4) * geom +
          8 * normalizedTraceJAverageThetaConst d * thetaSq := by
    calc
      ∫ a, Fell a ∂P ≤
          2 *
            ∫ a,
              descendantsAverageNormalizedFluctuationOperatorNormSq
                hP hStruct (ell : ℤ) (originCube d (j : ℤ)) (j - ell) a ∂P +
          8 *
            ∫ a,
              normalizedBlockJTraceAverageSq hP hStruct (ell : ℤ)
                (originCube d (j : ℤ)) (j - ell) a ∂P := hvar
      _ ≤
          2 * (normalizedMatrixAverageGeometricConst hP4 * geom) +
            8 *
              (normalizedTraceJAverageGeometricConst hP4 * geom +
                normalizedTraceJAverageThetaConst d * thetaSq) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hdesc (by norm_num : (0 : ℝ) ≤ 2))
            (mul_le_mul_of_nonneg_left htrace (by norm_num : (0 : ℝ) ≤ 8))
      _ =
          (2 * normalizedMatrixAverageGeometricConst hP4 +
              8 * normalizedTraceJAverageGeometricConst hP4) * geom +
            8 * normalizedTraceJAverageThetaConst d * thetaSq := by
          ring
  calc
    ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P
        = ∫ a, Fm a ∂P := by rfl
    _ ≤ ∫ a, 32 * Fell a + 2 * thetaSq ∂P := hmono
    _ = 32 * ∫ a, Fell a ∂P + 2 * thetaSq := hcenter_eval
    _ ≤
        32 *
            ((2 * normalizedMatrixAverageGeometricConst hP4 +
                8 * normalizedTraceJAverageGeometricConst hP4) * geom +
              8 * normalizedTraceJAverageThetaConst d * thetaSq) +
          2 * thetaSq := by
        have h32 : 0 ≤ (32 : ℝ) := by norm_num
        have hmul :=
          mul_le_mul_of_nonneg_left hFell_bound h32
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hmul (2 * thetaSq)
    _ =
        fluctuationOneScaleGeometricConst hP4 *
            Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) +
          fluctuationOneScaleThetaConst d *
            (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
        simp [fluctuationOneScaleGeometricConst, fluctuationOneScaleThetaConst,
          geom, thetaSq]
        ring

/-- Parameter-only version of the one-scale geometric fluctuation constant. -/
noncomputable def fluctuationOneScaleGeometricConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  32 * (2 * normalizedMatrixAverageGeometricConstParams params +
    8 * normalizedTraceJAverageGeometricConstParams params)

@[simp]
theorem fluctuationOneScaleGeometricConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    fluctuationOneScaleGeometricConstParams hP4.params =
      fluctuationOneScaleGeometricConst hP4 := rfl

private theorem int_toNat_nat_sub_of_le {j m : ℕ} (hjm : j ≤ m) :
    Int.toNat ((m : ℤ) - (j : ℤ)) = m - j := by
  have hsub : (m : ℤ) - (j : ℤ) = ((m - j : ℕ) : ℤ) := by
    omega
  rw [hsub]
  simp

theorem coarseFluctuationFullBlockSumAtScale_eq_nat_Icc
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) :
    let β := section53CoarseFluctuationBeta hP4
    coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m =
      ∑ j ∈ Finset.Icc (k + 1) m,
        varianceWeight β m j *
          ∫ a,
            Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  unfold coarseFluctuationFullBlockSumAtScale
  dsimp only
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by omega]
  refine
    (Finset.sum_bij
      (s := Finset.Icc (k + 1) m)
      (t := Finset.Icc (((k + 1 : ℕ) : ℤ)) (m : ℤ))
      (f := fun j =>
        (varianceWeight β m j *
          ∫ a,
            Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P : ℝ))
      (g := fun n =>
        (Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          ∫ a,
            Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) (originCube d n) a ∂P : ℝ))
      (fun j _hj => (j : ℤ))
      ?hmem ?hinj ?hsurj ?hterm).symm
  · intro j hj
    have hjb := Finset.mem_Icc.mp hj
    change (j : ℤ) ∈ Finset.Icc (((k + 1 : ℕ) : ℤ)) (m : ℤ)
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hjb.1, by exact_mod_cast hjb.2⟩
  · intro a _ha b _hb hab
    have hcast : (a : ℤ) = (b : ℤ) := by simpa using hab
    exact_mod_cast hcast
  · intro n hn
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_nonneg : 0 ≤ n := by
      have hk_nonneg : (0 : ℤ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.zero_le (k + 1)
      exact hk_nonneg.trans hn_bounds.1
    refine ⟨Int.toNat n, ?_, ?_⟩
    · have hcast : ((Int.toNat n : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
      apply Finset.mem_Icc.mpr
      constructor
      · have hlow : ((k + 1 : ℕ) : ℤ) ≤ ((Int.toNat n : ℕ) : ℤ) := by
          simpa [hcast] using hn_bounds.1
        exact_mod_cast hlow
      · have hhi : ((Int.toNat n : ℕ) : ℤ) ≤ (m : ℤ) := by
          simpa [hcast] using hn_bounds.2
        exact_mod_cast hhi
    · exact Int.toNat_of_nonneg hn_nonneg
  · intro j hj
    have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
    simp [β, varianceWeight, int_toNat_nat_sub_of_le hjm]

/-- The unconditional parameter-uniform estimate for the coarse fluctuation
sum used in the Section 5.6 assembly lemma. -/
theorem coarseFluctuationFullBlockSumAtScale_le_assembly_fluctuation_bound
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ktau Kgeom Ktheta : ℝ,
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2 →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {ell k m : ℕ}, ell < k → k < m →
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
          Ktau * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e +
            Kgeom *
              Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) +
              Ktheta * (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
  let Ktau : ℝ := 0
  let Kgeom : ℝ :=
    fluctuationOneScaleGeometricConstParams params * weightedScaleDecaySumConst d
  let Ktheta : ℝ :=
    weightedBetaSumConstParams params * fluctuationOneScaleThetaConst d
  refine ⟨Ktau, Kgeom, Ktheta, ?_⟩
  intro P hP _hstat hStruct hP4 hparams hsmall e _he ell k m hellk hkm
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let A : ℝ := fluctuationOneScaleGeometricConst hP4
  let Bconst : ℝ := fluctuationOneScaleThetaConst d
  let thetaSq : ℝ := (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ)
  let geomBottom : ℝ :=
    Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ))
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβeq :
      β = section53CoarseFluctuationBetaParams params := by
    dsimp [β]
    rw [← section53CoarseFluctuationBetaParams_eq_of_P4 hP4, hparams]
  have hAeq : A = fluctuationOneScaleGeometricConstParams params := by
    dsimp [A]
    rw [← fluctuationOneScaleGeometricConstParams_eq_of_P4 hP4, hparams]
  have hellk_le : ell ≤ k := hellk.le
  have hkm_le : k ≤ m := hkm.le
  have hsum_eq :=
    coarseFluctuationFullBlockSumAtScale_eq_nat_Icc
      hP hStruct hP4 k m
  have hpoint :
      ∀ j, j ∈ Finset.Icc (k + 1) m →
        ∫ a,
            Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P ≤
          A * Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) +
            Bconst * thetaSq := by
    intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    have hellj : ell ≤ j := by omega
    have hjm : j ≤ m := hj_bounds.2
    simpa [A, Bconst, thetaSq] using
      fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_geometric_add_theta
        hP hStruct hP4 hsmall hellj hjm
  have hsum_le :
      coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
        ∑ j ∈ Finset.Icc (k + 1) m,
          varianceWeight β m j *
            (A * Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) +
              Bconst * thetaSq) := by
    calc
      coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m =
          ∑ j ∈ Finset.Icc (k + 1) m,
            varianceWeight β m j *
              ∫ a,
                Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
                  hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P := by
            simpa [β] using hsum_eq
      _ ≤
          ∑ j ∈ Finset.Icc (k + 1) m,
            varianceWeight β m j *
              (A * Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) +
                Bconst * thetaSq) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact mul_le_mul_of_nonneg_left (hpoint j hj)
              (varianceWeight_nonneg β m j)
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using fluctuationOneScaleGeometricConst_nonneg hP4
  have hB_nonneg : 0 ≤ Bconst * thetaSq := by
    exact mul_nonneg (by simpa [Bconst] using fluctuationOneScaleThetaConst_nonneg d)
      (sq_nonneg _)
  have hweighted :
      (∑ j ∈ Finset.Icc (k + 1) m,
          varianceWeight β m j *
            (A * Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) +
              Bconst * thetaSq)) ≤
        A * weightedScaleDecaySumConst d * geomBottom +
          weightedBetaSumConst β * (Bconst * thetaSq) := by
    simpa [geomBottom] using
      sum_Icc_varianceWeight_mul_geometric_add_const_le
        (β := β) (A := A) (B := Bconst * thetaSq)
        hβ_pos hellk_le hA_nonneg hB_nonneg
  have hcombined :
      coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
        A * weightedScaleDecaySumConst d * geomBottom +
          weightedBetaSumConst β * (Bconst * thetaSq) :=
    hsum_le.trans hweighted
  calc
    coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
        A * weightedScaleDecaySumConst d * geomBottom +
          weightedBetaSumConst β * (Bconst * thetaSq) := hcombined
    _ =
        Ktau *
            tauAtScale P (m : ℤ) (k : ℤ)
              (specialPAtScale hP hStruct (m : ℤ) e)
              (specialQAtScale hP hStruct (m : ℤ) e) +
          Kgeom * geomBottom + Ktheta * thetaSq := by
        simp [Ktau, Kgeom, Ktheta, A, Bconst, thetaSq, geomBottom,
          hAeq, hβeq, weightedBetaSumConstParams]
        ring


end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
