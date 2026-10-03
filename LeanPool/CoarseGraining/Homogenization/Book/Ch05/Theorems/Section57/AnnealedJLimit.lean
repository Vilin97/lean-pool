/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UnitJTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.ScalarPreliminaries

/-! # Annealed JLimit -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

/-!
# Annealed bound for the limiting-normalized block response

This file supplies the deterministic annealed input in Corollary
`c.first.quenched.estimate`: after the main annealed theorem has made the
scalar contrast small, the annealed response with the limiting normalization
is small as well.
-/

noncomputable section

private theorem limit_normalized_scalar_coeff_le_theta_sub_one
    {b c L normSq : ℝ} (hL_pos : 0 < L) (hc_pos : 0 < c)
    (hc_le_L : c ≤ L) (hL_le_b : L ≤ b)
    (hnorm_le_one : normSq ≤ 1) :
    (1 / 2 : ℝ) * (b * L⁻¹ + L * c⁻¹ - 2) * normSq ≤ b * c⁻¹ - 1 := by
  let x : ℝ := b * L⁻¹
  let y : ℝ := L * c⁻¹
  have hx_one : 1 ≤ x := by
    have hmul := mul_le_mul_of_nonneg_right hL_le_b (inv_pos.mpr hL_pos).le
    calc
      1 = L * L⁻¹ := by field_simp [hL_pos.ne']
      _ ≤ b * L⁻¹ := hmul
      _ = x := rfl
  have hy_one : 1 ≤ y := by
    have hmul := mul_le_mul_of_nonneg_right hc_le_L (inv_pos.mpr hc_pos).le
    calc
      1 = c * c⁻¹ := by field_simp [hc_pos.ne']
      _ ≤ L * c⁻¹ := hmul
      _ = y := rfl
  have hcoeff_nonneg : 0 ≤ (1 / 2 : ℝ) * (x + y - 2) := by
    nlinarith
  have hxy_nonneg : 0 ≤ (x - 1) * (y - 1) :=
    mul_nonneg (sub_nonneg.mpr hx_one) (sub_nonneg.mpr hy_one)
  have hcoeff_le : (1 / 2 : ℝ) * (x + y - 2) ≤ x * y - 1 := by
    nlinarith
  calc
    (1 / 2 : ℝ) * (b * L⁻¹ + L * c⁻¹ - 2) * normSq =
        ((1 / 2 : ℝ) * (x + y - 2)) * normSq := by
          simp [x, y]
    _ ≤ (1 / 2 : ℝ) * (x + y - 2) :=
      mul_le_of_le_one_right hcoeff_nonneg hnorm_le_one
    _ ≤ x * y - 1 := hcoeff_le
    _ = b * c⁻¹ - 1 := by
      dsimp [x, y]
      field_simp [hL_pos.ne']

private theorem vecDot_sub_self_add_add_self {d : ℕ} (x y : Vec d) :
    vecDot (x - y) (x - y) + vecDot (x + y) (x + y) =
      2 * (vecDot x x + vecDot y y) := by
  simp [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, vecDot_comm]
  ring

private theorem expectedJScalarFormula_limit_pair_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℤ) {L : ℝ} (hL_pos : 0 < L) (u : Vec d) :
    expectedJScalarFormula hP hStruct m ((√L)⁻¹ • u) (√L • u) =
      (1 / 2 : ℝ) *
        (hP.barSigmaAtScale hStruct m * L⁻¹ +
          L * (hP.barSigmaStarAtScale hStruct m)⁻¹ - 2) *
        vecDot u u := by
  have hsqrt_ne : √L ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL_pos)
  simp [expectedJScalarFormula, vecDot_smul_left, vecDot_smul_right]
  field_simp [hsqrt_ne, hL_pos.ne']
  rw [Real.sq_sqrt hL_pos.le]
  ring

theorem abs_fullBlockVec_coord_le_one_of_dotProduct_le_one
    {d : ℕ} (e : FullBlockVec d) (he : dotProduct e e ≤ 1)
    (α : BlockCoord d) :
    |e α| ≤ 1 := by
  have hcoord_le :
      e α * e α ≤ dotProduct e e := by
    have hcoord_sq :
        e α ^ (2 : ℕ) ≤ ∑ β : BlockCoord d, e β ^ (2 : ℕ) :=
      Finset.single_le_sum
        (fun β _hβ => sq_nonneg (e β))
        (Finset.mem_univ α)
    simpa [dotProduct, pow_two] using hcoord_sq
  have hsq : |e α| ^ (2 : ℕ) ≤ (1 : ℝ) ^ (2 : ℕ) := by
    rw [sq_abs]
    nlinarith
  simpa using (sq_le_sq.mp hsq)

namespace GammaSigmaCoarseGrainedEllipticity

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}

/-- The annealed response with limiting scalar normalizers is controlled by
the scalar contrast at the same scale. -/
theorem integral_limitNormalizedBlockJObservable_le_thetaAtScale_sub_one
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (k : ℕ) (e : FullBlockVec d) (he_norm : dotProduct e e ≤ 1) :
    (∫ a,
      limitNormalizedBlockJObservable hP hStruct (originCube d (k : ℤ)) e a ∂P) ≤
      thetaAtScale hP hStruct (k : ℤ) - 1 := by
  let : IsProbabilityMeasure P := hP.isProbability
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  let L : ℝ := barSigmaLimit hP hStruct
  let b : ℝ := hP.barSigmaAtScale hStruct (k : ℤ)
  let c : ℝ := hP.barSigmaStarAtScale hStruct (k : ℤ)
  let x : Vec d := fun i => e (Sum.inl i)
  let y : Vec d := fun i => e (Sum.inr i)
  let p : Vec d := (√L)⁻¹ • x
  let q : Vec d := √L • y
  let pStar : Vec d := (√L)⁻¹ • y
  let qStar : Vec d := √L • x
  have hL_pos : 0 < L := by simpa [L] using hΓ.barSigmaLimit_pos
  have hc_pos : 0 < c := by
    simpa [c] using
      Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 k
  have hc_le_L : c ≤ L := by
    simpa [c, L] using hΓ.barSigmaStarAtScale_le_barSigmaLimit k
  have hL_le_b : L ≤ b := by
    simpa [L, b] using hΓ.barSigmaLimit_le_barSigmaAtScale k
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (k : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 k
  have hJ₁ :
      Integrable
        (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ))
          (p - pStar) (qStar - q)) P :=
    hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (originCube d (k : ℤ)) (p - pStar) (qStar - q) hBlock
  have hJ₂ :
      Integrable
        (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ))
          (pStar + p) (qStar + q)) P :=
    hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (originCube d (k : ℤ)) (pStar + p) (qStar + q) hBlock
  have hPvec_eq :
      scalarLimitInvSqrtBlockVec hP hStruct e = (p, q) := by
    apply Prod.ext
    · funext i
      change (Matrix.mulVec (scalarLimitInvSqrtMatrix hP hStruct) e) (Sum.inl i) =
        (√L)⁻¹ * e (Sum.inl i)
      simp [scalarLimitInvSqrtMatrix, Ch04.scalarFullBlockInvSqrtDiag,
        Matrix.mulVec, dotProduct, Matrix.diagonal, L]
    · funext i
      change (Matrix.mulVec (scalarLimitInvSqrtMatrix hP hStruct) e) (Sum.inr i) =
        √L * e (Sum.inr i)
      simp [scalarLimitInvSqrtMatrix, Ch04.scalarFullBlockInvSqrtDiag,
        Matrix.mulVec, dotProduct, Matrix.diagonal, L]
  have hQvec_eq :
      scalarLimitSqrtBlockVec hP hStruct e = (qStar, pStar) := by
    apply Prod.ext
    · funext i
      change (Matrix.mulVec (scalarLimitSqrtMatrix hP hStruct) e) (Sum.inl i) =
        √L * e (Sum.inl i)
      simp [scalarLimitSqrtMatrix, Section56.scalarFullBlockSqrtDiag,
        Matrix.mulVec, dotProduct, Matrix.diagonal, L]
    · funext i
      change (Matrix.mulVec (scalarLimitSqrtMatrix hP hStruct) e) (Sum.inr i) =
        (√L)⁻¹ * e (Sum.inr i)
      simp [scalarLimitSqrtMatrix, Section56.scalarFullBlockSqrtDiag,
        Matrix.mulVec, dotProduct, Matrix.diagonal, L]
  have hIntegral_half :
      (∫ a,
        limitNormalizedBlockJObservable hP hStruct (originCube d (k : ℤ)) e a ∂P) =
        (1 / 2 : ℝ) *
            Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ))
              (p - pStar) (qStar - q) +
          (1 / 2 : ℝ) *
            Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ))
              (pStar + p) (qStar + q) := by
    calc
      (∫ a,
        limitNormalizedBlockJObservable hP hStruct (originCube d (k : ℤ)) e a ∂P)
          =
        ∫ a, Ch04.blockJObservableCubeSet (originCube d (k : ℤ))
          p pStar q qStar a ∂P := by
            congr 1
            funext a
            simp [limitNormalizedBlockJObservable, Ch04.blockJObservableCubeSetBlockVec,
              hPvec_eq, hQvec_eq]
      _ =
        (1 / 2 : ℝ) *
            Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ))
              (p - pStar) (qStar - q) +
          (1 / 2 : ℝ) *
            Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ))
              (pStar + p) (qStar + q) :=
        Ch04.integral_blockJObservableCubeSet_eq_half_expectedResponseJCubeSet_add
          hStruct.adjoint_invariant (originCube d (k : ℤ))
          p pStar q qStar hJ₁ hJ₂
  have hResp₁ :
      Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ))
          (p - pStar) (qStar - q) =
        expectedJScalarFormula hP hStruct (k : ℤ)
          (p - pStar) (qStar - q) := by
    have h :=
      Section52.annealedResponseJAtScale_eq_expectedJScalarFormula
        hP hStruct (k : ℤ) (p - pStar) (qStar - q) hBlock
    simpa [Ch04.expectedResponseJCubeSet, Ch04.annealedResponseJAtScale,
      Ch04.responseJAtScale, Ch04.restrictionResponseJObservableCubeSet] using h
  have hResp₂ :
      Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ))
          (pStar + p) (qStar + q) =
        expectedJScalarFormula hP hStruct (k : ℤ)
          (pStar + p) (qStar + q) := by
    have h :=
      Section52.annealedResponseJAtScale_eq_expectedJScalarFormula
        hP hStruct (k : ℤ) (pStar + p) (qStar + q) hBlock
    simpa [Ch04.expectedResponseJCubeSet, Ch04.annealedResponseJAtScale,
      Ch04.responseJAtScale, Ch04.restrictionResponseJObservableCubeSet] using h
  have hsqrt_ne : √L ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL_pos)
  have hscalar :
      (1 / 2 : ℝ) * expectedJScalarFormula hP hStruct (k : ℤ)
          (p - pStar) (qStar - q) +
        (1 / 2 : ℝ) * expectedJScalarFormula hP hStruct (k : ℤ)
          (pStar + p) (qStar + q) =
        (1 / 2 : ℝ) * (b * L⁻¹ + L * c⁻¹ - 2) * dotProduct e e := by
    have hsplit : dotProduct e e = vecDot x x + vecDot y y := by
      unfold dotProduct
      rw [Fintype.sum_sum_type]
      simp [x, y, vecDot]
    have hp_minus : p - pStar = (√L)⁻¹ • (x - y) := by
      ext i
      simp [p, pStar, sub_eq_add_neg, mul_add]
    have hq_minus : qStar - q = √L • (x - y) := by
      ext i
      simp [qStar, q, sub_eq_add_neg, mul_add]
    have hp_plus : pStar + p = (√L)⁻¹ • (x + y) := by
      ext i
      simp [p, pStar, add_comm, mul_add]
    have hq_plus : qStar + q = √L • (x + y) := by
      ext i
      simp [qStar, q, mul_add]
    have hminus :=
      expectedJScalarFormula_limit_pair_eq hP hStruct (k : ℤ) hL_pos (x - y)
    have hplus :=
      expectedJScalarFormula_limit_pair_eq hP hStruct (k : ℤ) hL_pos (x + y)
    rw [hp_minus, hq_minus, hp_plus, hq_plus, hminus, hplus, hsplit]
    have hpara := vecDot_sub_self_add_add_self x y
    let coeff : ℝ := b * L⁻¹ + L * c⁻¹ - 2
    change
      (1 / 2 : ℝ) *
            ((1 / 2 : ℝ) * coeff * vecDot (x - y) (x - y)) +
          (1 / 2 : ℝ) *
            ((1 / 2 : ℝ) * coeff * vecDot (x + y) (x + y)) =
        (1 / 2 : ℝ) * coeff * (vecDot x x + vecDot y y)
    calc
      (1 / 2 : ℝ) *
            ((1 / 2 : ℝ) * coeff * vecDot (x - y) (x - y)) +
          (1 / 2 : ℝ) *
            ((1 / 2 : ℝ) * coeff * vecDot (x + y) (x + y))
          =
        (1 / 4 : ℝ) * coeff *
          (vecDot (x - y) (x - y) + vecDot (x + y) (x + y)) := by
            ring
      _ = (1 / 4 : ℝ) * coeff * (2 * (vecDot x x + vecDot y y)) := by
            rw [hpara]
      _ = (1 / 2 : ℝ) * coeff * (vecDot x x + vecDot y y) := by
            ring
  have hIntegral_eq :
      (∫ a,
        limitNormalizedBlockJObservable hP hStruct (originCube d (k : ℤ)) e a ∂P) =
        (1 / 2 : ℝ) * (b * L⁻¹ + L * c⁻¹ - 2) * dotProduct e e := by
    rw [hIntegral_half, hResp₁, hResp₂, hscalar]
  have hbound :=
    limit_normalized_scalar_coeff_le_theta_sub_one
      (b := b) (c := c) (L := L) (normSq := dotProduct e e)
      hL_pos hc_pos hc_le_L hL_le_b he_norm
  calc
    (∫ a,
      limitNormalizedBlockJObservable hP hStruct (originCube d (k : ℤ)) e a ∂P)
        =
      (1 / 2 : ℝ) * (b * L⁻¹ + L * c⁻¹ - 2) * dotProduct e e := hIntegral_eq
    _ ≤ b * c⁻¹ - 1 := hbound
    _ = thetaAtScale hP hStruct (k : ℤ) - 1 := by
      simp [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b, c]

end GammaSigmaCoarseGrainedEllipticity

end

end Section57
end Ch05
end Book
end Homogenization
