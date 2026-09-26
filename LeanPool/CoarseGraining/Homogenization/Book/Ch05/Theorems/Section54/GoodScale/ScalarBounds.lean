/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.GoodScale.SpecialVectorAlgebra
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole.ScalarChain

/-! # Scalar Bounds -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace GoodScale

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Scalar bounds for the good-scale lemma

This file supplies the `(P4)`-based scalar positivity, monotonicity, and
special-vector formula rewrites used by the good-scale parameter bounds.
-/

/-- Euclidean vector norm of a scalar multiple. -/
theorem vecNorm_smul {d : ℕ} (c : ℝ) (e : Vec d) :
    Ch02.vecNorm (c • e) = |c| * Ch02.vecNorm e := by
  change ‖(WithLp.toLp 2 (c • e) : EuclideanSpace ℝ (Fin d))‖ =
    |c| * ‖(WithLp.toLp 2 e : EuclideanSpace ℝ (Fin d))‖
  have h :
      (WithLp.toLp 2 (c • e) : EuclideanSpace ℝ (Fin d)) =
        c • (WithLp.toLp 2 e : EuclideanSpace ℝ (Fin d)) := by
    ext i
    rfl
  rw [h, norm_smul, Real.norm_eq_abs]

/-- A Euclidean unit vector has squared project norm one. -/
theorem vecNormSq_eq_one_of_vecNorm_eq_one {d : ℕ} {e : Vec d}
    (he : Ch02.vecNorm e = 1) :
    vecNormSq e = 1 := by
  rw [← Ch02.vecNorm_sq_eq_vecNormSq, he]
  norm_num

/-- Under `(P4)`, `\widehat\sigma_m` is strictly positive. -/
theorem sigmaHatAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < sigmaHatAtScale hP hStruct (m : ℤ) := by
  have hb := Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc := Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  dsimp [sigmaHatAtScale]
  exact Real.sqrt_pos_of_pos (mul_pos hb hc)

/-- Under `(P4)`, the contrast is monotone along nonnegative scales. -/
theorem thetaAtScale_mono_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {n m : ℕ} (hnm : n ≤ m) :
    thetaAtScale hP hStruct (m : ℤ) ≤
      thetaAtScale hP hStruct (n : ℤ) := by
  have hn_nonneg : 0 ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hnm_int : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast hnm
  have hParentBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hChildBlockInt :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 n
  have hDescBlockInt :
      ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hStruct.stationary hn_nonneg hnm_int hR hChildBlockInt
  exact
    Section52.thetaAtScale_mono_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct hn_nonneg hnm_int hParentBlockInt hChildBlockInt hDescBlockInt

/-- Under `(P4)`, the scalar contrast is at least one. -/
theorem one_le_thetaAtScale_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    1 ≤ thetaAtScale hP hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  exact
    Section52.one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct (m : ℤ) hBlock

/-- The scaled `p_e` centering has the manuscript norm. -/
theorem scaled_specialP_centering_vecNorm_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : Ch02.vecNorm e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    Ch02.vecNorm
        (Real.rpow (sigmaHatAtScale hP hStruct (m : ℤ)) (1 / 2 : ℝ) • p0_e) =
      |Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1| := by
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let sigma := sigmaHatAtScale hP hStruct (m : ℤ)
  let theta := thetaAtScale hP hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma : sigma = Real.sqrt (b * c) := by rfl
  have htheta : theta = b * c⁻¹ := by rfl
  have hcoeff := rpow_half_mul_specialP_centering_coeff_eq hb hc hsigma htheta
  have hp0 :
      c⁻¹ • (sigma ^ (1 / 2 : ℝ) • e) - sigma ^ (-(1 / 2 : ℝ)) • e =
        (c⁻¹ * sigma ^ (1 / 2 : ℝ) - sigma ^ (-(1 / 2 : ℝ))) • e := by
    rw [smul_smul]
    rw [← sub_smul]
  calc
    Ch02.vecNorm
        (sigma ^ (1 / 2 : ℝ) •
          (c⁻¹ • (sigma ^ (1 / 2 : ℝ) • e) -
            sigma ^ (-(1 / 2 : ℝ)) • e)) =
        Ch02.vecNorm
          ((sigma ^ (1 / 2 : ℝ) *
            (c⁻¹ * sigma ^ (1 / 2 : ℝ) - sigma ^ (-(1 / 2 : ℝ)))) • e) := by
      rw [hp0, smul_smul]
    _ = |sigma ^ (1 / 2 : ℝ) *
            (c⁻¹ * sigma ^ (1 / 2 : ℝ) - sigma ^ (-(1 / 2 : ℝ)))| *
          Ch02.vecNorm e := by
      rw [vecNorm_smul]
    _ = |Real.sqrt theta - 1| := by
      rw [hcoeff, he, mul_one]

/-- The scaled `q_e` centering has the manuscript norm. -/
theorem scaled_specialQ_centering_vecNorm_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : Ch02.vecNorm e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    Ch02.vecNorm
        (Real.rpow (sigmaHatAtScale hP hStruct (m : ℤ)) (-(1 / 2 : ℝ)) • q0_e) =
      |Real.sqrt (thetaAtScale hP hStruct (m : ℤ)) - 1| := by
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let sigma := sigmaHatAtScale hP hStruct (m : ℤ)
  let theta := thetaAtScale hP hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma : sigma = Real.sqrt (b * c) := by rfl
  have htheta : theta = b * c⁻¹ := by rfl
  have hcoeff := rpow_neg_half_mul_specialQ_centering_coeff_eq hb hc hsigma htheta
  have hq0 :
      sigma ^ (1 / 2 : ℝ) • e - b • (sigma ^ (-(1 / 2 : ℝ)) • e) =
        (sigma ^ (1 / 2 : ℝ) - b * sigma ^ (-(1 / 2 : ℝ))) • e := by
    rw [smul_smul]
    rw [← sub_smul]
  calc
    Ch02.vecNorm
        (sigma ^ (-(1 / 2 : ℝ)) •
          (sigma ^ (1 / 2 : ℝ) • e -
            b • (sigma ^ (-(1 / 2 : ℝ)) • e))) =
        Ch02.vecNorm
          ((sigma ^ (-(1 / 2 : ℝ)) *
            (sigma ^ (1 / 2 : ℝ) - b * sigma ^ (-(1 / 2 : ℝ)))) • e) := by
      rw [hq0, smul_smul]
    _ = |sigma ^ (-(1 / 2 : ℝ)) *
            (sigma ^ (1 / 2 : ℝ) - b * sigma ^ (-(1 / 2 : ℝ)))| *
          Ch02.vecNorm e := by
      rw [vecNorm_smul]
    _ = |Real.sqrt theta - 1| := by
      rw [hcoeff, abs_sub_comm, he, mul_one]

/-- The special-vector scalar formula for the expected response. -/
theorem expectedJScalarFormula_special_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m k : ℕ) (e : Vec d)
    (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    expectedJScalarFormula hP hStruct (k : ℤ) p_e q_e =
      (1 / 2 : ℝ) * (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
          hP.barSigmaAtScale hStruct (k : ℤ) +
        (1 / 2 : ℝ) * sigmaHatAtScale hP hStruct (m : ℤ) *
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ - 1 := by
  let sigma := sigmaHatAtScale hP hStruct (m : ℤ)
  have hb := Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc := Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma, sigmaHatAtScale]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have heDot : vecDot e e = 1 := by simpa [vecNormSq] using he
  have hcross :
      sigma ^ (1 / 2 : ℝ) * (sigma ^ (-(1 / 2 : ℝ)) * vecDot e e) = 1 := by
    rw [← mul_assoc, mul_comm (sigma ^ (1 / 2 : ℝ)) (sigma ^ (-(1 / 2 : ℝ)))]
    rw [rpow_neg_half_mul_rpow_half_eq_one hsigma_pos, one_mul, heDot]
  have hq : sigma ^ (1 / 2 : ℝ) * (sigma ^ (1 / 2 : ℝ) * vecDot e e) = sigma := by
    rw [← mul_assoc]
    rw [show sigma ^ (1 / 2 : ℝ) * sigma ^ (1 / 2 : ℝ) =
        (sigma ^ (1 / 2 : ℝ)) ^ 2 by ring]
    rw [rpow_half_sq_eq_self hsigma_pos, heDot, mul_one]
  have hp :
      sigma ^ (-(1 / 2 : ℝ)) *
          (sigma ^ (-(1 / 2 : ℝ)) * vecDot e e) = sigma⁻¹ := by
    rw [← mul_assoc]
    rw [show sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (-(1 / 2 : ℝ)) =
        (sigma ^ (-(1 / 2 : ℝ))) ^ 2 by ring]
    rw [rpow_neg_half_sq_eq_inv hsigma_pos, heDot, mul_one]
  have hcross2 :
      sigma ^ (2⁻¹ : ℝ) * (sigma ^ (-(2⁻¹ : ℝ)) * vecDot e e) = 1 := by
    convert hcross using 1
    all_goals norm_num
  have hq2 : sigma ^ (2⁻¹ : ℝ) * (sigma ^ (2⁻¹ : ℝ) * vecDot e e) = sigma := by
    convert hq using 1
    all_goals norm_num
  have hp2 :
      sigma ^ (-(2⁻¹ : ℝ)) * (sigma ^ (-(2⁻¹ : ℝ)) * vecDot e e) = sigma⁻¹ := by
    convert hp using 1
    all_goals norm_num
  dsimp [specialPAtScale, specialQAtScale]
  change expectedJScalarFormula hP hStruct (k : ℤ)
      (sigma ^ (-(1 / 2 : ℝ)) • e) (sigma ^ (1 / 2 : ℝ) • e) =
    (1 / 2 : ℝ) * sigma⁻¹ * hP.barSigmaAtScale hStruct (k : ℤ) +
      (1 / 2 : ℝ) * sigma * (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ - 1
  simp [expectedJScalarFormula, vecDot_smul_left, vecDot_smul_right]
  rw [hcross2, hq2, hp2]
  ring

/-- The special-vector scalar formula for the additivity defect. -/
theorem tauScalarFormula_special_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m k : ℕ) (e : Vec d)
    (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    tauScalarFormula hP hStruct (m : ℤ) (k : ℤ) p_e q_e =
      (1 / 2 : ℝ) * (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
          (hP.barSigmaAtScale hStruct (k : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)) +
        (1 / 2 : ℝ) * sigmaHatAtScale hP hStruct (m : ℤ) *
          ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) := by
  let sigma := sigmaHatAtScale hP hStruct (m : ℤ)
  have hb := Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc := Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma, sigmaHatAtScale]
    exact Real.sqrt_pos_of_pos (mul_pos hb hc)
  have heDot : vecDot e e = 1 := by simpa [vecNormSq] using he
  have hq : sigma ^ (1 / 2 : ℝ) * (sigma ^ (1 / 2 : ℝ) * vecDot e e) = sigma := by
    rw [← mul_assoc]
    rw [show sigma ^ (1 / 2 : ℝ) * sigma ^ (1 / 2 : ℝ) =
        (sigma ^ (1 / 2 : ℝ)) ^ 2 by ring]
    rw [rpow_half_sq_eq_self hsigma_pos, heDot, mul_one]
  have hp :
      sigma ^ (-(1 / 2 : ℝ)) *
          (sigma ^ (-(1 / 2 : ℝ)) * vecDot e e) = sigma⁻¹ := by
    rw [← mul_assoc]
    rw [show sigma ^ (-(1 / 2 : ℝ)) * sigma ^ (-(1 / 2 : ℝ)) =
        (sigma ^ (-(1 / 2 : ℝ))) ^ 2 by ring]
    rw [rpow_neg_half_sq_eq_inv hsigma_pos, heDot, mul_one]
  have hq2 : sigma ^ (2⁻¹ : ℝ) * (sigma ^ (2⁻¹ : ℝ) * vecDot e e) = sigma := by
    convert hq using 1
    all_goals norm_num
  have hp2 :
      sigma ^ (-(2⁻¹ : ℝ)) * (sigma ^ (-(2⁻¹ : ℝ)) * vecDot e e) = sigma⁻¹ := by
    convert hp using 1
    all_goals norm_num
  dsimp [specialPAtScale, specialQAtScale]
  change tauScalarFormula hP hStruct (m : ℤ) (k : ℤ)
      (sigma ^ (-(1 / 2 : ℝ)) • e) (sigma ^ (1 / 2 : ℝ) • e) =
    (1 / 2 : ℝ) * sigma⁻¹ *
        (hP.barSigmaAtScale hStruct (k : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)) +
      (1 / 2 : ℝ) * sigma *
        ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
  simp [tauScalarFormula, vecDot_smul_left, vecDot_smul_right]
  rw [hq2, hp2]
  ring

end

end GoodScale
end Section54
end Ch05
end Book
end Homogenization
