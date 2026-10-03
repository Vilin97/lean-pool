/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole.ScalarChain

/-! # Scale Compression -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Scalar compression at a good scale

This file records the scale-zero scalar comparisons used to compress the
unit-cube moment factors in the variance-bound proof.  These are internal
Section 5.4 bridges: they are derived from `(P4)` and the displayed good-scale
hypotheses, rather than being added to the public theorem statement.
-/

private theorem barSigmaAtScale_le_LambdaMomentAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP.barSigmaAtScale hStruct 0 ≤
      Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi := by
  have hξ_one : 1 ≤ hP4.xi := le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
  simpa using
    hP.barSigmaAtScale_le_LambdaMomentAtScale_of_integrable_factor_observables
      hStruct hP4.sUpper_pos hP4.sLower_pos hξ_one
      (fun n => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 n)
      (fun n => hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d (n : ℤ)) hP4.sUpper_pos)
      (fun n => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d (n : ℤ)) hP4.sLower_pos)
      (fun n => Section52.upperFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 n)
      (fun n => Section52.lowerFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 n)
      0

private theorem barSigmaStarAtScale_inv_le_lambdaInvMomentAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
      Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
  have hξ_one : 1 ≤ hP4.xi := le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
  simpa using
    hP.barSigmaStarAtScale_inv_le_lambdaInvMomentAtScale_of_integrable_factor_observables
      hStruct hP4.sUpper_pos hP4.sLower_pos hξ_one
      (fun n => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 n)
      (fun n => hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d (n : ℤ)) hP4.sUpper_pos)
      (fun n => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d (n : ℤ)) hP4.sLower_pos)
      (fun n => Section52.upperFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 n)
      (fun n => Section52.lowerFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 n)
      0

/-- Under `(P4)`, the starred scalar is bounded by the upper scalar at every
nonnegative scale. -/
theorem barSigmaStarAtScale_le_barSigmaAtScale_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    hP.barSigmaStarAtScale hStruct (m : ℤ) ≤
      hP.barSigmaAtScale hStruct (m : ℤ) := by
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hc_pos : 0 < c := by
    simpa [c] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have htheta :
      1 ≤ b * c⁻¹ := by
    simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b, c] using
      Section52.one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
        hP hStruct (m : ℤ) hBlock
  calc
    hP.barSigmaStarAtScale hStruct (m : ℤ) = c := rfl
    _ = c * 1 := by ring
    _ ≤ c * (b * c⁻¹) := mul_le_mul_of_nonneg_left htheta hc_pos.le
    _ = b := by field_simp [hc_pos.ne']
    _ = hP.barSigmaAtScale hStruct (m : ℤ) := rfl

/-- Good-scale comparison: the inverse upper normalization at scale `m` is
controlled by the scale-zero lower moment factor. -/
theorem barSigmaAtScale_inv_le_one_add_delta_mul_lambdaInvMomentAtScale_zero_of_good
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ)) :
    (hP.barSigmaAtScale hStruct (m : ℤ))⁻¹ ≤
      (1 + delta) *
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let b0 := hP.barSigmaAtScale hStruct 0
  let c0 := hP.barSigmaStarAtScale hStruct 0
  let L0inv := Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  have hfactor_nonneg : 0 ≤ 1 + delta := by linarith
  have hbm_pos : 0 < bm := by
    simpa [bm] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hb0_pos : 0 < b0 := by
    simpa [b0] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 0
  have hc0_pos : 0 < c0 := by
    simpa [c0] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 0
  have hbm_inv_le :
      bm⁻¹ ≤ (1 + delta) * b0⁻¹ := by
    have hratio : bm⁻¹ * b0 ≤ 1 + delta := by
      calc
        bm⁻¹ * b0 = b0 / bm := by ring
        _ ≤ 1 + delta := by
          exact (div_le_iff₀ hbm_pos).mpr (by simpa [bm, b0, mul_comm] using hgood_upper)
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hb0_pos).mpr hratio
  have hb0_inv_le_c0_inv : b0⁻¹ ≤ c0⁻¹ := by
    have hc0_le_b0 : c0 ≤ b0 := by
      simpa [b0, c0] using
        barSigmaStarAtScale_le_barSigmaAtScale_of_P4 hP hStruct hP4 0
    exact (inv_le_inv₀ hb0_pos hc0_pos).2 hc0_le_b0
  have hc0_inv_le_L0inv : c0⁻¹ ≤ L0inv := by
    simpa [c0, L0inv] using
      barSigmaStarAtScale_inv_le_lambdaInvMomentAtScale_zero_of_P4 hP hStruct hP4
  have hb0_inv_le_L0inv : b0⁻¹ ≤ L0inv :=
    hb0_inv_le_c0_inv.trans hc0_inv_le_L0inv
  calc
    (hP.barSigmaAtScale hStruct (m : ℤ))⁻¹ = bm⁻¹ := rfl
    _ ≤ (1 + delta) * b0⁻¹ := hbm_inv_le
    _ ≤ (1 + delta) * L0inv :=
      mul_le_mul_of_nonneg_left hb0_inv_le_L0inv hfactor_nonneg
    _ =
      (1 + delta) *
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := rfl

/-- Good-scale comparison: the starred normalization at scale `m` is controlled
by the scale-zero upper moment factor. -/
theorem barSigmaStarAtScale_le_one_add_delta_mul_LambdaMomentAtScale_zero_of_good
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (m : ℕ)
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) :
    hP.barSigmaStarAtScale hStruct (m : ℤ) ≤
      (1 + delta) *
        Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi := by
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let c0 := hP.barSigmaStarAtScale hStruct 0
  let b0 := hP.barSigmaAtScale hStruct 0
  let L0 := Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  have hfactor_nonneg : 0 ≤ 1 + delta := by linarith
  have hcm_pos : 0 < cm := by
    simpa [cm] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hc0_pos : 0 < c0 := by
    simpa [c0] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 0
  have hcm_le :
      cm ≤ (1 + delta) * c0 := by
    have hratio : cm * c0⁻¹ ≤ 1 + delta := by
      calc
        cm * c0⁻¹ ≤ cm * ((1 + delta) * cm⁻¹) :=
          mul_le_mul_of_nonneg_left (by simpa [cm, c0] using hgood_lower) hcm_pos.le
        _ = 1 + delta := by field_simp [hcm_pos.ne']
    have hdiv : cm / c0 ≤ 1 + delta := by
      simpa [div_eq_mul_inv] using hratio
    exact (div_le_iff₀ hc0_pos).mp hdiv
  have hc0_le_b0 : c0 ≤ b0 := by
    simpa [b0, c0] using
      barSigmaStarAtScale_le_barSigmaAtScale_of_P4 hP hStruct hP4 0
  have hb0_le_L0 : b0 ≤ L0 := by
    simpa [b0, L0] using
      barSigmaAtScale_le_LambdaMomentAtScale_zero_of_P4 hP hStruct hP4
  have hc0_le_L0 : c0 ≤ L0 := hc0_le_b0.trans hb0_le_L0
  calc
    hP.barSigmaStarAtScale hStruct (m : ℤ) = cm := rfl
    _ ≤ (1 + delta) * c0 := hcm_le
    _ ≤ (1 + delta) * L0 :=
      mul_le_mul_of_nonneg_left hc0_le_L0 hfactor_nonneg
    _ =
      (1 + delta) *
        Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi := rfl

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
