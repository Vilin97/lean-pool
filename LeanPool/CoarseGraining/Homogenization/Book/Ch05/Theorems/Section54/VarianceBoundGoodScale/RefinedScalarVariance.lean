/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.RefinedProbeMoments
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScalarVariance

/-! # Refined Scalar Variance -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Refined scalar variance estimates

This file reuses the scalar positive-part reduction from `ScalarVariance`, but
feeds it the sharper good-scale Rosenthal inputs from `RefinedProbeMoments`.
The resulting descendant-average budgets are expressed in terms of
`\widetilde\Theta_0`.
-/

private theorem widetildeThetaAtScale_zero_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ widetildeThetaAtScale P 0 hP4 := by
  simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale]
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)

private theorem coordinateProbeOriginMomentBudget_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) :
    0 ≤ 2 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) := by
  have hfactor : 0 ≤ 1 + delta := by linarith
  exact mul_nonneg (by norm_num)
    (mul_nonneg hfactor (widetildeThetaAtScale_zero_nonneg hP4))

private theorem pairProbeOriginMomentBudget_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) :
    0 ≤ 8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) := by
  have hfactor : 0 ≤ 1 + delta := by linarith
  exact mul_nonneg (by norm_num)
    (mul_nonneg hfactor (widetildeThetaAtScale_zero_nonneg hP4))

/-- Refined descendant-average budget for coordinate probes. -/
noncomputable def coordinateProbeRefinedDescendantAverageK
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (delta : ℝ) (j : ℕ) : ℝ :=
  let K0 := 2 * ((1 + delta) * widetildeThetaAtScale P 0 hP4)
  ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ)⁻¹ *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
        ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) ^
          (1 / (hP4.xi : ℝ)) * K0 +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
        Real.sqrt ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) * K0)

/-- Refined descendant-average budget for plus/minus pair probes. -/
noncomputable def pairProbeRefinedDescendantAverageK
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (delta : ℝ) (j : ℕ) : ℝ :=
  let K0 := 8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4)
  ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ)⁻¹ *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
        ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) ^
          (1 / (hP4.xi : ℝ)) * K0 +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
        Real.sqrt ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) * K0)

/-- Scalar variance budget for a single probe and refined descendant-average
budget `K`. -/
noncomputable def refinedScalarProbeVarianceBound
    {d : ℕ} (delta : ℝ) (q : FullBlockVec d) (K : ℝ) : ℝ :=
  4 * (delta * dotProduct q q) ^ (2 : ℕ) + 4 * K ^ (2 : ℕ) +
    2 * dotProduct q q * (delta * dotProduct q q + K)

/-- L1/L2 descendant-average bounds for coordinate probes with the refined
good-scale moment budget. -/
theorem coordinateProbe_restrictionCenteredDescendantAverage_abs_and_sq_le_refined
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m j : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (α : BlockCoord d) :
    let K := coordinateProbeRefinedDescendantAverageK hP4 delta j
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockCoordinateProbe α)) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockCoordinateProbe α)) a| ^ (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) := by
  dsimp only
  let K0 := 2 * ((1 + delta) * widetildeThetaAtScale P 0 hP4)
  let K := coordinateProbeRefinedDescendantAverageK hP4 delta j
  have hOrigin :=
    coordinateProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good
      hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower α
  have hroot :
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockCoordinateProbe α)) a| ^
          hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤ K := by
    have hraw :=
      fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_pow_rpow_inv_le
        hP hStruct hP4 (q := fullBlockCoordinateProbe α)
        (center := (m : ℤ)) (n := 0) (m := (j : ℤ)) (K := K0)
        (by norm_num) (by exact_mod_cast Nat.zero_le j)
        (by simpa [K0] using
          coordinateProbeOriginMomentBudget_nonneg hP4 hdelta_nonneg)
        hOrigin.1 (by simpa [K0, Ch04.annealedMomentRoot, one_div] using hOrigin.2)
    simpa [K, coordinateProbeRefinedDescendantAverageK, K0] using hraw
  exact
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_le_of_root
      hP hStruct hP4 (q := fullBlockCoordinateProbe α)
      (center := (m : ℤ)) (n := 0) (m := (j : ℤ))
      (by norm_num) (by exact_mod_cast Nat.zero_le j) hOrigin.1 hroot

private theorem pairProbe_restrictionCenteredDescendantAverage_abs_and_sq_le_refined_aux
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m j : ℕ)
    (_hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (_hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    {α β : BlockCoord d} (_hαβ : α ≠ β) (probe : FullBlockVec d)
    (hOrigin :
      Integrable
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
                probe) a| ^ hP4.xi) P ∧
        Ch04.annealedMomentRoot P hP4.xi
            (fun a =>
              |Ch04.restrictionCenteredOriginObservable P 0
                (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
                  probe) a|)
          ≤
            8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4)) :
    let K := pairProbeRefinedDescendantAverageK hP4 delta j
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ) probe) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ) probe) a| ^
            (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) := by
  dsimp only
  let K0 := 8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4)
  let K := pairProbeRefinedDescendantAverageK hP4 delta j
  have hroot :
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ) probe) a| ^
          hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤ K := by
    have hraw :=
      fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_pow_rpow_inv_le
        hP hStruct hP4 (q := probe)
        (center := (m : ℤ)) (n := 0) (m := (j : ℤ)) (K := K0)
        (by norm_num) (by exact_mod_cast Nat.zero_le j)
        (by simpa [K0] using pairProbeOriginMomentBudget_nonneg hP4 hdelta_nonneg)
        hOrigin.1 (by simpa [K0, Ch04.annealedMomentRoot, one_div] using hOrigin.2)
    simpa [K, pairProbeRefinedDescendantAverageK, K0] using hraw
  exact
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_le_of_root
      hP hStruct hP4 (q := probe)
      (center := (m : ℤ)) (n := 0) (m := (j : ℤ))
      (by norm_num) (by exact_mod_cast Nat.zero_le j) hOrigin.1 hroot

/-- L1/L2 descendant-average bounds for plus probes with the refined
good-scale moment budget. -/
theorem plusProbe_restrictionCenteredDescendantAverage_abs_and_sq_le_refined
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m j : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    let K := pairProbeRefinedDescendantAverageK hP4 delta j
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockPlusProbe α β)) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockPlusProbe α β)) a| ^ (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) :=
  pairProbe_restrictionCenteredDescendantAverage_abs_and_sq_le_refined_aux
    hP hStruct hP4 hdelta_nonneg m j hgood_upper hgood_lower hαβ
    (fullBlockPlusProbe α β)
    (plusProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good
      hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower hαβ)

/-- L1/L2 descendant-average bounds for minus probes with the refined
good-scale moment budget. -/
theorem minusProbe_restrictionCenteredDescendantAverage_abs_and_sq_le_refined
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m j : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    let K := pairProbeRefinedDescendantAverageK hP4 delta j
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockMinusProbe α β)) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockMinusProbe α β)) a| ^ (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) :=
  pairProbe_restrictionCenteredDescendantAverage_abs_and_sq_le_refined_aux
    hP hStruct hP4 hdelta_nonneg m j hgood_upper hgood_lower hαβ
    (fullBlockMinusProbe α β)
    (minusProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good
      hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower hαβ)

/-- Coordinate-probe scalar variance estimate using the refined descendant
average budget. -/
theorem coordinateProbe_scalarVariance_good_origin_le_refined
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m j : ℕ) (hj : j ≤ m)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (α : BlockCoord d) :
    let K := coordinateProbeRefinedDescendantAverageK hP4 delta j
    ∫ a,
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          (fullBlockCoordinateProbe α) (cubeSet (originCube d (j : ℤ))) a -
            dotProduct (fullBlockCoordinateProbe α) (fullBlockCoordinateProbe α)| ^
          (2 : ℕ) ∂P ≤
      refinedScalarProbeVarianceBound delta (fullBlockCoordinateProbe α) K := by
  dsimp only
  let K := coordinateProbeRefinedDescendantAverageK hP4 delta j
  have hOrigin :=
    coordinateProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good
      hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower α
  have hZ_int :=
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_integrable
      hP hStruct hP4 (q := fullBlockCoordinateProbe α)
      (center := (m : ℤ)) (n := 0) (m := (j : ℤ))
      (by norm_num) (by exact_mod_cast Nat.zero_le j) hOrigin.1
  have hZ_le :=
    coordinateProbe_restrictionCenteredDescendantAverage_abs_and_sq_le_refined
      hP hStruct hP4 hdelta_nonneg m j hgood_upper hgood_lower α
  simpa [K, refinedScalarProbeVarianceBound] using
    fullBlockNormalizedQuadraticObservable_scalarVariance_good_origin_le
      hP hStruct hP4 hdelta_nonneg m j hj hgood_upper hgood_lower
      (fullBlockCoordinateProbe α) hZ_int hZ_le

/-- Plus-probe scalar variance estimate using the refined descendant-average
budget. -/
theorem plusProbe_scalarVariance_good_origin_le_refined
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m j : ℕ) (hj : j ≤ m)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    let K := pairProbeRefinedDescendantAverageK hP4 delta j
    ∫ a,
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          (fullBlockPlusProbe α β) (cubeSet (originCube d (j : ℤ))) a -
            dotProduct (fullBlockPlusProbe α β) (fullBlockPlusProbe α β)| ^
          (2 : ℕ) ∂P ≤
      refinedScalarProbeVarianceBound delta (fullBlockPlusProbe α β) K := by
  dsimp only
  let K := pairProbeRefinedDescendantAverageK hP4 delta j
  have hOrigin :=
    plusProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good
      hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower hαβ
  have hZ_int :=
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_integrable
      hP hStruct hP4 (q := fullBlockPlusProbe α β)
      (center := (m : ℤ)) (n := 0) (m := (j : ℤ))
      (by norm_num) (by exact_mod_cast Nat.zero_le j) hOrigin.1
  have hZ_le :=
    plusProbe_restrictionCenteredDescendantAverage_abs_and_sq_le_refined
      hP hStruct hP4 hdelta_nonneg m j hgood_upper hgood_lower hαβ
  simpa [K, refinedScalarProbeVarianceBound] using
    fullBlockNormalizedQuadraticObservable_scalarVariance_good_origin_le
      hP hStruct hP4 hdelta_nonneg m j hj hgood_upper hgood_lower
      (fullBlockPlusProbe α β) hZ_int hZ_le

/-- Minus-probe scalar variance estimate using the refined descendant-average
budget. -/
theorem minusProbe_scalarVariance_good_origin_le_refined
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m j : ℕ) (hj : j ≤ m)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    let K := pairProbeRefinedDescendantAverageK hP4 delta j
    ∫ a,
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          (fullBlockMinusProbe α β) (cubeSet (originCube d (j : ℤ))) a -
            dotProduct (fullBlockMinusProbe α β) (fullBlockMinusProbe α β)| ^
          (2 : ℕ) ∂P ≤
      refinedScalarProbeVarianceBound delta (fullBlockMinusProbe α β) K := by
  dsimp only
  let K := pairProbeRefinedDescendantAverageK hP4 delta j
  have hOrigin :=
    minusProbe_centeredOrigin_momentRoot_le_widetildeTheta_of_good
      hP hStruct hP4 hdelta_nonneg m hgood_upper hgood_lower hαβ
  have hZ_int :=
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_integrable
      hP hStruct hP4 (q := fullBlockMinusProbe α β)
      (center := (m : ℤ)) (n := 0) (m := (j : ℤ))
      (by norm_num) (by exact_mod_cast Nat.zero_le j) hOrigin.1
  have hZ_le :=
    minusProbe_restrictionCenteredDescendantAverage_abs_and_sq_le_refined
      hP hStruct hP4 hdelta_nonneg m j hgood_upper hgood_lower hαβ
  simpa [K, refinedScalarProbeVarianceBound] using
    fullBlockNormalizedQuadraticObservable_scalarVariance_good_origin_le
      hP hStruct hP4 hdelta_nonneg m j hj hgood_upper hgood_lower
      (fullBlockMinusProbe α β) hZ_int hZ_le

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
