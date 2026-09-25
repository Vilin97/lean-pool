/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ProbeVariance

/-! # Scalar Variance -/

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
# Scalar variance estimates for the good-scale proof

This file combines the good-scale positive-part comparison, the P4
integrability bridges, and the Rosenthal descendant-average bounds into the
per-probe scalar variance estimates used by the finite-dimensional upgrade.
-/

/-- The descendant-average bound produced by Rosenthal for a coordinate probe. -/
noncomputable def coordinateProbeDescendantAverageK
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center m : ℤ) (α : BlockCoord d) : ℝ :=
  ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
        ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
          (1 / (hP4.xi : ℝ)) *
          (2 * coordinateProbeFactor hP hStruct center α *
            (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)) +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
        Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) *
          (2 * coordinateProbeFactor hP hStruct center α *
            (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)))

/-- The descendant-average bound produced by Rosenthal for a plus/minus pair
probe. -/
noncomputable def pairProbeDescendantAverageK
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center m : ℤ) (α β : BlockCoord d) : ℝ :=
  ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
        ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
          (1 / (hP4.xi : ℝ)) *
          (2 * pairProbeFactor hP hStruct center α β *
            (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)) +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
        Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) *
          (2 * pairProbeFactor hP hStruct center α β *
            (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)))

/-- Scalar variance estimate for a single normalized quadratic probe, assuming
the descendant average has already been bounded in L1 and L2. -/
theorem fullBlockNormalizedQuadraticObservable_scalarVariance_good_origin_le
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
    (q : FullBlockVec d) {K : ℝ}
    (hZ_int :
      Integrable
          (fun a : RegCoeffField d =>
            |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
              (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ) q) a|) P ∧
        Integrable
          (fun a : RegCoeffField d =>
            |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
              (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ) q) a| ^
                (2 : ℕ)) P)
    (hZ_le :
      (∫ a,
          |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
            (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ) q) a| ∂P ≤ K) ∧
        (∫ a,
          |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
            (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ) q) a| ^
              (2 : ℕ) ∂P ≤ K ^ (2 : ℕ))) :
    ∫ a,
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
          (cubeSet (originCube d (j : ℤ))) a - dotProduct q q| ^ (2 : ℕ) ∂P ≤
      4 * (delta * dotProduct q q) ^ (2 : ℕ) + 4 * K ^ (2 : ℕ) +
        2 * dotProduct q q * (delta * dotProduct q q + K) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : RegCoeffField d → ℝ := fun a =>
    fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
      (cubeSet (originCube d (j : ℤ))) a
  let Z : RegCoeffField d → ℝ :=
    Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
      (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ) q)
  let base : ℝ := dotProduct q q
  let err : ℝ := delta * base
  have hinputs :=
    integrable_fullBlockNormalizedQuadraticObservable_and_abs_sub_dotProduct_from_P4
      hP hStruct hP4 m j q
  have hbase_nonneg : 0 ≤ base := by
    simpa [base] using dotProduct_self_nonneg q
  have herr_nonneg : 0 ≤ err := by
    exact mul_nonneg hdelta_nonneg hbase_nonneg
  have hX_nonneg : ∀ᵐ a ∂P, 0 ≤ X a := by
    simpa [X] using
      fullBlockNormalizedQuadraticObservable_nonneg_ae
        hP hStruct (m : ℤ) q (originCube d (j : ℤ))
  have hmean_lower : base ≤ ∫ a, X a ∂P := by
    simpa [X, base] using
      dotProduct_le_integral_origin_fullBlockNormalizedQuadraticObservable_of_scalarChain
        hP hStruct hP4 m j hj q
  have hpos :
      (fun a : RegCoeffField d => max (X a - base) 0) ≤ᵐ[P]
        fun a => err + |Z a| := by
    simpa [X, Z, base, err] using
      fullBlockNormalizedQuadraticObservable_positivePart_good_origin_ae
        hP hStruct hP4 hdelta_nonneg m j hgood_upper hgood_lower q
  have hraw :=
    integral_abs_sub_sq_le_of_positivePart_control_of_centered_integrable
      (μ := P) (X := X) (Z := Z) (base := base) (err := err)
      hbase_nonneg herr_nonneg hX_nonneg hmean_lower
      (by simpa [X] using hinputs.1)
      (by simpa [X, base] using hinputs.2.1)
      (by simpa [X, base] using hinputs.2.2)
      (by simpa [Z] using hZ_int.1)
      (by simpa [Z] using hZ_int.2)
      hpos
  calc
    ∫ a, |X a - base| ^ (2 : ℕ) ∂P
        ≤ 4 * err ^ (2 : ℕ) + 4 * ∫ a, |Z a| ^ (2 : ℕ) ∂P +
            2 * base * (err + ∫ a, |Z a| ∂P) := hraw
    _ ≤ 4 * err ^ (2 : ℕ) + 4 * K ^ (2 : ℕ) +
        2 * base * (err + K) := by
          nlinarith [hbase_nonneg, hZ_le.1, hZ_le.2]
    _ =
        4 * (delta * dotProduct q q) ^ (2 : ℕ) + 4 * K ^ (2 : ℕ) +
          2 * dotProduct q q * (delta * dotProduct q q + K) := by
          simp [base, err]

/-- Coordinate-probe scalar variance estimate at a good scale. -/
theorem coordinateProbe_scalarVariance_good_origin_le
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
    let K := coordinateProbeDescendantAverageK hP hStruct hP4 (m : ℤ) (j : ℤ) α
    ∫ a,
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          (fullBlockCoordinateProbe α) (cubeSet (originCube d (j : ℤ))) a -
            dotProduct (fullBlockCoordinateProbe α) (fullBlockCoordinateProbe α)| ^
          (2 : ℕ) ∂P ≤
      4 * (delta * dotProduct (fullBlockCoordinateProbe α)
          (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
        4 * K ^ (2 : ℕ) +
        2 * dotProduct (fullBlockCoordinateProbe α) (fullBlockCoordinateProbe α) *
          (delta * dotProduct (fullBlockCoordinateProbe α) (fullBlockCoordinateProbe α) + K) := by
  dsimp only
  let K := coordinateProbeDescendantAverageK hP hStruct hP4 (m : ℤ) (j : ℤ) α
  have hOrigin :=
    coordinateProbe_centeredOrigin_momentRoot_le_factorSum
      hP hStruct hP4 (m : ℤ) α
  have hZ_int :=
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_integrable
      hP hStruct hP4 (q := fullBlockCoordinateProbe α)
      (center := (m : ℤ)) (n := 0) (m := (j : ℤ))
      (by norm_num) (by exact_mod_cast Nat.zero_le j) hOrigin.1
  have hZ_le : (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockCoordinateProbe α)) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockCoordinateProbe α)) a| ^ (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) := by
    simpa [K, coordinateProbeDescendantAverageK] using
      coordinateProbe_restrictionCenteredDescendantAverage_abs_and_sq_le
        hP hStruct hP4 (center := (m : ℤ)) (m := (j : ℤ))
        (by exact_mod_cast Nat.zero_le j) α
  simpa [K] using
    fullBlockNormalizedQuadraticObservable_scalarVariance_good_origin_le
      hP hStruct hP4 hdelta_nonneg m j hj hgood_upper hgood_lower
      (fullBlockCoordinateProbe α) hZ_int hZ_le

/-- Plus-pair scalar variance estimate at a good scale. -/
theorem plusProbe_scalarVariance_good_origin_le
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
    let K := pairProbeDescendantAverageK hP hStruct hP4 (m : ℤ) (j : ℤ) α β
    ∫ a,
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          (fullBlockPlusProbe α β) (cubeSet (originCube d (j : ℤ))) a -
            dotProduct (fullBlockPlusProbe α β) (fullBlockPlusProbe α β)| ^
          (2 : ℕ) ∂P ≤
      4 * (delta * dotProduct (fullBlockPlusProbe α β)
          (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
        4 * K ^ (2 : ℕ) +
        2 * dotProduct (fullBlockPlusProbe α β) (fullBlockPlusProbe α β) *
          (delta * dotProduct (fullBlockPlusProbe α β) (fullBlockPlusProbe α β) + K) := by
  dsimp only
  let K := pairProbeDescendantAverageK hP hStruct hP4 (m : ℤ) (j : ℤ) α β
  have hOrigin :=
    plusProbe_centeredOrigin_momentRoot_le_factorSum
      hP hStruct hP4 (m : ℤ) hαβ
  have hZ_int :=
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_integrable
      hP hStruct hP4 (q := fullBlockPlusProbe α β)
      (center := (m : ℤ)) (n := 0) (m := (j : ℤ))
      (by norm_num) (by exact_mod_cast Nat.zero_le j) hOrigin.1
  have hZ_le : (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockPlusProbe α β)) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockPlusProbe α β)) a| ^ (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) := by
    simpa [K, pairProbeDescendantAverageK] using
      plusProbe_restrictionCenteredDescendantAverage_abs_and_sq_le
        hP hStruct hP4 (center := (m : ℤ)) (m := (j : ℤ))
        (by exact_mod_cast Nat.zero_le j) hαβ
  simpa [K] using
    fullBlockNormalizedQuadraticObservable_scalarVariance_good_origin_le
      hP hStruct hP4 hdelta_nonneg m j hj hgood_upper hgood_lower
      (fullBlockPlusProbe α β) hZ_int hZ_le

/-- Minus-pair scalar variance estimate at a good scale. -/
theorem minusProbe_scalarVariance_good_origin_le
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
    let K := pairProbeDescendantAverageK hP hStruct hP4 (m : ℤ) (j : ℤ) α β
    ∫ a,
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ)
          (fullBlockMinusProbe α β) (cubeSet (originCube d (j : ℤ))) a -
            dotProduct (fullBlockMinusProbe α β) (fullBlockMinusProbe α β)| ^
          (2 : ℕ) ∂P ≤
      4 * (delta * dotProduct (fullBlockMinusProbe α β)
          (fullBlockMinusProbe α β)) ^ (2 : ℕ) +
        4 * K ^ (2 : ℕ) +
        2 * dotProduct (fullBlockMinusProbe α β) (fullBlockMinusProbe α β) *
          (delta * dotProduct (fullBlockMinusProbe α β) (fullBlockMinusProbe α β) + K) := by
  dsimp only
  let K := pairProbeDescendantAverageK hP hStruct hP4 (m : ℤ) (j : ℤ) α β
  have hOrigin :=
    minusProbe_centeredOrigin_momentRoot_le_factorSum
      hP hStruct hP4 (m : ℤ) hαβ
  have hZ_int :=
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_integrable
      hP hStruct hP4 (q := fullBlockMinusProbe α β)
      (center := (m : ℤ)) (n := 0) (m := (j : ℤ))
      (by norm_num) (by exact_mod_cast Nat.zero_le j) hOrigin.1
  have hZ_le : (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockMinusProbe α β)) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 (j : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (m : ℤ)
            (fullBlockMinusProbe α β)) a| ^ (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) := by
    simpa [K, pairProbeDescendantAverageK] using
      minusProbe_restrictionCenteredDescendantAverage_abs_and_sq_le
        hP hStruct hP4 (center := (m : ℤ)) (m := (j : ℤ))
        (by exact_mod_cast Nat.zero_le j) hαβ
  simpa [K] using
    fullBlockNormalizedQuadraticObservable_scalarVariance_good_origin_le
      hP hStruct hP4 hdelta_nonneg m j hj hgood_upper hgood_lower
      (fullBlockMinusProbe α β) hZ_int hZ_le

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
