/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingDefinitions
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspLocalization

/-!
# Finite-`p` local coarse-graining aggregation algebra

This file contains the elementary `ENNReal` power identities used to assemble
the finite-`p` local coarse-graining estimate.  It has no PDE content.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open scoped BigOperators ENNReal

noncomputable section

private theorem finiteLpExponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne

/-- The normalized `ENNReal` average over descendants at a prescribed
physical triadic scale. -/
noncomputable def descendantsAtScaleENNAverage {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (F : TriadicCube d → ℝ≥0∞) : ℝ≥0∞ :=
  ((descendantsAtScale Q k).card : ℝ≥0∞)⁻¹ *
    ∑ R ∈ descendantsAtScale Q k, F R

/-- At an admissible physical scale, the physical-scale average is precisely
the canonical depth-descendant average. -/
theorem descendantsAtScaleENNAverage_eq_descendantsENNAverage {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (F : TriadicCube d → ℝ≥0∞) :
    descendantsAtScaleENNAverage Q k F =
      descendantsENNAverage Q (Int.toNat (Q.scale - k)) F := by
  rw [descendantsAtScaleENNAverage, descendantsENNAverage,
    descendantsAtScale_eq_descendantsAtDepth Q hk]

/-- Raising the running-scale negative Besov seminorm to the finite exponent
recovers its unrooted depth-energy series. -/
theorem cubeEuclideanNegativeBesovESeminorm_rpow_eq_tsum_depthEnergy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    (cubeEuclideanNegativeBesovESeminorm Q s p F) ^ p.exponent.toReal =
      ∑' j : ℕ, cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
  rw [cubeEuclideanNegativeBesovESeminorm_eq_tsum_depthEnergy,
    ENNReal.rpow_inv_rpow (finiteLpExponent_toReal_pos p).ne']

/-- Raising the weighted local symmetric-energy aggregation to the finite
exponent exposes its exact running physical-scale series. -/
theorem weightedLocalSymmetricEnergyLp_rpow_eq_tsum {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q))
    (s1 s : FractionalOrder) (p : FiniteLpExponent) :
    (weightedLocalSymmetricEnergyLp Q n hn a u s1 s p) ^ p.exponent.toReal =
      ∑' j : ℕ,
        ENNReal.ofReal
            (Real.rpow 3 (-((s.1 - s1.1) * p.exponent.toReal * (j : ℝ)))) *
          ((descendantsAtScale Q (n - (j : ℤ))).card : ℝ≥0∞)⁻¹ *
            (descendantsAtScale Q (n - (j : ℤ))).attach.sum (fun R =>
              (localSymmetricEnergyENorm R.1
                (a.restrictToSubcube
                  (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
                (restrictH1ToSubcube u
                  (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^
                p.exponent.toReal) := by
  unfold weightedLocalSymmetricEnergyLp
  rw [one_div, ENNReal.rpow_inv_rpow (finiteLpExponent_toReal_pos p).ne']

/-- Normalized `ENNReal` descendant averages compose exactly across one
triadic generation. -/
theorem descendantsENNAverage_succ_eq_descendantsENNAverage_descendantsENNAverage
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ≥0∞) :
    descendantsENNAverage Q (j + 1) F =
      descendantsENNAverage Q j (fun R => descendantsENNAverage R 1 F) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hsum :
      ∑ S ∈ descendantsAtDepth Q (j + 1), F S =
        ∑ R ∈ D, ∑ S ∈ childCubes R, F S := by
    rw [descendantsAtDepth_succ, Finset.sum_biUnion]
    intro R hR S hS hRS
    exact disjoint_childCubes_of_ne hRS
  have hcoeff :
      (((descendantsAtDepth Q j).card * 3 ^ d : ℕ) : ℝ≥0∞)⁻¹ =
        ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ * ((3 ^ d : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [Nat.cast_mul]
    exact ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)
  calc
    descendantsENNAverage Q (j + 1) F =
        (((descendantsAtDepth Q j).card * 3 ^ d : ℕ) : ℝ≥0∞)⁻¹ *
          ∑ S ∈ descendantsAtDepth Q (j + 1), F S := by
            rw [descendantsENNAverage, descendantsAtDepth_card_succ]
    _ = (((descendantsAtDepth Q j).card * 3 ^ d : ℕ) : ℝ≥0∞)⁻¹ *
          ∑ R ∈ D, ∑ S ∈ childCubes R, F S := by rw [hsum]
    _ = ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (((3 ^ d : ℕ) : ℝ≥0∞)⁻¹ *
            ∑ R ∈ D, ∑ S ∈ childCubes R, F S) := by
          rw [hcoeff]
          ring
    _ = ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          ∑ R ∈ D, (((3 ^ d : ℕ) : ℝ≥0∞)⁻¹ *
            ∑ S ∈ childCubes R, F S) := by rw [Finset.mul_sum]
    _ = descendantsENNAverage Q j (fun R => descendantsENNAverage R 1 F) := by
          simp [descendantsENNAverage, D, childCubes_card]

/-- Normalized `ENNReal` descendant averages compose at arbitrary finite
depths. -/
theorem descendantsENNAverage_add_eq_descendantsENNAverage_descendantsENNAverage
    {d : ℕ} (Q : TriadicCube d) (j n : ℕ) (F : TriadicCube d → ℝ≥0∞) :
    descendantsENNAverage Q (j + n) F =
      descendantsENNAverage Q j (fun R => descendantsENNAverage R n F) := by
  induction n generalizing Q F with
  | zero => simp [descendantsENNAverage]
  | succ n ih =>
      calc
        descendantsENNAverage Q (j + (n + 1)) F =
            descendantsENNAverage Q (j + n)
              (fun R => descendantsENNAverage R 1 F) := by
                simpa [Nat.add_assoc] using
                  descendantsENNAverage_succ_eq_descendantsENNAverage_descendantsENNAverage
                    Q (j + n) F
        _ = descendantsENNAverage Q j (fun R =>
              descendantsENNAverage R n (fun S => descendantsENNAverage S 1 F)) := by
                simpa using ih Q (fun S => descendantsENNAverage S 1 F)
        _ = descendantsENNAverage Q j (fun R => descendantsENNAverage R (n + 1) F) := by
                refine congrArg (descendantsENNAverage Q j) ?_
                funext R
                symm
                exact
                  descendantsENNAverage_succ_eq_descendantsENNAverage_descendantsENNAverage
                    R n F

/-- The rooted geometric-tail loss is bounded by a single inverse gap, with
a constant independent of the finite exponent. -/
theorem geometricDiscount_rpow_neg_inv_le_twentyFive_mul_inv
    {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (halpha : 2 ≤ alpha) :
    Real.rpow (Book.Ch02.geometricDiscount delta alpha) (-1 / alpha) ≤
      25 * delta⁻¹ := by
  have halpha_pos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have hdisc_pos : 0 < Book.Ch02.geometricDiscount delta alpha :=
    Book.Ch02.book_geometricDiscount_pos (mul_pos hdelta halpha_pos)
  have hdisc_le_one : Book.Ch02.geometricDiscount delta alpha ≤ 1 := by
    unfold Book.Ch02.geometricDiscount
    have hpow_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-delta * alpha) :=
      Real.rpow_nonneg (by norm_num) _
    linarith
  have hpow_le :
      Real.rpow (Book.Ch02.geometricDiscount delta alpha) (-1 / alpha) ≤
        Real.rpow (Book.Ch02.geometricDiscount delta alpha) (-2 / alpha) := by
    apply Real.rpow_le_rpow_of_exponent_ge hdisc_pos hdisc_le_one
    field_simp [halpha_pos.ne']
    linarith
  have htail_le :
      Real.rpow (Book.Ch02.geometricDiscount delta alpha) (-2 / alpha) ≤
        25 * Real.rpow delta (-2 / alpha) :=
    Book.Ch02.geometricDiscount_rpow_neg_two_div_le_twentyFive_mul
      hdelta hdelta_le (by linarith)
  have hdelta_pow_le : Real.rpow delta (-2 / alpha) ≤ delta⁻¹ := by
    rw [show delta⁻¹ = Real.rpow delta (-1 : ℝ) by
      simpa using (Real.rpow_neg_one delta).symm]
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_le
    field_simp [halpha_pos.ne']
    linarith
  calc
    Real.rpow (Book.Ch02.geometricDiscount delta alpha) (-1 / alpha)
        ≤ Real.rpow (Book.Ch02.geometricDiscount delta alpha) (-2 / alpha) := hpow_le
    _ ≤ 25 * Real.rpow delta (-2 / alpha) := htail_le
    _ ≤ 25 * delta⁻¹ := by gcongr

/-- The preceding uniform tail bound specialized to a finite `Lp` exponent. -/
theorem geometricDiscount_rpow_neg_inv_le_twentyFive_mul_inv_finiteLp
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (p : FiniteLpExponent) (hp : 2 ≤ p.exponent.toReal) :
    Real.rpow (Book.Ch02.geometricDiscount delta p.exponent.toReal)
        (-1 / p.exponent.toReal) ≤ 25 * delta⁻¹ :=
  geometricDiscount_rpow_neg_inv_le_twentyFive_mul_inv hdelta hdelta_le hp

/-- `ENNReal` geometric-series form of the exponent-uniform rooted tail
bound.  The ratio is the triadic decay at gap `delta`. -/
theorem ENNReal_tsum_triadic_rpow_root_le_twentyFive_mul_inv
    {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (halpha : 2 ≤ alpha) :
    (∑' j : ℕ,
        (ENNReal.ofReal (Real.rpow 3 (-delta * alpha))) ^ j) ^ (1 / alpha) ≤
      ENNReal.ofReal (25 * delta⁻¹) := by
  have halpha_pos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have hratio_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-delta * alpha) :=
    Real.rpow_nonneg (by norm_num) _
  have hdisc_pos : 0 < Book.Ch02.geometricDiscount delta alpha :=
    Book.Ch02.book_geometricDiscount_pos (mul_pos hdelta halpha_pos)
  have htail :
      ∑' j : ℕ, (ENNReal.ofReal (Real.rpow 3 (-delta * alpha))) ^ j =
        ENNReal.ofReal (Book.Ch02.geometricDiscount delta alpha)⁻¹ := by
    rw [ENNReal.tsum_geometric, ENNReal.ofReal_inv_of_pos hdisc_pos]
    congr 1
    simpa [Book.Ch02.geometricDiscount] using
      (ENNReal.ofReal_sub 1 hratio_nonneg).symm
  have hroot :
      Real.rpow ((Book.Ch02.geometricDiscount delta alpha)⁻¹) (1 / alpha) =
        Real.rpow (Book.Ch02.geometricDiscount delta alpha) (-1 / alpha) := by
    calc
      Real.rpow ((Book.Ch02.geometricDiscount delta alpha)⁻¹) (1 / alpha) =
          Real.rpow (Book.Ch02.geometricDiscount delta alpha) (-(1 / alpha)) :=
            (Real.rpow_neg_eq_inv_rpow _ _).symm
      _ = Real.rpow (Book.Ch02.geometricDiscount delta alpha) (-1 / alpha) := by
            congr 1
            ring
  rw [htail, ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hdisc_pos)]
  apply ENNReal.ofReal_le_ofReal
  change Real.rpow ((Book.Ch02.geometricDiscount delta alpha)⁻¹) (1 / alpha) ≤
    25 * delta⁻¹
  rw [hroot]
  exact geometricDiscount_rpow_neg_inv_le_twentyFive_mul_inv hdelta hdelta_le halpha

/-- Finite-`Lp` specialization of the `ENNReal` triadic tail bound. -/
theorem ENNReal_tsum_triadic_rpow_root_le_twentyFive_mul_inv_finiteLp
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (p : FiniteLpExponent) (hp : 2 ≤ p.exponent.toReal) :
    (∑' j : ℕ,
        (ENNReal.ofReal (Real.rpow 3 (-delta * p.exponent.toReal))) ^ j) ^
          (1 / p.exponent.toReal) ≤
      ENNReal.ofReal (25 * delta⁻¹) :=
  ENNReal_tsum_triadic_rpow_root_le_twentyFive_mul_inv hdelta hdelta_le hp

end

end ABK26
end Ch03
end Book
end Homogenization
