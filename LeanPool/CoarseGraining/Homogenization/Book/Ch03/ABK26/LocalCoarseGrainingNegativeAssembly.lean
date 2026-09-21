/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingAggregation

/-!
# Exact negative-Besov assembly for local coarse graining

This module flattens the nested normalized descendant average in the
source-facing local negative Besov carrier into its physical-scale series.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open scoped BigOperators ENNReal

noncomputable section

private theorem finiteLpExponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne

private theorem descendantsENNAverage_tsum_eq_tsum_descendantsENNAverage
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℕ → ℝ≥0∞) :
    descendantsENNAverage Q j (fun R => ∑' n : ℕ, F R n) =
      ∑' n : ℕ, descendantsENNAverage Q j (fun R => F R n) := by
  classical
  unfold descendantsENNAverage
  rw [show (∑ R ∈ descendantsAtDepth Q j, (fun R => ∑' n : ℕ, F R n) R) =
      ∑' n : ℕ, ∑ R ∈ descendantsAtDepth Q j, F R n by
    exact (Summable.tsum_finsetSum (fun R _ => ENNReal.summable)).symm]
  rw [← ENNReal.tsum_mul_left]

private theorem physicalScaleDepth_add {d : ℕ} (Q : TriadicCube d)
    (n : ℤ) (hn : n ≤ Q.scale) (j : ℕ) :
    Int.toNat (Q.scale - (n - (j : ℤ))) = Int.toNat (Q.scale - n) + j := by
  have h0 : 0 ≤ Q.scale - n := by omega
  have hj : 0 ≤ (j : ℤ) := by positivity
  rw [show Q.scale - (n - (j : ℤ)) = (Q.scale - n) + j by ring,
    Int.toNat_add h0 hj]
  simp

private theorem descendantsAtScaleENNAverage_tsum_eq_tsum_descendantsAtScaleENNAverage
    {d : ℕ} (Q : TriadicCube d) (k : ℤ)
    (F : TriadicCube d → ℕ → ℝ≥0∞) :
    descendantsAtScaleENNAverage Q k (fun R => ∑' j : ℕ, F R j) =
      ∑' j : ℕ, descendantsAtScaleENNAverage Q k (fun R => F R j) := by
  classical
  unfold descendantsAtScaleENNAverage
  rw [show (∑ R ∈ descendantsAtScale Q k, (fun R => ∑' j : ℕ, F R j) R) =
      ∑' j : ℕ, ∑ R ∈ descendantsAtScale Q k, F R j by
    exact (Summable.tsum_finsetSum (fun R _ => ENNReal.summable)).symm]
  rw [← ENNReal.tsum_mul_left]

private theorem descendantsAtScaleENNAverage_mul_left {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (c : ℝ≥0∞) (F : TriadicCube d → ℝ≥0∞) :
    descendantsAtScaleENNAverage Q k (fun R => c * F R) =
      c * descendantsAtScaleENNAverage Q k F := by
  unfold descendantsAtScaleENNAverage
  rw [← Finset.mul_sum]
  ring

private theorem descendantsAtScaleENNAverage_nested_eq {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale) (j : ℕ)
    (F : TriadicCube d → ℝ≥0∞) :
    descendantsAtScaleENNAverage Q n (fun R =>
      descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F) =
      descendantsAtScaleENNAverage Q (n - (j : ℤ)) F := by
  rw [descendantsAtScaleENNAverage_eq_descendantsENNAverage Q n hn]
  have hinner : (fun R : TriadicCube d =>
      descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F) =
      (fun R => descendantsENNAverage R j F) := by
    funext R
    rw [descendantsAtScaleENNAverage_eq_descendantsENNAverage R
      (R.scale - (j : ℤ)) (by omega)]
    simp
  rw [hinner]
  rw [← descendantsENNAverage_add_eq_descendantsENNAverage_descendantsENNAverage]
  rw [← physicalScaleDepth_add Q n hn j]
  exact (descendantsAtScaleENNAverage_eq_descendantsENNAverage Q
    (n - (j : ℤ)) (by omega) F).symm

private theorem localFluxDefectNegativeBesovESeminorm_rpow_eq_tsum
    {d : ℕ} {Q R : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (u : H1Function (openCubeSet Q)) (s : FractionalOrder)
    (p : FiniteLpExponent) :
    (cubeEuclideanNegativeBesovESeminorm R s p
      (localFluxDefectL2Field a hRQ sigma0 u)) ^ p.exponent.toReal =
      ∑' j : ℕ,
        ENNReal.ofReal (Real.rpow 3
          (s.1 * p.exponent.toReal * ((R.scale - (j : ℤ) : ℤ) : ℝ))) *
          descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) (fun S =>
            (ENNReal.ofReal ‖cubeAverageVec S
              (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
                (u.grad x))‖) ^ p.exponent.toReal) := by
  rw [cubeEuclideanNegativeBesovESeminorm_rpow_eq_tsum_depthEnergy]
  apply tsum_congr
  intro j
  unfold cubeEuclideanNegativeBesovDepthEnergy descendantsAtScaleENNAverage
  simp only [localFluxDefectL2Field, mul_assoc]
  have hsum := Finset.sum_attach (descendantsAtScale R (R.scale - (j : ℤ)))
    (fun S =>
      (ENNReal.ofReal ‖cubeAverageVec S
        (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
          (u.grad x))‖) ^ p.exponent.toReal)
  rw [hsum]

private theorem descendantsAtScaleENNAverage_negativeDepth_tsum_eq
    {d : ℕ} (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (F : TriadicCube d → ℝ≥0∞) :
    descendantsAtScaleENNAverage Q n (fun R => ∑' j : ℕ,
      ENNReal.ofReal (Real.rpow 3
        (s.1 * p.exponent.toReal * ((R.scale - (j : ℤ) : ℤ) : ℝ))) *
        descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F) =
      ∑' j : ℕ,
        ENNReal.ofReal (Real.rpow 3
          (s.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
          descendantsAtScaleENNAverage Q (n - (j : ℤ)) F := by
  rw [descendantsAtScaleENNAverage_tsum_eq_tsum_descendantsAtScaleENNAverage]
  apply tsum_congr
  intro j
  have hweight : ∀ R ∈ descendantsAtScale Q n,
      ENNReal.ofReal (Real.rpow 3
        (s.1 * p.exponent.toReal * ((R.scale - (j : ℤ) : ℤ) : ℝ))) =
        ENNReal.ofReal (Real.rpow 3
          (s.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) := by
    intro R hR
    rw [descendant_scale_eq_of_mem_descendantsAtScale hR]
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3
    (s.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ)))
  calc
    descendantsAtScaleENNAverage Q n (fun R =>
        ENNReal.ofReal (Real.rpow 3
          (s.1 * p.exponent.toReal * ((R.scale - (j : ℤ) : ℤ) : ℝ))) *
          descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F) =
        descendantsAtScaleENNAverage Q n (fun R =>
          c * descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F) := by
            unfold descendantsAtScaleENNAverage
            congr 1
            apply Finset.sum_congr rfl
            intro R hR
            exact congrArg (fun z : ℝ≥0∞ =>
              z * descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F)
              (hweight R hR)
    _ = c * descendantsAtScaleENNAverage Q n (fun R =>
          descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F) :=
      descendantsAtScaleENNAverage_mul_left Q n c _
    _ = ENNReal.ofReal (Real.rpow 3
          (s.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
        descendantsAtScaleENNAverage Q (n - (j : ℤ)) F := by
      rw [descendantsAtScaleENNAverage_nested_eq Q n hn j F]

/-- Raising the local finite-`p` flux-defect negative Besov average exposes
the exact physical-scale depth series. -/
theorem localFluxDefectNegativeBesovLpAverage_rpow_eq_tsum_descendantsAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (u : H1Function (openCubeSet Q))
    (s : FractionalOrder) (p : FiniteLpExponent) :
    (localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p) ^
        p.exponent.toReal =
      ∑' j : ℕ,
        ENNReal.ofReal (Real.rpow 3
          (-(s.1 * p.exponent.toReal * (j : ℝ)))) *
          descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
            (ENNReal.ofReal ‖cubeAverageVec R
              (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
                (u.grad x))‖) ^ p.exponent.toReal) := by
  classical
  let alpha : ℝ := p.exponent.toReal
  let F : TriadicCube d → ℝ≥0∞ := fun R =>
    (ENNReal.ofReal ‖cubeAverageVec R
      (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
        (u.grad x))‖) ^ alpha
  have halpha : 0 < alpha := finiteLpExponent_toReal_pos p
  have hbase : 0 ≤ Real.rpow 3 (-s.1 * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  unfold localFluxDefectNegativeBesovLpAverage
  rw [ENNReal.mul_rpow_of_nonneg _ _ halpha.le]
  have halpha_inv : 1 / p.exponent.toReal = alpha⁻¹ := by simp [alpha]
  rw [halpha_inv]
  rw [ENNReal.rpow_inv_rpow halpha.ne']
  rw [ENNReal.ofReal_rpow_of_nonneg hbase halpha.le]
  have hbase_pow : Real.rpow 3 (-s.1 * (n : ℝ)) ^ alpha =
      Real.rpow 3 ((-s.1 * (n : ℝ)) * alpha) :=
    (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
  rw [hbase_pow]
  have hinner :
      ((descendantsAtScale Q n).card : ℝ≥0∞)⁻¹ *
        (descendantsAtScale Q n).attach.sum (fun R =>
          (cubeEuclideanNegativeBesovESeminorm R.1 s p
            (localFluxDefectL2Field a
              (openCubeSet_subset_of_mem_descendantsAtScale hn R.2)
              sigma0 u)) ^ alpha) =
        descendantsAtScaleENNAverage Q n (fun R => ∑' j : ℕ,
          ENNReal.ofReal (Real.rpow 3
            (s.1 * alpha * ((R.scale - (j : ℤ) : ℤ) : ℝ))) *
            descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F) := by
    unfold descendantsAtScaleENNAverage
    let D : Finset (TriadicCube d) := descendantsAtScale Q n
    have hterm (R : TriadicCube d) (hR : R ∈ D) :
        (cubeEuclideanNegativeBesovESeminorm R s p
          (localFluxDefectL2Field a
            (openCubeSet_subset_of_mem_descendantsAtScale hn hR)
            sigma0 u)) ^ alpha =
          ∑' j : ℕ,
            ENNReal.ofReal (Real.rpow 3
              (s.1 * alpha * ((R.scale - (j : ℤ) : ℤ) : ℝ))) *
              descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F := by
      simpa only [F, alpha] using
        (localFluxDefectNegativeBesovESeminorm_rpow_eq_tsum a sigma0
          (openCubeSet_subset_of_mem_descendantsAtScale hn hR) u s p)
    have hsum :
        (∑ R ∈ D.attach,
          (cubeEuclideanNegativeBesovESeminorm R.1 s p
            (localFluxDefectL2Field a
              (openCubeSet_subset_of_mem_descendantsAtScale hn R.2)
              sigma0 u)) ^ alpha) =
          ∑ R ∈ D, ∑' j : ℕ,
            ENNReal.ofReal (Real.rpow 3
              (s.1 * alpha * ((R.scale - (j : ℤ) : ℤ) : ℝ))) *
              descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F := by
      let f : TriadicCube d → ℝ≥0∞ := fun R => ∑' j : ℕ,
        ENNReal.ofReal (Real.rpow 3
          (s.1 * alpha * ((R.scale - (j : ℤ) : ℤ) : ℝ))) *
          descendantsAtScaleENNAverage R (R.scale - (j : ℤ)) F
      calc
        (∑ R ∈ D.attach,
            (cubeEuclideanNegativeBesovESeminorm R.1 s p
              (localFluxDefectL2Field a
                (openCubeSet_subset_of_mem_descendantsAtScale hn R.2)
                sigma0 u)) ^ alpha) =
            ∑ R ∈ D.attach, f R.1 := by
          apply Finset.sum_congr rfl
          intro R hR
          simpa only [f] using hterm R.1 R.2
        _ = ∑ R ∈ D, f R := Finset.sum_attach D f
        _ = _ := by rfl
    simpa only [D] using! congrArg
      (fun z : ℝ≥0∞ => ((descendantsAtScale Q n).card : ℝ≥0∞)⁻¹ * z) hsum
  rw [hinner, descendantsAtScaleENNAverage_negativeDepth_tsum_eq Q n hn s p F]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  rw [← mul_assoc]
  congr 1
  calc
    ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ) * alpha)) *
        ENNReal.ofReal (Real.rpow 3
          (s.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) =
        ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ) * alpha) *
          Real.rpow 3
            (s.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) :=
      (ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)).symm
    _ = ENNReal.ofReal (Real.rpow 3
          (-(s.1 * p.exponent.toReal * (j : ℝ)))) := by
      congr 1
      calc
        Real.rpow 3 (-s.1 * (n : ℝ) * alpha) *
            Real.rpow 3
              (s.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ)) =
            Real.rpow 3 (-s.1 * (n : ℝ) * alpha +
              s.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ)) :=
              (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
        _ = Real.rpow 3 (-(s.1 * p.exponent.toReal * (j : ℝ))) := by
          congr 1
          dsimp [alpha]
          push_cast
          ring

end
end ABK26
end Ch03
end Book
end Homogenization
