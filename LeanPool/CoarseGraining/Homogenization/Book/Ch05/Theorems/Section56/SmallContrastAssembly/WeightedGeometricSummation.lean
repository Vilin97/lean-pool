/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.GeometricSum
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastJBound.Preliminaries

/-! # Weighted Geometric Summation -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace SmallContrastAssembly

open Section53.JUpperBoundCoarseFluctuations
open Section54.VarianceBoundGoodScale

/-!
# Weighted geometric summations for the Section 5.6 assembly step

These are the deterministic summation estimates used to convert the
beta-weighted scale-by-scale bounds in the small-contrast iteration into the
manuscript-style geometric tail at the bottom scale.
-/

/-- Constant for summing the spatial decay tail `3^{-d r}`. -/
noncomputable def weightedScaleDecaySumConst (d : ℕ) : ℝ :=
  (geometricDiscount (d : ℝ) 1)⁻¹

/-- Constant for summing the beta weights attached to the coarse-fluctuation
iteration. -/
noncomputable def weightedBetaSumConst (β : ℝ) : ℝ :=
  (geometricDiscount β 1)⁻¹

/-- Parameter-only beta-weight summation constant. -/
noncomputable def weightedBetaSumConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  weightedBetaSumConst (section53CoarseFluctuationBetaParams params)

/-- Parameter-only constant for the deterministic tau-sum compression. -/
noncomputable def coarseFluctuationTauSumConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  5 * (section53CoarseFluctuationBetaParams params)⁻¹

theorem weightedScaleDecaySumConst_pos {d : ℕ} [NeZero d] :
    0 < weightedScaleDecaySumConst d := by
  dsimp [weightedScaleDecaySumConst]
  have hd_nat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hd_nat
  exact inv_pos.mpr (geometricDiscount_pos (by simpa using hd))

theorem weightedScaleDecaySumConst_nonneg {d : ℕ} [NeZero d] :
    0 ≤ weightedScaleDecaySumConst d :=
  (weightedScaleDecaySumConst_pos (d := d)).le

theorem weightedBetaSumConst_pos {β : ℝ} (hβ : 0 < β) :
    0 < weightedBetaSumConst β := by
  dsimp [weightedBetaSumConst]
  exact inv_pos.mpr (geometricDiscount_pos (by simpa using hβ))

theorem weightedBetaSumConst_nonneg {β : ℝ} (hβ : 0 < β) :
    0 ≤ weightedBetaSumConst β :=
  (weightedBetaSumConst_pos hβ).le

theorem weightedBetaSumConstParams_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < weightedBetaSumConstParams params := by
  dsimp [weightedBetaSumConstParams]
  exact weightedBetaSumConst_pos (section53CoarseFluctuationBetaParams_pos params)

theorem coarseFluctuationTauSumConstParams_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < coarseFluctuationTauSumConstParams params := by
  dsimp [coarseFluctuationTauSumConstParams]
  exact mul_pos (by norm_num)
    (inv_pos.mpr (section53CoarseFluctuationBetaParams_pos params))

/-- A shifted finite tail of `3^{-α r}` is bounded by the full geometric
series. -/
theorem sum_Icc_shifted_rpow_decay_le_inv_geometricDiscount {α : ℝ}
    (hα : 0 < α) (k m : ℕ) :
    (∑ j ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-α * ((j - k : ℕ) : ℝ))) ≤
      (geometricDiscount α 1)⁻¹ := by
  classical
  let f : ℕ → ℝ := fun r => Real.rpow (3 : ℝ) (-α * (r : ℝ))
  let s : Finset ℕ := (Finset.Icc (k + 1) m).image fun j => j - k
  have hinj : Set.InjOn (fun j => j - k) (Finset.Icc (k + 1) m) := by
    intro a ha b hb hab
    have ha' : a ∈ Finset.Icc (k + 1) m := by simpa using ha
    have hb' : b ∈ Finset.Icc (k + 1) m := by simpa using hb
    have ha_ge : k ≤ a := by
      have h := (Finset.mem_Icc.mp ha').1
      omega
    have hb_ge : k ≤ b := by
      have h := (Finset.mem_Icc.mp hb').1
      omega
    have hab' : a - k = b - k := by simpa using hab
    calc
      a = (a - k) + k := (Nat.sub_add_cancel ha_ge).symm
      _ = (b - k) + k := by rw [hab']
      _ = b := Nat.sub_add_cancel hb_ge
  have hsum_image :
      (∑ j ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-α * ((j - k : ℕ) : ℝ))) =
        ∑ r ∈ s, f r := by
    calc
      (∑ j ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-α * ((j - k : ℕ) : ℝ))) =
          ∑ j ∈ Finset.Icc (k + 1) m, f (j - k) := by
            simp [f]
      _ = ∑ r ∈ s, f r := by
            simpa [s] using
              (Finset.sum_image (s := Finset.Icc (k + 1) m)
                (g := fun j => j - k) (f := f) hinj).symm
  have hsummable : Summable f :=
    Section52.summable_rpow_three_neg_mul_nat hα
  rw [hsum_image]
  calc
    (∑ r ∈ s, f r) ≤ ∑' r : ℕ, f r :=
      hsummable.sum_le_tsum s
        (fun r _hr => Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    _ = (geometricDiscount α 1)⁻¹ := by
      simpa [f] using
        Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hα

/-- The shifted beta-weight sum over `j = k + 1, ..., m` is bounded by the
full beta geometric tail. -/
theorem sum_Icc_shifted_varianceWeight_le_inv_geometricDiscount {β : ℝ}
    (hβ : 0 < β) (k m : ℕ) :
    (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j) ≤
      weightedBetaSumConst β := by
  classical
  let f : ℕ → ℝ := fun r => Real.rpow (3 : ℝ) (-β * (r : ℝ))
  let s : Finset ℕ := (Finset.Icc (k + 1) m).image fun j => m - j
  have hinj : Set.InjOn (fun j => m - j) (Finset.Icc (k + 1) m) := by
    intro a ha b hb hab
    have ha_le : a ≤ m := (Finset.mem_Icc.mp ha).2
    have hb_le : b ≤ m := (Finset.mem_Icc.mp hb).2
    exact (tsub_right_inj ha_le hb_le).1 hab
  have hsum_image :
      (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j) =
        ∑ r ∈ s, f r := by
    calc
      (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j) =
          ∑ j ∈ Finset.Icc (k + 1) m, f (m - j) := by
            simp [f, varianceWeight]
      _ = ∑ r ∈ s, f r := by
            simpa [s] using
              (Finset.sum_image (s := Finset.Icc (k + 1) m)
                (g := fun j => m - j) (f := f) hinj).symm
  have hsummable : Summable f :=
    Section52.summable_rpow_three_neg_mul_nat hβ
  rw [hsum_image]
  dsimp [weightedBetaSumConst]
  calc
    (∑ r ∈ s, f r) ≤ ∑' r : ℕ, f r :=
      hsummable.sum_le_tsum s
        (fun r _hr => Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    _ = (geometricDiscount β 1)⁻¹ := by
      simpa [f] using
        Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hβ

/-- The spatially decaying term in the fluctuation budget sums to the bottom
scale `3^{-d(k-ell)}` up to a dimension-only constant. -/
theorem sum_Icc_varianceWeight_mul_scaleDecay_le_const
    {β : ℝ} (hβ_nonneg : 0 ≤ β) {d : ℕ} [NeZero d]
    {ell k m : ℕ} (hellk : ell ≤ k) :
    (∑ j ∈ Finset.Icc (k + 1) m,
        varianceWeight β m j *
          Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ))) ≤
      weightedScaleDecaySumConst d *
        Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) := by
  classical
  let baseDecay : ℝ :=
    Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ))
  let tail : ℕ → ℝ := fun r =>
    Real.rpow (3 : ℝ) (-(d : ℝ) * (r : ℝ))
  have hbase_nonneg : 0 ≤ baseDecay := by
    dsimp [baseDecay]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hd_nat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hd_nat
  have htail_sum :
      (∑ j ∈ Finset.Icc (k + 1) m, tail (j - k)) ≤
        weightedScaleDecaySumConst d := by
    simpa [tail, weightedScaleDecaySumConst] using
      sum_Icc_shifted_rpow_decay_le_inv_geometricDiscount (α := (d : ℝ)) hd k m
  have hpoint :
      ∀ j, j ∈ Finset.Icc (k + 1) m →
        varianceWeight β m j *
            Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) ≤
          baseDecay * tail (j - k) := by
    intro j hj
    have hj_ge : k ≤ j := by
      have h := (Finset.mem_Icc.mp hj).1
      omega
    have hsub : j - ell = (k - ell) + (j - k) := by omega
    have hexp :
        -(d : ℝ) * ((j - ell : ℕ) : ℝ) =
          -(d : ℝ) * ((k - ell : ℕ) : ℝ) +
            (-(d : ℝ) * ((j - k : ℕ) : ℝ)) := by
      rw [hsub, Nat.cast_add]
      ring
    have hdecay_eq :
        Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) =
          baseDecay * tail (j - k) := by
      dsimp [baseDecay, tail]
      rw [hexp]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hweight_le_one : varianceWeight β m j ≤ 1 := by
      unfold varianceWeight
      have hdist_nonneg : 0 ≤ ((m - j : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le (m - j)
      have hexp_nonpos : -β * ((m - j : ℕ) : ℝ) ≤ 0 := by nlinarith
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3) hexp_nonpos
    have hdecay_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    calc
      varianceWeight β m j *
          Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ))
          ≤ 1 * Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hweight_le_one hdecay_nonneg
      _ = baseDecay * tail (j - k) := by rw [one_mul, hdecay_eq]
  calc
    (∑ j ∈ Finset.Icc (k + 1) m,
        varianceWeight β m j *
          Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ))) ≤
        ∑ j ∈ Finset.Icc (k + 1) m, baseDecay * tail (j - k) :=
      Finset.sum_le_sum hpoint
    _ = baseDecay * ∑ j ∈ Finset.Icc (k + 1) m, tail (j - k) := by
      rw [Finset.mul_sum]
    _ ≤ baseDecay * weightedScaleDecaySumConst d :=
      mul_le_mul_of_nonneg_left htail_sum hbase_nonneg
    _ = weightedScaleDecaySumConst d * baseDecay := by ring

/-- Weighted summation of a geometric contribution plus a nonnegative constant
contribution. -/
theorem sum_Icc_varianceWeight_mul_geometric_add_const_le
    {β A B : ℝ} (hβ : 0 < β) {d : ℕ} [NeZero d]
    {ell k m : ℕ} (hellk : ell ≤ k)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B) :
    (∑ j ∈ Finset.Icc (k + 1) m,
        varianceWeight β m j *
          (A * Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) + B)) ≤
      A * weightedScaleDecaySumConst d *
          Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) +
        weightedBetaSumConst β * B := by
  classical
  have hscale :
      (∑ j ∈ Finset.Icc (k + 1) m,
          varianceWeight β m j *
            Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ))) ≤
        weightedScaleDecaySumConst d *
          Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) :=
    sum_Icc_varianceWeight_mul_scaleDecay_le_const (β := β) hβ.le hellk
  have hweight :
      (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j) ≤
        weightedBetaSumConst β :=
    sum_Icc_shifted_varianceWeight_le_inv_geometricDiscount hβ k m
  have hleft_eq :
      (∑ j ∈ Finset.Icc (k + 1) m,
          varianceWeight β m j *
            (A * Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) + B)) =
        A *
            (∑ j ∈ Finset.Icc (k + 1) m,
              varianceWeight β m j *
                Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ))) +
          (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j) * B := by
    let D : ℕ → ℝ := fun j =>
      Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ))
    have htermA :
        (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j * (A * D j)) =
          A * (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j * D j) := by
      calc
        (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j * (A * D j)) =
            ∑ j ∈ Finset.Icc (k + 1) m, A * (varianceWeight β m j * D j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
        _ = A * (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j * D j) := by
              rw [Finset.mul_sum]
    have htermB :
        (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j * B) =
          (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j) * B := by
      rw [Finset.sum_mul]
    calc
      (∑ j ∈ Finset.Icc (k + 1) m,
          varianceWeight β m j *
            (A * Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)) + B)) =
          (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j * (A * D j)) +
            (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j * B) := by
            simp [D, mul_add, Finset.sum_add_distrib]
      _ =
          A *
              (∑ j ∈ Finset.Icc (k + 1) m,
                varianceWeight β m j *
                  Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ))) +
            (∑ j ∈ Finset.Icc (k + 1) m, varianceWeight β m j) * B := by
            rw [htermA, htermB]
  rw [hleft_eq]
  exact add_le_add
    (by
      calc
        A *
            (∑ j ∈ Finset.Icc (k + 1) m,
              varianceWeight β m j *
                Real.rpow (3 : ℝ) (-(d : ℝ) * ((j - ell : ℕ) : ℝ)))
            ≤ A *
                (weightedScaleDecaySumConst d *
                  Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left hscale hA_nonneg
        _ = A * weightedScaleDecaySumConst d *
              Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) := by ring)
    (mul_le_mul_of_nonneg_right hweight hB_nonneg)

/-- Parameter-dependent version of the deterministic tau-sum compression.  The
constant depends on the quantitative ellipticity package, not on the law. -/
theorem coarseFluctuationTauSumAtScale_le_const_tauAtScale_of_params
    {d : ℕ} [NeZero d] (params : QuantitativeCoarseGrainedEllipticityParams d)
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = params)
    {k m : ℕ} (hkm : k ≤ m) (e : Vec d) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    coarseFluctuationTauSumAtScale hP hStruct hP4 k m e ≤
      coarseFluctuationTauSumConstParams params *
        tauAtScale P (m : ℤ) (k : ℤ) p_e q_e := by
  dsimp only
  have hraw :=
    coarseFluctuationTauSumAtScale_le_five_beta_inv_tauAtScale
      hP hstat hStruct hP4 hkm e
  have hβeq :
      section53CoarseFluctuationBeta hP4 =
        section53CoarseFluctuationBetaParams params := by
    rw [← section53CoarseFluctuationBetaParams_eq_of_P4 hP4, hparams]
  simpa [coarseFluctuationTauSumConstParams, hβeq] using hraw

end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
