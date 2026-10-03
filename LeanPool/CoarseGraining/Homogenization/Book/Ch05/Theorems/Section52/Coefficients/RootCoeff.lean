/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.Coefficients.Constants

/-! # Root Coeff -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

theorem section52LargeScaleLpRootCoeff_eq_const_mul_decay_mul_gap_rpow
    {d ξ : ℕ} {s : ℝ} {m : ℕ} {n : ℤ}
    (hn : n ∈ section52LargeScaleSet m) :
    section52LargeScaleLpRootCoeff d ξ s m n =
      (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ) (-(d - s) * (Int.toNat n : ℝ)) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hn_nonneg : 0 ≤ n := section52LargeScaleSet_mem_nonneg hn
  have hn_le : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
  rw [section52LargeScaleLpRootCoeff, section52LargeScaleWeight, geometricWeight_one_eq]
  rw [section52_descendantsAtScale_originCube_large_card_rpow d ξ m hn_le]
  rw [section52_descendantsAtScale_originCube_int_zero_card_inv d hn_nonneg]
  rw [section52_descendantsAtScale_originCube_int_zero_card_rpow d ξ hn_nonneg]
  have hdepth :
      (Int.toNat ((m : ℤ) - n) : ℝ) + (Int.toNat n : ℝ) = (m : ℝ) := by
    exact_mod_cast section52LargeScaleSet_toNat_sub_add_toNat hn
  have hpow :
      Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.rpow (3 : ℝ)
            (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
              Real.rpow (3 : ℝ) (((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ)) =
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ) (-(d - s) * (Int.toNat n : ℝ)) := by
    calc
      Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.rpow (3 : ℝ)
            (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
              Real.rpow (3 : ℝ) (((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ)) =
        (Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.rpow (3 : ℝ)
              (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ))) *
          (Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
            Real.rpow (3 : ℝ) (((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ))) := by
          ring
      _ =
        Real.rpow (3 : ℝ)
            (-s * (Int.toNat ((m : ℤ) - n) : ℝ) +
              ((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.rpow (3 : ℝ)
            (-(d : ℝ) * (Int.toNat n : ℝ) +
              ((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ)) := by
          have hAB :
              Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
                  Real.rpow (3 : ℝ)
                    (((d : ℝ) / (ξ : ℝ)) *
                      (Int.toNat ((m : ℤ) - n) : ℝ)) =
                Real.rpow (3 : ℝ)
                  (-s * (Int.toNat ((m : ℤ) - n) : ℝ) +
                    ((d : ℝ) / (ξ : ℝ)) *
                      (Int.toNat ((m : ℤ) - n) : ℝ)) :=
            (Real.rpow_add h3
              (-s * (Int.toNat ((m : ℤ) - n) : ℝ))
              (((d : ℝ) / (ξ : ℝ)) *
                (Int.toNat ((m : ℤ) - n) : ℝ))).symm
          have hCD :
              Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
                  Real.rpow (3 : ℝ)
                    (((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ)) =
                Real.rpow (3 : ℝ)
                  (-(d : ℝ) * (Int.toNat n : ℝ) +
                    ((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ)) :=
            (Real.rpow_add h3
              (-(d : ℝ) * (Int.toNat n : ℝ))
              (((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ))).symm
          exact congrArg₂ (fun x y : ℝ => x * y) hAB hCD
      _ =
        Real.rpow (3 : ℝ)
          ((-s * (Int.toNat ((m : ℤ) - n) : ℝ) +
              ((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) +
            (-(d : ℝ) * (Int.toNat n : ℝ) +
              ((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ))) := by
          exact (Real.rpow_add h3
            (-s * (Int.toNat ((m : ℤ) - n) : ℝ) +
              ((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ))
            (-(d : ℝ) * (Int.toNat n : ℝ) +
              ((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ))).symm
      _ =
        Real.rpow (3 : ℝ)
          (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ) + -(d - s) *
            (Int.toNat n : ℝ)) := by
          congr 1
          have hdepth_sub :
              (Int.toNat ((m : ℤ) - n) : ℝ) =
                (m : ℝ) - (Int.toNat n : ℝ) := by
            linarith
          rw [hdepth_sub]
          ring_nf
      _ =
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ) (-(d - s) * (Int.toNat n : ℝ)) := by
          exact Real.rpow_add h3
            (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))
            (-(d - s) * (Int.toNat n : ℝ))
  calc
    geometricDiscount s 1 * Real.rpow (3 : ℝ)
        (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        (Real.rpow (3 : ℝ)
          (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          (Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
            (Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ *
              Real.rpow (3 : ℝ)
                (((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ)) * 2))) =
      (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
        (Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.rpow (3 : ℝ)
            (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
              Real.rpow (3 : ℝ)
                (((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ))) := by
        ring
    _ =
      (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
        (Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ) (-(d - s) * (Int.toNat n : ℝ))) := by
        rw [hpow]
    _ =
      (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ) (-(d - s) * (Int.toNat n : ℝ)) := by
        ring

theorem section52LargeScaleSqrtRootCoeff_eq_const_mul_decay_mul_gap_rpow
    {d ξ : ℕ} {s : ℝ} {m : ℕ} {n : ℤ}
    (hn : n ∈ section52LargeScaleSet m) :
    section52LargeScaleSqrtRootCoeff d ξ s m n =
      (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ)
            (-(((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) * (Int.toNat n : ℝ)) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hn_nonneg : 0 ≤ n := section52LargeScaleSet_mem_nonneg hn
  have hn_le : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
  rw [section52LargeScaleSqrtRootCoeff, section52LargeScaleWeight, geometricWeight_one_eq]
  rw [section52_descendantsAtScale_originCube_large_card_rpow d ξ m hn_le]
  rw [section52_descendantsAtScale_originCube_int_zero_card_inv d hn_nonneg]
  rw [section52_descendantsAtScale_originCube_int_zero_card_sqrt d hn_nonneg]
  have hdepth :
      (Int.toNat ((m : ℤ) - n) : ℝ) + (Int.toNat n : ℝ) = (m : ℝ) := by
    exact_mod_cast section52LargeScaleSet_toNat_sub_add_toNat hn
  have hpow :
      Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.rpow (3 : ℝ)
            (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
              Real.rpow (3 : ℝ) (((d : ℝ) / 2) * (Int.toNat n : ℝ)) =
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ)
            (-(((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) *
              (Int.toNat n : ℝ)) := by
    calc
      Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.rpow (3 : ℝ)
            (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
              Real.rpow (3 : ℝ) (((d : ℝ) / 2) * (Int.toNat n : ℝ)) =
        (Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.rpow (3 : ℝ)
              (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ))) *
          (Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
            Real.rpow (3 : ℝ) (((d : ℝ) / 2) * (Int.toNat n : ℝ))) := by
          ring
      _ =
        Real.rpow (3 : ℝ)
            (-s * (Int.toNat ((m : ℤ) - n) : ℝ) +
              ((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.rpow (3 : ℝ)
            (-(d : ℝ) * (Int.toNat n : ℝ) +
              ((d : ℝ) / 2) * (Int.toNat n : ℝ)) := by
          have hAB :
              Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
                  Real.rpow (3 : ℝ)
                    (((d : ℝ) / (ξ : ℝ)) *
                      (Int.toNat ((m : ℤ) - n) : ℝ)) =
                Real.rpow (3 : ℝ)
                  (-s * (Int.toNat ((m : ℤ) - n) : ℝ) +
                    ((d : ℝ) / (ξ : ℝ)) *
                      (Int.toNat ((m : ℤ) - n) : ℝ)) :=
            (Real.rpow_add h3
              (-s * (Int.toNat ((m : ℤ) - n) : ℝ))
              (((d : ℝ) / (ξ : ℝ)) *
                (Int.toNat ((m : ℤ) - n) : ℝ))).symm
          have hCD :
              Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
                  Real.rpow (3 : ℝ) (((d : ℝ) / 2) * (Int.toNat n : ℝ)) =
                Real.rpow (3 : ℝ)
                  (-(d : ℝ) * (Int.toNat n : ℝ) +
                    ((d : ℝ) / 2) * (Int.toNat n : ℝ)) :=
            (Real.rpow_add h3
              (-(d : ℝ) * (Int.toNat n : ℝ))
              (((d : ℝ) / 2) * (Int.toNat n : ℝ))).symm
          exact congrArg₂ (fun x y : ℝ => x * y) hAB hCD
      _ =
        Real.rpow (3 : ℝ)
          ((-s * (Int.toNat ((m : ℤ) - n) : ℝ) +
              ((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) +
            (-(d : ℝ) * (Int.toNat n : ℝ) +
              ((d : ℝ) / 2) * (Int.toNat n : ℝ))) := by
          exact (Real.rpow_add h3
            (-s * (Int.toNat ((m : ℤ) - n) : ℝ) +
              ((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ))
            (-(d : ℝ) * (Int.toNat n : ℝ) +
              ((d : ℝ) / 2) * (Int.toNat n : ℝ))).symm
      _ =
        Real.rpow (3 : ℝ)
          (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ) +
            -(((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) *
              (Int.toNat n : ℝ)) := by
          congr 1
          have hdepth_sub :
              (Int.toNat ((m : ℤ) - n) : ℝ) =
                (m : ℝ) - (Int.toNat n : ℝ) := by
            linarith
          rw [hdepth_sub]
          ring_nf
      _ =
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ)
            (-(((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) *
              (Int.toNat n : ℝ)) := by
          exact Real.rpow_add h3
            (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))
            (-(((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) *
              (Int.toNat n : ℝ))
  calc
    geometricDiscount s 1 * Real.rpow (3 : ℝ)
        (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        (Real.rpow (3 : ℝ)
          (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          (Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
            (Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ *
              Real.rpow (3 : ℝ) (((d : ℝ) / 2) *
                (Int.toNat n : ℝ)) * 2))) =
      (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
        (Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.rpow (3 : ℝ)
            (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) *
              Real.rpow (3 : ℝ) (((d : ℝ) / 2) *
                (Int.toNat n : ℝ))) := by
        ring
    _ =
      (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
        (Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ)
            (-(((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) *
              (Int.toNat n : ℝ))) := by
        rw [hpow]
    _ =
      (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          Real.rpow (3 : ℝ)
            (-(((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) *
              (Int.toNat n : ℝ)) := by
        ring

theorem section52LargeScaleLpRootCoeff_scale_sum_le_geometricDiscount
    {d ξ : ℕ} {s : ℝ} (m : ℕ)
    (hs : 0 ≤ s) (hgap : 0 < (d : ℝ) - s) :
    (∑ n ∈ section52LargeScaleSet m,
        section52LargeScaleLpRootCoeff d ξ s m n) ≤
      (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ := by
  let coeff : ℝ :=
    (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
      Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ := by
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  have hdisc_nonneg : 0 ≤ geometricDiscount s 1 :=
    geometricDiscount_nonneg (by simpa using hs)
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hraw :=
    section52LargeScaleSet_raw_rpow_sum_le_inv_geometricDiscount
      (m := m) hgap
  calc
    (∑ n ∈ section52LargeScaleSet m,
        section52LargeScaleLpRootCoeff d ξ s m n) =
        ∑ n ∈ section52LargeScaleSet m,
          coeff * Real.rpow (3 : ℝ) (-((d : ℝ) - s) * (Int.toNat n : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [section52LargeScaleLpRootCoeff_eq_const_mul_decay_mul_gap_rpow
            (d := d) (ξ := ξ) (s := s) (m := m) hn]
    _ = coeff *
        (∑ n ∈ section52LargeScaleSet m,
          Real.rpow (3 : ℝ) (-((d : ℝ) - s) * (Int.toNat n : ℝ))) := by
          simp [Finset.mul_sum]
    _ ≤ coeff * (geometricDiscount ((d : ℝ) - s) 1)⁻¹ :=
          mul_le_mul_of_nonneg_left hraw hcoeff_nonneg
    _ =
      (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ := by
          simp [coeff]

theorem section52LargeScaleSqrtRootCoeff_scale_sum_le_geometricDiscount
    {d ξ : ℕ} {s : ℝ} (m : ℕ)
    (hs : 0 ≤ s) (hgap : 0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) :
    (∑ n ∈ section52LargeScaleSet m,
        section52LargeScaleSqrtRootCoeff d ξ s m n) ≤
      (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          (geometricDiscount (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) 1)⁻¹ := by
  let gap : ℝ := ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s
  let coeff : ℝ :=
    (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
      Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  have hdisc_nonneg : 0 ≤ geometricDiscount s 1 :=
    geometricDiscount_nonneg (by simpa using hs)
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hgap' : 0 < gap := by simpa [gap] using hgap
  have hraw :=
    section52LargeScaleSet_raw_rpow_sum_le_inv_geometricDiscount
      (m := m) hgap'
  calc
    (∑ n ∈ section52LargeScaleSet m,
        section52LargeScaleSqrtRootCoeff d ξ s m n) =
        ∑ n ∈ section52LargeScaleSet m,
          coeff * Real.rpow (3 : ℝ) (-gap * (Int.toNat n : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [section52LargeScaleSqrtRootCoeff_eq_const_mul_decay_mul_gap_rpow
            (d := d) (ξ := ξ) (s := s) (m := m) hn]
    _ = coeff *
        (∑ n ∈ section52LargeScaleSet m,
          Real.rpow (3 : ℝ) (-gap * (Int.toNat n : ℝ))) := by
          simp [Finset.mul_sum]
    _ ≤ coeff * (geometricDiscount gap 1)⁻¹ :=
          mul_le_mul_of_nonneg_left hraw hcoeff_nonneg
    _ =
      (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
        Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
          (geometricDiscount (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) 1)⁻¹ := by
          simp [coeff, gap]

theorem section52LargeScaleRootCoeff_scale_sum_le_geometricDiscount
    {d ξ : ℕ} {s : ℝ} (m : ℕ)
    (hs : 0 ≤ s) (hgapLp : 0 < (d : ℝ) - s)
    (hgapSqrt : 0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) :
    (∑ n ∈ section52LargeScaleSet m,
        section52LargeScaleRootCoeff d ξ s m n) ≤
      ((2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
        (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
          (geometricDiscount (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) 1)⁻¹) *
        Real.rpow (3 : ℝ)
          (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) := by
  have hLp :=
    section52LargeScaleLpRootCoeff_scale_sum_le_geometricDiscount
      (d := d) (ξ := ξ) (s := s) m hs hgapLp
  have hSqrt :=
    section52LargeScaleSqrtRootCoeff_scale_sum_le_geometricDiscount
      (d := d) (ξ := ξ) (s := s) m hs hgapSqrt
  have hsplit :
      (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleRootCoeff d ξ s m n) =
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleLpRootCoeff d ξ s m n) +
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleSqrtRootCoeff d ξ s m n) := by
    simp [section52LargeScaleRootCoeff, Finset.sum_add_distrib]
  calc
    (∑ n ∈ section52LargeScaleSet m,
        section52LargeScaleRootCoeff d ξ s m n) =
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleLpRootCoeff d ξ s m n) +
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleSqrtRootCoeff d ξ s m n) := hsplit
    _ ≤
        (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
            Real.rpow (3 : ℝ)
              (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
              (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
          (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
            Real.rpow (3 : ℝ)
              (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) *
              (geometricDiscount (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) 1)⁻¹ :=
        add_le_add hLp hSqrt
    _ =
      ((2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
        (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
          (geometricDiscount (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) 1)⁻¹) *
        Real.rpow (3 : ℝ)
          (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) := by
        ring

theorem section52LargeScaleRootCoeff_scale_sum_le_momentBoundCoeff
    {d ξ : ℕ} [NeZero d] {s : ℝ} (m : ℕ)
    (hξ_one : 1 ≤ (ξ : ℝ)) (hξ_two : (2 : ℝ) ≤ (ξ : ℝ))
    (hs : 0 ≤ s) (hs_lt_one : s < 1)
    (hgapSqrt : 0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) :
    (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleRootCoeff d ξ s m n) ≤
      section52MomentBoundCoeff d ξ (section52LargeScalarAbsorptionConst d) s m := by
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hd_ge_one : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d)))
  have hgapLp : 0 < (d : ℝ) - s := by
    linarith
  let component : ℝ :=
    (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ * geometricDiscount s 1) *
        (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
      (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ * geometricDiscount s 1) *
        (geometricDiscount (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) 1)⁻¹
  let decay : ℝ :=
    Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))
  let delta : ℝ := ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s
  have hscale :
      (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleRootCoeff d ξ s m n) ≤ component * decay := by
    simpa [component, decay] using
      section52LargeScaleRootCoeff_scale_sum_le_geometricDiscount
        (d := d) (ξ := ξ) (s := s) m hs hgapLp hgapSqrt
  have hentry_nonneg :
      0 ≤ (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) := by
    positivity
  have habsorb :
      (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) * component ≤
        section52LargeScalarAbsorptionConst d * ((ξ : ℝ) * delta⁻¹) := by
    simpa [component, delta] using
      section52LargeScalarAbsorptionConst_absorbs
        (d := d) (ξ := ξ) (s := s)
        hξ_one hξ_two hs hs_lt_one hgapSqrt
  have hdecay_nonneg : 0 ≤ decay :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  calc
    (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleRootCoeff d ξ s m n) ≤
        (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
          (component * decay) :=
      mul_le_mul_of_nonneg_left hscale hentry_nonneg
    _ =
        ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) * component) *
          decay := by ring
    _ ≤ (section52LargeScalarAbsorptionConst d * ((ξ : ℝ) * delta⁻¹)) * decay :=
      mul_le_mul_of_nonneg_right habsorb hdecay_nonneg
    _ = section52MomentBoundCoeff d ξ (section52LargeScalarAbsorptionConst d) s m := by
      simp [section52MomentBoundCoeff, delta, decay, div_eq_mul_inv]
      ring_nf
      exact Or.inl trivial

theorem section52SmallRawCoeff_eq
    {d ξ m : ℕ} {s r : ℝ} (hr : 0 < r) :
    (((25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
        section52SmallTailWeight r m) *
        ((descendantsAtScale (originCube d (m : ℤ)) 0).card : ℝ) ^
          (1 / (ξ : ℝ))) =
      625 * s⁻¹ ^ 2 * (r - s)⁻¹ ^ 2 *
        Real.rpow (3 : ℝ) (-(r - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  let e : ℝ := -r * (m : ℝ)
  let f : ℝ := ((d : ℝ) / (ξ : ℝ)) * (m : ℝ)
  have hW : section52SmallTailWeight r m = Real.rpow (3 : ℝ) e := by
    simpa [e] using section52SmallTailWeight_eq_rpow hr m
  have hcard :
      (((descendantsAtScale (originCube d (m : ℤ)) 0).card : ℝ) ^
          (1 / (ξ : ℝ))) =
        Real.rpow (3 : ℝ) f := by
    have h :=
      section52_descendantsAtScale_originCube_int_zero_card_rpow
        (d := d) (ξ := ξ) (n := (m : ℤ))
        (by exact_mod_cast Nat.zero_le m)
    simpa [f] using h
  have hpowe : Real.rpow (3 : ℝ) e ≠ 0 :=
    (Real.rpow_pos_of_pos h3 e).ne'
  have hpow_mul :
      Real.rpow (3 : ℝ) e * Real.rpow (3 : ℝ) f =
        Real.rpow (3 : ℝ) (e + f) :=
    (Real.rpow_add h3 e f).symm
  have hdiv_pow :
      Real.rpow (3 : ℝ) e ^ 2 / Real.rpow (3 : ℝ) e =
        Real.rpow (3 : ℝ) e := by
    rw [sq]
    field_simp [hpowe]
  calc
    (((25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
        section52SmallTailWeight r m) *
        ((descendantsAtScale (originCube d (m : ℤ)) 0).card : ℝ) ^
          (1 / (ξ : ℝ))) =
      (((25 * s⁻¹ * (r - s)⁻¹ * Real.rpow (3 : ℝ) e) ^ 2 /
          Real.rpow (3 : ℝ) e) *
        Real.rpow (3 : ℝ) f) := by
        rw [hW, hcard]
    _ =
      ((625 * s⁻¹ ^ 2 * (r - s)⁻¹ ^ 2 *
          (Real.rpow (3 : ℝ) e ^ 2 / Real.rpow (3 : ℝ) e)) *
        Real.rpow (3 : ℝ) f) := by
        ring
    _ =
      (625 * s⁻¹ ^ 2 * (r - s)⁻¹ ^ 2 *
          Real.rpow (3 : ℝ) e) *
        Real.rpow (3 : ℝ) f := by
        rw [hdiv_pow]
    _ =
      625 * s⁻¹ ^ 2 * (r - s)⁻¹ ^ 2 *
        (Real.rpow (3 : ℝ) e * Real.rpow (3 : ℝ) f) := by
        ring
    _ =
      625 * s⁻¹ ^ 2 * (r - s)⁻¹ ^ 2 *
        Real.rpow (3 : ℝ) (e + f) := by
        rw [hpow_mul]
    _ =
      625 * s⁻¹ ^ 2 * (r - s)⁻¹ ^ 2 *
        Real.rpow (3 : ℝ) (-(r - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) := by
        congr 1
        dsimp [e, f]
        ring_nf

theorem section52RawTwoExponentCoeff_le_twoExponentMomentBoundCoeff
    {d ξ m : ℕ} [NeZero d] {s r : ℝ}
    (hξ_one : 1 ≤ ξ) (hξ_two : 2 ≤ ξ)
    (hs : 0 < s) (hsr : s < r) (hr_lt_one : r < 1)
    (hlargeGap : 0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - r) :
    (((25 * s⁻¹ * (r - s)⁻¹ *
            Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
          section52SmallTailWeight r m) *
          ((descendantsAtScale (originCube d (m : ℤ)) 0).card : ℝ) ^
            (1 / (ξ : ℝ))) +
        ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleRootCoeff d ξ r m n) ≤
      section52TwoExponentMomentBoundCoeff d ξ
        (625 + section52LargeScalarAbsorptionConst d) s r m := by
  let D := descendantsAtScale (originCube d (m : ℤ)) 0
  let L : ℝ := section52LargeScalarAbsorptionConst d
  let A : ℝ := (ξ : ℝ) / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - r)
  let B : ℝ := (r - s)⁻¹ ^ 2
  let S2 : ℝ := s⁻¹ ^ 2
  let decay : ℝ :=
    Real.rpow (3 : ℝ) (-(r - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))
  have hr_pos : 0 < r := hs.trans hsr
  have hs_le_one : s ≤ 1 := le_trans hsr.le hr_lt_one.le
  have hS2_ge_one : 1 ≤ S2 := by
    have hone_le_inv : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_le_one
    dsimp [S2]
    calc
      (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ s⁻¹ ^ 2 := pow_le_pow_left₀ zero_le_one hone_le_inv 2
  have hS2_nonneg : 0 ≤ S2 := by
    dsimp [S2]
    exact sq_nonneg _
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by exact_mod_cast Nat.zero_le ξ) hlargeGap.le
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact sq_nonneg _
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact section52LargeScalarAbsorptionConst_nonneg d
  have hdecay_nonneg : 0 ≤ decay := by
    dsimp [decay]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hsmall_eq :
      (((25 * s⁻¹ * (r - s)⁻¹ *
            Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
          section52SmallTailWeight r m) *
          (D.card : ℝ) ^ (1 / (ξ : ℝ))) =
        625 * S2 * B * decay := by
    dsimp [D, S2, B, decay]
    exact section52SmallRawCoeff_eq (d := d) (ξ := ξ) (m := m)
      (s := s) (r := r) hr_pos
  have hlarge :
      ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleRootCoeff d ξ r m n) ≤
        L * A * decay := by
    have hξ_one_real : (1 : ℝ) ≤ (ξ : ℝ) := by exact_mod_cast hξ_one
    have hξ_two_real : (2 : ℝ) ≤ (ξ : ℝ) := by exact_mod_cast hξ_two
    have h :=
      section52LargeScaleRootCoeff_scale_sum_le_momentBoundCoeff
        (d := d) (ξ := ξ) (s := r) m
        hξ_one_real hξ_two_real hr_pos.le hr_lt_one hlargeGap
    simpa [section52MomentBoundCoeff, L, A, decay, div_eq_mul_inv,
      mul_assoc] using h
  have hlarge_absorb :
      L * A * decay ≤ L * (S2 * A) * decay := by
    have hA_le : A ≤ S2 * A := by
      calc
        A = 1 * A := by ring
        _ ≤ S2 * A := mul_le_mul_of_nonneg_right hS2_ge_one hA_nonneg
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hA_le hL_nonneg) hdecay_nonneg
  have hfinal :
      625 * S2 * B * decay + L * (S2 * A) * decay ≤
        (625 + L) * S2 * (A + B) * decay := by
    have hterm1 : 0 ≤ 625 * S2 * A * decay := by positivity
    have hterm2 : 0 ≤ L * S2 * B * decay := by positivity
    nlinarith
  calc
    (((25 * s⁻¹ * (r - s)⁻¹ *
            Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
          section52SmallTailWeight r m) *
          (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
        ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleRootCoeff d ξ r m n)
        ≤ 625 * S2 * B * decay + L * A * decay := by
          rw [hsmall_eq]
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hlarge (625 * S2 * B * decay)
    _ ≤ 625 * S2 * B * decay + L * (S2 * A) * decay :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hlarge_absorb (625 * S2 * B * decay)
    _ ≤ (625 + L) * S2 * (A + B) * decay := hfinal
    _ = section52TwoExponentMomentBoundCoeff d ξ
        (625 + section52LargeScalarAbsorptionConst d) s r m := by
          simp [section52TwoExponentMomentBoundCoeff, section52MomentLossCoeff,
            L, A, B, S2, decay, div_eq_mul_inv]
          ring_nf
          exact Or.inl trivial

end

end Section52
end Ch05
end Book
end Homogenization
