/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder

/-!
# Pk Bounds Unconditional Scale

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-! The three scale calculations used when the fixed-time pressure estimates are
assembled over a smaller parabolic cylinder. -/

theorem pressureP234_scale
    {r ρ α β A K : ℝ} {X : ℝ≥0∞} {V : Set Vec3}
    (hr : 0 < r) (hρ : 0 < ρ) (hα : 0 ≤ α)
    (hA : 0 ≤ A)
    (hKeq : K = A * α / ρ ^ (3 / 2 : ℝ))
    (hX : X ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal (r ^ (1 / 3 : ℝ)) *
      ENNReal.ofReal (Real.sqrt ρ * β))
    (hV : volume V = ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℕ))) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (3 * (ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume V * X) ^
          (2 / 3 : ℝ) ≤
      ENNReal.ofReal (3 ^ (2 / 3 : ℝ) * A *
        (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * (r / ρ) * α * β) := by
  have hρ0 : 0 ≤ ρ := hρ.le
  have hK' : ENNReal.ofReal K = ENNReal.ofReal A * ENNReal.ofReal α /
      ENNReal.ofReal (ρ ^ (3 / 2 : ℝ)) := by
    rw [hKeq, div_eq_mul_inv]
    calc
      ENNReal.ofReal (A * α * (ρ ^ (3 / 2 : ℝ))⁻¹) =
          ENNReal.ofReal A * ENNReal.ofReal α *
            ENNReal.ofReal ((ρ ^ (3 / 2 : ℝ))⁻¹) := by
        rw [show A * α * (ρ ^ (3 / 2 : ℝ))⁻¹ =
          A * (α * (ρ ^ (3 / 2 : ℝ))⁻¹) by ring_nf]
        rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hα]
        ac_rfl
      _ = ENNReal.ofReal A * ENNReal.ofReal α /
          ENNReal.ofReal (ρ ^ (3 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hρ _)]
        rfl
  rw [hV, hK']
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hro : ENNReal.ofReal r ^ (-4 / 3 : ℝ) =
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) :=
    ENNReal.ofReal_rpow_of_pos hr
  have hrr : ENNReal.ofReal r ^ (3 : ℝ) =
      ENNReal.ofReal (r ^ (3 : ℝ)) :=
    ENNReal.ofReal_rpow_of_pos hr
  have hvol : ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℕ)) =
      ENNReal.ofReal (4 * Real.pi / 3) * ENNReal.ofReal (r ^ (3 : ℕ)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
  rw [← hro, hvol]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hrr' : ENNReal.ofReal (r ^ (3 : ℕ)) ^ (2 / 3 : ℝ) =
      ENNReal.ofReal r ^ (2 : ℝ) := by
    rw [show (r ^ (3 : ℕ) : ℝ) = r ^ (3 : ℝ) by norm_num]
    rw [← hrr, ← ENNReal.rpow_mul]
    norm_num
  rw [hrr']
  rw [← ENNReal.rpow_mul]
  norm_num
  let C : ℝ≥0∞ := ENNReal.ofReal r ^ (-4 / 3 : ℝ) *
        (3 ^ (2 / 3 : ℝ) *
          (ENNReal.ofReal (A * α) / ENNReal.ofReal (ρ ^ (3 / 2 : ℝ))) *
          (ENNReal.ofReal (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
            ENNReal.ofReal r ^ (2 : ℝ)))
  have hC : 0 ≤ C := by positivity
  calc
    _ = C * X ^ (2 / 3 : ℝ) := by
      dsimp [C]
      rw [ENNReal.ofReal_mul hA]
      norm_num
      ac_rfl
    _ ≤ C * (ENNReal.ofReal (r ^ (1 / 3 : ℝ)) *
          ENNReal.ofReal (Real.sqrt ρ * β)) :=
      mul_le_mul_of_nonneg_left hX hC
    _ = ENNReal.ofReal (3 ^ (2 / 3 : ℝ) * A *
        (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * (r / ρ) * α * β) := by
      dsimp [C]
      simp only [div_eq_mul_inv]
      rw [ENNReal.ofReal_mul hA]
      rw [← ENNReal.ofReal_rpow_of_pos hρ]
      rw [Real.sqrt_eq_rpow]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ρ ^ (1 / 2 : ℝ))]
      rw [← ENNReal.ofReal_rpow_of_pos hr]
      rw [← ENNReal.ofReal_rpow_of_pos hρ]
      have hr2 : ENNReal.ofReal r ^ (2 : ℝ) =
          ENNReal.ofReal (r ^ (2 : ℝ)) := ENNReal.ofReal_rpow_of_pos hr
      have hro' : ENNReal.ofReal r ^ (-4 * (3 : ℝ)⁻¹) =
          ENNReal.ofReal (r ^ (-4 * (3 : ℝ)⁻¹)) :=
        ENNReal.ofReal_rpow_of_pos hr
      have hvpow : ENNReal.ofReal (4 * Real.pi * (3 : ℝ)⁻¹) ^
          (2 * (3 : ℝ)⁻¹) =
          ENNReal.ofReal ((4 * Real.pi * (3 : ℝ)⁻¹) ^ (2 * (3 : ℝ)⁻¹)) :=
        ENNReal.ofReal_rpow_of_pos (by positivity)
      have h3pow : (3 : ℝ≥0∞) ^ (2 * (3 : ℝ)⁻¹) =
          ENNReal.ofReal (3 ^ (2 * (3 : ℝ)⁻¹)) := by
        convert ENNReal.ofReal_rpow_of_pos (x := (3 : ℝ))
          (p := (2 / 3 : ℝ)) (by norm_num) using 1 <;> norm_num
      have hrhopow : ENNReal.ofReal ρ ^ (3 * (2 : ℝ)⁻¹) =
          ENNReal.ofReal (ρ ^ (3 * (2 : ℝ)⁻¹)) :=
        ENNReal.ofReal_rpow_of_pos hρ
      have hrhohalf : ENNReal.ofReal ρ ^ (1 / 2 : ℝ) =
          ENNReal.ofReal (ρ ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_pos hρ
      have hrthird' : ENNReal.ofReal r ^ (1 * (3 : ℝ)⁻¹) =
          ENNReal.ofReal (r ^ (1 * (3 : ℝ)⁻¹)) :=
        ENNReal.ofReal_rpow_of_pos hr
      rw [hro', hr2, hvpow, h3pow, hrthird', hrhopow, hrhohalf]
      rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hρ _)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply congrArg ENNReal.ofReal
      field_simp
      have hrprod : r ^ (-(4 / 3 : ℝ)) * r ^ (2 : ℝ) *
          r ^ (1 / 3 : ℝ) = r := by
        rw [← Real.rpow_add hr, ← Real.rpow_add hr]
        norm_num
      have hrhoprod : ρ ^ (1 / 2 : ℝ) * ρ = ρ ^ (3 / 2 : ℝ) := by
        calc
          ρ ^ (1 / 2 : ℝ) * ρ = ρ ^ (1 / 2 : ℝ) * ρ ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = ρ ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hρ _ _).symm
          _ = ρ ^ (3 / 2 : ℝ) := by norm_num
      calc
        _ = (r ^ (-(4 / 3 : ℝ)) * r ^ (2 : ℝ) *
            r ^ (1 / 3 : ℝ)) * (ρ ^ (1 / 2 : ℝ) * ρ) *
              (A * α * β) := by ring_nf
        _ = r * ρ ^ (3 / 2 : ℝ) * (A * α * β) := by
              rw [hrprod, hrhoprod]
        _ = _ := by ring_nf

private lemma pressure_three_factor {R Y : ℝ≥0∞} :
    R * (3 * Y ^ (2 / 3 : ℝ)) =
      ENNReal.ofReal (3 ^ (1 / 3 : ℝ)) *
        (R * (3 * Y) ^ (2 / 3 : ℝ)) := by
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [h3]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    (by norm_num)]
  have hconst : ENNReal.ofReal (3 ^ (1 / 3 : ℝ)) *
      ENNReal.ofReal (3 ^ (2 / 3 : ℝ)) = ENNReal.ofReal (3 : ℝ) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  calc
    _ = ENNReal.ofReal (3 : ℝ) * (R * Y ^ (2 / 3 : ℝ)) := by ring_nf
    _ = (ENNReal.ofReal (3 ^ (1 / 3 : ℝ)) *
        ENNReal.ofReal (3 ^ (2 / 3 : ℝ))) *
        (R * Y ^ (2 / 3 : ℝ)) := by rw [hconst]
    _ = _ := by ring_nf

theorem pressureP234_scale_cylinder
    {r ρ α β A K : ℝ} {X : ℝ≥0∞} {V : Set Vec3}
    (hr : 0 < r) (hρ : 0 < ρ) (hα : 0 ≤ α)
    (hA : 0 ≤ A)
    (hKeq : K = A * α / ρ ^ (3 / 2 : ℝ))
    (hX : X ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal (r ^ (1 / 3 : ℝ)) *
      ENNReal.ofReal (Real.sqrt ρ * β))
    (hV : volume V = ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℕ))) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (3 * ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume V * X) ^
          (2 / 3 : ℝ)) ≤
      ENNReal.ofReal (3 * A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
        (r / ρ) * α * β) := by
  have hbase := pressureP234_scale hr hρ hα hA hKeq hX hV
  let Y : ℝ≥0∞ := (ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume V * X
  have hfactor := pressure_three_factor
    (R := ENNReal.ofReal (r ^ (-4 / 3 : ℝ))) (Y := Y)
  have hmul := mul_le_mul_of_nonneg_left hbase
    (by positivity : 0 ≤ ENNReal.ofReal (3 ^ (1 / 3 : ℝ)))
  calc
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (3 * ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume V * X) ^
          (2 / 3 : ℝ)) =
      ENNReal.ofReal (3 ^ (1 / 3 : ℝ)) *
        (ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) * (3 * Y) ^
          (2 / 3 : ℝ)) := by simpa [Y] using hfactor
    _ ≤ ENNReal.ofReal (3 ^ (1 / 3 : ℝ)) *
        ENNReal.ofReal (3 ^ (2 / 3 : ℝ) * A *
          (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * (r / ρ) * α * β) := by
      simpa [Y, mul_assoc] using hmul
    _ = ENNReal.ofReal (3 * A * (4 * Real.pi / 3) ^
        (2 / 3 : ℝ) * (r / ρ) * α * β) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have hpow : (3 : ℝ) ^ (1 / 3 : ℝ) * 3 ^ (2 / 3 : ℝ) = 3 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        norm_num
      congr 1
      calc
        3 ^ (1 / 3 : ℝ) *
              (3 ^ (2 / 3 : ℝ) * A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
                (r / ρ) * α * β) =
            (3 ^ (1 / 3 : ℝ) * 3 ^ (2 / 3 : ℝ)) * A *
              (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * (r / ρ) * α * β := by ring_nf
        _ = 3 * A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
              (r / ρ) * α * β := by rw [hpow]

private lemma pressure_two_factor {R Y : ℝ≥0∞} :
    R * (2 * Y ^ (2 / 3 : ℝ)) =
      ENNReal.ofReal (2 ^ (1 / 3 : ℝ)) *
        (R * (2 * Y) ^ (2 / 3 : ℝ)) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [h2]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num)]
  have hconst : ENNReal.ofReal (2 ^ (1 / 3 : ℝ)) *
      ENNReal.ofReal (2 ^ (2 / 3 : ℝ)) = ENNReal.ofReal (2 : ℝ) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    _ = ENNReal.ofReal (2 : ℝ) * (R * Y ^ (2 / 3 : ℝ)) := by ring_nf
    _ = (ENNReal.ofReal (2 ^ (1 / 3 : ℝ)) *
        ENNReal.ofReal (2 ^ (2 / 3 : ℝ))) *
        (R * Y ^ (2 / 3 : ℝ)) := by rw [hconst]
    _ = _ := by ring_nf

theorem pressureP56_scale
    {r ρ δ A K : ℝ} {X : ℝ≥0∞} {V : Set Vec3}
    (hr : 0 < r) (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hKeq : K = A / ρ ^ (2 : ℝ))
    (hX : X ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal (ρ ^ (4 / 3 : ℝ)) *
      ENNReal.ofReal (δ ^ 2))
    (hV : volume V = ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℕ))) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (2 * (ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume V * X) ^
          (2 / 3 : ℝ) ≤
      ENNReal.ofReal (2 ^ (2 / 3 : ℝ) * A *
        (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * r ^ (2 / 3 : ℝ) *
          ρ ^ (-(2 / 3 : ℝ)) * δ ^ 2) := by
  have hK' : ENNReal.ofReal K = ENNReal.ofReal A /
      ENNReal.ofReal (ρ ^ (2 : ℝ)) := by
    rw [hKeq, div_eq_mul_inv]
    calc
      ENNReal.ofReal (A * (ρ ^ (2 : ℝ))⁻¹) =
          ENNReal.ofReal A * ENNReal.ofReal ((ρ ^ (2 : ℝ))⁻¹) := by
        rw [ENNReal.ofReal_mul hA]
      _ = ENNReal.ofReal A / ENNReal.ofReal (ρ ^ (2 : ℝ)) := by
        rw [ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hρ _)]
        rfl
  rw [hV, hK']
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hro : ENNReal.ofReal r ^ (-4 / 3 : ℝ) =
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) := ENNReal.ofReal_rpow_of_pos hr
  rw [← hro]
  have hvol : ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℕ)) =
      ENNReal.ofReal (4 * Real.pi / 3) * ENNReal.ofReal (r ^ (3 : ℕ)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
  rw [hvol, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hrr : ENNReal.ofReal (r ^ (3 : ℕ)) ^ (2 / 3 : ℝ) =
      ENNReal.ofReal r ^ (2 : ℝ) := by
    rw [show (r ^ (3 : ℕ) : ℝ) = r ^ (3 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.rpow_mul]
    norm_num
  rw [hrr]
  rw [← ENNReal.rpow_mul]
  norm_num
  let C : ℝ≥0∞ := ENNReal.ofReal r ^ (-4 / 3 : ℝ) *
        (2 ^ (2 / 3 : ℝ) *
          (ENNReal.ofReal A / ENNReal.ofReal (ρ ^ (2 : ℝ))) *
          (ENNReal.ofReal (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
            ENNReal.ofReal r ^ (2 : ℝ)))
  have hC : 0 ≤ C := by positivity
  calc
    _ = C * X ^ (2 / 3 : ℝ) := by
      dsimp [C]
      norm_num
      ac_rfl
    _ ≤ C * (ENNReal.ofReal (ρ ^ (4 / 3 : ℝ)) * ENNReal.ofReal (δ ^ 2)) :=
      mul_le_mul_of_nonneg_left hX hC
    _ = ENNReal.ofReal (2 ^ (2 / 3 : ℝ) * A *
        (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * r ^ (2 / 3 : ℝ) *
          ρ ^ (-(2 / 3 : ℝ)) * δ ^ 2) := by
      dsimp [C]
      simp only [div_eq_mul_inv]
      rw [ENNReal.ofReal_rpow_of_pos hr]
      rw [ENNReal.ofReal_rpow_of_pos
        (by positivity : (0 : ℝ) < 4 * Real.pi * (3 : ℝ)⁻¹)]
      have h2pow : (2 : ℝ≥0∞) ^ (2 * (3 : ℝ)⁻¹) =
          ENNReal.ofReal (2 ^ (2 * (3 : ℝ)⁻¹)) := by
        convert ENNReal.ofReal_rpow_of_pos (x := (2 : ℝ))
          (p := (2 / 3 : ℝ)) (by norm_num) using 1 <;> norm_num
      rw [h2pow]
      rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hρ _)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      have hvr : ENNReal.ofReal ((4 * Real.pi * (3 : ℝ)⁻¹) ^
          (2 * (3 : ℝ)⁻¹)) * ENNReal.ofReal (r ^ (2 : ℝ)) =
          ENNReal.ofReal ((4 * Real.pi * (3 : ℝ)⁻¹) ^
            (2 * (3 : ℝ)⁻¹) * r ^ (2 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      have hr2 : ENNReal.ofReal r ^ (2 : ℝ) =
          ENNReal.ofReal (r ^ (2 : ℝ)) := ENNReal.ofReal_rpow_of_pos hr
      rw [hr2, hvr]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply congrArg ENNReal.ofReal
      have hrprod : r ^ (-(4 / 3 : ℝ)) * r ^ (2 : ℝ) =
          r ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add hr]
        norm_num
      have hrhoprod : ρ ^ (4 / 3 : ℝ) * (ρ ^ (2 : ℝ))⁻¹ =
          ρ ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
        norm_num
      calc
        _ = (r ^ (-(4 / 3 : ℝ)) * r ^ (2 : ℝ)) *
            (ρ ^ (4 / 3 : ℝ) * (ρ ^ (2 : ℝ))⁻¹) *
            (2 ^ (2 / 3 : ℝ) * A * (4 * Real.pi / 3) ^
              (2 / 3 : ℝ) * δ ^ 2) := by ring_nf
        _ = r ^ (2 / 3 : ℝ) * ρ ^ (-(2 / 3 : ℝ)) *
            (2 ^ (2 / 3 : ℝ) * A * (4 * Real.pi / 3) ^
              (2 / 3 : ℝ) * δ ^ 2) := by
          rw [hrprod, hrhoprod]
        _ = _ := by
          norm_num
          ring_nf

theorem pressureP56_scale_cylinder
    {r ρ δ A K : ℝ} {X : ℝ≥0∞} {V : Set Vec3}
    (hr : 0 < r) (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hKeq : K = A / ρ ^ (2 : ℝ))
    (hX : X ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal (ρ ^ (4 / 3 : ℝ)) *
      ENNReal.ofReal (δ ^ 2))
    (hV : volume V = ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℕ))) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (2 * ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume V * X) ^
          (2 / 3 : ℝ)) ≤
      ENNReal.ofReal (2 * A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
        (r / ρ) ^ (2 / 3 : ℝ) * δ ^ 2) := by
  have hbase := pressureP56_scale hr hρ hA hKeq hX hV
  let Y : ℝ≥0∞ := (ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume V * X
  have hfactor := pressure_two_factor
    (R := ENNReal.ofReal (r ^ (-4 / 3 : ℝ))) (Y := Y)
  have hmul := mul_le_mul_of_nonneg_left hbase
    (by positivity : 0 ≤ ENNReal.ofReal (2 ^ (1 / 3 : ℝ)))
  calc
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (2 * ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume V * X) ^
          (2 / 3 : ℝ)) =
      ENNReal.ofReal (2 ^ (1 / 3 : ℝ)) *
        (ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) * (2 * Y) ^
          (2 / 3 : ℝ)) := by simpa [Y] using hfactor
    _ ≤ ENNReal.ofReal (2 ^ (1 / 3 : ℝ)) *
        ENNReal.ofReal (2 ^ (2 / 3 : ℝ) * A *
          (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * r ^ (2 / 3 : ℝ) *
          ρ ^ (-(2 / 3 : ℝ)) * δ ^ 2) := by
      simpa [Y, mul_assoc] using hmul
    _ = ENNReal.ofReal (2 * A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
        (r / ρ) ^ (2 / 3 : ℝ) * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have hpow : (2 : ℝ) ^ (1 / 3 : ℝ) * 2 ^ (2 / 3 : ℝ) = 2 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      have hdiv : (r / ρ) ^ (2 / 3 : ℝ) =
          r ^ (2 / 3 : ℝ) * ρ ^ (-(2 / 3 : ℝ)) := by
        rw [Real.div_rpow hr.le hρ.le]
        rw [div_eq_mul_inv, ← Real.rpow_neg hρ.le]
      congr 1
      calc
        2 ^ (1 / 3 : ℝ) *
              (2 ^ (2 / 3 : ℝ) * A * (4 * Real.pi / 3) ^
                (2 / 3 : ℝ) * r ^ (2 / 3 : ℝ) *
                ρ ^ (-(2 / 3 : ℝ)) * δ ^ 2) =
            (2 ^ (1 / 3 : ℝ) * 2 ^ (2 / 3 : ℝ)) * A *
              (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
              (r ^ (2 / 3 : ℝ) * ρ ^ (-(2 / 3 : ℝ))) * δ ^ 2 := by ring_nf
        _ = 2 * A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
              (r / ρ) ^ (2 / 3 : ℝ) * δ ^ 2 := by rw [hpow, ← hdiv]

theorem pressureP8_scale
    {q r ρ lam A K : ℝ} {X : ℝ≥0∞} {V : Set Vec3}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hA : 0 ≤ A)
    (hKeq : K = A * ρ ^ (1 - 3 / q))
    (hX : X ^ (2 / 3 : ℝ) ≤
      ENNReal.ofReal (r ^ (2 * (2 / 3 - 1 / q))) *
        ENNReal.ofReal (ρ ^ (5 / q - 3) * lam))
    (hV : volume V = ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℕ))) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume V * X) ^
          (2 / 3 : ℝ) ≤
      ENNReal.ofReal (A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
        r ^ (2 - 2 / q) * ρ ^ (-2 + 2 / q) * lam) := by
  have hK' : ENNReal.ofReal K = ENNReal.ofReal A *
      ENNReal.ofReal (ρ ^ (1 - 3 / q)) := by
    rw [hKeq, ENNReal.ofReal_mul hA]
  rw [hV, hK']
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [← ENNReal.rpow_mul]
  norm_num
  have hkpow : (ENNReal.ofReal (ρ ^ (1 - 3 / q)) ^ (3 / 2 : ℝ)) ^
      (2 / 3 : ℝ) = ENNReal.ofReal (ρ ^ (1 - 3 / q)) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hkpow]
  have hvol : ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℕ)) =
      ENNReal.ofReal (4 * Real.pi / 3) * ENNReal.ofReal (r ^ (3 : ℕ)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
  rw [hvol, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hrr : ENNReal.ofReal (r ^ (3 : ℕ)) ^ (2 / 3 : ℝ) =
      ENNReal.ofReal r ^ (2 : ℝ) := by
    rw [show (r ^ (3 : ℕ) : ℝ) = r ^ (3 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.rpow_mul]
    norm_num
  rw [hrr]
  let C : ℝ≥0∞ := ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (ENNReal.ofReal A * ENNReal.ofReal (ρ ^ (1 - 3 / q)) *
          (ENNReal.ofReal (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
            ENNReal.ofReal r ^ (2 : ℝ)))
  have hC : 0 ≤ C := by positivity
  calc
    _ = C * X ^ (2 / 3 : ℝ) := by
      dsimp [C]
      norm_num
      ac_rfl
    _ ≤ C * (ENNReal.ofReal (r ^ (2 * (2 / 3 - 1 / q))) *
          ENNReal.ofReal (ρ ^ (5 / q - 3) * lam)) :=
      mul_le_mul_of_nonneg_left hX hC
    _ = ENNReal.ofReal (A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
        r ^ (2 - 2 / q) * ρ ^ (-2 + 2 / q) * lam) := by
      dsimp [C]
      simp only [div_eq_mul_inv]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ρ ^ (5 * q⁻¹ - 3))]
      rw [ENNReal.ofReal_rpow_of_pos hr]
      rw [ENNReal.ofReal_rpow_of_pos
        (by positivity : (0 : ℝ) < 4 * Real.pi * (3 : ℝ)⁻¹)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply congrArg ENNReal.ofReal
      have hrprod : r ^ (-(4 / 3 : ℝ)) * r ^ (2 : ℝ) *
          r ^ (2 * (2 / 3 - 1 / q)) = r ^ (2 - 2 / q) := by
        rw [← Real.rpow_add hr, ← Real.rpow_add hr]
        congr 1
        ring_nf
      have hrhoprod : ρ ^ (1 - 3 / q) *
          ρ ^ (5 / q - 3) = ρ ^ (-2 + 2 / q) := by
        rw [← Real.rpow_add hρ]
        congr 1
        ring_nf
      calc
        _ = (r ^ (-(4 / 3 : ℝ)) * r ^ (2 : ℝ) *
            r ^ (2 * (2 / 3 - 1 / q))) *
            (ρ ^ (1 - 3 / q) * ρ ^ (5 / q - 3)) *
            (A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * lam) := by ring_nf
        _ = r ^ (2 - 2 / q) * ρ ^ (-2 + 2 / q) *
            (A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) * lam) := by
          rw [hrprod, hrhoprod]
        _ = _ := by ring_nf

end CKN
