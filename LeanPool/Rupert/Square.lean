/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Basic
import LeanPool.Rupert.Convex
import LeanPool.Rupert.Equivalences.RupertEquivRupertPrime

/-!
# LeanPool.Rupert.Square

Imported Lean Pool material for `LeanPool.Rupert.Square`.
-/

namespace Square

open Matrix
open Real

/--
A square in the xy-plane, centered at the origin and with side length 2.
-/
abbrev vertices : Fin 4 → ℝ³ :=
  ![!₂[-1, -1, 0], !₂[1, -1, 0], !₂[-1, 1, 0], !₂[1, 1, 0]]

/-- square root of one-half -/
noncomputable def rh : ℝ := √2/2

-- A simple algebraic fact about √2/2 that arises multiple times
-- FIXME: is there a systematic naming convention that would give me a less
-- opaque name for this
theorem rh_lemma : rh * rh + rh * rh  = 1 := by
  calc rh * rh + rh * rh
       _ = 2 * (√2 / 2)^2 := by rw[rh]; ring
       _ = 2 * ((√2 * √2) / 2^2) := by rw[div_pow]; ring
       _ = 2 * (2 / 2^2) := by simp
       _ = 1 := by norm_num

/-- Rotation matrix for the inner square shadow. -/
abbrev innerRot : Matrix (Fin 3) (Fin 3) ℝ :=
   !![1, 0, 0;
      0, 0,-1;
      0, 1, 0]

lemma innerRot_so3 : innerRot ∈ SO3 := by
  dsimp only [innerRot]
  rw [mem_specialOrthogonalGroup_iff]
  constructor
  · constructor <;> (ext i j; fin_cases i, j) <;>
     simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [det_succ_row_zero, Fin.sum_univ_three]

/-- Rotation matrix for the outer square shadow. -/
noncomputable abbrev outerRot : Matrix (Fin 3) (Fin 3) ℝ :=
   !![ rh, rh, 0;
      -rh, rh, 0;
        0,  0, 1]

lemma outerRot_so3 : outerRot ∈ SO3 := by
  dsimp only [outerRot]
  rw [mem_specialOrthogonalGroup_iff]
  constructor
  · constructor <;> (ext i j; fin_cases i, j) <;>
     simp [Matrix.mul_apply, Fin.sum_univ_three, rh_lemma]
  · simp [det_succ_row_zero, Fin.sum_univ_three, rh_lemma]

theorem square_is_rupert : IsRupert vertices := by
/-

The diagram shows the (x,y) plane, the z axis runs through the
screen. The rotation innerRot rotates about the x axis, creating the
horizontal slot shape.  The rotation outerRot rotates the (x,y) plane
by π/4 radians. No offset translation is needed.

      +
     / \
    /   \
   /     \
  + ----- +
   \     /
    \   /
     \ /
      +
-/
 rw [rupert_iff_rupert']
 let innerOffset : ℝ² := 0
 use innerRot, innerRot_so3, innerOffset, outerRot, outerRot_so3
 intro inner_shadow outerShadow x hx
 obtain ⟨ε₀, hε₀0, hε₀⟩ : ∃ ε₀, 0 < ε₀ ∧ ε₀ < √2/2 := by
   use 0.00001
   have h : 1 / 2 < √2 / 2 := by
     suffices H : 1 < √2 by linarith
     exact one_lt_sqrt_two
   constructor
   · norm_num
   · linarith
 have zero_in_outer : Metric.ball 0 ε₀ ⊆ convexHull ℝ outerShadow := by
   intro v hv
   simp only [Metric.mem_ball, dist_zero_right] at hv
   rw [mem_convexHull_iff_exists_fintype]
   use Fin 4, inferInstance
   use ![1/4 + v 0 / (2 * √2), 1/4 - v 0 / (2*√2),
         1/4 + v 1 / (2 * √2), 1/4 - v 1 / (2 * √2)]
   use ![!₂[√2, 0], !₂[-√2, 0], !₂[0, √2], !₂[0, -√2]]
   obtain ⟨h2', h0'⟩ := abs_le.mp (Real.norm_eq_abs _ ▸ (PiLp.norm_apply_le v 0))
   obtain ⟨h4', h3'⟩ := abs_le.mp (Real.norm_eq_abs _ ▸ (PiLp.norm_apply_le v 1))
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro i
     fin_cases i
     · simp only [Fin.isValue, one_div, Fin.zero_eta, cons_val_zero]
       suffices H : 0 * (2 * √2) ≤ (4⁻¹ + v 0 / (2 * √2)) * (2 * √2) by
         have : 0 < 2 * √2 := by positivity
         exact le_of_mul_le_mul_right H this
       rw [zero_mul]
       ring_nf
       rw [mul_assoc]
       simp
       linarith
     · simp only [Fin.isValue, one_div, Fin.mk_one, cons_val_one, cons_val_zero,
         sub_nonneg]
       suffices H : v 0 / (2 * √2) * (2 * √2) ≤ 4⁻¹ * (2 * √2) by
         have : 0 < 2 * √2 := by positivity
         exact le_of_mul_le_mul_right H this
       simp
       linarith
     · simp only [Fin.isValue, one_div, Fin.reduceFinMk, cons_val]
       suffices H : 0 * (2 * √2) ≤ (4⁻¹ + v 1 / (2 * √2)) * (2 * √2) by
         have : 0 < 2 * √2 := by positivity
         exact le_of_mul_le_mul_right H this
       rw [zero_mul]
       ring_nf
       rw [mul_assoc]
       simp
       linarith
     · simp only [Fin.isValue, one_div, Fin.reduceFinMk, cons_val, sub_nonneg]
       suffices H : v 1 / (2 * √2) * (2 * √2) ≤ 4⁻¹ * (2 * √2) by
         have : 0 < 2 * √2 := by positivity
         exact le_of_mul_le_mul_right H this
       simp
       linarith
   · simp [Fin.sum_univ_four]
     ring
   · intro i
     fin_cases i
     · refine ⟨3, ?_⟩
       simp [projXy, rh]
     · refine ⟨0, ?_⟩
       simp [projXy, rh]
       ring_nf
     · refine ⟨2, ?_⟩
       simp [projXy, rh]
     · refine ⟨1, ?_⟩
       simp [projXy, rh]
       ring_nf
   · rw [Fin.sum_univ_four]
     ext i
     fin_cases i <;> (simp; grind)
 -- subset_interior_hull
 let ε₁ : ℝ := 0.001
 have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num
 have negx_in_outer : !₂[-1, 0] ∈ interior (convexHull ℝ outerShadow) := by
   apply Convex.mem_interior_hull hε₀0 hε₁ zero_in_outer
   rw [mem_convexHull_iff_exists_fintype]
   -- we need to write (-1,0) as a convex combination of
   -- (-(1-ε)√2, 0), ((1-ε)√2, 0)
   use Fin 2, inferInstance
   use ![((1-ε₁)* √2 - 1) / (2 * (1 - ε₁) * √2),
         ((1-ε₁)* √2 + 1) /(2 * (1 - ε₁) * √2)]
   use ![!₂[(1-ε₁) * √2, 0], !₂[-(1-ε₁) * √2, 0]]
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro i; fin_cases i
     · simp only [Fin.zero_eta, Fin.isValue, cons_val_zero]
       have h1 : 0 ≤ 2 * (1 - 1e-3) * √2 := by positivity
       suffices H : (0:ℝ) ≤ (1 - 1e-3) * √2 - 1 from div_nonneg H h1
       suffices H : (1:ℝ) ≤ (1 - 1e-3) * √2 from sub_nonneg_of_le H
       refine (sq_le_sq₀ zero_le_one (by positivity)).mp ?_
       rw [mul_pow, Real.sq_sqrt zero_le_two]
       norm_num
     · simp only [Fin.mk_one, Fin.isValue, cons_val_one, cons_val_fin_one]
       positivity
   · simp only [Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one,
                cons_val_fin_one]
     field_simp; ring
   · intro i
     fin_cases i
     · unfold outerShadow projXy outerRot rh
       simp only [Fin.isValue, cons_val_zero, neg_sub, Fin.zero_eta, Set.mem_image]
       use !₂[√2, 0]
       constructor
       · rw [Set.mem_setOf]
         use 3; simp
       · ext i
         fin_cases i <;> simp
     · simp only [projXy, outerRot, rh, Fin.isValue, cons_val_fin_one,
        cons_val_one, neg_sub, Fin.mk_one, Set.mem_image, outerShadow]
       use !₂[-√2, 0]
       constructor
       · rw [Set.mem_setOf]
         use 0
         simp [vecHead, vecTail]
         ring_nf
       · ext i; fin_cases i
         · simp; ring
         · simp
   · ext i
     fin_cases i
     · simp; field
     · simp
 have posx_in_outer : !₂[1, 0] ∈ interior (convexHull ℝ outerShadow) := by
   apply Convex.mem_interior_hull hε₀0 hε₁ zero_in_outer
   rw [mem_convexHull_iff_exists_fintype]
   -- we need to write (1,0) as a convex combination of
   -- (-(1-ε)√2, 0), ((1-ε)√2, 0)
   use Fin 2, inferInstance
   use ![((1-ε₁)* √2 + 1) / (2 * (1 - ε₁) * √2),
         ((1-ε₁)* √2 - 1) /(2 * (1 - ε₁) * √2)]
   use ![!₂[(1-ε₁) * √2, 0], !₂[-(1-ε₁) * √2, 0]]
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro i; fin_cases i
     · simp only [Fin.zero_eta, Fin.isValue, cons_val_zero]
       positivity
     · simp only [Fin.mk_one, Fin.isValue, cons_val_one, cons_val_fin_one]
       have h1 : 0 ≤ 2 * (1 - 1e-3) * √2 := by positivity
       suffices H : (0:ℝ) ≤ (1 - 1e-3) * √2 - 1 from div_nonneg H h1
       suffices H : (1:ℝ) ≤ (1 - 1e-3) * √2 from sub_nonneg_of_le H
       refine (sq_le_sq₀ zero_le_one (by positivity)).mp ?_
       rw [mul_pow, Real.sq_sqrt zero_le_two]
       norm_num
   · simp; field
   · intro i
     fin_cases i
     · unfold outerShadow projXy outerRot rh
       simp only [Fin.isValue, cons_val_zero, neg_sub, Fin.zero_eta, Set.mem_image]
       use !₂[√2, 0]
       constructor
       · use 3; simp
       · ext i
         fin_cases i <;> simp
     · simp only [projXy,outerRot, rh, Fin.isValue,
        cons_val_fin_one, cons_val_one, neg_sub, Fin.mk_one, Set.mem_image, outerShadow]
       use !₂[-√2, 0]
       constructor
       · use 0; simp; ring_nf
       · ext i; fin_cases i
         · norm_num
         · simp
   · ext i
     fin_cases i
     · simp; field
     · simp
 -- we have y ∈ ℝ³ that came from the square, which after being rotated by
 -- innerRot and projected, is x
 rw [Set.mem_setOf] at hx
 obtain ⟨y, proj_rot_y_eq_x⟩ := hx
 rw [← proj_rot_y_eq_x]
 unfold innerOffset
 simp only [zero_add]
 fin_cases y
 · simpa [projXy, vecHead, vecTail] using negx_in_outer
 · simpa [projXy, vecHead, vecTail] using posx_in_outer
 · simpa [projXy, vecHead, vecTail] using negx_in_outer
 · simpa [projXy, vecHead, vecTail] using posx_in_outer

end Square
