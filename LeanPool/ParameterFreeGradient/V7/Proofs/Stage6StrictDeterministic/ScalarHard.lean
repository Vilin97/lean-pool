/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import Mathlib.Analysis.Calculus.Deriv.Pow
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage6StrictDeterministic.HSelection
public import Mathlib.Analysis.Convex.Deriv

/-!
Calculus, convexity, minimizers, and growth of the scalar affine-quadratic-affine hard
objective.
-/

@[expose] public section

namespace V7.Stage6StrictDeterministic

/-- The piecewise linear-quadratic hard objective in displacement coordinates. -/
noncomputable def hardValue (eps H z : ℝ) : ℝ :=
  let g := 2 * eps
  if z ≤ H then -g * z
  else if z ≤ 3 * H then -g * z + (g / (2 * H)) * (z - H) ^ 2
  else g * z - 4 * g * H

/-- The continuous piecewise affine slope of the hard objective. -/
noncomputable def hardSlope (eps H z : ℝ) : ℝ :=
  let g := 2 * eps
  if z ≤ H then -g else if z ≤ 3 * H then g * (z / H - 2) else g

theorem hardValue_of_le {eps H z : ℝ} (hz : z ≤ H) :
    hardValue eps H z = -(2 * eps) * z := by simp [hardValue, hz]

theorem hardValue_of_middle {eps H z : ℝ} (hzH : H < z) (hz3 : z ≤ 3 * H) :
    hardValue eps H z =
      -(2 * eps) * z + ((2 * eps) / (2 * H)) * (z - H) ^ 2 := by
  simp [hardValue, not_le.mpr hzH, hz3]

theorem hardValue_of_right {eps H z : ℝ} (hH : 0 ≤ H) (hz3 : 3 * H < z) :
    hardValue eps H z = (2 * eps) * z - 4 * (2 * eps) * H := by
  have hzH : ¬ z ≤ H := by intro h; linarith
  simp [hardValue, hzH, not_le.mpr hz3]

theorem hardSlope_of_le {eps H z : ℝ} (hz : z ≤ H) :
    hardSlope eps H z = -(2 * eps) := by simp [hardSlope, hz]

theorem hardSlope_of_middle {eps H z : ℝ} (hzH : H < z) (hz3 : z ≤ 3 * H) :
    hardSlope eps H z = (2 * eps) * (z / H - 2) := by
  simp [hardSlope, not_le.mpr hzH, hz3]

theorem hardSlope_of_right {eps H z : ℝ} (hH : 0 ≤ H) (hz3 : 3 * H < z) :
    hardSlope eps H z = 2 * eps := by
  have hzH : ¬ z ≤ H := by intro h; linarith
  simp [hardSlope, hzH, not_le.mpr hz3]

private theorem left_hasDerivAt (eps z : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -(2 * eps) * y) (-(2 * eps)) z := by
  simpa using (hasDerivAt_id z).const_mul (-(2 * eps))

private theorem middle_hasDerivAt {eps H z : ℝ} (hH : H ≠ 0) :
    HasDerivAt
      (fun y : ℝ ↦ -(2 * eps) * y +
        ((2 * eps) / (2 * H)) * (y - H) ^ 2)
      ((2 * eps) * (z / H - 2)) z := by
  have hlin := left_hasDerivAt eps z
  have hsub : HasDerivAt (fun y : ℝ ↦ y - H) 1 z :=
    (hasDerivAt_id z).sub_const H
  have hsq := hsub.pow 2
  have hquad := hsq.const_mul ((2 * eps) / (2 * H))
  have hsum0 := hlin.add hquad
  have hsum1 : HasDerivAt
      (((fun u : ℝ ↦ -(2 * eps) * u) +
        (fun u : ℝ ↦ ((2 * eps) / (2 * H)) * (u - H) ^ 2)) : ℝ → ℝ)
      (-(2 * eps) +
        ((2 * eps) / (2 * H)) * ((2 : ℝ) * (z - H))) z := by
    apply hsum0.congr_deriv
    norm_num
  have heq : ∀ᶠ y in nhds z,
      (fun u : ℝ ↦ -(2 * eps) * u +
        ((2 * eps) / (2 * H)) * (u - H) ^ 2) y =
      (((fun u : ℝ ↦ -(2 * eps) * u) +
        (fun u : ℝ ↦ ((2 * eps) / (2 * H)) * (u - H) ^ 2)) : ℝ → ℝ) y := by
    filter_upwards [] with y
    rfl
  have hsum := hsum1.congr_of_eventuallyEq heq
  apply hsum.congr_deriv
  field_simp [hH]
  ring

private theorem right_hasDerivAt (eps H z : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (2 * eps) * y - 4 * (2 * eps) * H)
      (2 * eps) z := by
  simpa using (((hasDerivAt_id z).const_mul (2 * eps)).sub_const
    (4 * (2 * eps) * H))

/-- The literal frozen affine--quadratic--affine value has the literal frozen
piecewise derivative, including both seams. -/
theorem hardValue_hasDerivAt {eps H : ℝ} (hH : 0 < H) (z : ℝ) :
    HasDerivAt (hardValue eps H) (hardSlope eps H z) z := by
  have hH0 : H ≠ 0 := ne_of_gt hH
  rcases lt_trichotomy z H with hzH | hzEq | hHz
  · have heq : ∀ᶠ y in nhds z,
        hardValue eps H y = (fun u : ℝ ↦ -(2 * eps) * u) y := by
      filter_upwards [Iio_mem_nhds hzH] with y hy
      exact hardValue_of_le hy.le
    have hslope : hardSlope eps H z = -(2 * eps) := hardSlope_of_le hzH.le
    rw [hslope]
    exact (left_hasDerivAt eps z).congr_of_eventuallyEq heq
  · subst z
    have hleft : HasDerivWithinAt (hardValue eps H) (-(2 * eps))
        (Set.Iic H) H := by
      refine (left_hasDerivAt eps H).hasDerivWithinAt.congr_of_mem ?_ (Set.mem_Iic.mpr le_rfl)
      intro y hy
      exact hardValue_of_le hy
    have hmiddle : HasDerivWithinAt (hardValue eps H) (-(2 * eps))
        (Set.Ici H ∩ Set.Iic (3 * H)) H := by
      have hpoly : HasDerivWithinAt
          (fun y : ℝ ↦ -(2 * eps) * y +
            ((2 * eps) / (2 * H)) * (y - H) ^ 2)
          ((2 * eps) * (H / H - 2))
          (Set.Ici H ∩ Set.Iic (3 * H)) H :=
        (middle_hasDerivAt (eps := eps) (z := H) hH0).hasDerivWithinAt
      have hderiv : (2 * eps) * (H / H - 2) = -(2 * eps) := by
        field_simp
        ring
      rw [hderiv] at hpoly
      refine hpoly.congr_of_mem ?_
        ⟨Set.mem_Ici.mpr le_rfl, Set.mem_Iic.mpr (by linarith)⟩
      intro y hy
      by_cases hyH : y = H
      · subst y
        simp [hardValue]
      · exact hardValue_of_middle (lt_of_le_of_ne hy.1 (Ne.symm hyH)) hy.2
    have hu := hleft.union hmiddle
    have hset : Set.Iic H ∪ (Set.Ici H ∩ Set.Iic (3 * H)) = Set.Iic (3 * H) := by
      ext y
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_inter_iff, Set.mem_Ici]
      constructor
      · rintro (hy | hy)
        · linarith
        · exact hy.2
      · intro hy
        by_cases hyH : y ≤ H
        · exact Or.inl hyH
        · exact Or.inr ⟨le_of_not_ge hyH, hy⟩
    rw [hset] at hu
    have hfull := hu.hasDerivAt (Iic_mem_nhds (by linarith : H < 3 * H))
    rw [hardSlope_of_le (eps := eps) (H := H) le_rfl]
    exact hfull
  · rcases lt_trichotomy z (3 * H) with hz3 | hz3eq | h3z
    · have heq : ∀ᶠ y in nhds z,
          hardValue eps H y = (fun u : ℝ ↦ -(2 * eps) * u +
            ((2 * eps) / (2 * H)) * (u - H) ^ 2) y := by
        filter_upwards [Ioi_mem_nhds hHz, Iio_mem_nhds hz3] with y hyH hy3
        exact hardValue_of_middle hyH hy3.le
      rw [hardSlope_of_middle hHz hz3.le]
      exact (middle_hasDerivAt (eps := eps) (z := z) hH0).congr_of_eventuallyEq heq
    · subst z
      have hmiddle : HasDerivWithinAt (hardValue eps H) (2 * eps)
          (Set.Ici H ∩ Set.Iic (3 * H)) (3 * H) := by
        have hpoly : HasDerivWithinAt
            (fun y : ℝ ↦ -(2 * eps) * y +
              ((2 * eps) / (2 * H)) * (y - H) ^ 2)
            ((2 * eps) * ((3 * H) / H - 2))
            (Set.Ici H ∩ Set.Iic (3 * H)) (3 * H) :=
          (middle_hasDerivAt (eps := eps) (z := 3 * H) hH0).hasDerivWithinAt
        have hderiv : (2 * eps) * ((3 * H) / H - 2) = 2 * eps := by
          field_simp
          ring
        rw [hderiv] at hpoly
        refine hpoly.congr_of_mem ?_
          ⟨Set.mem_Ici.mpr (by linarith), Set.mem_Iic.mpr le_rfl⟩
        intro y hy
        by_cases hyH : y = H
        · subst y
          simp [hardValue]
        · exact hardValue_of_middle (lt_of_le_of_ne hy.1 (Ne.symm hyH)) hy.2
      have hright : HasDerivWithinAt (hardValue eps H) (2 * eps)
          (Set.Ici (3 * H)) (3 * H) := by
        refine (right_hasDerivAt eps H (3 * H)).hasDerivWithinAt.congr_of_mem ?_
          (Set.mem_Ici.mpr le_rfl)
        intro y hy
        by_cases hy3 : y = 3 * H
        · subst y
          rw [hardValue_of_middle (by linarith : H < 3 * H) le_rfl]
          field_simp [hH0]
          ring
        · exact hardValue_of_right hH.le (lt_of_le_of_ne hy (Ne.symm hy3))
      have hu := hmiddle.union hright
      have hset : (Set.Ici H ∩ Set.Iic (3 * H)) ∪ Set.Ici (3 * H) = Set.Ici H := by
        ext y
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic]
        constructor
        · rintro (hy | hy)
          · exact hy.1
          · linarith
        · intro hy
          by_cases hy3 : y ≤ 3 * H
          · exact Or.inl ⟨hy, hy3⟩
          · exact Or.inr (le_of_not_ge hy3)
      rw [hset] at hu
      have hfull := hu.hasDerivAt (Ici_mem_nhds (by linarith : H < 3 * H))
      have hslope : hardSlope eps H (3 * H) = 2 * eps := by
        rw [hardSlope_of_middle (by linarith : H < 3 * H) le_rfl]
        field_simp [hH0]
        ring
      rw [hslope]
      exact hfull
    · have heq : ∀ᶠ y in nhds z,
          hardValue eps H y =
            (fun u : ℝ ↦ (2 * eps) * u - 4 * (2 * eps) * H) y := by
        filter_upwards [Ioi_mem_nhds h3z] with y hy
        exact hardValue_of_right hH.le hy
      rw [hardSlope_of_right hH.le h3z]
      exact (right_hasDerivAt eps H z).congr_of_eventuallyEq heq

theorem hardValue_differentiable {eps H : ℝ} (hH : 0 < H) :
    Differentiable ℝ (hardValue eps H) :=
  fun z ↦ (hardValue_hasDerivAt hH z).differentiableAt

theorem deriv_hardValue {eps H : ℝ} (hH : 0 < H) (z : ℝ) :
    deriv (hardValue eps H) z = hardSlope eps H z :=
  (hardValue_hasDerivAt hH z).deriv

/-- The scaled displacement clipped to the interval from minus one to one. -/
noncomputable def clippedCoordinate (H z : ℝ) : ℝ :=
  min 1 (max (-1) (z / H - 2))

theorem hardSlope_eq_clipped {eps H z : ℝ} (hH : 0 < H) :
    hardSlope eps H z = (2 * eps) * clippedCoordinate H z := by
  unfold hardSlope clippedCoordinate
  split_ifs with hzH hz3
  · have hzdiv : z / H ≤ 1 := (div_le_one hH).mpr hzH
    have ha : z / H - 2 ≤ -1 := by linarith
    have hmax : max (-1) (z / H - 2) = -1 := max_eq_left ha
    have hmin : min 1 (-1 : ℝ) = -1 := min_eq_right (by norm_num)
    rw [hmax, hmin]
    ring
  · have hHlt : H < z := lt_of_not_ge hzH
    have hzdiv_lower : -1 < z / H - 2 := by
      have := (one_lt_div hH).mpr hHlt
      linarith
    have hzdiv_upper : z / H - 2 ≤ 1 := by
      exact (sub_le_iff_le_add).mpr ((div_le_iff₀ hH).mpr (by linarith))
    have hmax : max (-1) (z / H - 2) = z / H - 2 :=
      max_eq_right hzdiv_lower.le
    have hmin : min 1 (z / H - 2) = z / H - 2 :=
      min_eq_right hzdiv_upper
    rw [hmax, hmin]
  · have h3lt : 3 * H < z := lt_of_not_ge hz3
    have hzdiv : 1 < z / H - 2 := by
      have := (lt_div_iff₀ hH).mpr h3lt
      linarith
    have hmax : max (-1) (z / H - 2) = z / H - 2 :=
      max_eq_right (by linarith)
    have hmin : min 1 (z / H - 2) = 1 := min_eq_left hzdiv.le
    rw [hmax, hmin]
    ring

theorem clippedCoordinate_monotone {H : ℝ} (hH : 0 < H) :
    Monotone (clippedCoordinate H) := by
  intro x y hxy
  unfold clippedCoordinate
  apply min_le_min le_rfl
  apply max_le_max le_rfl
  have := div_le_div_of_nonneg_right hxy hH.le
  linarith

theorem hardSlope_monotone {eps H : ℝ} (heps : 0 < eps) (hH : 0 < H) :
    Monotone (hardSlope eps H) := by
  intro x y hxy
  rw [hardSlope_eq_clipped hH, hardSlope_eq_clipped hH]
  exact mul_le_mul_of_nonneg_left (clippedCoordinate_monotone hH hxy) (by linarith)

/-- Scalar convexity follows from the globally monotone literal derivative. -/
theorem hardValue_convex {eps H : ℝ} (heps : 0 < eps) (hH : 0 < H) :
    ConvexOn ℝ Set.univ (hardValue eps H) := by
  have hderiv : Monotone (deriv (hardValue eps H)) := by
    intro x y hxy
    rw [deriv_hardValue hH, deriv_hardValue hH]
    exact hardSlope_monotone heps hH hxy
  exact hderiv.convexOn_univ_of_deriv (hardValue_differentiable hH)

theorem clippedCoordinate_lipschitz (H x y : ℝ) :
    |clippedCoordinate H x - clippedCoordinate H y| ≤
      |x / H - 2 - (y / H - 2)| := by
  have hmin := norm_inf_sub_inf_le_norm
    (max (-1) (x / H - 2)) (max (-1) (y / H - 2)) (1 : ℝ)
  have hmax := norm_sup_sub_sup_le_norm
    (x / H - 2) (y / H - 2) (-1 : ℝ)
  have hmin' : |clippedCoordinate H x - clippedCoordinate H y| ≤
      |max (-1) (x / H - 2) - max (-1) (y / H - 2)| := by
    simpa [clippedCoordinate, Real.norm_eq_abs, min_comm] using hmin
  have hmax' : |max (-1) (x / H - 2) - max (-1) (y / H - 2)| ≤
      |x / H - 2 - (y / H - 2)| := by
    simpa [Real.norm_eq_abs, max_comm] using hmax
  exact hmin'.trans hmax'

theorem hardSlope_lipschitz {eps H : ℝ} (heps : 0 < eps) (hH : 0 < H)
    (x y : ℝ) :
    |hardSlope eps H x - hardSlope eps H y| ≤
      ((2 * eps) / H) * |x - y| := by
  rw [hardSlope_eq_clipped hH, hardSlope_eq_clipped hH]
  have hclip := clippedCoordinate_lipschitz H x y
  have hg : 0 ≤ 2 * eps := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hclip hg
  have habs : |x / H - 2 - (y / H - 2)| = |x - y| / H := by
    have heq : x / H - 2 - (y / H - 2) = (x - y) / H := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hH]
  rw [habs] at hscaled
  calc
    |2 * eps * clippedCoordinate H x - 2 * eps * clippedCoordinate H y| =
        (2 * eps) * |clippedCoordinate H x - clippedCoordinate H y| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hg]
    _ ≤ (2 * eps) * (|x - y| / H) := hscaled
    _ = (2 * eps / H) * |x - y| := by ring

theorem hardValue_at_minimizer {eps H : ℝ} (hH : 0 < H) :
    hardValue eps H (2 * H) = -3 * eps * H := by
  rw [hardValue_of_middle (by linarith : H < 2 * H) (by linarith : 2 * H ≤ 3 * H)]
  field_simp [ne_of_gt hH]
  ring

theorem hardValue_minimum {eps H : ℝ} (heps : 0 < eps) (hH : 0 < H)
    (z : ℝ) : hardValue eps H (2 * H) ≤ hardValue eps H z := by
  rw [hardValue_at_minimizer hH]
  by_cases hzH : z ≤ H
  · rw [hardValue_of_le hzH]
    nlinarith
  · have hHz : H < z := lt_of_not_ge hzH
    by_cases hz3 : z ≤ 3 * H
    · rw [hardValue_of_middle hHz hz3]
      have hcoef : 0 ≤ eps / H := (div_pos heps hH).le
      have hsquare : 0 ≤ (z - 2 * H) ^ 2 := sq_nonneg _
      have hidentity :
          -(2 * eps) * z + ((2 * eps) / (2 * H)) * (z - H) ^ 2 +
              3 * eps * H = (eps / H) * (z - 2 * H) ^ 2 := by
        field_simp [ne_of_gt hH]
        ring
      nlinarith [mul_nonneg hcoef hsquare]
    · rw [hardValue_of_right hH.le (lt_of_not_ge hz3)]
      nlinarith

theorem hardValue_eq_minimizer_iff {eps H : ℝ} (heps : 0 < eps) (hH : 0 < H)
    (z : ℝ) : hardValue eps H z = hardValue eps H (2 * H) ↔ z = 2 * H := by
  constructor
  · intro heq
    rw [hardValue_at_minimizer hH] at heq
    by_cases hzH : z ≤ H
    · rw [hardValue_of_le hzH] at heq
      nlinarith
    · have hHz : H < z := lt_of_not_ge hzH
      by_cases hz3 : z ≤ 3 * H
      · rw [hardValue_of_middle hHz hz3] at heq
        have hidentity :
            -(2 * eps) * z + ((2 * eps) / (2 * H)) * (z - H) ^ 2 +
                3 * eps * H = (eps / H) * (z - 2 * H) ^ 2 := by
          field_simp [ne_of_gt hH]
          ring
        have hprod : (eps / H) * (z - 2 * H) ^ 2 = 0 := by
          linarith
        rcases mul_eq_zero.mp hprod with hcoef | hsquare
        · exact False.elim ((div_ne_zero (ne_of_gt heps) (ne_of_gt hH)) hcoef)
        · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
      · rw [hardValue_of_right hH.le (lt_of_not_ge hz3)] at heq
        nlinarith
  · rintro rfl
    rfl

/-- A global linear lower bound exposing both affine tails. -/
theorem hardValue_linear_lower {eps H : ℝ} (heps : 0 < eps) (hH : 0 < H)
    (z : ℝ) :
    (2 * eps) * |z| - 4 * (2 * eps) * H ≤ hardValue eps H z := by
  by_cases hzH : z ≤ H
  · rw [hardValue_of_le hzH]
    by_cases hz0 : z ≤ 0
    · rw [abs_of_nonpos hz0]
      nlinarith
    · rw [abs_of_pos (lt_of_not_ge hz0)]
      nlinarith
  · have hHz : H < z := lt_of_not_ge hzH
    have hz0 : 0 < z := hH.trans hHz
    rw [abs_of_pos hz0]
    by_cases hz3 : z ≤ 3 * H
    · rw [hardValue_of_middle hHz hz3]
      have hcoef : 0 ≤ eps / H := (div_pos heps hH).le
      have hsquare : 0 ≤ (z - 3 * H) ^ 2 := sq_nonneg _
      have hidentity :
          (-(2 * eps) * z + ((2 * eps) / (2 * H)) * (z - H) ^ 2) -
              ((2 * eps) * z - 4 * (2 * eps) * H) =
            (eps / H) * (z - 3 * H) ^ 2 := by
        field_simp [ne_of_gt hH]
        ring
      nlinarith [mul_nonneg hcoef hsquare]
    · rw [hardValue_of_right hH.le (lt_of_not_ge hz3)]

end V7.Stage6StrictDeterministic
