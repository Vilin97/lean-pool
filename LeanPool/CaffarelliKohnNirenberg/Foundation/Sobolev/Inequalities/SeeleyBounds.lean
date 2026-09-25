/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Seeley
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Quantitative bounds for the two-reflection extension

This file records the derivative and Jacobian estimates on the closed annulus.
The constants are deliberately coarse absolute constants; their role is to
make the change-of-variables estimates explicit.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem seeleyBounds_annulus_mem_of_closed {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) : x ∈ seeleyAnnulus := by
  exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩

private theorem seeleyBounds_second_den_ne_zero {x : Vec 3}
    (hx : x ∈ seeleyAnnulus) :
    (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x ≠ 0 := by
  have ht : 0 < vecEuclideanNorm x := by linarith only [hx.1]
  have hfactor : 0 < 2 * vecEuclideanNorm x - 1 := by
    linarith only [hx.1]
  exact (mul_pos hfactor ht).ne'

private theorem seeley_det_rank_one (a b : ℝ) (x : Vec 3)
    (L : (Vec 3) →L[ℝ] (Vec 3))
    (hL : ∀ z, L z = a • z - (b * ∑ i : Fin 3, x i * z i) • x) :
    L.det = a ^ 2 * (a - b * ∑ i : Fin 3, x i * x i) := by
  rw [show L.det = (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3))
      (Pi.basisFun ℝ (Fin 3)) L.toLinearMap).det by
        rw [LinearMap.det_toMatrix]]
  rw [Matrix.det_fin_three]
  simp only [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  have hentry (i j : Fin 3) :
      (L.toLinearMap (Pi.single j 1)) i =
        a * (if i = j then 1 else 0) - (b * x j) * x i := by
    change L (Pi.single j 1) i = _
    rw [hL]
    simp [Pi.single_apply]
  rw [hentry, hentry, hentry, hentry, hentry, hentry, hentry, hentry, hentry]
  norm_num [Fin.sum_univ_succ]
  ring_nf

private theorem seeley_det_one {x : Vec 3} (hx : x ∈ seeleyAnnulus) :
    (fderiv ℝ seeleyReflectionOne x).det = -(vecNormSq x)⁻¹ ^ 3 := by
  have hq0 : vecNormSq x ≠ 0 := by
    rw [← vecEuclideanNorm_sq]
    have ht : 0 < vecEuclideanNorm x := by linarith only [hx.1]
    positivity
  have hdet := seeley_det_rank_one (vecNormSq x)⁻¹
    ((vecNormSq x)⁻¹ ^ 2 * 2) x (fderiv ℝ seeleyReflectionOne x) (by
      intro z
      rw [seeleyReflectionOne_fderiv_apply hx z]
      simp only [mul_assoc])
  rw [hdet]
  field_simp [hq0]
  rw [← vecNormSq_eq_sum_sq]
  ring_nf

private theorem seeley_det_two {x : Vec 3} (hx : x ∈ seeleyAnnulus) :
    (fderiv ℝ seeleyReflectionTwo x).det =
      -2 * vecEuclideanNorm x ^ 2 /
        ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4 := by
  let t : ℝ := vecEuclideanNorm x
  let d : ℝ := (2 * t - 1) * t
  have hq : vecNormSq x = t ^ 2 := by
    exact (vecEuclideanNorm_sq x).symm
  have hq0 : vecNormSq x ≠ 0 := by
    rw [← vecEuclideanNorm_sq]
    have ht : 0 < vecEuclideanNorm x := by linarith only [hx.1]
    positivity
  have hden0 : d ≠ 0 := by
    dsimp [d]
    exact seeleyBounds_second_den_ne_zero hx
  have hdet := seeley_det_rank_one d⁻¹
    (d⁻¹ ^ 2 * (4 * t - 1) * (2 * t)⁻¹ * 2) x
    (fderiv ℝ seeleyReflectionTwo x) (by
      intro z
      rw [seeleyReflectionTwo_fderiv_apply hx z]
      dsimp [d, t]
      ring_nf)
  rw [hdet]
  have hqsum : (∑ i : Fin 3, x i * x i) = t ^ 2 := by
    calc
      _ = vecNormSq x := by rfl
      _ = t ^ 2 := hq
  rw [hqsum]
  dsimp [d, t] at hden0 ⊢
  have htpos : 0 < vecEuclideanNorm x := by linarith only [hx.1]
  have ht0 : vecEuclideanNorm x ≠ 0 := htpos.ne'
  have hfactor0 : 2 * vecEuclideanNorm x - 1 ≠ 0 := by
    linarith only [hx.1]
  field_simp [hden0, hq0, ht0, hfactor0]
  ring_nf

private theorem seeley_closed_bounds {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    1 ≤ vecEuclideanNorm x ∧ vecEuclideanNorm x ≤ 2 :=
  hx

private theorem seeley_closed_sq_bounds {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    1 ≤ vecNormSq x ∧ vecNormSq x ≤ 4 := by
  have ht := seeley_closed_bounds hx
  have hsq := vecEuclideanNorm_sq x
  constructor
  · nlinarith only [ht.1, sq_nonneg (vecEuclideanNorm x - 1), hsq]
  · nlinarith only [ht.2, vecEuclideanNorm_nonneg x,
      sq_nonneg (vecEuclideanNorm x - 2), hsq]

private theorem seeley_closed_den_bounds {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    1 ≤ (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x ∧
      (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x ≤ 6 := by
  have ht := seeley_closed_bounds hx
  constructor <;> nlinarith only [ht.1, ht.2, vecEuclideanNorm_nonneg x,
    sq_nonneg (vecEuclideanNorm x - 1), sq_nonneg (vecEuclideanNorm x - 2)]

theorem seeleyReflectionOne_fderiv_det_bounds {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    (1 / 64 : ℝ) ≤ |(fderiv ℝ seeleyReflectionOne x).det| ∧
      |(fderiv ℝ seeleyReflectionOne x).det| ≤ 1 := by
  have hA := seeley_det_one (seeleyBounds_annulus_mem_of_closed hx)
  have hq := seeley_closed_sq_bounds hx
  have hqpos : 0 < vecNormSq x := by linarith only [hq.1]
  rw [hA, abs_neg, abs_pow, abs_of_pos (inv_pos.mpr hqpos)]
  constructor
  · have hpow : vecNormSq x ^ 3 ≤ 4 ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) hq.2 3
    have hpos : 0 < vecNormSq x ^ 3 := pow_pos hqpos 3
    have hi : (1 / 4 : ℝ) ≤ (vecNormSq x)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hqpos hq.2
    have hipow : (1 / 4 : ℝ) ^ 3 ≤ (vecNormSq x)⁻¹ ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hi 3
    calc
      (1 / 64 : ℝ) = (1 / 4 : ℝ) ^ 3 := by norm_num
      _ ≤ (vecNormSq x)⁻¹ ^ 3 := hipow
  · have hpow : 1 ≤ vecNormSq x ^ 3 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num) hq.1 3
    have hi := (inv_le_one₀ (by positivity)).2 hpow
    simpa only [inv_pow] using hi

theorem seeleyReflectionTwo_fderiv_det_bounds {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    (1 / 648 : ℝ) ≤ |(fderiv ℝ seeleyReflectionTwo x).det| ∧
      |(fderiv ℝ seeleyReflectionTwo x).det| ≤ 8 := by
  let t := vecEuclideanNorm x
  let d := (2 * t - 1) * t
  have ht := seeley_closed_bounds hx
  have hd := seeley_closed_den_bounds hx
  have hdet := seeley_det_two (seeleyBounds_annulus_mem_of_closed hx)
  have hrewrite :
      -2 * vecEuclideanNorm x ^ 2 /
          ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4 =
        -(2 * vecEuclideanNorm x ^ 2 /
          ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4) := by ring_nf
  rw [hdet, hrewrite, abs_neg, abs_of_nonneg]
  · constructor
    · have ht2 : 1 ≤ vecEuclideanNorm x ^ 2 := by
        nlinarith only [ht.1, sq_nonneg (vecEuclideanNorm x - 1)]
      have hd4 :
          ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4 ≤ 6 ^ 4 := by
        exact pow_le_pow_left₀ (by linarith only [hd.1]) hd.2 4
      have hpos : 0 <
          ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4 := by
        have hdenpos : 0 <
            (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x := by
          linarith only [hd.1]
        positivity
      rw [div_eq_mul_inv]
      have hinv : (6 : ℝ)⁻¹ ^ 4 ≤
          ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 4 := by
        have hbase : (6 : ℝ)⁻¹ ≤
            ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ := by
          exact (inv_le_inv₀ (by positivity) (by linarith only [hd.1])).2 hd.2
        exact pow_le_pow_left₀ (by positivity) hbase 4
      calc
        (1 / 648 : ℝ) = 2 / (6 : ℝ) ^ 4 := by norm_num
        _ ≤ 2 * vecEuclideanNorm x ^ 2 / 6 ^ 4 := by
          exact div_le_div₀ (by positivity) (by nlinarith only [ht2])
            (by positivity) le_rfl
        _ ≤ 2 * vecEuclideanNorm x ^ 2 /
            ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4 := by
          exact div_le_div_of_nonneg_left (by positivity) hpos hd4
    · have ht2 : vecEuclideanNorm x ^ 2 ≤ 4 := by
        nlinarith only [ht.2, vecEuclideanNorm_nonneg x,
          sq_nonneg (vecEuclideanNorm x - 2)]
      have hd4 : 1 ≤
          ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4 := by
        simpa only [one_pow] using pow_le_pow_left₀ (by norm_num) hd.1 4
      have hdenpos : 0 <
          ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) := by
        linarith only [hd.1]
      calc
        2 * vecEuclideanNorm x ^ 2 /
            ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4 ≤
            2 * 4 / ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4 := by
              gcongr
        _ ≤ 8 := by
          have hpos4 : 0 <
              ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) ^ 4 := by
            positivity
          rw [div_le_iff₀ hpos4]
          nlinarith only [hd4]
  · positivity

private theorem seeleyBounds_norm_le {x : Vec 3} :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

private theorem seeleyBounds_dot_abs_le {x z : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |∑ i : Fin 3, x i * z i| ≤ 6 * ‖z‖ := by
  have hxi (i : Fin 3) : |x i| ≤ 2 := by
    exact (abs_apply_le_vecEuclideanNorm x i).trans hx.2
  have hzi (i : Fin 3) : |z i| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
  calc
    |∑ i : Fin 3, x i * z i| ≤ ∑ i : Fin 3, |x i * z i| := by
      simpa using
        (Finset.abs_sum_le_sum_abs (fun i : Fin 3 => x i * z i) Finset.univ)
    _ ≤ ∑ i : Fin 3, 2 * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hxi i) (hzi i) (abs_nonneg _) (by norm_num)
    _ = 6 * ‖z‖ := by
      simp only [Fin.sum_univ_three]
      ring_nf

private theorem seeleyBounds_q_inv_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |(vecNormSq x)⁻¹| ≤ 1 := by
  have hq := seeley_closed_sq_bounds hx
  have hqpos : 0 < vecNormSq x := by linarith only [hq.1]
  rw [abs_of_pos (inv_pos.mpr hqpos)]
  exact (inv_le_one₀ hqpos).2 hq.1

private theorem seeleyBounds_q_inv_sq_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |(vecNormSq x)⁻¹ ^ 2| ≤ 1 := by
  have hi := seeleyBounds_q_inv_le hx
  rw [abs_pow]
  simpa only [one_pow] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hi

private theorem seeleyBounds_den_inv_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹| ≤ 1 := by
  have hd := seeley_closed_den_bounds hx
  have hdpos : 0 < (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x := by
    linarith only [hd.1]
  rw [abs_of_pos (inv_pos.mpr hdpos)]
  exact (inv_le_one₀ hdpos).2 hd.1

private theorem seeleyBounds_den_inv_sq_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2| ≤ 1 := by
  have hi := seeleyBounds_den_inv_le hx
  rw [abs_pow]
  simpa only [one_pow] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hi

theorem seeleyReflectionOne_fderiv_norm_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    ‖fderiv ℝ seeleyReflectionOne x‖ ≤ 25 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  have hdot := seeleyBounds_dot_abs_le hx (z := z)
  have hcoef :
      |(vecNormSq x)⁻¹ ^ 2 * (2 * ∑ i : Fin 3, x i * z i)| ≤ 12 * ‖z‖ := by
    calc
      _ = |(vecNormSq x)⁻¹ ^ 2| * |2 * ∑ i : Fin 3, x i * z i| := abs_mul _ _
      _ ≤ 1 * (2 * (6 * ‖z‖)) := by
        gcongr
        · exact seeleyBounds_q_inv_sq_le hx
        · rw [abs_mul]
          exact mul_le_mul (by norm_num) hdot (by norm_num) (by positivity)
      _ = 12 * ‖z‖ := by ring_nf
  have hxnorm : ‖x‖ ≤ 2 :=
    (seeleyBounds_norm_le (x := x)).trans hx.2
  rw [seeleyReflectionOne_fderiv_apply (seeleyBounds_annulus_mem_of_closed hx) z]
  calc
    ‖(vecNormSq x)⁻¹ • z -
        ((vecNormSq x)⁻¹ ^ 2 * (2 * ∑ i : Fin 3, x i * z i)) • x‖ ≤
        ‖(vecNormSq x)⁻¹ • z‖ +
          ‖((vecNormSq x)⁻¹ ^ 2 * (2 * ∑ i : Fin 3, x i * z i)) • x‖ :=
      norm_sub_le _ _
    _ = |(vecNormSq x)⁻¹| * ‖z‖ +
        |(vecNormSq x)⁻¹ ^ 2 * (2 * ∑ i : Fin 3, x i * z i)| * ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖z‖ + (12 * ‖z‖) * 2 := by
      exact add_le_add
        (mul_le_mul (seeleyBounds_q_inv_le hx) (le_refl (‖z‖))
          (norm_nonneg _) (by positivity))
        (mul_le_mul hcoef hxnorm (norm_nonneg _) (by positivity))
    _ ≤ 25 * ‖z‖ := by
      calc
        _ = 25 * ‖z‖ := by ring_nf
        _ ≤ _ := le_rfl

theorem seeleyReflectionTwo_fderiv_norm_le {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    ‖fderiv ℝ seeleyReflectionTwo x‖ ≤ 169 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  have hdot := seeleyBounds_dot_abs_le hx (z := z)
  have ht := seeley_closed_bounds hx
  have hfactor : |4 * vecEuclideanNorm x - 1| ≤ 7 := by
    rw [abs_of_nonneg]
    · linarith only [ht.2]
    · linarith only [ht.1]
  have hnormcoef :
      |(4 * vecEuclideanNorm x - 1) *
          ((2 * vecEuclideanNorm x)⁻¹ *
            (2 * ∑ i : Fin 3, x i * z i))| ≤ 84 * ‖z‖ := by
    have htpos : 0 < 2 * vecEuclideanNorm x := by
      linarith only [ht.1]
    have hinv : |(2 * vecEuclideanNorm x)⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr htpos)]
      exact (inv_le_one₀ htpos).2 (by linarith only [ht.1])
    have htwo : |2 * ∑ i : Fin 3, x i * z i| ≤ 2 * (6 * ‖z‖) := by
      rw [abs_mul]
      exact mul_le_mul (by norm_num) hdot (by norm_num) (by positivity)
    have hinner : |(2 * vecEuclideanNorm x)⁻¹| *
        |2 * ∑ i : Fin 3, x i * z i| ≤ 1 * (2 * (6 * ‖z‖)) :=
      mul_le_mul hinv htwo (abs_nonneg _) (by positivity)
    calc
      _ = |4 * vecEuclideanNorm x - 1| *
          (|(2 * vecEuclideanNorm x)⁻¹| *
            |2 * ∑ i : Fin 3, x i * z i|) := by rw [abs_mul, abs_mul]
      _ ≤ 7 * (1 * (2 * (6 * ‖z‖))) := by
        exact mul_le_mul hfactor hinner (by positivity) (by norm_num)
      _ = 84 * ‖z‖ := by ring_nf
  have hcoef :
      |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2 *
          ((4 * vecEuclideanNorm x - 1) *
            ((2 * vecEuclideanNorm x)⁻¹ *
              (2 * ∑ i : Fin 3, x i * z i)))| ≤ 84 * ‖z‖ := by
    calc
      _ = |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2| *
          |(4 * vecEuclideanNorm x - 1) *
            ((2 * vecEuclideanNorm x)⁻¹ *
              (2 * ∑ i : Fin 3, x i * z i))| := abs_mul _ _
      _ ≤ 1 * (84 * ‖z‖) := by
        exact mul_le_mul (seeleyBounds_den_inv_sq_le hx) hnormcoef
          (by positivity) (by positivity)
      _ = 84 * ‖z‖ := by ring_nf
  have hxnorm : ‖x‖ ≤ 2 :=
    (seeleyBounds_norm_le (x := x)).trans hx.2
  rw [seeleyReflectionTwo_fderiv_apply (seeleyBounds_annulus_mem_of_closed hx) z]
  calc
    ‖((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ • z -
        (((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2 *
          ((4 * vecEuclideanNorm x - 1) *
            ((2 * vecEuclideanNorm x)⁻¹ *
              (2 * ∑ i : Fin 3, x i * z i)))) • x‖ ≤
        ‖((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ • z‖ +
          ‖(((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2 *
            ((4 * vecEuclideanNorm x - 1) *
              ((2 * vecEuclideanNorm x)⁻¹ *
                (2 * ∑ i : Fin 3, x i * z i)))) • x‖ :=
      norm_sub_le _ _
    _ = |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹| * ‖z‖ +
        |((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ ^ 2 *
          ((4 * vecEuclideanNorm x - 1) *
            ((2 * vecEuclideanNorm x)⁻¹ *
              (2 * ∑ i : Fin 3, x i * z i)))| * ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖z‖ + (84 * ‖z‖) * 2 := by
      exact add_le_add
        (mul_le_mul (seeleyBounds_den_inv_le hx) (le_refl (‖z‖))
          (norm_nonneg _) (by positivity))
        (mul_le_mul hcoef hxnorm (by positivity) (by norm_num))
    _ ≤ 169 * ‖z‖ := by
      calc
        _ = 169 * ‖z‖ := by ring_nf
        _ ≤ _ := le_rfl

theorem seeleyReflectionOne_lintegral_comp_le (g : Vec 3 → ℝ≥0∞) :
    ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionOne x) ∂volume ≤
      64 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
  have hpoint : ∀ x ∈ seeleyClosedAnnulus,
      g (seeleyReflectionOne x) ≤
        (64 : ℝ≥0∞) *
          (ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| *
            g (seeleyReflectionOne x)) := by
    intro x hx
    have hdet : (1 / 64 : ℝ≥0∞) ≤
        ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| := by
      calc
        (1 / 64 : ℝ≥0∞) = ENNReal.ofReal (1 / 64 : ℝ) := by
          rw [show (1 / 64 : ℝ) = (64 : ℝ)⁻¹ by norm_num,
            ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
        _ ≤ ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| :=
          ENNReal.ofReal_le_ofReal (seeleyReflectionOne_fderiv_det_bounds hx).1
    have hmul := mul_le_mul_of_nonneg_right hdet
      (bot_le : (0 : ℝ≥0∞) ≤ g (seeleyReflectionOne x))
    calc
      g (seeleyReflectionOne x) =
          (64 : ℝ≥0∞) * ((1 / 64 : ℝ≥0∞) * g (seeleyReflectionOne x)) := by
            rw [show (1 / 64 : ℝ≥0∞) = (64 : ℝ≥0∞)⁻¹ by
              simp only [div_eq_mul_inv, one_mul]]
            calc
              _ = 1 * g (seeleyReflectionOne x) := (one_mul _).symm
              _ = (64 : ℝ≥0∞) * (64 : ℝ≥0∞)⁻¹ *
                  g (seeleyReflectionOne x) := by
                    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
              _ = (64 : ℝ≥0∞) *
                  ((64 : ℝ≥0∞)⁻¹ * g (seeleyReflectionOne x)) := by
                    rw [mul_assoc]
      _ ≤ (64 : ℝ≥0∞) *
          (ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| *
            g (seeleyReflectionOne x)) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
  calc
    ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionOne x) ∂volume ≤
        ∫⁻ x in seeleyClosedAnnulus,
          (64 : ℝ≥0∞) *
            (ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| *
              g (seeleyReflectionOne x)) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem seeleyClosedAnnulus_measurableSet] with x hx
          exact hpoint x hx
    _ = 64 * ∫⁻ x in seeleyClosedAnnulus,
          ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| *
            g (seeleyReflectionOne x) ∂volume := by
          rw [lintegral_const_mul' 64 _ (by norm_num)]
    _ = 64 * ∫⁻ y in seeleyReflectionOne '' seeleyClosedAnnulus,
          g y ∂volume := by
          rw [seeley_changeVariables_lintegral_one]
    _ ≤ 64 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
          gcongr
          intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          exact seeleyReflectionOne_maps_closedAnnulus hx

theorem seeleyReflectionTwo_lintegral_comp_le (g : Vec 3 → ℝ≥0∞) :
    ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionTwo x) ∂volume ≤
      648 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
  have hpoint : ∀ x ∈ seeleyClosedAnnulus,
      g (seeleyReflectionTwo x) ≤
        (648 : ℝ≥0∞) *
          (ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| *
            g (seeleyReflectionTwo x)) := by
    intro x hx
    have hdet : (1 / 648 : ℝ≥0∞) ≤
        ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| := by
      calc
        (1 / 648 : ℝ≥0∞) = ENNReal.ofReal (1 / 648 : ℝ) := by
          rw [show (1 / 648 : ℝ) = (648 : ℝ)⁻¹ by norm_num,
            ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
        _ ≤ ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| :=
          ENNReal.ofReal_le_ofReal (seeleyReflectionTwo_fderiv_det_bounds hx).1
    have hmul := mul_le_mul_of_nonneg_right hdet
      (bot_le : (0 : ℝ≥0∞) ≤ g (seeleyReflectionTwo x))
    calc
      g (seeleyReflectionTwo x) =
          (648 : ℝ≥0∞) * ((1 / 648 : ℝ≥0∞) * g (seeleyReflectionTwo x)) := by
            rw [show (1 / 648 : ℝ≥0∞) = (648 : ℝ≥0∞)⁻¹ by
              simp only [div_eq_mul_inv, one_mul]]
            calc
              _ = 1 * g (seeleyReflectionTwo x) := (one_mul _).symm
              _ = (648 : ℝ≥0∞) * (648 : ℝ≥0∞)⁻¹ *
                  g (seeleyReflectionTwo x) := by
                    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
              _ = (648 : ℝ≥0∞) *
                  ((648 : ℝ≥0∞)⁻¹ * g (seeleyReflectionTwo x)) := by
                    rw [mul_assoc]
      _ ≤ (648 : ℝ≥0∞) *
          (ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| *
            g (seeleyReflectionTwo x)) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
  calc
    ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionTwo x) ∂volume ≤
        ∫⁻ x in seeleyClosedAnnulus,
          (648 : ℝ≥0∞) *
            (ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| *
              g (seeleyReflectionTwo x)) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem seeleyClosedAnnulus_measurableSet] with x hx
          exact hpoint x hx
    _ = 648 * ∫⁻ x in seeleyClosedAnnulus,
          ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| *
            g (seeleyReflectionTwo x) ∂volume := by
          rw [lintegral_const_mul' 648 _ (by norm_num)]
    _ = 648 * ∫⁻ y in seeleyReflectionTwo '' seeleyClosedAnnulus,
          g y ∂volume := by
          rw [seeley_changeVariables_lintegral_two]
    _ ≤ 648 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
          gcongr
          intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          exact seeleyReflectionTwo_maps_closedAnnulus hx

end
end CKN
