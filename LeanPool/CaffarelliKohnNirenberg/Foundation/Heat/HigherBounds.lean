/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Bounds

/-!
# Higher Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

private lemma heatKernel_third_derivative_abs_le {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i j k : Fin 3) :
    |heatKernelSpaceThirdDerivative x t i j k| ≤
      heatKernel x t *
        ((vec3EuclideanNorm x) ^ 3 / (8 * t ^ 3) +
          3 * vec3EuclideanNorm x / (4 * t ^ 2)) := by
  let s : ℝ := vec3EuclideanNorm x
  have hs : 0 ≤ s := by
    dsimp [s]
    exact vec3EuclideanNorm_nonneg x
  have hxi : ∀ q : Fin 3, |x q| ≤ s := by
    intro q
    exact abs_vec3_component_le_norm x q
  have hij : |(if i = j then x k else 0)| ≤ s := by
    split_ifs with h
    · simpa using hxi k
    · simp only [abs_zero]
      exact hs
  have hik : |(if i = k then x j else 0)| ≤ s := by
    split_ifs with h
    · simpa using hxi j
    · simp only [abs_zero]
      exact hs
  have hjk : |(if j = k then x i else 0)| ≤ s := by
    split_ifs with h
    · simpa using hxi i
    · simp only [abs_zero]
      exact hs
  rw [heatKernelSpaceThirdDerivative, ite_eq_left ht, abs_mul]
  rw [abs_of_nonneg (heatKernel_nonneg x t)]
  have hfirst :
      |-(x i) * (x j) * (x k) / (8 * t ^ 3)| ≤ s ^ 3 / (8 * t ^ 3) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (8 * t ^ 3 : ℝ))]
    simp only [abs_mul, abs_neg]
    have hp : |x i| * |x j| ≤ s * s := by
      exact mul_le_mul (hxi i) (hxi j) (abs_nonneg _) hs
    have hp' : |x i| * |x j| * |x k| ≤ s * s * s := by
      exact mul_le_mul hp (hxi k)
        (abs_nonneg _) (mul_nonneg hs hs)
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      |x i| * |x j| * |x k| ≤ s * s * s := hp'
      _ = s ^ 3 := by ring
  have hsecond :
      |((if i = j then x k else 0) +
        (if i = k then x j else 0) +
        (if j = k then x i else 0)) / (4 * t ^ 2)| ≤
      3 * s / (4 * t ^ 2) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (4 * t ^ 2 : ℝ))]
    have habs :
        |(if i = j then x k else 0) +
            (if i = k then x j else 0) +
            (if j = k then x i else 0)| ≤
          |(if i = j then x k else 0)| +
            |(if i = k then x j else 0)| +
              |(if j = k then x i else 0)| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hsum :
        |(if i = j then x k else 0)| +
            |(if i = k then x j else 0)| +
              |(if j = k then x i else 0)| ≤ 3 * s := by
      calc
        _ ≤ s + s + s := add_le_add (add_le_add hij hik) hjk
        _ = 3 * s := by ring
    exact div_le_div_of_nonneg_right (habs.trans hsum) (by positivity)
  have htotal :
      |-(x i) * (x j) * (x k) / (8 * t ^ 3) +
        ((if i = j then x k else 0) +
          (if i = k then x j else 0) +
          (if j = k then x i else 0)) / (4 * t ^ 2)| ≤
        s ^ 3 / (8 * t ^ 3) + 3 * s / (4 * t ^ 2) := by
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  have hmul := mul_le_mul_of_nonneg_right htotal (heatKernel_nonneg x t)
  rw [show (s ^ 3 / (8 * t ^ 3) + 3 * s / (4 * t ^ 2)) * heatKernel x t =
      heatKernel x t * (s ^ 3 / (8 * t ^ 3) + 3 * s / (4 * t ^ 2)) by ring] at hmul
  exact hmul

lemma heatKernelSpaceThirdDerivative_abs_le_rho_inv_six
    {x : Vec3} {t : ℝ} (ht : 0 < t) (i j k : Fin 3) :
    |heatKernelSpaceThirdDerivative x t i j k| ≤
      1000000000000 / rhoTwo x t ^ 6 := by
  let s : ℝ := vec3EuclideanNorm x
  let z : ℝ := Real.sqrt t
  let a : ℝ := (∑ q, x q ^ 2) / (4 * t)
  let u : ℝ := s / z
  have hs : 0 ≤ s := by
    dsimp [s]
    exact vec3EuclideanNorm_nonneg x
  have hz : 0 < z := Real.sqrt_pos.2 ht
  have htz : z ^ 2 = t := Real.sq_sqrt ht.le
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hsu : s = z * u := by
    dsimp [u]
    field_simp
  have hua : u ^ 2 = 4 * a := by
    dsimp [u, a, s]
    rw [div_pow, vec3EuclideanNorm_sq, htz]
    field_simp [htz]
  have h1u : 1 + u ≤ 3 * (1 + a) := by
    have hu_le : u ≤ 2 * (1 + a) := by
      nlinarith only [hua, sq_nonneg (u - 1)]
    nlinarith only [ha, hu_le]
  have hG : heatKernel x t ≤ z ^ (-(3 : ℝ)) * Real.exp (-a) := by
    rw [heatKernel_eq_formula_sum ht]
    have harg : -(∑ q, x q ^ 2) / (4 * t) = -a := by
      dsimp [a]
      ring
    rw [harg]
    exact mul_le_mul_of_nonneg_right (heat_prefactor_le ht) (Real.exp_nonneg _)
  have hrho : rhoTwo x t = z * (1 + u) := by
    change s + z = z * (1 + u)
    rw [hsu]
    ring
  have hscaled :
      rhoTwo x t ^ 6 * |heatKernelSpaceThirdDerivative x t i j k| ≤
        ((1 : ℝ) / 8 * u ^ 3 + 3 / 4 * u) *
          (1 + u) ^ 6 * Real.exp (-a) := by
    rw [hrho]
    calc
      (z * (1 + u)) ^ 6 *
          |heatKernelSpaceThirdDerivative x t i j k| ≤
          (z * (1 + u)) ^ 6 *
            (heatKernel x t *
              (s ^ 3 / (8 * t ^ 3) + 3 * s / (4 * t ^ 2))) := by
        gcongr
        exact heatKernel_third_derivative_abs_le ht i j k
      _ ≤ (z * (1 + u)) ^ 6 *
          ((z ^ (-(3 : ℝ)) * Real.exp (-a)) *
            (s ^ 3 / (8 * t ^ 3) + 3 * s / (4 * t ^ 2))) := by
        gcongr
      _ = ((1 : ℝ) / 8 * u ^ 3 + 3 / 4 * u) *
          (1 + u) ^ 6 * Real.exp (-a) := by
        rw [hsu, ← htz, heat_rpow_neg_three z hz]
        field_simp [hz.ne']
  have hu_bound :
      ((1 : ℝ) / 8 * u ^ 3 + 3 / 4 * u) * (1 + u) ^ 6 *
          Real.exp (-a) ≤ 1000000000000 := by
    have hu1 : u ≤ 3 * (1 + a) := by
      nlinarith only [h1u]
    have hpoly :
        ((1 : ℝ) / 8 * u ^ 3 + 3 / 4 * u) * (1 + u) ^ 6 *
            Real.exp (-a) ≤
          ((1 : ℝ) / 8 * (3 * (1 + a)) ^ 3 +
            3 / 4 * (3 * (1 + a))) *
            (3 * (1 + a)) ^ 6 * Real.exp (-a) := by
      gcongr
    calc
      ((1 : ℝ) / 8 * u ^ 3 + 3 / 4 * u) * (1 + u) ^ 6 *
          Real.exp (-a) ≤
        ((1 : ℝ) / 8 * (3 * (1 + a)) ^ 3 +
          3 / 4 * (3 * (1 + a))) *
          (3 * (1 + a)) ^ 6 * Real.exp (-a) := hpoly
      _ ≤ 1000000000000 := by
        have hpa :
            ((1 : ℝ) / 8 * (3 * (1 + a)) ^ 3 +
              3 / 4 * (3 * (1 + a))) *
              (3 * (1 + a)) ^ 6 * Real.exp (-a) ≤
            10000 * (1 + a) ^ 9 * Real.exp (-a) := by
          have hA : 1 ≤ 1 + a := by linarith only [ha]
          have hA7 : (1 + a) ^ 7 ≤ (1 + a) ^ 9 :=
            pow_le_pow_right₀ hA (by norm_num)
          have hA9 : 0 ≤ (1 + a) ^ 9 := by positivity
          calc
            ((1 : ℝ) / 8 * (3 * (1 + a)) ^ 3 +
                3 / 4 * (3 * (1 + a))) *
                (3 * (1 + a)) ^ 6 * Real.exp (-a) =
                ((19683 : ℝ) / 8 * (1 + a) ^ 9 +
                  (6561 : ℝ) / 4 * (1 + a) ^ 7) * Real.exp (-a) := by ring
            _ ≤ (10000 * (1 + a) ^ 9) * Real.exp (-a) := by
              gcongr
              nlinarith only [hA7, hA9]
            _ = 10000 * (1 + a) ^ 9 * Real.exp (-a) := by ring
        calc
          ((1 : ℝ) / 8 * (3 * (1 + a)) ^ 3 +
              3 / 4 * (3 * (1 + a))) *
              (3 * (1 + a)) ^ 6 * Real.exp (-a) ≤
              10000 * (1 + a) ^ 9 * Real.exp (-a) := hpa
          _ ≤ 10000 * ((2 : ℝ) ^ (9 - 1) *
              (1 + (Nat.factorial 9 : ℝ))) := by
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left
                (one_add_pow_exp_neg_le (n := 9) ha)
                (by norm_num : 0 ≤ (10000 : ℝ)))
          _ ≤ 1000000000000 := by norm_num
  have hρ : 0 < rhoTwo x t := by
    unfold rhoTwo
    positivity
  apply (le_div_iff₀ (pow_pos hρ 6)).2
  calc
    |heatKernelSpaceThirdDerivative x t i j k| * rhoTwo x t ^ 6 =
        rhoTwo x t ^ 6 * |heatKernelSpaceThirdDerivative x t i j k| := by ring
    _ ≤ 1000000000000 := hscaled.trans hu_bound

private lemma heatKernel_fourth_derivative_abs_le {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i j k l : Fin 3) :
    |heatKernelSpaceFourthDerivative x t i j k l| ≤
      heatKernel x t *
        ((vec3EuclideanNorm x) ^ 4 / (16 * t ^ 4) +
          3 * (vec3EuclideanNorm x) ^ 2 / (4 * t ^ 3) +
          3 / (4 * t ^ 2)) := by
  let s : ℝ := vec3EuclideanNorm x
  have hs : 0 ≤ s := by
    dsimp [s]
    exact vec3EuclideanNorm_nonneg x
  have hxi : ∀ q : Fin 3, |x q| ≤ s := by
    intro q
    exact abs_vec3_component_le_norm x q
  have hfour :
      |(x i) * (x j) * (x k) * (x l) / (16 * t ^ 4)| ≤
        s ^ 4 / (16 * t ^ 4) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (16 * t ^ 4 : ℝ))]
    simp only [abs_mul]
    have hij : |x i| * |x j| ≤ s * s :=
      mul_le_mul (hxi i) (hxi j) (abs_nonneg _) hs
    have hijk : |x i| * |x j| * |x k| ≤ s * s * s :=
      mul_le_mul hij (hxi k) (abs_nonneg _) (mul_nonneg hs hs)
    have hijkl : |x i| * |x j| * |x k| * |x l| ≤
        s * s * s * s :=
      mul_le_mul hijk (hxi l) (abs_nonneg _) (mul_nonneg (mul_nonneg hs hs) hs)
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      |x i| * |x j| * |x k| * |x l| ≤ s * s * s * s := hijkl
      _ = s ^ 4 := by ring
  have hpair :
      |((if i = j then (x k) * (x l) else 0) +
        (if i = k then (x j) * (x l) else 0) +
        (if i = l then (x j) * (x k) else 0) +
        (if j = k then (x i) * (x l) else 0) +
        (if j = l then (x i) * (x k) else 0) +
        (if k = l then (x i) * (x j) else 0)) / (8 * t ^ 3)| ≤
      3 * s ^ 2 / (4 * t ^ 3) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (8 * t ^ 3 : ℝ))]
    let a₁ : ℝ := if i = j then (x k) * (x l) else 0
    let a₂ : ℝ := if i = k then (x j) * (x l) else 0
    let a₃ : ℝ := if i = l then (x j) * (x k) else 0
    let a₄ : ℝ := if j = k then (x i) * (x l) else 0
    let a₅ : ℝ := if j = l then (x i) * (x k) else 0
    let a₆ : ℝ := if k = l then (x i) * (x j) else 0
    have hterm : ∀ a b : Fin 3, |x a * x b| ≤ s ^ 2 := by
      intro a b
      rw [abs_mul]
      exact (mul_le_mul (hxi a) (hxi b) (abs_nonneg _) hs).trans_eq (by ring)
    have hif : ∀ (P : Prop) [Decidable P] (a b : Fin 3),
        |(if P then x a * x b else 0)| ≤ s ^ 2 := by
      intro P _ a b
      split_ifs with hP
      · exact hterm a b
      · rw [abs_zero]
        positivity
    have hsum :
        |a₁| + |a₂| + |a₃| + |a₄| + |a₅| + |a₆| ≤ 6 * s ^ 2 := by
      dsimp [a₁, a₂, a₃, a₄, a₅, a₆]
      calc
        _ ≤ s ^ 2 + s ^ 2 + s ^ 2 + s ^ 2 + s ^ 2 + s ^ 2 := by
          gcongr
          · exact hif _ _ _
          · exact hif _ _ _
          · exact hif _ _ _
          · exact hif _ _ _
          · exact hif _ _ _
          · exact hif _ _ _
        _ = 6 * s ^ 2 := by ring
    have habs : |a₁ + a₂ + a₃ + a₄ + a₅ + a₆| ≤
        |a₁| + |a₂| + |a₃| + |a₄| + |a₅| + |a₆| := by
      calc
        |a₁ + a₂ + a₃ + a₄ + a₅ + a₆| ≤
            |a₁ + a₂ + a₃ + a₄ + a₅| + |a₆| := abs_add_le _ _
        _ ≤ (|a₁ + a₂ + a₃ + a₄| + |a₅|) + |a₆| := by
          gcongr
          exact abs_add_le _ _
        _ ≤ ((|a₁ + a₂ + a₃| + |a₄|) + |a₅|) + |a₆| := by
          gcongr
          exact abs_add_le _ _
        _ ≤ (((|a₁ + a₂| + |a₃|) + |a₄|) + |a₅|) + |a₆| := by
          gcongr
          exact abs_add_le _ _
        _ ≤ |a₁| + |a₂| + |a₃| + |a₄| + |a₅| + |a₆| := by
          gcongr
          exact abs_add_le _ _
    change |a₁ + a₂ + a₃ + a₄ + a₅ + a₆| / (8 * t ^ 3) ≤
      3 * s ^ 2 / (4 * t ^ 3)
    calc
      |a₁ + a₂ + a₃ + a₄ + a₅ + a₆| / (8 * t ^ 3) ≤
          (6 * s ^ 2) / (8 * t ^ 3) :=
        div_le_div_of_nonneg_right (habs.trans hsum) (by positivity)
      _ = 3 * s ^ 2 / (4 * t ^ 3) := by ring
  have hconst :
      |((if i = j then (if k = l then (1 : ℝ) else 0) else 0) +
        (if i = k then (if j = l then (1 : ℝ) else 0) else 0) +
        (if i = l then (if j = k then (1 : ℝ) else 0) else 0)) /
        (4 * t ^ 2)| ≤ 3 / (4 * t ^ 2) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (4 * t ^ 2 : ℝ))]
    let b₁ : ℝ := if i = j then (if k = l then (1 : ℝ) else 0) else 0
    let b₂ : ℝ := if i = k then (if j = l then (1 : ℝ) else 0) else 0
    let b₃ : ℝ := if i = l then (if j = k then (1 : ℝ) else 0) else 0
    have hsum :
        |b₁| + |b₂| + |b₃| ≤ 3 := by
      dsimp [b₁, b₂, b₃]
      split_ifs <;> norm_num
    have habs : |b₁ + b₂ + b₃| ≤ |b₁| + |b₂| + |b₃| := by
      calc
        |b₁ + b₂ + b₃| ≤ |b₁ + b₂| + |b₃| := abs_add_le _ _
        _ ≤ (|b₁| + |b₂|) + |b₃| := by
          gcongr
          exact abs_add_le _ _
        _ = |b₁| + |b₂| + |b₃| := by ring
    change |b₁ + b₂ + b₃| / (4 * t ^ 2) ≤ 3 / (4 * t ^ 2)
    exact (div_le_div_of_nonneg_right (habs.trans hsum) (by positivity)).trans_eq
      (by ring)
  rw [heatKernelSpaceFourthDerivative, ite_eq_left ht, abs_mul]
  rw [abs_of_nonneg (heatKernel_nonneg x t)]
  have htotal :
      |(x i) * (x j) * (x k) * (x l) / (16 * t ^ 4) -
        (((if i = j then (x k) * (x l) else 0) +
          (if i = k then (x j) * (x l) else 0) +
          (if i = l then (x j) * (x k) else 0) +
          (if j = k then (x i) * (x l) else 0) +
          (if j = l then (x i) * (x k) else 0) +
          (if k = l then (x i) * (x j) else 0)) / (8 * t ^ 3)) +
        (((if i = j then (if k = l then (1 : ℝ) else 0) else 0) +
          (if i = k then (if j = l then (1 : ℝ) else 0) else 0) +
          (if i = l then (if j = k then (1 : ℝ) else 0) else 0)) /
          (4 * t ^ 2))| ≤
      s ^ 4 / (16 * t ^ 4) + 3 * s ^ 2 / (4 * t ^ 3) +
        3 / (4 * t ^ 2) := by
    let A : ℝ := (x i) * (x j) * (x k) * (x l) / (16 * t ^ 4)
    let B : ℝ := ((if i = j then (x k) * (x l) else 0) +
      (if i = k then (x j) * (x l) else 0) +
      (if i = l then (x j) * (x k) else 0) +
      (if j = k then (x i) * (x l) else 0) +
      (if j = l then (x i) * (x k) else 0) +
      (if k = l then (x i) * (x j) else 0)) / (8 * t ^ 3)
    let C : ℝ := ((if i = j then (if k = l then (1 : ℝ) else 0) else 0) +
      (if i = k then (if j = l then (1 : ℝ) else 0) else 0) +
      (if i = l then (if j = k then (1 : ℝ) else 0) else 0)) /
      (4 * t ^ 2)
    have hA : |A| ≤ s ^ 4 / (16 * t ^ 4) := by
      dsimp [A]
      exact hfour
    have hB : |B| ≤ 3 * s ^ 2 / (4 * t ^ 3) := by
      dsimp [B]
      exact hpair
    have hC : |C| ≤ 3 / (4 * t ^ 2) := by
      dsimp [C]
      exact hconst
    change |A - B + C| ≤ s ^ 4 / (16 * t ^ 4) + 3 * s ^ 2 / (4 * t ^ 3) +
      3 / (4 * t ^ 2)
    have hsub : |A - B| ≤ |A| + |B| := by
      simpa [abs_neg] using (abs_sub_le A 0 B)
    calc
      |A - B + C| ≤ |A - B| + |C| := abs_add_le _ _
      _ ≤ (|A| + |B|) + |C| := add_le_add hsub le_rfl
      _ ≤ s ^ 4 / (16 * t ^ 4) + 3 * s ^ 2 / (4 * t ^ 3) +
          3 / (4 * t ^ 2) := add_le_add (add_le_add hA hB) hC
  calc
    _ ≤ (s ^ 4 / (16 * t ^ 4) + 3 * s ^ 2 / (4 * t ^ 3) +
        3 / (4 * t ^ 2)) * heatKernel x t :=
      mul_le_mul_of_nonneg_right htotal (heatKernel_nonneg x t)
    _ = heatKernel x t *
        (s ^ 4 / (16 * t ^ 4) + 3 * s ^ 2 / (4 * t ^ 3) +
          3 / (4 * t ^ 2)) := by ring

lemma heatKernelSpaceFourthDerivative_abs_le_rho_inv_seven
    {x : Vec3} {t : ℝ} (ht : 0 < t) (i j k l : Fin 3) :
    |heatKernelSpaceFourthDerivative x t i j k l| ≤
      1000000000000000000000000000000 / rhoTwo x t ^ 7 := by
  let s : ℝ := vec3EuclideanNorm x
  let z : ℝ := Real.sqrt t
  let a : ℝ := (∑ q, x q ^ 2) / (4 * t)
  let u : ℝ := s / z
  have hs : 0 ≤ s := by
    dsimp [s]
    exact vec3EuclideanNorm_nonneg x
  have hz : 0 < z := Real.sqrt_pos.2 ht
  have htz : z ^ 2 = t := Real.sq_sqrt ht.le
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hsu : s = z * u := by
    dsimp [u]
    field_simp
  have hua : u ^ 2 = 4 * a := by
    dsimp [u, a, s]
    rw [div_pow, vec3EuclideanNorm_sq, htz]
    field_simp [htz]
  have h1u : 1 + u ≤ 3 * (1 + a) := by
    have hu_le : u ≤ 2 * (1 + a) := by
      nlinarith only [hua, sq_nonneg (u - 1)]
    nlinarith only [ha, hu_le]
  have hG : heatKernel x t ≤ z ^ (-(3 : ℝ)) * Real.exp (-a) := by
    rw [heatKernel_eq_formula_sum ht]
    have harg : -(∑ q, x q ^ 2) / (4 * t) = -a := by
      dsimp [a]
      ring
    rw [harg]
    exact mul_le_mul_of_nonneg_right (heat_prefactor_le ht) (Real.exp_nonneg _)
  have hrho : rhoTwo x t = z * (1 + u) := by
    change s + z = z * (1 + u)
    rw [hsu]
    ring
  have hscaled :
      rhoTwo x t ^ 7 * |heatKernelSpaceFourthDerivative x t i j k l| ≤
        (u ^ 4 / 16 + 3 * u ^ 2 / 4 + 3 / 4) *
          (1 + u) ^ 7 * Real.exp (-a) := by
    rw [hrho]
    calc
      (z * (1 + u)) ^ 7 *
          |heatKernelSpaceFourthDerivative x t i j k l| ≤
          (z * (1 + u)) ^ 7 *
            (heatKernel x t *
              (s ^ 4 / (16 * t ^ 4) + 3 * s ^ 2 / (4 * t ^ 3) +
                3 / (4 * t ^ 2))) := by
        gcongr
        exact heatKernel_fourth_derivative_abs_le ht i j k l
      _ ≤ (z * (1 + u)) ^ 7 *
          ((z ^ (-(3 : ℝ)) * Real.exp (-a)) *
            (s ^ 4 / (16 * t ^ 4) + 3 * s ^ 2 / (4 * t ^ 3) +
              3 / (4 * t ^ 2))) := by
        gcongr
      _ = (u ^ 4 / 16 + 3 * u ^ 2 / 4 + 3 / 4) *
          (1 + u) ^ 7 * Real.exp (-a) := by
        rw [hsu, ← htz, heat_rpow_neg_three z hz]
        field_simp [hz.ne']
  have hu_bound :
      (u ^ 4 / 16 + 3 * u ^ 2 / 4 + 3 / 4) *
          (1 + u) ^ 7 * Real.exp (-a) ≤
            1000000000000000000000000000000 := by
    have hu1 : u ≤ 3 * (1 + a) := by
      nlinarith only [h1u]
    have hpoly :
        (u ^ 4 / 16 + 3 * u ^ 2 / 4 + 3 / 4) *
            (1 + u) ^ 7 * Real.exp (-a) ≤
          ((3 * (1 + a)) ^ 4 / 16 +
            3 * (3 * (1 + a)) ^ 2 / 4 + 3 / 4) *
            (3 * (1 + a)) ^ 7 * Real.exp (-a) := by
      gcongr
    calc
      (u ^ 4 / 16 + 3 * u ^ 2 / 4 + 3 / 4) *
          (1 + u) ^ 7 * Real.exp (-a) ≤
        ((3 * (1 + a)) ^ 4 / 16 +
          3 * (3 * (1 + a)) ^ 2 / 4 + 3 / 4) *
          (3 * (1 + a)) ^ 7 * Real.exp (-a) := hpoly
      _ ≤ 2187000000000000 * ((2 : ℝ) ^ (11 - 1) *
          (1 + (Nat.factorial 11 : ℝ))) := by
        have hA : 1 ≤ 1 + a := by linarith only [ha]
        have hA2 : (1 + a) ^ 2 ≤ (1 + a) ^ 4 :=
          pow_le_pow_right₀ hA (by norm_num)
        have hA4 : 0 ≤ (1 + a) ^ 4 := by positivity
        have hA4one : 1 ≤ (1 + a) ^ 4 := by
          exact one_le_pow₀ hA
        have hcoeff :
            (3 * (1 + a)) ^ 4 / 16 +
              3 * (3 * (1 + a)) ^ 2 / 4 + 3 / 4 ≤
              1000000000000 * (1 + a) ^ 4 := by
          calc
            _ = (81 / 16 : ℝ) * (1 + a) ^ 4 +
                (27 / 4 : ℝ) * (1 + a) ^ 2 + 3 / 4 := by ring
            _ ≤ 1000000000000 * (1 + a) ^ 4 := by
              calc
                _ ≤ (81 / 16 : ℝ) * (1 + a) ^ 4 +
                    (27 / 4 : ℝ) * (1 + a) ^ 4 + 3 / 4 := by
                  gcongr
                _ ≤ 1000000000000 * (1 + a) ^ 4 := by
                  nlinarith only [hA4, hA4one]
        calc
          _ ≤ (1000000000000 * (1 + a) ^ 4) *
              (3 * (1 + a)) ^ 7 * Real.exp (-a) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeff (by positivity))
              (Real.exp_nonneg _)
          _ = 2187000000000000 * (1 + a) ^ 11 * Real.exp (-a) := by ring
          _ ≤ 2187000000000000 * ((2 : ℝ) ^ (11 - 1) *
              (1 + (Nat.factorial 11 : ℝ))) := by
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left
                (one_add_pow_exp_neg_le (n := 11) ha)
                (by norm_num : 0 ≤ (2187000000000000 : ℝ)))
      _ ≤ 1000000000000000000000000000000 := by norm_num
  have hρ : 0 < rhoTwo x t := by
    unfold rhoTwo
    positivity
  apply (le_div_iff₀ (pow_pos hρ 7)).2
  calc
    |heatKernelSpaceFourthDerivative x t i j k l| * rhoTwo x t ^ 7 =
        rhoTwo x t ^ 7 * |heatKernelSpaceFourthDerivative x t i j k l| := by ring
    _ ≤ 1000000000000000000000000000000 := hscaled.trans hu_bound

end CKN.Foundation.Heat
