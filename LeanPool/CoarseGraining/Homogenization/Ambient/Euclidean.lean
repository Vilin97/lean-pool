/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.HilbertFinite

/-! # Euclidean -/

namespace Homogenization

/-!
# Explicit Euclidean magnitude on `Vec d`

The project's algebraic carrier `Vec d = Fin d → ℝ` deliberately retains its
default product/sup norm.  This file supplies the Euclidean magnitude and
distance as explicit real-valued functions on that same carrier, without
introducing a competing norm or metric instance.
-/

/-- The Euclidean magnitude of a project vector. -/
noncomputable def euclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

/-- The Euclidean distance between two project vectors. -/
noncomputable def euclideanDist {d : ℕ} (x y : Vec d) : ℝ :=
  euclideanNorm (x - y)

theorem euclideanNorm_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

@[simp] theorem euclideanNorm_sq {d : ℕ} (x : Vec d) :
    euclideanNorm x ^ 2 = vecNormSq x := by
  rw [euclideanNorm, Real.sq_sqrt (vecNormSq_nonneg x)]

@[simp] theorem euclideanNorm_eq_zero_iff {d : ℕ} {x : Vec d} :
    euclideanNorm x = 0 ↔ x = 0 := by
  rw [euclideanNorm, Real.sqrt_eq_zero (vecNormSq_nonneg x), vecNormSq_eq_zero_iff]

@[simp] theorem euclideanNorm_zero {d : ℕ} :
    euclideanNorm (0 : Vec d) = 0 := by
  simp [euclideanNorm, vecNormSq, vecDot]

@[simp] theorem euclideanNorm_neg {d : ℕ} (x : Vec d) :
    euclideanNorm (-x) = euclideanNorm x := by
  unfold euclideanNorm
  congr 1
  unfold vecNormSq vecDot
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp

@[simp] theorem euclideanNorm_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  rw [← sq_eq_sq₀ (euclideanNorm_nonneg _) (mul_nonneg (abs_nonneg _) (euclideanNorm_nonneg _)),
    euclideanNorm_sq, vecNormSq_smul, mul_pow, sq_abs, euclideanNorm_sq]

/-- The explicit Euclidean magnitude agrees with the norm on the separate
Euclidean Hilbert realization of the same vector. -/
theorem euclideanNorm_eq_norm_ofVec {d : ℕ} (x : Vec d) :
    euclideanNorm x = ‖HilbertVec.ofVec x‖ := by
  rw [← sq_eq_sq₀ (euclideanNorm_nonneg _) (norm_nonneg _), euclideanNorm_sq,
    HilbertVec.norm_sq_eq_sum_sq]
  simp [vecNormSq, vecDot, pow_two]

theorem euclideanDist_nonneg {d : ℕ} (x y : Vec d) :
    0 ≤ euclideanDist x y :=
  euclideanNorm_nonneg _

@[simp] theorem euclideanDist_self {d : ℕ} (x : Vec d) :
    euclideanDist x x = 0 := by
  simp [euclideanDist]

@[simp] theorem euclideanDist_eq_zero_iff {d : ℕ} {x y : Vec d} :
    euclideanDist x y = 0 ↔ x = y := by
  rw [euclideanDist, euclideanNorm_eq_zero_iff, sub_eq_zero]

theorem euclideanDist_comm {d : ℕ} (x y : Vec d) :
    euclideanDist x y = euclideanDist y x := by
  unfold euclideanDist
  have hsub : y - x = -(x - y) := by
    ext i
    simp
  rw [hsub, euclideanNorm_neg]

/-- Squaring the explicit Euclidean distance recovers the coordinate square
sum of the displacement. -/
@[simp] theorem euclideanDist_sq {d : ℕ} (x y : Vec d) :
    euclideanDist x y ^ 2 = vecNormSq (x - y) :=
  euclideanNorm_sq (x - y)

/-- Scalar dilations scale explicit Euclidean distance by the scalar's
absolute value. -/
theorem euclideanDist_smul {d : ℕ} (c : ℝ) (x y : Vec d) :
    euclideanDist (c • x) (c • y) = |c| * euclideanDist x y := by
  have hsub : c • x - c • y = c • (x - y) := by
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [euclideanDist, hsub, euclideanNorm_smul]
  rfl

/-- Translating both arguments by the same vector leaves explicit Euclidean
distance unchanged. -/
theorem euclideanDist_add_right {d : ℕ} (x y z : Vec d) :
    euclideanDist (x + z) (y + z) = euclideanDist x y := by
  have hsub : x + z - (y + z) = x - y := by
    ext i
    simp
  rw [euclideanDist, hsub]
  rfl

/-- The explicit Euclidean distance agrees with the Hilbert distance on the
separate Euclidean realization of project vectors. -/
theorem euclideanDist_eq_norm_sub_ofVec {d : ℕ} (x y : Vec d) :
    euclideanDist x y = ‖HilbertVec.ofVec x - HilbertVec.ofVec y‖ := by
  rw [euclideanDist, euclideanNorm_eq_norm_ofVec]
  congr 1

@[simp] theorem euclideanDist_zero_left {d : ℕ} (x : Vec d) :
    euclideanDist 0 x = euclideanNorm x := by
  simp [euclideanDist]

@[simp] theorem euclideanDist_zero_right {d : ℕ} (x : Vec d) :
    euclideanDist x 0 = euclideanNorm x := by
  simp [euclideanDist]

end Homogenization
