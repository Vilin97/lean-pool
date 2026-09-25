/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Vec3 Norm

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

noncomputable section

namespace CKN.Foundation.Parabolic

/-- The Euclidean norm on `Vec3` satisfies the triangle inequality. -/
theorem vec3EuclideanNorm_add_le (v w : Vec3) :
    vec3EuclideanNorm (v + w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

/-- The Euclidean norm on `Vec3` is invariant under negation. -/
theorem vec3EuclideanNorm_neg (v : Vec3) :
    vec3EuclideanNorm (-v) = vec3EuclideanNorm v := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_neg, norm_neg]

/-- The Euclidean norm on `Vec3` satisfies the reverse triangle inequality. -/
theorem vec3EuclideanNorm_sub_le (v w : Vec3) :
    vec3EuclideanNorm (v - w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  calc
    vec3EuclideanNorm (v - w) = vec3EuclideanNorm (v + (-w)) := by rw [sub_eq_add_neg]
    _ ≤ vec3EuclideanNorm v + vec3EuclideanNorm (-w) := vec3EuclideanNorm_add_le v (-w)
    _ = vec3EuclideanNorm v + vec3EuclideanNorm w := by rw [vec3EuclideanNorm_neg]

/-- Each component of a vector in `Vec3` is bounded in absolute value by the Euclidean norm. -/
theorem abs_apply_le_vec3EuclideanNorm (v : Vec3) (i : Fin 3) :
    |v i| ≤ vec3EuclideanNorm v := by
  unfold vec3EuclideanNorm
  have h := Finset.single_le_sum (fun j _hj => sq_nonneg (v j)) (Finset.mem_univ i)
  have hsq : (v i) ^ 2 ≤ ∑ j : Fin 3, (v j) ^ 2 := by
    simpa [sq_abs] using h
  exact Real.abs_le_sqrt hsq

/-- The sup norm on `Vec3` (the default `‖·‖` for `Fin 3 → ℝ`) is bounded by the Euclidean norm. -/
theorem norm_le_vec3EuclideanNorm (v : Vec3) :
    ‖v‖ ≤ vec3EuclideanNorm v := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖v i‖₊) ≤
      ⟨vec3EuclideanNorm v, vec3EuclideanNorm_nonneg v⟩ := by
    apply Finset.sup_le
    intro i hi
    have hi' : |v i| ≤ vec3EuclideanNorm v := abs_apply_le_vec3EuclideanNorm v i
    exact_mod_cast hi'
  exact_mod_cast hnn

/-- The Euclidean norm on `Vec3` is bounded by `√3` times the sup norm. -/
theorem vec3EuclideanNorm_le_sqrt_three_mul_norm (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    rw [vec3EuclideanNorm, Real.sq_sqrt
      (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))),
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      (∑ i : Fin 3, v i ^ 2) ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        have h := norm_le_pi_norm v i
        exact (sq_le_sq₀ (abs_nonneg (v i)) (norm_nonneg v)).2 h
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := by
    rwa [sq_le_sq] at hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2

/-- The Euclidean norm on `Vec3` is bounded by the sum of absolute values of its components. -/
theorem vec3EuclideanNorm_le_sum_abs (v : Vec3) :
    vec3EuclideanNorm v ≤ ∑ i : Fin 3, |v i| := by
  unfold vec3EuclideanNorm
  have hsum : (∑ i : Fin 3, (v i) ^ 2) ≤ (∑ i : Fin 3, |v i|) ^ 2 := by
    calc
      (∑ i : Fin 3, (v i) ^ 2) = ∑ i : Fin 3, |v i| ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [sq_abs]
      _ ≤ (∑ i : Fin 3, |v i|) ^ 2 := by
        simp_rw [Fin.sum_univ_three]
        have h0 : 0 ≤ |v 0| := abs_nonneg _
        have h1 : 0 ≤ |v 1| := abs_nonneg _
        have h2 : 0 ≤ |v 2| := abs_nonneg _
        nlinarith only [h0, h1, h2]
  let S := ∑ i : Fin 3, |v i|
  have hS : 0 ≤ S := Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (v i))
  calc
    Real.sqrt (∑ i : Fin 3, (v i) ^ 2) ≤ Real.sqrt (S ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = |S| := by rw [Real.sqrt_sq_eq_abs]
    _ = S := abs_of_nonneg hS
    _ = ∑ i : Fin 3, |v i| := rfl

/-- The Euclidean norm on `Vec3` is continuous with respect to the product topology. -/
theorem continuous_vec3EuclideanNorm :
    Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
  change Continuous (fun z : Vec3 => Real.sqrt (∑ i : Fin 3, (z i) ^ 2))
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i hi
  exact ((continuous_apply i).pow 2)

end CKN.Foundation.Parabolic
