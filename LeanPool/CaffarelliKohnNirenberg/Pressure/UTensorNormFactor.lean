/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsBasic

/-!
# UTensor Norm Factor

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open CKN.Foundation.Parabolic

namespace CKN

/-- The Frobenius norm of the velocity tensor `u_i (u_j - c_j)` factors as
`|u| · |u - c|`. -/
theorem pressureUTensorNorm_eq_mul
    (u : ParabolicPoint → Vec3) (c : ℝ → Vec3) (s : ℝ) (y : Vec3) :
    pressureUTensorNorm u c s y = vec3EuclideanNorm (u (y, s)) *
      vec3EuclideanNorm (u (y, s) - c s) := by
  unfold pressureUTensorNorm
  simp only [pressureUTensor]
  unfold vec3EuclideanNorm
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
      (-u (y, s) i * (u (y, s) j - c s j)) ^ (2 : ℕ)) =
      (∑ i : Fin 3, u (y, s) i ^ 2) *
        (∑ j : Fin 3, (u (y, s) - c s) j ^ 2) := by
    have hneg : (∑ i : Fin 3, ∑ j : Fin 3,
        (-u (y, s) i * (u (y, s) j - c s j)) ^ (2 : ℕ)) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          (u (y, s) i * (u (y, s) j - c s j)) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    rw [hneg]
    calc
      (∑ i : Fin 3, ∑ j : Fin 3, (u (y, s) i *
          (u (y, s) j - c s j)) ^ (2 : ℕ)) =
          ∑ i : Fin 3, u (y, s) i ^ 2 *
            (∑ j : Fin 3, (u (y, s) j - c s j) ^ (2 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = (∑ i : Fin 3, u (y, s) i ^ 2) *
            (∑ j : Fin 3, (u (y, s) - c s) j ^ (2 : ℕ)) := by
        rw [Finset.sum_mul]
        rfl
  rw [hsum, Real.sqrt_mul
    (Finset.sum_nonneg (fun i _ => sq_nonneg (u (y, s) i)))]

end CKN
