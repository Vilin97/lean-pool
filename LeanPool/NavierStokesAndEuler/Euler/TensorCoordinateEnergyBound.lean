/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpFiniteTensorReconstruction
import Mathlib.Algebra.Order.Star.Real

/-!
# Bounding a tensor by the energies of its coordinate evaluations

The reconstruction map is fixed in each derivative order.  Its operator norm
therefore gives a finite constant converting the sum of the scalar coordinate
energies into a bound for the literal tensor norm.
-/

@[expose] public section


noncomputable section

namespace EulerComparatorRecovery

open EulerSmoothLimit EulerLpFiniteTensor

/-- The product norm of finitely many Euclidean vectors is bounded by their
combined scalar coordinate energy. -/
theorem tuple_norm_sq_le_coordinate_energy {ι : Type*} [Fintype ι]
    (v : ι → Space) :
    ‖v‖ ^ 2 ≤ ∑ i : ι, ∑ j : Fin 3, (v i j) ^ 2 := by
  classical
  let S : ℝ := ∑ i : ι, ∑ j : Fin 3, (v i j) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm : ‖v‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) hS).mpr
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg (v k j))
      (Finset.mem_univ i)
  calc
    ‖v‖ ^ 2 ≤ (Real.sqrt S) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg S)).mpr hnorm
    _ = S := Real.sq_sqrt hS

/-- A tensor's squared operator norm is bounded by the sum of the squared
scalar coordinate evaluations, with a constant depending only on its order. -/
theorem tensor_norm_sq_le_coordinate_energy (n : ℕ)
    (A : Space [×n]→L[ℝ] Space) :
    ‖A‖ ^ 2 ≤ ‖tensorReassembly (V := Space) n‖ ^ 2 *
      ∑ w : Fin n → Fin 3, ∑ j : Fin 3,
        (A (fun i => direction (w i)) j) ^ 2 := by
  have hnorm : ‖A‖ ≤ ‖tensorReassembly (V := Space) n‖ *
      ‖tensorCoordinates n A‖ := by
    simpa only [tensorReassembly_coordinates] using
      (tensorReassembly (V := Space) n).le_opNorm (tensorCoordinates n A)
  have hsq : ‖A‖ ^ 2 ≤ ‖tensorReassembly (V := Space) n‖ ^ 2 *
      ‖tensorCoordinates n A‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg A)
        (mul_nonneg (norm_nonneg (tensorReassembly (V := Space) n))
          (norm_nonneg (tensorCoordinates n A)))).mpr hnorm
  exact hsq.trans (mul_le_mul_of_nonneg_left
    (tuple_norm_sq_le_coordinate_energy (tensorCoordinates n A)) (sq_nonneg _))

end EulerComparatorRecovery
