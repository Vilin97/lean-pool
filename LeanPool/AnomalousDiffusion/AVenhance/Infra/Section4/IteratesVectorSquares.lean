/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergy

/-! Quadratic vector algebra for actual material forcing energies. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance

/-- Entrywise matrix control costs four in the actual Euclidean vector square. -/
theorem iterate_matrix_vector_sq_bound (Q : Matrix (Fin 2) (Fin 2) ℝ) (u : Vec 2)
    {D : ℝ} (hQ : ∀ i j, |Q i j| ≤ D) :
    vecNormSq (Q.mulVec u) ≤ 4 * D ^ 2 * vecNormSq u := by
  have ht := iterate_matrix_pairing_abs_bound (by norm_num : (0 : ℝ) < 1 / 2)
    Q (Q.mulVec u) u hQ
  change |vecNormSq (Q.mulVec u)| ≤ _ at ht
  rw [abs_of_nonneg (vecNormSq_nonneg _)] at ht
  rw [show D ^ 2 / (1 / (2 : ℝ)) = 2 * D ^ 2 by ring] at ht
  linarith only [ht]

/-- Subtracting two actual vectors costs at most twice their squared energies. -/
theorem iterate_vecNormSq_sub_le (u v : Vec 2) :
    vecNormSq (u - v) ≤ 2 * (vecNormSq u + vecNormSq v) := by
  simp only [vecNormSq, vecDot, Pi.sub_apply, Fin.sum_univ_two]
  nlinarith only [sq_nonneg (u 0 + v 0), sq_nonneg (u 1 + v 1)]

/-- The three actual terms in a material-gradient equation have a uniform
 quadratic energy allocation. -/
theorem iterate_material_vector_sq_bound (κ : ℝ) (a f e : Vec 2) :
    vecNormSq (κ • a + f - e) ≤
      2 * κ ^ 2 * vecNormSq a + 4 * vecNormSq f + 4 * vecNormSq e := by
  have hc (j : Fin 2) : (κ * a j + f j - e j) ^ 2 ≤
      2 * κ ^ 2 * (a j) ^ 2 + 4 * (f j) ^ 2 + 4 * (e j) ^ 2 := by
    nlinarith only [sq_nonneg (κ * a j - (f j - e j)), sq_nonneg (f j + e j)]
  simp only [vecNormSq, vecDot, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_two]
  nlinarith only [hc 0, hc 1]

end AVenhance.Infra.Section4
