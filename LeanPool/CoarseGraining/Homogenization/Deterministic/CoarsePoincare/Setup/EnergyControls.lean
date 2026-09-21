/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup.UniformBounds

/-! # Energy Controls -/

namespace Homogenization

noncomputable section

open scoped BigOperators

theorem abs_vecDot_matVecMul_le_matNorm_mul_vecNormSq {d : ℕ} (A : Mat d) (x : Vec d) :
    |vecDot x (matVecMul A x)| ≤ matNorm A * vecNormSq x := by
  have hsum :
      vecDot x (matVecMul A x) =
        ∑ z ∈ Finset.univ ×ˢ Finset.univ, A z.1 z.2 * (x z.1 * x z.2) := by
    unfold vecDot matVecMul
    calc
      ∑ i, x i * ∑ j, A i j * x j = ∑ i, ∑ j, x i * (A i j * x j) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, A i j * (x i * x j) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = ∑ z ∈ Finset.univ ×ˢ Finset.univ, A z.1 z.2 * (x z.1 * x z.2) := by
        rw [← Finset.sum_product']
  have hcs :
      (∑ z ∈ Finset.univ ×ˢ Finset.univ, A z.1 z.2 * (x z.1 * x z.2)) ^ 2 ≤
        (∑ z ∈ Finset.univ ×ˢ Finset.univ, (A z.1 z.2) ^ 2) *
          (∑ z ∈ Finset.univ ×ˢ Finset.univ, (x z.1 * x z.2) ^ 2) := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (s := Finset.univ ×ˢ Finset.univ)
        (f := fun z : Fin d × Fin d => A z.1 z.2)
        (g := fun z : Fin d × Fin d => x z.1 * x z.2))
  have hA_sq :
      (∑ z ∈ Finset.univ ×ˢ Finset.univ, (A z.1 z.2) ^ 2) = matNormSq A := by
    unfold matNormSq
    rw [← Finset.sum_product']
  have hx_sq :
      (∑ z ∈ Finset.univ ×ˢ Finset.univ, (x z.1 * x z.2) ^ 2) =
        (vecNormSq x) ^ 2 := by
    calc
      ∑ z ∈ Finset.univ ×ˢ Finset.univ, (x z.1 * x z.2) ^ 2
          = ∑ i, ∑ j, (x i * x j) ^ 2 := by
              symm
              exact (Finset.sum_product' Finset.univ Finset.univ
                (fun i j => (x i * x j) ^ 2)).symm
      _ = ∑ i, x i ^ 2 * ∑ j, x j ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              ∑ j, (x i * x j) ^ 2 = ∑ j, x i ^ 2 * x j ^ 2 := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                ring
              _ = x i ^ 2 * ∑ j, x j ^ 2 := by
                rw [Finset.mul_sum]
      _ = (∑ i, x i ^ 2) * (∑ j, x j ^ 2) := by
            simpa using (Finset.sum_mul Finset.univ (fun i => x i ^ 2) (∑ j, x j ^ 2)).symm
      _ = (vecNormSq x) ^ 2 := by
            simp [vecNormSq, vecDot, pow_two]
  have hsq :
      (vecDot x (matVecMul A x)) ^ 2 ≤ matNormSq A * (vecNormSq x) ^ 2 := by
    rw [hsum]
    rw [hA_sq, hx_sq] at hcs
    exact hcs
  have hrhs_nonneg : 0 ≤ matNorm A * vecNormSq x := by
    exact mul_nonneg (matNorm_nonneg A) (vecNormSq_nonneg x)
  have hsq_abs :
      |vecDot x (matVecMul A x)| ^ 2 ≤ (matNorm A * vecNormSq x) ^ 2 := by
    have hmul_sq :
        (matNorm A * vecNormSq x) ^ 2 = matNormSq A * (vecNormSq x) ^ 2 := by
      calc
        (matNorm A * vecNormSq x) ^ 2 = (matNorm A) ^ 2 * (vecNormSq x) ^ 2 := by
          ring
        _ = matNormSq A * (vecNormSq x) ^ 2 := by
          unfold matNorm
          rw [Real.sq_sqrt (matNormSq_nonneg A)]
    calc
      |vecDot x (matVecMul A x)| ^ 2 = (vecDot x (matVecMul A x)) ^ 2 := by
        rw [sq_abs]
      _ ≤ matNormSq A * (vecNormSq x) ^ 2 := hsq
      _ = (matNorm A * vecNormSq x) ^ 2 := by
        exact hmul_sq.symm
  simpa [abs_of_nonneg hrhs_nonneg] using (sq_le_sq.mp hsq_abs)

theorem vecDot_matVecMul_le_matNorm_mul_vecNormSq_of_posSemidef {d : ℕ} {A : Mat d}
    (hA : A.PosSemidef) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ matNorm A * vecNormSq x := by
  have hnonneg : 0 ≤ vecDot x (matVecMul A x) := by
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hA.dotProduct_mulVec_nonneg x
  simpa [abs_of_nonneg hnonneg] using abs_vecDot_matVecMul_le_matNorm_mul_vecNormSq A x

theorem vecNormSq_le_matNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse {d : ℕ}
    {A B : Mat d} (hB : B.PosSemidef)
    (hleftInv : ∀ ξ : Vec d, matVecMul B (matVecMul A ξ) = ξ) (ξ : Vec d) :
    vecNormSq ξ ≤ matNorm B * vecDot ξ (matVecMul A ξ) := by
  let η : Vec d := matVecMul A ξ
  have hBsymm : B.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hB.1
  have hBnonneg : ∀ z : Vec d, 0 ≤ vecDot z (matVecMul B z) := by
    intro z
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hB.dotProduct_mulVec_nonneg z
  have hηeq : matVecMul B η = ξ := by
    simpa [η] using hleftInv ξ
  have hξη_nonneg : 0 ≤ vecDot ξ η := by
    have := hBnonneg η
    simpa [hηeq, vecDot_comm, η] using this
  have hcs :
      vecNormSq ξ ^ 2 ≤ vecDot ξ (matVecMul B ξ) * vecDot ξ η := by
    have hraw := sq_vecDot_matVecMul_le_of_isSymm_of_nonneg hBsymm hBnonneg ξ η
    simpa [vecNormSq, hηeq, vecDot_comm, η] using hraw
  have hfirst :
      vecDot ξ (matVecMul B ξ) ≤ matNorm B * vecNormSq ξ :=
    vecDot_matVecMul_le_matNorm_mul_vecNormSq_of_posSemidef hB ξ
  have hmain :
      vecNormSq ξ ^ 2 ≤ (matNorm B * vecNormSq ξ) * vecDot ξ η := by
    exact le_trans hcs <| mul_le_mul_of_nonneg_right hfirst hξη_nonneg
  by_cases hx : vecNormSq ξ = 0
  · rw [hx]
    nlinarith [matNorm_nonneg B]
  · have hx_pos : 0 < vecNormSq ξ := by
      exact lt_of_le_of_ne (vecNormSq_nonneg ξ) (by simpa [eq_comm] using hx)
    have hnorm_nonneg : 0 ≤ matNorm B := matNorm_nonneg B
    nlinarith


end

end Homogenization
