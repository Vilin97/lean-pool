/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Erdős 97 convex-octagon formalization: Gram -/

namespace Erdos97Octagon

open scoped InnerProductSpace
open Module Matrix

/-- Three vectors in the Euclidean plane cannot be linearly independent. -/
lemma not_linearIndependent_three (u : Fin 3 → Plane) :
    ¬ LinearIndependent ℝ u := by
  intro h
  have hcard := h.fintype_card_le_finrank
  have hfr : finrank ℝ Plane = 2 := by simp [Plane]
  rw [hfr, Fintype.card_fin] at hcard
  omega

/-- The determinant of the Gram matrix of three planar vectors vanishes. -/
lemma gram_det_eq_zero (u : Fin 3 → Plane) :
    (Matrix.of fun i j => (⟪u i, u j⟫_ℝ : ℝ)).det = 0 := by
  obtain ⟨g, hg, i0, hi0⟩ :=
    (Fintype.not_linearIndependent_iff).1 (not_linearIndependent_three u)
  set G : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun i j => (⟪u i, u j⟫_ℝ : ℝ) with hG
  have hker : G *ᵥ g = 0 := by
    funext i
    rw [Matrix.mulVec, Pi.zero_apply, dotProduct]
    have hrew : (∑ j, G i j * g j) = ⟪u i, ∑ j, g j • u j⟫_ℝ := by
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hG, Matrix.of_apply, real_inner_smul_right]
      ring
    rw [hrew, hg, inner_zero_right]
  have hgne : g ≠ 0 := by
    intro h
    exact hi0 (by rw [h]; rfl)
  exact Matrix.exists_mulVec_eq_zero_iff.1 ⟨g, hgne, hker⟩

/-- Expands a `3 × 3` Gram determinant into scalar inner products. -/
lemma gram3_expand (a b c : Plane) :
    (Matrix.of fun i j => (⟪(![a, b, c]) i, (![a, b, c]) j⟫_ℝ : ℝ)).det =
      ⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ * ⟪c, c⟫_ℝ -
        ⟪a, a⟫_ℝ * ⟪b, c⟫_ℝ * ⟪c, b⟫_ℝ -
        ⟪a, b⟫_ℝ * ⟪b, a⟫_ℝ * ⟪c, c⟫_ℝ +
        ⟪a, b⟫_ℝ * ⟪b, c⟫_ℝ * ⟪c, a⟫_ℝ +
        ⟪a, c⟫_ℝ * ⟪b, a⟫_ℝ * ⟪c, b⟫_ℝ -
        ⟪a, c⟫_ℝ * ⟪b, b⟫_ℝ * ⟪c, a⟫_ℝ := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]

end Erdos97Octagon
