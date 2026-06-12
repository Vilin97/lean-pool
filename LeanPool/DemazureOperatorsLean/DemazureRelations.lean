/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/

import LeanPool.DemazureOperatorsLean.Demazure
import LeanPool.DemazureOperatorsLean.DemazureAux
import LeanPool.DemazureOperatorsLean.DemazureAuxRelations

/-!
# LeanPool.DemazureOperatorsLean.DemazureRelations
-/

noncomputable section
open MvPolynomial

namespace Demazure

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

/- Now we prove the relations for the actual Demazure operator on polynomials.
There isn't a lot of math going on here, we just take the results from DemAux and
translate them to Demazure-/

-- Demazure operator has order two
lemma demazure_order_two : ∀ (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ),
  DemazureLinear i (DemazureLinear i p) = 0 := by
  intro i p
  apply eq_zero_of_mk'_zero.mp
  dsimp [DemazureLinear]
  rw[← demazure_definitions_equivalent]
  rw[← demazure_definitions_equivalent]
  exact demaux_order_two i (mk' p)

-- Demazure operators with adjacent indices have a braid relation
lemma demazure_commutes_adjacent (i : Fin n) (h : i + 1 < n) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  (DemazureLinear i ∘ DemazureLinear ⟨i+1, h⟩ ∘ DemazureLinear i) p =
    (DemazureLinear ⟨i+1, h⟩ ∘ DemazureLinear i ∘ DemazureLinear ⟨i+1, h⟩) p := by
  intro p
  dsimp [DemazureLinear]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  apply demaux_commutes_adjacent

-- Demazure operators with non-adjacent indices commute
lemma demazure_commutes_non_adjacent (i j : Fin n) (h : NonAdjacent i j) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      (DemazureLinear i ∘ DemazureLinear j) p = (DemazureLinear j ∘ DemazureLinear i) p := by
  intro p
  dsimp [DemazureLinear]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  apply demaux_commutes_non_adjacent
  exact h

-- Relation between demazure operator and multiplication by non-adjacent monomials
lemma demazure_mul_monomial_non_adjacent (i j : Fin n) (h : NonAdjacent i j) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      DemazureLinear i (p * X (Fin.castSucc j)) =
        (DemazureLinear i p) * (X (Fin.castSucc j)) := by
  intro p
  dsimp [DemazureLinear]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  rw[← mk'_mul]
  rw[← mk'_mul]
  rw[← demazure_definitions_equivalent]
  rw[mk'_mul]
  apply demaux_mul_monomial_non_adjacent i j h

-- Relation between demazure operator and multiplication by adjacent monomial
lemma demazure_mul_monomial_adjacent (i : Fin n) (h : i + 1 < n) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      (DemazureLinear i (p * X (Fin.castSucc i))) =
        (DemazureLinear i p) * (X (Fin.succ i)) + p := by
  intro p
  dsimp [DemazureLinear]
  apply eq_of_eq_mk'.mp
  rw[mk'_add]
  rw[← mk'_mul]
  repeat rw[← demazure_definitions_equivalent]
  apply demaux_mul_monomial_adjacent i h

-- Symmetric polynomials act as scalars wrt Demazure operators
lemma demazure_mul_symm (i : Fin n) (g f : MvPolynomial (Fin (n + 1)) ℂ)
    (h : MvPolynomial.IsSymmetric g) :
    DemazureLinear i (g*f) = g*(DemazureLinear i f) := by
  dsimp [DemazureLinear]
  rw[← eq_of_eq_mk']
  rw[← demazure_definitions_equivalent]
  rw [← mk'_mul]
  rw [← mk'_mul]
  rw[← demazure_definitions_equivalent]
  have : IsSymmetric (mk' g) := by
    dsimp [IsSymmetric]
    use (toFrac g)
    dsimp [toFrac]
    exact ⟨rfl, h, MvPolynomial.IsSymmetric.one⟩
  exact demaux_mul_symm i (mk' g) (mk' f) this

/- This enables to define the Demazure operator as a linear map over the ring of
symmetric polynomials, the main result of this project -/
/-- The Demazure operator as a linear map over the symmetric-polynomial subalgebra. -/
def Dem (i : Fin n) : LinearMap (RingHom.id (MvPolynomial.symmetricSubalgebra (Fin (n + 1)) ℂ))
 (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) where
  toFun := DemazureFun i
  map_add' := demazure_map_add i
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply]
    let p : MvPolynomial (Fin (n + 1)) ℂ := r
    have wah : p = r := by rfl
    have h : MvPolynomial.IsSymmetric p := by
      apply (MvPolynomial.mem_symmetricSubalgebra p).mp
      rw[wah]
      exact SetLike.coe_mem r
    exact demazure_mul_symm i p x h

end Demazure

end
