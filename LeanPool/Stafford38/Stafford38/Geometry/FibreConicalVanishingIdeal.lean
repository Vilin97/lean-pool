/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.GeneralConormalContainment

/-!
# Fibre-conical zero sets have homogeneous vanishing ideals
-/

namespace Stafford38.Geometry.FibreConicalVanishingIdeal

open Stafford38.Characteristic
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.GeneralConormalContainment
open Stafford38.WeylFiltration

noncomputable section

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}

/-- Stability under every nonzero scalar dilation in each cotangent fibre. -/
def IsFibreConical (W : Set (PhaseVar n → k)) : Prop :=
  ∀ q ∈ W, ∀ a : k, a ≠ 0 →
    Sum.elim (fun i => q (.inl i)) (fun i => a * q (.inr i)) ∈ W

omit [CharZero k] [IsAlgClosed k] in
/-- The coefficient of fibre degree `d` on a fibre line is evaluation of the
`d`th order-weight homogeneous component. -/
theorem coeff_fibreLinePolynomial_eq_eval_weightedHomogeneousComponent
    (y ξ : Fin n → k) (g : SymbolRing k n) (d : ℕ) :
    (fibreLinePolynomial y ξ g).coeff d =
      MvPolynomial.eval (Sum.elim y ξ)
        (DirectSum.decompose (orderDecomposition (k := k) (n := n)) g d :
          SymbolRing k n) := by
  induction g using MvPolynomial.induction_on generalizing d with
  | C c =>
      have hC : MvPolynomial.C c ∈ orderDecomposition (k := k) (n := n) 0 :=
        MvPolynomial.isWeightedHomogeneous_C (@orderWeight n) c
      cases d with
      | zero =>
          rw [DirectSum.decompose_of_mem_same
            (orderDecomposition (k := k) (n := n)) hC]
          simp
      | succ d =>
          rw [DirectSum.decompose_of_mem_ne
            (orderDecomposition (k := k) (n := n)) hC (Nat.succ_ne_zero d).symm]
          simp
  | add P Q hP hQ =>
      rw [fibreLinePolynomial_add, Polynomial.coeff_add,
        DirectSum.decompose_add]
      change _ = MvPolynomial.eval (Sum.elim y ξ)
        ((DirectSum.decompose (orderDecomposition (k := k) (n := n)) P d :
          SymbolRing k n) +
         (DirectSum.decompose (orderDecomposition (k := k) (n := n)) Q d :
          SymbolRing k n))
      rw [MvPolynomial.eval_add, hP, hQ]
  | mul_X P i hP =>
      rcases i with i | i
      · have hX : MvPolynomial.X (Sum.inl i : PhaseVar n) ∈
            orderDecomposition (k := k) (n := n) 0 :=
          MvPolynomial.isWeightedHomogeneous_X k (@orderWeight n) _
        rw [DirectSum.coe_decompose_mul_of_right_mem_of_le
          (orderDecomposition (k := k) (n := n)) hX (Nat.zero_le d)]
        simp [fibreLinePolynomial_mul, hP]
      · have hX : MvPolynomial.X (Sum.inr i : PhaseVar n) ∈
            orderDecomposition (k := k) (n := n) 1 :=
          MvPolynomial.isWeightedHomogeneous_X k (@orderWeight n) _
        cases d with
        | zero =>
            rw [DirectSum.coe_decompose_mul_of_right_mem_of_not_le
              (orderDecomposition (k := k) (n := n)) hX (by omega)]
            simp [fibreLinePolynomial_mul]
        | succ d =>
            rw [DirectSum.coe_decompose_mul_of_right_mem_of_le
              (orderDecomposition (k := k) (n := n)) hX (by omega)]
            rw [fibreLinePolynomial_mul, fibreLinePolynomial_X_fibre, ← mul_assoc,
              Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]
            simp [hP]

omit [CharZero k] in
/-- Fibre-conicality makes the vanishing ideal homogeneous for fibre degree. -/
theorem vanishingIdeal_isHomogeneous_of_isFibreConical
    (W : Set (PhaseVar n → k)) (hW : IsFibreConical W) :
    (MvPolynomial.vanishingIdeal k W).IsHomogeneous
      (orderDecomposition (k := k) (n := n)) := by
  intro d g hg
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hg ⊢
  intro q hq
  let y : Fin n → k := fun i => q (.inl i)
  let ξ : Fin n → k := fun i => q (.inr i)
  have hline : fibreLinePolynomial y ξ g = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.infinite_univ.sdiff (Set.finite_singleton 0))
    intro a ha
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] at ha
    change Polynomial.eval a (fibreLinePolynomial y ξ g) = 0
    rw [eval_fibreLinePolynomial]
    exact hg _ (hW q hq a ha)
  have hqeq : q = Sum.elim y ξ := by
    funext i
    cases i <;> rfl
  rw [hqeq]
  change MvPolynomial.eval (Sum.elim y ξ)
      (DirectSum.decompose (orderDecomposition (k := k) (n := n)) g d :
        SymbolRing k n) = 0
  rw [← coeff_fibreLinePolynomial_eq_eval_weightedHomogeneousComponent y ξ g d,
    hline, Polynomial.coeff_zero]

end
end Stafford38.Geometry.FibreConicalVanishingIdeal
