/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.InitialIdealHomogeneous
public import LeanPool.Stafford38.Stafford38.Characteristic.ReducedSupportIdeal


/-!
# Zero-section containment of the reduced order support

The differential-order initial ideal is homogeneous for fibre degree.  At the
level of field-valued points this forces every fibre-conical support fibre to
contain its zero: if `(y, ξ)` is a common zero of the reduced order support
ideal, then `(y, 0)` is a common zero as well.

The proof does not assume conicality of the radical.  For an element of the
radical, it takes a power in the order initial ideal, extracts its fibre-degree
zero component there, and then uses reducedness of the ground field.
-/

@[expose] public section

namespace Stafford38.Characteristic.ZeroSectionContainment

open Stafford38.Characteristic
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicInitialIdealHomogeneous
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

private abbrev orderDecomposition :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)

/-- The symbol grading by momentum degree used to isolate the zero section. -/
local instance orderGradedAlgebraInstance :
    GradedAlgebra (orderDecomposition (n := n) k) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

/-- Evaluation of the fibre-degree-zero component at `(y, ξ)` is evaluation
of the original polynomial at `(y, 0)`. -/
private theorem eval_zeroComponent
    (y ξ : Fin n → k) (P : SymbolRing k n) :
    MvPolynomial.eval (Sum.elim y ξ)
        (DirectSum.decompose (orderDecomposition (n := n) k) P 0 :
          SymbolRing k n) =
      MvPolynomial.eval (zeroSectionPoint y) P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hC : MvPolynomial.C a ∈ orderDecomposition (n := n) k 0 :=
        MvPolynomial.isWeightedHomogeneous_C (@orderWeight n) a
      let C0 : orderDecomposition (n := n) k 0 := ⟨MvPolynomial.C a, hC⟩
      have hd := congrArg (fun z => z 0)
        (DirectSum.decompose_coe (orderDecomposition (n := n) k) C0)
      have hd' : (DirectSum.decompose (orderDecomposition (n := n) k)
          (MvPolynomial.C a) 0 : SymbolRing k n) = MvPolynomial.C a := by
        simpa [C0] using congrArg Subtype.val hd
      rw [hd']
      simp
  | add P Q hP hQ =>
      rw [DirectSum.decompose_add]
      change MvPolynomial.eval (Sum.elim y ξ)
          ((DirectSum.decompose (orderDecomposition (n := n) k) P 0 :
              SymbolRing k n) +
            (DirectSum.decompose (orderDecomposition (n := n) k) Q 0 :
              SymbolRing k n)) = _
      simp only [MvPolynomial.eval_add, hP, hQ]
  | mul_X P i hP =>
      rcases i with i | i
      · have hX : MvPolynomial.X (Sum.inl i : PhaseVar n) ∈
            orderDecomposition (n := n) k 0 := by
          exact MvPolynomial.isWeightedHomogeneous_X k (@orderWeight n)
            (Sum.inl i)
        rw [DirectSum.coe_decompose_mul_of_right_mem_of_le
          (orderDecomposition (n := n) k) hX (Nat.zero_le 0)]
        simp only [ MvPolynomial.eval_mul, hP,
          MvPolynomial.eval_X]
        rfl
      · have hX : MvPolynomial.X (Sum.inr i : PhaseVar n) ∈
            orderDecomposition (n := n) k 1 := by
          exact MvPolynomial.isWeightedHomogeneous_X k (@orderWeight n)
            (Sum.inr i)
        rw [DirectSum.coe_decompose_mul_of_right_mem_of_not_le
          (orderDecomposition (n := n) k) hX (by omega)]
        simp [zeroSectionPoint]

/-- A field-valued common zero of the reduced order support ideal remains a
common zero after its fibre coordinate is set to zero. -/
theorem zeroSection_mem_of_mem_reducedOrderSupport_zeroSet
    (I : RightIdeal (PresentedWeyl k n)) (y ξ : Fin n → k)
    (hpoint : ∀ P ∈ reducedOrderSupportIdeal k I,
      MvPolynomial.eval (Sum.elim y ξ) P = 0) :
    ∀ P ∈ reducedOrderSupportIdeal k I,
      MvPolynomial.eval (zeroSectionPoint y) P = 0 := by
  intro P hP
  obtain ⟨m, hm⟩ := (mem_reducedOrderSupportIdeal_iff k I P).mp hP
  have hcomponent :
      (DirectSum.decompose (orderDecomposition (n := n) k) (P ^ m) 0 :
        SymbolRing k n) ∈ orderInitialIdeal k I :=
    coe_mem_orderInitialIdeal_of_mem_orderSymbolRelation k I 0
      (DirectSum.decompose (orderDecomposition (n := n) k) (P ^ m) 0)
      (decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal
        k I (P ^ m) hm 0)
  have hevalComponent := hpoint _
    (orderInitialIdeal_le_reducedOrderSupportIdeal k I hcomponent)
  rw [eval_zeroComponent k y ξ (P ^ m)] at hevalComponent
  rw [map_pow] at hevalComponent
  exact (pow_eq_zero_iff'.mp hevalComponent).1


end

end Stafford38.Characteristic.ZeroSectionContainment
