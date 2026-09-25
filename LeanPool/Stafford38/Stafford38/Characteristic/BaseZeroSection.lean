/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Algebra.MvPolynomial.Monad
public import LeanPool.Stafford38.Stafford38.Characteristic.ZeroSectionContainment


/-!
# Zero-section containment over the contracted base zero locus

The fibre-degree-zero component of a phase-space polynomial is its
specialization at zero fibre coordinates, lifted back from the base ring.
Consequently a common zero of the contracted reduced order-support ideal
already determines a zero-section point of the full reduced support; no
chosen point in the original support fibre is needed.
-/

@[expose] public section

namespace Stafford38.Characteristic.BaseZeroSection

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

/-- The decomposition of the symbol ring by homogeneous momentum order. -/
abbrev orderDecomposition :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)

/-- The graded algebra structure on symbols induced by the order weights. -/
local instance orderGradedAlgebraInstance :
    GradedAlgebra (orderDecomposition (n := n) k) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

/-- Set all fibre variables to zero and retain the base variables. -/
def fibreZeroSpecialization :
    SymbolRing k n →ₐ[k] MvPolynomial (Fin n) k :=
  MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 0))

@[simp]
theorem fibreZeroSpecialization_X_base (i : Fin n) :
    fibreZeroSpecialization k (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X i := by
  simp [fibreZeroSpecialization]

@[simp]
theorem fibreZeroSpecialization_X_fibre (i : Fin n) :
    fibreZeroSpecialization k (MvPolynomial.X (Sum.inr i)) = 0 := by
  simp [fibreZeroSpecialization]

/-- Evaluating after zero-fibre specialization is evaluation at the
corresponding zero-section point. -/
theorem eval_fibreZeroSpecialization
    (y : Fin n → k) (P : SymbolRing k n) :
    MvPolynomial.eval y (fibreZeroSpecialization k P) =
      MvPolynomial.eval (zeroSectionPoint y) P := by
  change MvPolynomial.aeval y
      (MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 0)) P) = _
  rw [MvPolynomial.aeval_bind₁]
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  rcases i with i | i <;> simp [zeroSectionPoint]

/-- A base polynomial lifted to phase space evaluates independently of the
fibre coordinate. -/
theorem eval_baseLift
    (y ξ : Fin n → k) (f : MvPolynomial (Fin n) k) :
    MvPolynomial.eval (Sum.elim y ξ) (baseLift f) =
      MvPolynomial.eval y f := by
  change MvPolynomial.aeval (Sum.elim y ξ)
      (MvPolynomial.rename Sum.inl f) = _
  rw [MvPolynomial.aeval_rename]
  rfl

/-- The order-degree-zero component is exactly zero-fibre specialization,
viewed again in the phase-space polynomial ring. -/
theorem zeroComponent_eq_baseLift_fibreZeroSpecialization
    (P : SymbolRing k n) :
    (DirectSum.decompose (orderDecomposition (n := n) k) P 0 :
        SymbolRing k n) =
      baseLift (fibreZeroSpecialization k P) := by
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
      simp [fibreZeroSpecialization, baseLift]
  | add P Q hP hQ =>
      rw [DirectSum.decompose_add]
      change
        (DirectSum.decompose (orderDecomposition (n := n) k) P 0 :
            SymbolRing k n) +
          (DirectSum.decompose (orderDecomposition (n := n) k) Q 0 :
            SymbolRing k n) = _
      simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      rcases i with i | i
      · have hX : MvPolynomial.X (Sum.inl i : PhaseVar n) ∈
            orderDecomposition (n := n) k 0 :=
          MvPolynomial.isWeightedHomogeneous_X k (@orderWeight n) (Sum.inl i)
        rw [DirectSum.coe_decompose_mul_of_right_mem_of_le
          (orderDecomposition (n := n) k) hX (Nat.zero_le 0)]
        simp only [ map_mul, hP, fibreZeroSpecialization_X_base]
        simp [baseLift]
      · have hX : MvPolynomial.X (Sum.inr i : PhaseVar n) ∈
            orderDecomposition (n := n) k 1 :=
          MvPolynomial.isWeightedHomogeneous_X k (@orderWeight n) (Sum.inr i)
        rw [DirectSum.coe_decompose_mul_of_right_mem_of_not_le
          (orderDecomposition (n := n) k) hX (by omega)]
        simp

/-- Every base point of the contracted reduced order-support zero locus lifts
canonically to a zero-section point of the full reduced support. -/
theorem zeroSection_mem_of_mem_reducedOrderBaseZeroSet
    (I : RightIdeal (PresentedWeyl k n)) (y : Fin n → k)
    (hy : ∀ f ∈ reducedOrderBaseIdeal k I,
      MvPolynomial.eval y f = 0) :
    ∀ P ∈ reducedOrderSupportIdeal k I,
      MvPolynomial.eval (zeroSectionPoint y) P = 0 := by
  intro P hP
  obtain ⟨m, hm⟩ := (mem_reducedOrderSupportIdeal_iff k I P).mp hP
  let f := fibreZeroSpecialization k (P ^ m)
  have hcomponent :
      (DirectSum.decompose (orderDecomposition (n := n) k) (P ^ m) 0 :
        SymbolRing k n) ∈ orderInitialIdeal k I :=
    coe_mem_orderInitialIdeal_of_mem_orderSymbolRelation k I 0
      (DirectSum.decompose (orderDecomposition (n := n) k) (P ^ m) 0)
      (decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal
        k I (P ^ m) hm 0)
  have hbaseLift : baseLift f ∈ reducedOrderSupportIdeal k I := by
    rw [← zeroComponent_eq_baseLift_fibreZeroSpecialization]
    exact orderInitialIdeal_le_reducedOrderSupportIdeal k I hcomponent
  have hfy : MvPolynomial.eval y f = 0 :=
    hy f ((mem_reducedOrderBaseIdeal_iff k I f).mpr hbaseLift)
  have heval :
      MvPolynomial.eval (zeroSectionPoint y) (P ^ m) = 0 := by
    rw [← eval_fibreZeroSpecialization k y (P ^ m)]
    exact hfy
  rw [map_pow] at heval
  exact (pow_eq_zero_iff'.mp heval).1

/-- Field-valued projection is exact: a base point annihilates the contracted
ideal if and only if some fibre point over it annihilates the full reduced
support ideal. The forward witness is canonically the zero fibre. -/
theorem mem_reducedOrderBaseZeroSet_iff_exists_supportFibre
    (I : RightIdeal (PresentedWeyl k n)) (y : Fin n → k) :
    (∀ f ∈ reducedOrderBaseIdeal k I, MvPolynomial.eval y f = 0) ↔
      ∃ ξ : Fin n → k,
        ∀ P ∈ reducedOrderSupportIdeal k I,
          MvPolynomial.eval (Sum.elim y ξ) P = 0 := by
  constructor
  · intro hy
    refine ⟨0, ?_⟩
    have hpoint : Sum.elim y (0 : Fin n → k) = zeroSectionPoint y := by
      funext i
      rcases i with i | i <;> rfl
    rw [hpoint]
    exact zeroSection_mem_of_mem_reducedOrderBaseZeroSet k I y hy
  · rintro ⟨ξ, hξ⟩ f hf
    have hLift := hξ (baseLift f)
      ((mem_reducedOrderBaseIdeal_iff k I f).mp hf)
    rw [eval_baseLift k y ξ f] at hLift
    exact hLift


end

end Stafford38.Characteristic.BaseZeroSection
