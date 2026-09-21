/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientSupport
import Mathlib.RingTheory.Ideal.Colon

/-!
# The symbol-ring module on the actual associated graded quotient

The filtered quotient construction already gives the actual degree pieces of
`A / I`, their external direct sum, and an exact global symbol map whose kernel
is `orderInitialIdeal`.  This file uses that exact bridge to put the genuine
`SymbolRing`-module structure on a dedicated copy of the actual associated
graded object.

The construction is not merely additive: the resulting module is linearly
equivalent over `SymbolRing` to its cyclic quotient by `orderInitialIdeal`, and
its annihilator is proved equal (not merely comparable) to that ideal.  No
Rees algebra, radical involutivity, or Gabber theorem is asserted here.
-/

namespace Stafford38.CharacteristicAssociatedGradedModule

open Stafford38.Characteristic
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.CharacteristicFilteredQuotientSupport
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylPBW

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

private abbrev orderDecomposition :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)

/-- The graded algebra structure given by the order weights on symbol variables. -/
local instance orderGradedAlgebraInstance :
    GradedAlgebra (orderDecomposition (n := n) k) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

/-- A dedicated type for the actual external direct sum of the order-filtered
quotient pieces.  The new type keeps the symbol-ring action introduced below
from creating an instance on the underlying `DirectSum` globally. -/
def OrderAssociatedGradedModule
    (I : RightIdeal (PresentedWeyl k n)) :=
  QuotientOrderAssociatedGraded k I

instance (I : RightIdeal (PresentedWeyl k n)) : AddCommGroup
    (OrderAssociatedGradedModule k I) :=
  inferInstanceAs (AddCommGroup (QuotientOrderAssociatedGraded k I))

instance (I : RightIdeal (PresentedWeyl k n)) : Module k
    (OrderAssociatedGradedModule k I) :=
  inferInstanceAs (Module k (QuotientOrderAssociatedGraded k I))

/-- The exact additive identification of the actual associated graded object
with the cyclic symbol quotient. -/
def orderAssociatedGradedAddEquivCharacteristic
    (I : RightIdeal (PresentedWeyl k n)) :
    OrderAssociatedGradedModule k I ≃+
      OrderCharacteristicModule k I :=
  quotientOrderAssociatedGradedAddEquivCharacteristic k I

/-- The change from the quotient by the restricted `k`-submodule to the
ideal quotient is also `k`-linear. -/
def restrictScalarsQuotientLinearEquiv
    (I : RightIdeal (PresentedWeyl k n)) :
    (SymbolRing k n ⧸ (orderInitialIdeal k I).restrictScalars k) ≃ₗ[k]
      OrderCharacteristicModule k I :=
  { restrictScalarsQuotientAddEquiv k I with
    map_smul' := by
      intro c q
      refine Submodule.Quotient.induction_on _ q ?_
      intro P
      rfl }

@[simp]
theorem restrictScalarsQuotientLinearEquiv_mk
    (I : RightIdeal (PresentedWeyl k n)) (P : SymbolRing k n) :
    restrictScalarsQuotientLinearEquiv k I
        (Submodule.Quotient.mk P) =
      Ideal.Quotient.mk (orderInitialIdeal k I) P :=
  rfl

/-- Before adding the full symbol action, the global identification is the
existing `k`-linear equivalence. -/
def orderAssociatedGradedLinearEquivCharacteristicOverBase
    (I : RightIdeal (PresentedWeyl k n)) :
    OrderAssociatedGradedModule k I ≃ₗ[k]
      OrderCharacteristicModule k I :=
  quotientOrderAssociatedGradedEquivCharacteristic k I ≪≫ₗ
    restrictScalarsQuotientLinearEquiv k I

/-- The symbol-ring action transported through the exact global symbol map. -/
noncomputable instance (I : RightIdeal (PresentedWeyl k n)) :
    Module (SymbolRing k n) (OrderAssociatedGradedModule k I) :=
  (orderAssociatedGradedAddEquivCharacteristic k I).module (SymbolRing k n)

/-- The transported symbol action restricts to the original coefficient-field
action on the actual associated graded pieces. -/
noncomputable instance (I : RightIdeal (PresentedWeyl k n)) :
    IsScalarTower k (SymbolRing k n) (OrderAssociatedGradedModule k I) :=
  LinearEquiv.isScalarTower (A := SymbolRing k n)
    (orderAssociatedGradedLinearEquivCharacteristicOverBase k I)

/-- The actual associated graded quotient is a genuine module over the symbol
ring, linearly equivalent over that ring to the cyclic quotient by the order
initial ideal. -/
def orderAssociatedGradedLinearEquivCharacteristic
    (I : RightIdeal (PresentedWeyl k n)) :
    OrderAssociatedGradedModule k I ≃ₗ[SymbolRing k n]
      OrderCharacteristicModule k I :=
  { orderAssociatedGradedAddEquivCharacteristic k I with
    map_smul' := by
      intro P q
      change orderAssociatedGradedAddEquivCharacteristic k I
          ((orderAssociatedGradedAddEquivCharacteristic k I).symm
            (P • orderAssociatedGradedAddEquivCharacteristic k I q)) =
      P • orderAssociatedGradedAddEquivCharacteristic k I q
      exact (orderAssociatedGradedAddEquivCharacteristic k I).apply_symm_apply _ }

/-- Insert one actual order-graded quotient piece into the global direct sum. -/
def orderAssociatedGradedOf
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (q : QuotientOrderGradedPiece k I N) :
    OrderAssociatedGradedModule k I :=
  DirectSum.of (fun N => QuotientOrderGradedPiece k I N) N q

private theorem orderCharacteristicModuleEquivRelationGraded_mk
    (I : RightIdeal (PresentedWeyl k n)) (P : SymbolRing k n) :
    orderCharacteristicModuleEquivRelationGraded k I
        (Submodule.Quotient.mk P) =
      symbolToOrderRelationGraded k I P := by
  rfl

/-- The global characteristic equivalence sends the class of a filtered
representative in degree `N` to the class of its degree-`N` principal symbol.
This is the commuting-square statement that connects the transported module
to the actual filtered quotient pieces. -/
theorem orderAssociatedGradedLinearEquivCharacteristic_of_mk
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ)
    (z : orderPiece k n N) :
    orderAssociatedGradedLinearEquivCharacteristic k I
        (orderAssociatedGradedOf k I N
          (orderPieceToQuotientGraded k I N z)) =
      Ideal.Quotient.mk (orderInitialIdeal k I)
        (presentedPrincipalComponent k orderWeight N z) := by
  change restrictScalarsQuotientLinearEquiv k I
      (quotientOrderAssociatedGradedEquivCharacteristic k I
        (orderAssociatedGradedOf k I N
          (orderPieceToQuotientGraded k I N z))) = _
  have hsource :
      quotientOrderAssociatedGradedEquivCharacteristic k I
          (orderAssociatedGradedOf k I N
            (orderPieceToQuotientGraded k I N z)) =
        Submodule.Quotient.mk
          (presentedPrincipalComponent k orderWeight N z) := by
    have htrans := LinearEquiv.trans_apply
      (e₁₂ := quotientOrderAssociatedGradedEquivSymbols k I)
      (e₂₃ := (orderCharacteristicModuleEquivRelationGraded k I).symm)
      (orderAssociatedGradedOf k I N (orderPieceToQuotientGraded k I N z))
    rw [quotientOrderAssociatedGradedEquivCharacteristic, htrans]
    apply (orderCharacteristicModuleEquivRelationGraded k I).injective
    rw [LinearEquiv.apply_symm_apply]
    apply DFinsupp.ext
    intro M
    rw [orderCharacteristicModuleEquivRelationGraded_mk]
    rw [symbolToOrderRelationGraded_apply]
    change
      ((DFinsupp.mapRange.linearEquiv fun L =>
          quotientOrderGradedPieceEquivSymbols k I L)
        (DirectSum.of (fun L => QuotientOrderGradedPiece k I L) N
          (orderPieceToQuotientGraded k I N z))) M =
        Submodule.Quotient.mk
          ((DirectSum.decompose
            (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n))
            (principalComponentOnPiece k (@orderWeight n) N z :
              SymbolRing k n)) M)
    rw [DFinsupp.mapRange.linearEquiv_apply, DirectSum.decompose_coe]
    change quotientOrderGradedPieceEquivSymbols k I M
        ((DirectSum.of (fun L => QuotientOrderGradedPiece k I L) N
          (orderPieceToQuotientGraded k I N z)) M) =
      Submodule.Quotient.mk
        ((DirectSum.of (fun L =>
          MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) L) N
          (principalComponentOnPiece k (@orderWeight n) N z)) M)
    by_cases hMN : N = M
    · subst M
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same,
        quotientOrderGradedPieceEquivSymbols_mk]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hMN),
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hMN)]
      rw [(quotientOrderGradedPieceEquivSymbols k I M).map_zero]
      exact (Submodule.Quotient.mk_zero _).symm
  calc
    _ = restrictScalarsQuotientLinearEquiv k I
        (Submodule.Quotient.mk
          (presentedPrincipalComponent k orderWeight N z)) :=
      congrArg (restrictScalarsQuotientLinearEquiv k I) hsource
    _ = _ := restrictScalarsQuotientLinearEquiv_mk k I _

private theorem symbol_smul_characteristicModule_mk
    (I : RightIdeal (PresentedWeyl k n)) (P Q : SymbolRing k n) :
    P • Ideal.Quotient.mk (orderInitialIdeal k I) Q =
      Ideal.Quotient.mk (orderInitialIdeal k I) (P * Q) := by
  change P • (Submodule.Quotient.mk Q :
      SymbolRing k n ⧸
        (orderInitialIdeal k I : Submodule (SymbolRing k n) (SymbolRing k n))) =
    Submodule.Quotient.mk (P * Q)
  rw [← Submodule.Quotient.mk_smul
    (orderInitialIdeal k I : Submodule (SymbolRing k n) (SymbolRing k n))
    P Q]
  rfl

/-- Multiplication by a homogeneous symbol on the transported global module
is exactly the canonical degree-shifting action on the actual quotient graded
piece.  The right side is the action constructed from right multiplication in
the filtered Weyl quotient, not a second transported definition. -/
theorem smul_orderAssociatedGradedOf_eq_of_homogeneousAction
    (I : RightIdeal (PresentedWeyl k n)) {N M : ℕ}
    (P : MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) M)
    (q : QuotientOrderGradedPiece k I N) :
    (P : SymbolRing k n) • orderAssociatedGradedOf k I N q =
      orderAssociatedGradedOf k I (N + M)
        (quotientOrderHomogeneousAction k I P q) := by
  obtain ⟨z, rfl⟩ := orderPieceToQuotientGraded_surjective k I N q
  obtain ⟨y, hy⟩ :=
    principalComponentOnPiece_surjective k (@orderWeight n) P
  subst P
  apply (orderAssociatedGradedLinearEquivCharacteristic k I).injective
  rw [map_smul, orderAssociatedGradedLinearEquivCharacteristic_of_mk,
    quotientOrderHomogeneousAction_mk_mul,
    orderAssociatedGradedLinearEquivCharacteristic_of_mk,
    symbol_smul_characteristicModule_mk]
  apply congrArg (Ideal.Quotient.mk (orderInitialIdeal k I))
  rw [presentedPrincipalComponent_mul_order k z.property y.property]
  exact mul_comm _ _

/-- Representative form of homogeneous compatibility: the symbol of `y`
acting on the degree-`N` class of `z` is the degree-`N+M` class represented by
the written-order Weyl product `z * y`. -/
theorem smul_orderAssociatedGradedOf_mk_eq_of_mul
    (I : RightIdeal (PresentedWeyl k n)) {N M : ℕ}
    (z : orderPiece k n N) (y : orderPiece k n M) :
    (principalComponentOnPiece k (@orderWeight n) M y : SymbolRing k n) •
        orderAssociatedGradedOf k I N
          (orderPieceToQuotientGraded k I N z) =
      orderAssociatedGradedOf k I (N + M)
        (orderPieceToQuotientGraded k I (N + M)
          ⟨(z : PresentedWeyl k n) * y,
            mul_mem_orderPiece k z.property y.property⟩) := by
  rw [smul_orderAssociatedGradedOf_eq_of_homogeneousAction,
    quotientOrderHomogeneousAction_mk_mul]

/-- The unit operator belongs to the degree-zero order piece. -/
def orderPieceOne : orderPiece k n 0 :=
  ⟨1, by
    rw [orderPiece, mem_presentedWeightPiece]
    intro m hm
    rw [presentedNormalFormLinearEquiv_one] at hm
    have hm0 : m = 0 := by
      symm
      simpa [MvPolynomial.coeff_one] using hm
    subst m
    simp [monomialWeight]⟩

@[simp]
theorem presentedPrincipalComponent_orderPieceOne :
    presentedPrincipalComponent k (@orderWeight n) 0
        (orderPieceOne (n := n) k) = 1 := by
  change presentedPrincipalComponent k (@orderWeight n) 0
    (1 : PresentedWeyl k n) = 1
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, presentedNormalFormLinearEquiv_one]
  conv_lhs => rw [show (1 : SymbolRing k n) =
    MvPolynomial.monomial 0 1 by simp]
  rw [weightedHomogeneousComponent_monomial]
  simp [monomialWeight]

/-- The literal degree-zero class of the unit operator in the actual filtered
quotient. -/
def orderAssociatedGradedOneClass
    (I : RightIdeal (PresentedWeyl k n)) :
    OrderAssociatedGradedModule k I :=
  orderAssociatedGradedOf k I 0
    (orderPieceToQuotientGraded k I 0 (orderPieceOne (n := n) k))

/-- The distinguished cyclic vector corresponding to the class of `1` in the
symbol quotient. -/
def orderAssociatedGradedGenerator
    (I : RightIdeal (PresentedWeyl k n)) :
    OrderAssociatedGradedModule k I :=
  (orderAssociatedGradedLinearEquivCharacteristic k I).symm 1

@[simp]
theorem orderAssociatedGradedLinearEquivCharacteristic_generator
    (I : RightIdeal (PresentedWeyl k n)) :
    orderAssociatedGradedLinearEquivCharacteristic k I
        (orderAssociatedGradedGenerator k I) = 1 :=
  (orderAssociatedGradedLinearEquivCharacteristic k I).apply_symm_apply 1

/-- The transported cyclic generator is not an abstract chosen preimage: it
is exactly the degree-zero class of the unit filtered representative. -/
theorem orderAssociatedGradedGenerator_eq_oneClass
    (I : RightIdeal (PresentedWeyl k n)) :
    orderAssociatedGradedGenerator k I =
      orderAssociatedGradedOneClass k I := by
  apply (orderAssociatedGradedLinearEquivCharacteristic k I).injective
  rw [orderAssociatedGradedLinearEquivCharacteristic_generator,
    orderAssociatedGradedOneClass,
    orderAssociatedGradedLinearEquivCharacteristic_of_mk,
    presentedPrincipalComponent_orderPieceOne]
  exact (Ideal.Quotient.mk (orderInitialIdeal k I)).map_one

private theorem symbol_smul_one_characteristicModule
    (I : RightIdeal (PresentedWeyl k n)) (P : SymbolRing k n) :
    P • (1 : OrderCharacteristicModule k I) =
      Ideal.Quotient.mk (orderInitialIdeal k I) P := by
  rw [← (Ideal.Quotient.mk (orderInitialIdeal k I)).map_one]
  change P • (Submodule.Quotient.mk (1 : SymbolRing k n) :
      SymbolRing k n ⧸
        (orderInitialIdeal k I : Submodule (SymbolRing k n) (SymbolRing k n))) =
    Submodule.Quotient.mk P
  rw [← Submodule.Quotient.mk_smul
    (orderInitialIdeal k I : Submodule (SymbolRing k n) (SymbolRing k n))
    P (1 : SymbolRing k n)]
  simp

/-- Every element of the actual associated graded quotient is a symbol
multiple of the distinguished generator. -/
theorem exists_smul_orderAssociatedGradedGenerator
    (I : RightIdeal (PresentedWeyl k n))
    (q : OrderAssociatedGradedModule k I) :
    ∃ P : SymbolRing k n, P • orderAssociatedGradedGenerator k I = q := by
  obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective
    (orderAssociatedGradedLinearEquivCharacteristic k I q)
  refine ⟨P, ?_⟩
  apply (orderAssociatedGradedLinearEquivCharacteristic k I).injective
  rw [map_smul, orderAssociatedGradedLinearEquivCharacteristic_generator]
  rw [symbol_smul_one_characteristicModule]
  exact hP

/-- A symbol kills the cyclic generator exactly when it belongs to the order
initial ideal.  This is the elementwise form of the exact annihilator theorem. -/
theorem smul_orderAssociatedGradedGenerator_eq_zero_iff
    (I : RightIdeal (PresentedWeyl k n)) (P : SymbolRing k n) :
    P • orderAssociatedGradedGenerator k I = 0 ↔
      P ∈ orderInitialIdeal k I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    have h' : P • (1 : OrderCharacteristicModule k I) = 0 := by
      simpa only [map_smul,
        orderAssociatedGradedLinearEquivCharacteristic_generator, map_zero]
        using congrArg (orderAssociatedGradedLinearEquivCharacteristic k I) h
    rw [symbol_smul_one_characteristicModule] at h'
    exact h'
  · intro h
    apply (orderAssociatedGradedLinearEquivCharacteristic k I).injective
    rw [map_smul, orderAssociatedGradedLinearEquivCharacteristic_generator,
      map_zero]
    rw [symbol_smul_one_characteristicModule]
    exact h

/-- The annihilator of the actual associated graded quotient is exactly the
order initial ideal. -/
theorem annihilator_orderAssociatedGradedModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module.annihilator (SymbolRing k n) (OrderAssociatedGradedModule k I) =
      orderInitialIdeal k I := by
  rw [(orderAssociatedGradedLinearEquivCharacteristic k I).annihilator_eq]
  exact Ideal.annihilator_quotient


end

end Stafford38.CharacteristicAssociatedGradedModule
