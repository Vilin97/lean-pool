/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.InitialIdealHomogeneous


/-!
# Global support of the filtered right-ideal quotient

The exact homogeneous relation theorem identifies, as an additive group and
as a vector space over the coefficient field, the external direct sum of the
actual filtered quotient pieces with the quotient of the symbol ring by the
order initial ideal.

The further transport of the full symbol-ring module structure, and hence the
support equality, is not proved in this file.  No conclusion about vanishing
of the ungraded Weyl quotient is made here.
-/

@[expose] public section

namespace Stafford38.CharacteristicFilteredQuotientSupport

open Stafford38.Characteristic
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicInitialIdealHomogeneous
open Stafford38.EulerSurjectivity
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

private abbrev orderDecomposition :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)

/-- The weighted graded-algebra structure used for support of the filtered quotient. -/
local instance orderGradedAlgebraInstance :
    GradedAlgebra (orderDecomposition (n := n) k) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

/-- Decompose a symbol into homogeneous pieces and reduce each piece by the
exact relation submodule of the filtered quotient. -/
def symbolToOrderRelationGraded
    (I : RightIdeal (PresentedWeyl k n)) :
    SymbolRing k n →ₗ[k] OrderSymbolRelationGraded k I :=
  (DFinsupp.mapRange.linearMap fun N =>
      (orderSymbolRelation k I N).mkQ).comp
    (DirectSum.decomposeLinearEquiv (orderDecomposition (n := n) k)).toLinearMap

@[simp]
theorem symbolToOrderRelationGraded_apply
    (I : RightIdeal (PresentedWeyl k n)) (P : SymbolRing k n) (N : ℕ) :
    symbolToOrderRelationGraded k I P N =
      Submodule.Quotient.mk
        (DirectSum.decompose (orderDecomposition (n := n) k) P N) := by
  rfl

/-- The global symbol map is onto: choose a representative in each nonzero
homogeneous quotient component and reassemble the resulting finite family. -/
theorem symbolToOrderRelationGraded_surjective
    (I : RightIdeal (PresentedWeyl k n)) :
    Function.Surjective (symbolToOrderRelationGraded k I) := by
  classical
  intro q
  let lift : ∀ N,
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N ⧸
        orderSymbolRelation k I N) →
      MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N :=
    fun N qN => if hq : qN = 0 then 0 else Classical.choose
      (Submodule.Quotient.mk_surjective (orderSymbolRelation k I N) qN)
  have hlift : ∀ N qN, Submodule.Quotient.mk (lift N qN) = qN := by
    intro N qN
    by_cases hq : qN = 0
    · simp [lift, hq]
    · simpa [lift, hq] using Classical.choose_spec
        (Submodule.Quotient.mk_surjective (orderSymbolRelation k I N) qN)
  let q' : DirectSum ℕ (fun N =>
      MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n) N) :=
    DFinsupp.mapRange lift (fun N => by simp [lift]) q
  refine ⟨(DirectSum.decomposeLinearEquiv
    (orderDecomposition (n := n) k)).symm q', ?_⟩
  apply DFinsupp.ext
  intro N
  rw [symbolToOrderRelationGraded_apply]
  have hd := (DirectSum.decomposeAddEquiv
    (orderDecomposition (n := n) k)).apply_symm_apply q'
  rw [show DirectSum.decompose (orderDecomposition (n := n) k)
      ((DirectSum.decomposeLinearEquiv
        (orderDecomposition (n := n) k)).symm q') N = q' N from
    congrArg (fun z => z N) hd]
  change Submodule.Quotient.mk (q' N) = q N
  exact hlift N (q N)

/-- The kernel of the global symbol map is exactly the order initial ideal,
viewed as a `k`-submodule. -/
theorem ker_symbolToOrderRelationGraded
    (I : RightIdeal (PresentedWeyl k n)) :
    LinearMap.ker (symbolToOrderRelationGraded k I) =
      (orderInitialIdeal k I).restrictScalars k := by
  ext P
  constructor
  · intro hP
    rw [LinearMap.mem_ker] at hP
    have hcomponent : ∀ N,
        DirectSum.decompose (orderDecomposition (n := n) k) P N ∈
          orderSymbolRelation k I N := by
      intro N
      rw [← Submodule.Quotient.mk_eq_zero]
      exact congrArg (fun q => q N) hP
    change P ∈ orderInitialIdeal k I
    classical
    rw [← DirectSum.sum_support_decompose (orderDecomposition (n := n) k) P]
    apply Ideal.sum_mem
    intro N hN
    exact (mem_orderSymbolRelation_iff_coe_mem_orderInitialIdeal k I N _).mp
      (hcomponent N)
  · intro hP
    rw [LinearMap.mem_ker]
    apply DFinsupp.ext
    intro N
    change Submodule.Quotient.mk
      (DirectSum.decompose (orderDecomposition (n := n) k) P N) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal
      k I P hP N

/-- The cyclic order-characteristic module is linearly equivalent over the
coefficient field to the direct sum of the exact homogeneous quotients. -/
def orderCharacteristicModuleEquivRelationGraded
    (I : RightIdeal (PresentedWeyl k n)) :
    (SymbolRing k n ⧸ (orderInitialIdeal k I).restrictScalars k) ≃ₗ[k]
      OrderSymbolRelationGraded k I :=
  Submodule.quotEquivOfEq _ _ (ker_symbolToOrderRelationGraded k I).symm ≪≫ₗ
    (symbolToOrderRelationGraded k I).quotKerEquivOfSurjective
      (symbolToOrderRelationGraded_surjective k I)

/-- The actual associated graded object is globally equivalent, as a
`k`-vector space, to the cyclic symbol quotient.  Its restriction to each
degree is the previously proved filtered-quotient equivalence. -/
def quotientOrderAssociatedGradedEquivCharacteristic
    (I : RightIdeal (PresentedWeyl k n)) :
    QuotientOrderAssociatedGraded k I ≃ₗ[k]
      (SymbolRing k n ⧸ (orderInitialIdeal k I).restrictScalars k) :=
  quotientOrderAssociatedGradedEquivSymbols k I ≪≫ₗ
    (orderCharacteristicModuleEquivRelationGraded k I).symm

/-- Restricting the scalar ring of an ideal does not change the underlying
additive quotient. -/
def restrictScalarsQuotientAddEquiv
    (I : RightIdeal (PresentedWeyl k n)) :
    (SymbolRing k n ⧸ (orderInitialIdeal k I).restrictScalars k) ≃+
      OrderCharacteristicModule k I where
  toEquiv := Quotient.congr (Equiv.refl _) (by
    intro P Q
    rfl)
  map_add' q r := by
    refine Quotient.inductionOn₂ q r ?_
    intro P Q
    rfl

/-- Additive global equivalence from the actual associated graded pieces to
the cyclic symbol quotient. -/
def quotientOrderAssociatedGradedAddEquivCharacteristic
    (I : RightIdeal (PresentedWeyl k n)) :
    QuotientOrderAssociatedGraded k I ≃+ OrderCharacteristicModule k I :=
  (quotientOrderAssociatedGradedEquivCharacteristic k I).toAddEquiv.trans
    (restrictScalarsQuotientAddEquiv k I)


end

end Stafford38.CharacteristicFilteredQuotientSupport
