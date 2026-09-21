/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Weyl.AssociatedGraded
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Algebra.TransferInstance

/-!
# The associated graded algebra of the presented Weyl algebra

The degree-wise filtered quotients assemble into an external direct sum. Its
canonical symbol map is an algebra equivalence with the commutative symbol
polynomial ring. For the Bernstein and differential-order filtrations, the
transported multiplication is proved to be the multiplication induced by Weyl
products of filtered representatives.
-/

namespace Stafford38.WeylAssociatedGraded

open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol

noncomputable section

universe u

variable (k : Type u) [Field k]

-- The quotient instances used to define the graded pieces are local to
-- `AssociatedGraded`; restate them here for the external direct sum.
local instance (priority := 10000) presentedAssociatedGradedPieceAddCommGroup'
    {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    AddCommGroup (presentedAssociatedGradedPiece k w N) :=
  @Submodule.Quotient.addCommGroup k (presentedWeightPiece k w N) _
    (presentedWeightPiece k w N).addCommGroup
    (presentedWeightPiece k w N).module
    (LinearMap.ker (principalComponentOnPiece k w N))

local instance (priority := 10000) presentedAssociatedGradedPieceModule'
    {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    Module k (presentedAssociatedGradedPiece k w N) :=
  @Submodule.Quotient.module k (presentedWeightPiece k w N) _
    (presentedWeightPiece k w N).addCommGroup
    (presentedWeightPiece k w N).module
    (LinearMap.ker (principalComponentOnPiece k w N))

/-- The external direct sum of all filtered quotient pieces. This is a new
type so its algebra structure can be transported without changing the
canonical module structures on the individual quotient pieces. -/
def PresentedAssociatedGraded {n : ℕ} (w : PhaseVar n → ℕ) :=
  DirectSum ℕ (fun N => presentedAssociatedGradedPiece k w N)

/-- The direct sum of the piecewise principal-component equivalences, followed
by weighted-homogeneous recomposition. -/
def presentedAssociatedGradedRawLinearEquiv {n : ℕ} (w : PhaseVar n → ℕ) :
    DirectSum ℕ (fun N => presentedAssociatedGradedPiece k w N) ≃ₗ[k]
      SymbolRing k n := by
  letI := MvPolynomial.weightedDecomposition k w
  exact (DFinsupp.mapRange.linearEquiv fun N =>
      presentedAssociatedGradedPieceEquiv k w N).trans
    (DirectSum.decomposeLinearEquiv
      (MvPolynomial.weightedHomogeneousSubmodule k w)).symm

def presentedAssociatedGradedRawEquiv {n : ℕ} (w : PhaseVar n → ℕ) :
    PresentedAssociatedGraded k w ≃ SymbolRing k n :=
  (presentedAssociatedGradedRawLinearEquiv k w).toEquiv

/-- The commutative ring structure transported through the global symbol
equivalence. The representative multiplication theorems below identify it
with the multiplication induced by the two Weyl filtrations used downstream. -/
noncomputable instance presentedAssociatedGradedCommRing {n : ℕ}
    (w : PhaseVar n → ℕ) : CommRing (PresentedAssociatedGraded k w) :=
  Equiv.commRing (presentedAssociatedGradedRawEquiv k w)

noncomputable instance presentedAssociatedGradedAlgebra {n : ℕ}
    (w : PhaseVar n → ℕ) : Algebra k (PresentedAssociatedGraded k w) :=
  Equiv.algebra k (presentedAssociatedGradedRawEquiv k w)

/-- The associated graded algebra is the commutative symbol polynomial
algebra. -/
def presentedAssociatedGradedAlgEquiv {n : ℕ} (w : PhaseVar n → ℕ) :
    PresentedAssociatedGraded k w ≃ₐ[k] SymbolRing k n :=
  Equiv.algEquiv k (presentedAssociatedGradedRawEquiv k w)

/-- Insert one quotient piece into the external direct sum. -/
def presentedAssociatedGradedOf {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ)
    (z : presentedAssociatedGradedPiece k w N) :
    PresentedAssociatedGraded k w :=
  DirectSum.of (fun N => presentedAssociatedGradedPiece k w N) N z

@[simp] theorem presentedAssociatedGradedAlgEquiv_of {n : ℕ}
    (w : PhaseVar n → ℕ) (N : ℕ)
    (z : presentedAssociatedGradedPiece k w N) :
    presentedAssociatedGradedAlgEquiv k w
        (presentedAssociatedGradedOf k w N z) =
      (presentedAssociatedGradedPieceEquiv k w N z : SymbolRing k n) := by
  let := MvPolynomial.weightedDecomposition k w
  change presentedAssociatedGradedRawLinearEquiv k w
      (DirectSum.of (fun N => presentedAssociatedGradedPiece k w N) N z) = _
  rw [presentedAssociatedGradedRawLinearEquiv, LinearEquiv.trans_apply]
  have hmap :
      (DFinsupp.mapRange.linearEquiv fun N =>
          presentedAssociatedGradedPieceEquiv k w N)
          (DirectSum.of (fun N => presentedAssociatedGradedPiece k w N) N z) =
        DirectSum.of (fun N =>
          MvPolynomial.weightedHomogeneousSubmodule k w N) N
          (presentedAssociatedGradedPieceEquiv k w N z) := by
    rw [DFinsupp.mapRange.linearEquiv_apply]
    exact DFinsupp.mapRange_single
  calc
    _ = (DirectSum.decomposeLinearEquiv
        (MvPolynomial.weightedHomogeneousSubmodule k w)).symm
          (DirectSum.of (fun N =>
            MvPolynomial.weightedHomogeneousSubmodule k w N) N
            (presentedAssociatedGradedPieceEquiv k w N z)) :=
      congrArg _ hmap
    _ = _ := by
      rw [DirectSum.decomposeLinearEquiv_symm_apply,
        DirectSum.decompose_symm_of]

/-- Homogeneous insertion is additive even though the ring structure on the
new external-direct-sum type is transported from the symbol ring. -/
theorem presentedAssociatedGradedOf_add {n N : ℕ}
    (w : PhaseVar n → ℕ)
    (x y : presentedAssociatedGradedPiece k w N) :
    presentedAssociatedGradedOf k w N (x + y) =
      presentedAssociatedGradedOf k w N x +
        presentedAssociatedGradedOf k w N y := by
  apply (presentedAssociatedGradedAlgEquiv k w).injective
  rw [map_add, presentedAssociatedGradedAlgEquiv_of,
    presentedAssociatedGradedAlgEquiv_of,
    presentedAssociatedGradedAlgEquiv_of]
  exact congrArg Subtype.val
    ((presentedAssociatedGradedPieceEquiv k w N).map_add x y)

/-- Insert the class of a filtered representative into the external direct
sum. -/
def presentedAssociatedGradedMk {n N : ℕ} (w : PhaseVar n → ℕ)
    (z : presentedWeightPiece k w N) : PresentedAssociatedGraded k w :=
  presentedAssociatedGradedOf k w N (Submodule.Quotient.mk z)

@[simp] theorem presentedAssociatedGradedAlgEquiv_mk {n N : ℕ}
    (w : PhaseVar n → ℕ) (z : presentedWeightPiece k w N) :
    presentedAssociatedGradedAlgEquiv k w
        (presentedAssociatedGradedMk k w z) =
      presentedPrincipalComponent k w N z := by
  rw [presentedAssociatedGradedMk, presentedAssociatedGradedAlgEquiv_of,
    presentedAssociatedGradedPieceEquiv_mk]
  rfl

def bernsteinMulRepresentative {n N M : ℕ}
    (x : bernsteinPiece k n N) (y : bernsteinPiece k n M) :
    bernsteinPiece k n (N + M) :=
  ⟨(x : PresentedWeyl k n) * y,
    mul_mem_bernsteinPiece k x.property y.property⟩

def orderMulRepresentative {n N M : ℕ}
    (x : orderPiece k n N) (y : orderPiece k n M) :
    orderPiece k n (N + M) :=
  ⟨(x : PresentedWeyl k n) * y,
    mul_mem_orderPiece k x.property y.property⟩

/-- On Bernstein-homogeneous classes, external graded multiplication is
represented by multiplication in the Weyl algebra. -/
theorem presentedAssociatedGradedMk_mul_bernstein {n N M : ℕ}
    (x : bernsteinPiece k n N) (y : bernsteinPiece k n M) :
    presentedAssociatedGradedMk k bernsteinWeight x *
        presentedAssociatedGradedMk k bernsteinWeight y =
      presentedAssociatedGradedMk k bernsteinWeight
        (bernsteinMulRepresentative k x y) := by
  apply (presentedAssociatedGradedAlgEquiv k bernsteinWeight).injective
  rw [map_mul,
    presentedAssociatedGradedAlgEquiv_mk (n := n) k bernsteinWeight x,
    presentedAssociatedGradedAlgEquiv_mk (n := n) k bernsteinWeight y,
    presentedAssociatedGradedAlgEquiv_mk (n := n) k bernsteinWeight
      (bernsteinMulRepresentative k x y)]
  simpa [bernsteinMulRepresentative] using
    (presentedPrincipalComponent_mul_bernstein k x.property y.property).symm

/-- On order-homogeneous classes, external graded multiplication is
represented by multiplication in the Weyl algebra. -/
theorem presentedAssociatedGradedMk_mul_order {n N M : ℕ}
    (x : orderPiece k n N) (y : orderPiece k n M) :
    presentedAssociatedGradedMk k orderWeight x *
        presentedAssociatedGradedMk k orderWeight y =
      presentedAssociatedGradedMk k orderWeight
        (orderMulRepresentative k x y) := by
  apply (presentedAssociatedGradedAlgEquiv k orderWeight).injective
  rw [map_mul,
    presentedAssociatedGradedAlgEquiv_mk (n := n) k orderWeight x,
    presentedAssociatedGradedAlgEquiv_mk (n := n) k orderWeight y,
    presentedAssociatedGradedAlgEquiv_mk (n := n) k orderWeight
      (orderMulRepresentative k x y)]
  simpa [orderMulRepresentative] using
    (presentedPrincipalComponent_mul_order k x.property y.property).symm

/- Exact statement pins for the public API and focused checker. -/
example {n : ℕ} (w : PhaseVar n → ℕ) :
    PresentedAssociatedGraded k w ≃ₐ[k] SymbolRing k n :=
  presentedAssociatedGradedAlgEquiv k w

example {n N : ℕ} (w : PhaseVar n → ℕ)
    (z : presentedWeightPiece k w N) :
    presentedAssociatedGradedAlgEquiv k w
        (presentedAssociatedGradedMk k w z) =
      presentedPrincipalComponent k w N z :=
  presentedAssociatedGradedAlgEquiv_mk k w z

example {n N M : ℕ} (x : orderPiece k n N) (y : orderPiece k n M) :
    presentedAssociatedGradedMk k orderWeight x *
        presentedAssociatedGradedMk k orderWeight y =
      presentedAssociatedGradedMk k orderWeight
        ⟨(x : PresentedWeyl k n) * (y : PresentedWeyl k n),
          mul_mem_orderPiece k x.property y.property⟩ :=
  presentedAssociatedGradedMk_mul_order k x y


end

end Stafford38.WeylAssociatedGraded
