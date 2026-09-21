/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedModule
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalAxisAvoidanceConsumer

/-!
# The exact strictness interface for canonical noncharacteristic cancellation

For the canonical filtered Weyl quotient, the previously isolated
`CoordinateCancellation` condition is not an additional mysterious property:
it is exactly injectivity of the distinguished coordinate on every actual
order-associated-graded piece.  This file proves that equivalence and gives a
commutative saturation criterion which is sufficient for it.

The remaining implication is the load-bearing noncharacteristic theorem:
`IsPBWMonicAt` must force the displayed coordinate action to be injective (or,
equivalently, force saturation of the canonical order initial ideal by the
coordinate).  Monicity and unrestricted surjectivity alone do not prove that
strictness statement; no such implication is assumed here.
-/

namespace Stafford38.CanonicalNoncharacteristicCancellation

open Stafford38.CanonicalAxisAvoidanceConsumer
open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientGraded
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicInitialIdealHomogeneous
open Stafford38.EulerSurjectivity
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylEulerResidue
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

variable (k : Type u) [Field k] [Algebra ℚ k]

private abbrev CanonicalIdeal (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :=
  canonicalRightIdeal (presentedCoordinate k n) d N

/-- The distinguished coordinate, regarded as a homogeneous order-zero
symbol. -/
def coordinateOrderSymbol (n : ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule k
      (@orderWeight (n + 1)) 0 :=
  principalComponentOnPiece k (@orderWeight (n + 1)) 0
    ⟨presentedCoordinate k n,
      presentedCoordinate_mem_orderPiece_zero k n⟩

/-- Multiplication by the distinguished coordinate on the actual degree-`m`
associated-graded piece of the canonical filtered quotient. -/
def canonicalGradedCoordinateAction (n N m : ℕ)
    (d : PresentedWeyl k (n + 1)) :
    QuotientOrderGradedPiece k (CanonicalIdeal k n N d) m →ₗ[k]
      QuotientOrderGradedPiece k (CanonicalIdeal k n N d) m := by
  simpa using
    (quotientOrderHomogeneousAction (N := m) (M := 0)
      k (CanonicalIdeal k n N d) (coordinateOrderSymbol k n))

@[simp] theorem canonicalGradedCoordinateAction_mk
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (z : orderPiece k (n + 1) m) :
    canonicalGradedCoordinateAction k n N m d
        (orderPieceToQuotientGraded k (CanonicalIdeal k n N d) m z) =
      orderPieceToQuotientGraded k (CanonicalIdeal k n N d) m
        ⟨(z : PresentedWeyl k (n + 1)) * presentedCoordinate k n,
          mul_mem_orderPiece k z.property
            (presentedCoordinate_mem_orderPiece_zero k n)⟩ := by
  change quotientOrderHomogeneousAction k (CanonicalIdeal k n N d)
      (coordinateOrderSymbol k n)
        (orderPieceToQuotientGraded k (CanonicalIdeal k n N d) m z) = _
  simpa [coordinateOrderSymbol] using
    quotientOrderHomogeneousAction_mk_mul k (CanonicalIdeal k n N d) z
      ⟨presentedCoordinate k n,
        presentedCoordinate_mem_orderPiece_zero k n⟩

/-- Degreewise coordinate cancellation is exactly injectivity of coordinate
multiplication on every actual associated-graded quotient piece.  Thus the
previously conditional consumer's hypothesis is the strictness part of the
noncharacteristic inverse-image theorem, expressed without any geometric
terminology. -/
theorem coordinateCancellation_iff_forall_graded_injective
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    CoordinateCancellation k n N d ↔
      ∀ m, Function.Injective
        (canonicalGradedCoordinateAction k n N m d) := by
  let I := CanonicalIdeal k n N d
  let x := presentedCoordinate k n
  constructor
  · intro hcancel m
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm
    · intro q hq
      obtain ⟨z, rfl⟩ :=
        orderPieceToQuotientGraded_surjective k I m q
      rw [LinearMap.mem_ker] at hq
      have hproduct :
          (z : PresentedWeyl k (n + 1)) * x ∈
            rightIdealKSubmodule k I ⊔
              presentedStrictLowerPiece k orderWeight m := by
        have hproductKer :
            ⟨(z : PresentedWeyl k (n + 1)) * x,
              mul_mem_orderPiece k z.property
                (presentedCoordinate_mem_orderPiece_zero k n)⟩ ∈
              LinearMap.ker (orderPieceToQuotientGraded k I m) := by
          rw [LinearMap.mem_ker]
          simpa [I, x] using hq
        rw [ker_orderPieceToQuotientGraded] at hproductKer
        exact hproductKer
      have hz := hcancel m z z.property hproduct
      rw [Submodule.mem_bot]
      rw [← LinearMap.mem_ker, ker_orderPieceToQuotientGraded]
      change (z : PresentedWeyl k (n + 1)) ∈
        rightIdealKSubmodule k I ⊔
          presentedStrictLowerPiece k orderWeight m
      exact hz
    · exact bot_le
  · intro hinjective m z hz hzx
    let zz : orderPiece k (n + 1) m := ⟨z, hz⟩
    have hproductZero :
        orderPieceToQuotientGraded k (CanonicalIdeal k n N d) m
            ⟨z * presentedCoordinate k n,
              mul_mem_orderPiece k hz
                (presentedCoordinate_mem_orderPiece_zero k n)⟩ = 0 := by
      rw [← LinearMap.mem_ker, ker_orderPieceToQuotientGraded]
      exact hzx
    have hzero :
        orderPieceToQuotientGraded k (CanonicalIdeal k n N d) m zz = 0 := by
      apply hinjective m
      rw [map_zero, canonicalGradedCoordinateAction_mk]
      exact hproductZero
    change z ∈ rightIdealKSubmodule k (CanonicalIdeal k n N d) ⊔
      presentedStrictLowerPiece k orderWeight m
    have hzker : zz ∈ LinearMap.ker
        (orderPieceToQuotientGraded k (CanonicalIdeal k n N d) m) := by
      rw [LinearMap.mem_ker]
      exact hzero
    rw [ker_orderPieceToQuotientGraded] at hzker
    exact hzker

/-- Saturation of the concrete order initial ideal by the coordinate implies
the exact degreewise cancellation needed by the canonical consumer.  This is
a sufficient commutative-algebra formulation of strictness; it is not assumed
to follow from monicity in this file. -/
theorem coordinateCancellation_of_initialIdeal_coordinate_saturated
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hsaturated :
      (orderInitialIdeal k (CanonicalIdeal k n N d)).colon
          ({MvPolynomial.X (Sum.inl (0 : Fin (n + 1)))} :
            Set (SymbolRing k (n + 1))) =
        orderInitialIdeal k (CanonicalIdeal k n N d)) :
    CoordinateCancellation k n N d := by
  rw [coordinateCancellation_iff_forall_graded_injective]
  intro m
  let I := CanonicalIdeal k n N d
  let X := coordinateOrderSymbol k n
  have hX : (X : SymbolRing k (n + 1)) =
      MvPolynomial.X (.inl (0 : Fin (n + 1))) :=
    coe_coordinate_order_symbol k n
  have hsymbol : Function.Injective
      (homogeneousSymbolAction (N := m) (M := 0) k I X) := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm
    · intro q hq
      rw [LinearMap.mem_ker] at hq
      rw [Submodule.mem_bot]
      refine Submodule.Quotient.induction_on _ q ?_ hq
      intro P hP
      rw [homogeneousSymbolAction_mk,
        Submodule.Quotient.mk_eq_zero] at hP
      have hPX : (P : SymbolRing k (n + 1)) *
          MvPolynomial.X (.inl (0 : Fin (n + 1))) ∈
            orderInitialIdeal k I := by
        rw [← hX]
        exact (mem_orderSymbolRelation_iff_coe_mem_orderInitialIdeal
          k I m (homogeneousRightMul k X P)).mp hP
      have hPcolon : (P : SymbolRing k (n + 1)) ∈
          (orderInitialIdeal k I).colon
            ({MvPolynomial.X (Sum.inl (0 : Fin (n + 1)))} :
              Set (SymbolRing k (n + 1))) :=
        Submodule.mem_colon_singleton.mpr hPX
      have hPJ : (P : SymbolRing k (n + 1)) ∈ orderInitialIdeal k I := by
        rw [hsaturated] at hPcolon
        exact hPcolon
      rw [Submodule.Quotient.mk_eq_zero]
      exact (mem_orderSymbolRelation_iff_coe_mem_orderInitialIdeal
        k I m P).mpr hPJ
    · exact bot_le
  intro q₁ q₂ hq
  apply (quotientOrderGradedPieceEquivSymbols k I m).injective
  apply hsymbol
  rw [← quotientOrderHomogeneousAction_compatibility,
    ← quotientOrderHomogeneousAction_compatibility]
  exact congrArg (quotientOrderGradedPieceEquivSymbols k I m) hq

/-- A saturated canonical initial ideal therefore satisfies the already
formalized scheme-level coordinate-axis avoidance conclusion. -/
theorem canonical_support_disjoint_coordinate_zeroLocus_of_saturated
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (hsaturated :
      (orderInitialIdeal k (CanonicalIdeal k n N d)).colon
          ({MvPolynomial.X (Sum.inl (0 : Fin (n + 1)))} :
            Set (SymbolRing k (n + 1))) =
        orderInitialIdeal k (CanonicalIdeal k n N d)) :
    Disjoint
      (orderCharacteristicSupport k (CanonicalIdeal k n N d))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) := by
  exact canonical_orderCharacteristicSupport_disjoint_coordinate_zeroLocus
    k n N hd
      (coordinateCancellation_of_initialIdeal_coordinate_saturated
        k n N d hsaturated)


end

end Stafford38.CanonicalNoncharacteristicCancellation
