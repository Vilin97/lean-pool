/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalMonicSaturation


/-!
# A unit-only strict coordinate criterion for canonical axis avoidance

The terminal axis-avoidance argument does not require coordinate cancellation
on every associated-graded piece.  It only needs the degree-zero class of `1`
to lie in the image of the coordinate action.  Equivalently, it is enough to
have one representative of order zero whose coordinate multiple equals `1`
in the literal canonical quotient.

This file proves that this single strict unit preimage puts a relation
`P * X - 1` in the order initial ideal and hence excludes the distinguished
coordinate hyperplane from characteristic support.  It also records that the
previous all-degree cancellation and strict-lower-preimage hypotheses imply
the unit-only condition.  No converse is asserted.
-/

@[expose] public section

namespace Stafford38.CanonicalUnitCoordinatePreimage

open Stafford38.CanonicalAxisAvoidanceConsumer
open Stafford38.CanonicalMonicSaturation
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

/-- The weakest concrete filtered input used by the terminal axis argument:
the quotient class of `1` has one coordinate predecessor of order zero. -/
def StrictUnitCoordinatePreimage (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) : Prop :=
  ∃ y : PresentedWeyl k (n + 1),
    y ∈ orderPiece k (n + 1) 0 ∧
      qmk (CanonicalIdeal k n N d) (y * presentedCoordinate k n) =
        qmk (CanonicalIdeal k n N d) 1

/-- The previous all-degree cancellation hypothesis implies the unit-only
criterion, by strictifying an unrestricted preimage only at degree zero. -/
theorem strictUnitCoordinatePreimage_of_coordinateCancellation
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (hcancel : CoordinateCancellation k n N d) :
    StrictUnitCoordinatePreimage k n N d := by
  obtain ⟨y, hy, hyx⟩ := exists_strict_coordinate_preimage
    k n N 0 hd hcancel 1 (orderPieceOne (n := n + 1) k).property
  exact ⟨y, hy, hyx⟩

omit [Algebra ℚ k] in
/-- Uniform strict-lower coordinate division is also stronger than necessary:
only its instance at cutoff `1` and target `1` is used here. -/
theorem strictUnitCoordinatePreimage_of_strictLowerCoordinatePreimages
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hstrict : StrictLowerCoordinatePreimages k n N d) :
    StrictUnitCoordinatePreimage k n N d := by
  have hone : (1 : PresentedWeyl k (n + 1)) ∈
      presentedStrictLowerPiece k orderWeight 1 := by
    change (1 : PresentedWeyl k (n + 1)) ∈ orderPiece k (n + 1) 0
    exact (orderPieceOne (n := n + 1) k).property
  obtain ⟨y, hy, hyx⟩ := hstrict 1 1 hone
  have hy0 : y ∈ orderPiece k (n + 1) 0 := by
    change y ∈ orderPiece k (n + 1) 0 at hy
    exact hy
  exact ⟨y, hy0, hyx⟩

omit [Algebra ℚ k] in
/-- A single strict unit preimage gives the exact degree-zero initial relation
needed for scheme-level coordinate-axis avoidance. -/
theorem canonical_orderInitialIdeal_sup_coordinate_eq_top_of_strictUnit
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hunit : StrictUnitCoordinatePreimage k n N d) :
    orderInitialIdeal k (CanonicalIdeal k n N d) ⊔
        Ideal.span {MvPolynomial.X (.inl (0 : Fin (n + 1)))} = ⊤ := by
  let I := CanonicalIdeal k n N d
  let x := presentedCoordinate k n
  obtain ⟨y, hy, hyx⟩ := hunit
  have hx : x ∈ orderPiece k (n + 1) 0 :=
    presentedCoordinate_mem_orderPiece_zero k n
  have hyxOrder : y * x ∈ orderPiece k (n + 1) 0 :=
    mul_mem_orderPiece k hy hx
  have honeOrder : (1 : PresentedWeyl k (n + 1)) ∈
      orderPiece k (n + 1) 0 :=
    (orderPieceOne (n := n + 1) k).property
  have hdiffOrder : y * x - 1 ∈ orderPiece k (n + 1) 0 :=
    (orderPiece k (n + 1) 0).sub_mem hyxOrder honeOrder
  have hdiffIdeal : y * x - 1 ∈ I :=
    (Submodule.Quotient.eq I).mp hyx
  have hrelation := principalComponent_mem_orderSymbolRelation
    k I 0 (y * x - 1) hdiffOrder hdiffIdeal
  have hinitial :
      ((principalComponentOnPiece k (@orderWeight (n + 1)) 0
          ⟨y * x - 1, hdiffOrder⟩ :
        MvPolynomial.weightedHomogeneousSubmodule k
          (@orderWeight (n + 1)) 0) : SymbolRing k (n + 1)) ∈
        orderInitialIdeal k I :=
    coe_mem_orderInitialIdeal_of_mem_orderSymbolRelation k I 0 _ hrelation
  let Y : MvPolynomial.weightedHomogeneousSubmodule k
      (@orderWeight (n + 1)) 0 :=
    principalComponentOnPiece k (@orderWeight (n + 1)) 0 ⟨y, hy⟩
  have hYX : (Y : SymbolRing k (n + 1)) *
        MvPolynomial.X (.inl (0 : Fin (n + 1))) - 1 ∈
      orderInitialIdeal k I := by
    convert hinitial using 1
    change (Y : SymbolRing k (n + 1)) *
        MvPolynomial.X (.inl (0 : Fin (n + 1))) - 1 =
      presentedPrincipalComponent k orderWeight 0 (y * x - 1)
    rw [map_sub, presentedPrincipalComponent_mul_order k hy hx]
    have honePC : presentedPrincipalComponent k orderWeight 0
        (1 : PresentedWeyl k (n + 1)) = 1 := by
      change presentedPrincipalComponent k orderWeight 0
          ((orderPieceOne (n := n + 1) k : orderPiece k (n + 1) 0) :
            PresentedWeyl k (n + 1)) = 1
      exact presentedPrincipalComponent_orderPieceOne (n := n + 1) k
    rw [honePC]
    rw [show MvPolynomial.X (.inl (0 : Fin (n + 1))) =
        presentedPrincipalComponent k orderWeight 0 x by
      exact (coe_coordinate_order_symbol k n).symm]
    change presentedPrincipalComponent k orderWeight 0 y *
        presentedPrincipalComponent k orderWeight 0 x - 1 = _
    rfl
  apply (Ideal.eq_top_iff_one _).2
  rw [show (1 : SymbolRing k (n + 1)) =
      -((Y : SymbolRing k (n + 1)) *
          MvPolynomial.X (.inl (0 : Fin (n + 1))) - 1) +
        (Y : SymbolRing k (n + 1)) *
          MvPolynomial.X (.inl (0 : Fin (n + 1))) by ring]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left ((orderInitialIdeal k I).neg_mem hYX))
    (Submodule.mem_sup_right (by
      rw [Ideal.mem_span_singleton]
      exact ⟨(Y : SymbolRing k (n + 1)), by rw [mul_comm]⟩))

omit [Algebra ℚ k] in
/-- The terminal set-theoretic conclusion follows from the unit-only strict
preimage; neither all-degree cancellation nor graded injectivity is consumed. -/
theorem canonical_orderCharacteristicSupport_disjoint_coordinate_zeroLocus_of_strictUnit
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hunit : StrictUnitCoordinatePreimage k n N d) :
    Disjoint
      (orderCharacteristicSupport k (CanonicalIdeal k n N d))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) := by
  rw [Set.disjoint_left]
  intro p hp hpx
  rw [orderCharacteristicSupport_eq_zeroLocus,
    PrimeSpectrum.mem_zeroLocus] at hp
  rw [PrimeSpectrum.mem_zeroLocus] at hpx
  have htop :=
    canonical_orderInitialIdeal_sup_coordinate_eq_top_of_strictUnit
      k n N hunit
  have hle : orderInitialIdeal k (CanonicalIdeal k n N d) ⊔
      Ideal.span {MvPolynomial.X (.inl (0 : Fin (n + 1)))} ≤ p.asIdeal :=
    sup_le hp (Ideal.span_le.mpr hpx)
  rw [htop] at hle
  exact p.2.ne_top (top_unique hle)


end

end Stafford38.CanonicalUnitCoordinatePreimage
