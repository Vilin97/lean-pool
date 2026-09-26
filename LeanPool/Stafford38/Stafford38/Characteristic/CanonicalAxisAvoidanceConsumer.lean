/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientGraded
public import LeanPool.Stafford38.Stafford38.Characteristic.InitialIdealHomogeneous
public import LeanPool.Stafford38.Stafford38.Weyl.QuotientTransport


/-!
# Conditional consumer for canonical axis avoidance

This file assumes, but does not prove, the missing degreewise cancellation
statement for the canonical filtered quotient.  It combines that hypothesis
with the proved surjectivity of right multiplication by the distinguished
coordinate and derives strict filtered surjectivity and its associated-graded
form.
-/

@[expose] public section

namespace Stafford38.CanonicalAxisAvoidanceConsumer

open Stafford38.Characteristic
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
open Stafford38.WeylPBW
open Stafford38.WeylQuotientTransport

noncomputable section

universe u

variable (k : Type u) [Field k] [Algebra ℚ k]

/-- The canonical right ideal determined by the Weyl element and its monic degree. -/
abbrev CanonicalIdeal (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :=
  canonicalRightIdeal (presentedCoordinate k n) d N

omit [Algebra ℚ k] in
/-- The distinguished coordinate belongs to differential order zero. -/
theorem presentedCoordinate_mem_orderPiece_zero (n : ℕ) :
    presentedCoordinate k n ∈ orderPiece k (n + 1) 0 := by
  rw [orderPiece, mem_presentedWeightPiece,
    presentedCoordinate, presentedNormalFormLinearEquiv_generator]
  intro m hm
  rw [MvPolynomial.coeff_X] at hm
  split at hm
  · next heq =>
      subst m
      simp [monomialWeight, orderWeight, fibreWeight]
  · exact (hm rfl).elim

/-- The exact missing input: multiplication by the coordinate can be
cancelled in every degree of the actual filtered quotient. -/
def CoordinateCancellation (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) : Prop :=
  ∀ (m : ℕ) (z : PresentedWeyl k (n + 1)),
    z ∈ orderPiece k (n + 1) m →
    z * presentedCoordinate k n ∈
        rightIdealKSubmodule k (CanonicalIdeal k n N d) ⊔
          presentedStrictLowerPiece k orderWeight m →
    z ∈ rightIdealKSubmodule k (CanonicalIdeal k n N d) ⊔
      presentedStrictLowerPiece k orderWeight m

/-- Cancellation plus unrestricted quotient surjectivity lowers an arbitrary
predecessor until it has no larger order than the target. -/
theorem exists_strict_coordinate_preimage
    (n N m : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : Stafford38.WeylPBWMonicBridge.IsPBWMonicAt k
      (.inr (0 : Fin (n + 1))) N d)
    (hcancel : CoordinateCancellation k n N d)
    (z : PresentedWeyl k (n + 1))
    (hz : z ∈ orderPiece k (n + 1) m) :
    ∃ y : PresentedWeyl k (n + 1),
      y ∈ orderPiece k (n + 1) m ∧
      qmk (CanonicalIdeal k n N d) (y * presentedCoordinate k n) =
        qmk (CanonicalIdeal k n N d) z := by
  let I := CanonicalIdeal k n N d
  let x := presentedCoordinate k n
  have hsurj : Function.Surjective (rightMul I x) := by
    exact presentedCanonicalRightQuotient_rightMul_coordinate_surjective
      (k := k) n N hd
  obtain ⟨q, hq⟩ := hsurj (qmk I z)
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I q
  change rightMul I x (qmk I y) = qmk I z at hq
  rw [← qmk_right_mul] at hq
  obtain ⟨L, hyL⟩ := exists_mem_orderPiece k y
  have hdesc : ∀ L, ∀ y : PresentedWeyl k (n + 1),
      y ∈ orderPiece k (n + 1) L → qmk I (y * x) = qmk I z →
      ∃ y' : PresentedWeyl k (n + 1),
        y' ∈ orderPiece k (n + 1) m ∧ qmk I (y' * x) = qmk I z := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro y hyL hyx
      by_cases hLm : L ≤ m
      · exact ⟨y, presentedWeightPiece_mono k orderWeight hLm hyL, hyx⟩
      · have hmL : m < L := Nat.lt_of_not_ge hLm
        have hzLower : z ∈ presentedStrictLowerPiece k orderWeight L := by
          cases L with
          | zero => omega
          | succ L =>
              simp only [presentedStrictLowerPiece]
              exact presentedWeightPiece_mono k orderWeight (Nat.le_of_lt_succ hmL) hz
        have hyxSub : y * x - z ∈ I :=
          (Submodule.Quotient.eq I).mp hyx
        have hyxMem : y * x ∈
            rightIdealKSubmodule k I ⊔
              presentedStrictLowerPiece k orderWeight L := by
          rw [show y * x = (y * x - z) + z by abel]
          exact Submodule.add_mem _
            (Submodule.mem_sup_left hyxSub)
            (Submodule.mem_sup_right hzLower)
        have hyMem := hcancel L y hyL hyxMem
        obtain ⟨i, hi, l, hl, hil⟩ := Submodule.mem_sup.mp hyMem
        cases L with
        | zero => omega
        | succ L =>
            simp only [presentedStrictLowerPiece] at hl
            have hyl : qmk I y = qmk I l := by
              apply (Submodule.Quotient.eq I).2
              rw [← hil]
              simpa using hi
            have hlx : qmk I (l * x) = qmk I z := by
              rw [qmk_right_mul, ← hyl, ← qmk_right_mul]
              exact hyx
            exact ih L (Nat.lt_succ_self L) l hl hlx
  exact hdesc L y hyL hq

/-- Every actual associated-graded piece has surjective multiplication by
the order-zero coordinate symbol. -/
theorem canonical_graded_coordinate_surjective
    (n N m : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : Stafford38.WeylPBWMonicBridge.IsPBWMonicAt k
      (.inr (0 : Fin (n + 1))) N d)
    (hcancel : CoordinateCancellation k n N d) :
    Function.Surjective
      (quotientOrderHomogeneousAction (N := m) (M := 0)
        k (CanonicalIdeal k n N d)
        (principalComponentOnPiece k (@orderWeight (n + 1)) 0
          ⟨presentedCoordinate k n,
            presentedCoordinate_mem_orderPiece_zero k n⟩)) := by
  intro q
  obtain ⟨z, rfl⟩ := orderPieceToQuotientGraded_surjective
    k (CanonicalIdeal k n N d) m q
  obtain ⟨y, hy, hyx⟩ :=
    exists_strict_coordinate_preimage k n N m hd hcancel z z.property
  refine ⟨orderPieceToQuotientGraded k (CanonicalIdeal k n N d) m ⟨y, hy⟩, ?_⟩
  rw [quotientOrderHomogeneousAction_mk_mul]
  have hyx' : (rightIdealKSubmodule k (CanonicalIdeal k n N d)).mkQ
        (y * presentedCoordinate k n) =
      (rightIdealKSubmodule k (CanonicalIdeal k n N d)).mkQ z :=
    congrArg
      (filteredRightQuotientEquivRightQuotient k
        (CanonicalIdeal k n N d)).symm hyx
  apply (Submodule.Quotient.eq _).2
  change (orderPieceToQuotientPiece k (CanonicalIdeal k n N d) m
      ⟨y * presentedCoordinate k n, _⟩ :
        FilteredRightQuotient k (CanonicalIdeal k n N d)) -
      orderPieceToQuotientPiece k (CanonicalIdeal k n N d) m z ∈
        quotientOrderStrictLowerPiece k (CanonicalIdeal k n N d) m
  rw [show (orderPieceToQuotientPiece k (CanonicalIdeal k n N d) m
      ⟨y * presentedCoordinate k n, _⟩ :
        FilteredRightQuotient k (CanonicalIdeal k n N d)) =
      (rightIdealKSubmodule k (CanonicalIdeal k n N d)).mkQ
        (y * presentedCoordinate k n) from rfl]
  rw [show (orderPieceToQuotientPiece k (CanonicalIdeal k n N d) m z :
      FilteredRightQuotient k (CanonicalIdeal k n N d)) =
      (rightIdealKSubmodule k (CanonicalIdeal k n N d)).mkQ z from rfl]
  rw [hyx', sub_self]
  exact Submodule.zero_mem _

omit [Algebra ℚ k] in
/-- The order-zero principal symbol of the distinguished coordinate is the
corresponding base variable. -/
theorem coe_coordinate_order_symbol (n : ℕ) :
    ((principalComponentOnPiece k (@orderWeight (n + 1)) 0
        ⟨presentedCoordinate k n,
          presentedCoordinate_mem_orderPiece_zero k n⟩) :
      SymbolRing k (n + 1)) =
      MvPolynomial.X (.inl (0 : Fin (n + 1))) := by
  ext m
  change (presentedPrincipalComponent k orderWeight 0
        (presentedCoordinate k n)).coeff m = _
  rw [coeff_presentedPrincipalComponent, presentedCoordinate,
    presentedNormalFormLinearEquiv_generator, MvPolynomial.coeff_X]
  by_cases hm : Finsupp.single (.inl (0 : Fin (n + 1))) 1 = m
  · subst m
    simp [monomialWeight, orderWeight, fibreWeight]
  · simp [hm]

/-- Conditional scheme-level axis avoidance: the order initial ideal together
with the distinguished coordinate generates the unit ideal. -/
theorem canonical_orderInitialIdeal_sup_coordinate_eq_top
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : Stafford38.WeylPBWMonicBridge.IsPBWMonicAt k
      (.inr (0 : Fin (n + 1))) N d)
    (hcancel : CoordinateCancellation k n N d) :
    orderInitialIdeal k (CanonicalIdeal k n N d) ⊔
        Ideal.span {MvPolynomial.X (.inl (0 : Fin (n + 1)))} = ⊤ := by
  let I := CanonicalIdeal k n N d
  let X : MvPolynomial.weightedHomogeneousSubmodule k
      (@orderWeight (n + 1)) 0 :=
    principalComponentOnPiece k (@orderWeight (n + 1)) 0
      ⟨presentedCoordinate k n, presentedCoordinate_mem_orderPiece_zero k n⟩
  let oneH : MvPolynomial.weightedHomogeneousSubmodule k
      (@orderWeight (n + 1)) 0 :=
    ⟨1, MvPolynomial.isWeightedHomogeneous_one k orderWeight⟩
  have hsurjActual := canonical_graded_coordinate_surjective
    k n N 0 hd hcancel
  have hsurjSymbol : Function.Surjective
      (homogeneousSymbolAction (N := 0) (M := 0) k I X) := by
    intro q
    obtain ⟨r, hr⟩ := hsurjActual
      ((quotientOrderGradedPieceEquivSymbols k I 0).symm q)
    refine ⟨quotientOrderGradedPieceEquivSymbols k I 0 r, ?_⟩
    rw [← quotientOrderHomogeneousAction_compatibility]
    simpa [I, X] using congrArg
      (quotientOrderGradedPieceEquivSymbols k I 0) hr
  obtain ⟨q, hq⟩ := hsurjSymbol (Submodule.Quotient.mk oneH)
  obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective
    (orderSymbolRelation k I 0) q
  rw [homogeneousSymbolAction_mk] at hq
  have hrel : homogeneousRightMul k X P - oneH ∈
      orderSymbolRelation k I 0 :=
    (Submodule.Quotient.eq _).mp hq
  have hJ : ((homogeneousRightMul k X P - oneH :
      MvPolynomial.weightedHomogeneousSubmodule k
        (@orderWeight (n + 1)) 0) : SymbolRing k (n + 1)) ∈
      orderInitialIdeal k I :=
    (mem_orderSymbolRelation_iff_coe_mem_orderInitialIdeal k I 0 _).mp hrel
  have hJ' : (P : SymbolRing k (n + 1)) *
        MvPolynomial.X (.inl (0 : Fin (n + 1))) - 1 ∈
      orderInitialIdeal k I := by
    convert hJ using 1
    simp only [Submodule.coe_sub, coe_homogeneousRightMul]
    rw [show (X : SymbolRing k (n + 1)) =
      MvPolynomial.X (.inl (0 : Fin (n + 1))) by
        exact coe_coordinate_order_symbol k n]
  apply (Ideal.eq_top_iff_one _).2
  rw [show (1 : SymbolRing k (n + 1)) =
      -((P : SymbolRing k (n + 1)) * MvPolynomial.X (.inl 0) - 1) +
        (P : SymbolRing k (n + 1)) * MvPolynomial.X (.inl 0) by ring]
  apply Submodule.add_mem
  · apply Submodule.mem_sup_left
    apply (orderInitialIdeal k I).neg_mem
    exact hJ'
  · apply Submodule.mem_sup_right
    rw [Ideal.mem_span_singleton]
    exact ⟨(P : SymbolRing k (n + 1)), by rw [mul_comm]⟩

/-- Set-theoretic consequence: the canonical order-characteristic support is
disjoint from the distinguished coordinate hyperplane. -/
theorem canonical_orderCharacteristicSupport_disjoint_coordinate_zeroLocus
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : Stafford38.WeylPBWMonicBridge.IsPBWMonicAt k
      (.inr (0 : Fin (n + 1))) N d)
    (hcancel : CoordinateCancellation k n N d) :
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
  have htop := canonical_orderInitialIdeal_sup_coordinate_eq_top
    k n N hd hcancel
  have hle : orderInitialIdeal k (CanonicalIdeal k n N d) ⊔
      Ideal.span {MvPolynomial.X (.inl (0 : Fin (n + 1)))} ≤ p.asIdeal :=
    sup_le hp (Ideal.span_le.mpr hpx)
  rw [htop] at hle
  exact p.2.ne_top (top_unique hle)


end

end Stafford38.CanonicalAxisAvoidanceConsumer
