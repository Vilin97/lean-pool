/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalNoncharacteristicCancellation
import LeanPool.Stafford38.Stafford38.Weyl.CoordinateCommutatorSymbol
import LeanPool.Stafford38.Stafford38.Weyl.FilteredCommutator

/-!
# A concrete filtered criterion for canonical monic saturation

For every degree, ordinary injectivity of coordinate multiplication on the
canonical right quotient, together with coordinate preimages that preserve
strict lower-order pieces, implies the exact cancellation statement on every
actual associated-graded piece.  This is an ambient filtered/Ore criterion:
it does not mention the initial ideal or assume its saturation.

For a Bernstein-monic operator of degree one, commutation with the selected
coordinate is exactly `-1`.  Hence the two literal canonical generators
`d` and `x * d` already generate the unit right ideal.  This proves coordinate
saturation (and therefore strict noncharacteristic cancellation) without
assuming a generic D-module inverse-image theorem.

The argument deliberately stops at degree one.  For degree at least two, the
same commutator has positive differential order; proving saturation then needs
an order-preserving reduction of those higher commutators.  Existing monic Ore
division and the positive Euler residue provide unrestricted coordinate
preimages, but do not provide the strict differential-order estimate isolated
below.
-/

namespace Stafford38.CanonicalMonicSaturation

open Stafford38.CanonicalAxisAvoidanceConsumer
open Stafford38.CanonicalNoncharacteristicCancellation
open Stafford38.Characteristic
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylCoordinateCommutatorSymbol
open Stafford38.WeylEulerResidue
open Stafford38.WeylFilteredCommutator
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport

noncomputable section

universe u

variable (k : Type u) [Field k] [Algebra ℚ k]

private abbrev CanonicalIdeal (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :=
  canonicalRightIdeal (presentedCoordinate k n) d N

/-- The concrete filtered estimate missing from unrestricted Euler
surjectivity: every class represented below order `m` has a coordinate
predecessor represented below the same order.  This is stated in the ambient
Weyl algebra, not in the associated graded or the initial ideal. -/
def StrictLowerCoordinatePreimages (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) : Prop :=
  ∀ (m : ℕ) (l : PresentedWeyl k (n + 1)),
    l ∈ presentedStrictLowerPiece k orderWeight m →
    ∃ y : PresentedWeyl k (n + 1),
      y ∈ presentedStrictLowerPiece k orderWeight m ∧
      qmk (CanonicalIdeal k n N d)
          (y * presentedCoordinate k n) =
        qmk (CanonicalIdeal k n N d) l

/-- A genuinely general filtered reduction.  Ordinary cancellation on the
canonical quotient and strict-order coordinate division together imply the
load-bearing cancellation theorem on every filtration degree. -/
theorem coordinateCancellation_of_quotient_injective_of_strict_preimages
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hinjective : Function.Injective
      (rightMul (CanonicalIdeal k n N d) (presentedCoordinate k n)))
    (hstrict : StrictLowerCoordinatePreimages k n N d) :
    CoordinateCancellation k n N d := by
  intro m z hz hzx
  obtain ⟨i, hi, l, hl, hil⟩ := Submodule.mem_sup.mp hzx
  obtain ⟨y, hy, hyx⟩ := hstrict m l hl
  have hzxl : qmk (CanonicalIdeal k n N d)
        (z * presentedCoordinate k n) =
      qmk (CanonicalIdeal k n N d) l := by
    apply (Submodule.Quotient.eq (CanonicalIdeal k n N d)).2
    rw [← hil]
    simpa using hi
  have hxy : rightMul (CanonicalIdeal k n N d)
        (presentedCoordinate k n) (qmk (CanonicalIdeal k n N d) z) =
      rightMul (CanonicalIdeal k n N d)
        (presentedCoordinate k n) (qmk (CanonicalIdeal k n N d) y) := by
    rw [← qmk_right_mul, ← qmk_right_mul, hzxl, hyx]
  have hzy : qmk (CanonicalIdeal k n N d) z =
      qmk (CanonicalIdeal k n N d) y := hinjective hxy
  have hdiff : z - y ∈ CanonicalIdeal k n N d :=
    (Submodule.Quotient.eq (CanonicalIdeal k n N d)).mp hzy
  rw [show z = (z - y) + y by abel]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left hdiff)
    (Submodule.mem_sup_right hy)

/-- Actual-graded form of the general filtered reduction. -/
theorem canonical_graded_coordinateAction_injective_of_quotient_injective_of_strict_preimages
    (n N m : ℕ) (d : PresentedWeyl k (n + 1))
    (hinjective : Function.Injective
      (rightMul (CanonicalIdeal k n N d) (presentedCoordinate k n)))
    (hstrict : StrictLowerCoordinatePreimages k n N d) :
    Function.Injective (canonicalGradedCoordinateAction k n N m d) := by
  exact (coordinateCancellation_iff_forall_graded_injective k n N d).mp
    (coordinateCancellation_of_quotient_injective_of_strict_preimages
      k n N d hinjective hstrict) m

/-- Monicity supplies the unfiltered version of
`StrictLowerCoordinatePreimages`: every quotient class has some coordinate
predecessor.  The absent conclusion is precisely that a lower-order class can
be assigned a lower-order predecessor. -/
theorem canonical_unrestricted_coordinate_preimages_of_monic
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (z : PresentedWeyl k (n + 1)) :
    ∃ y : PresentedWeyl k (n + 1),
      qmk (CanonicalIdeal k n N d)
          (y * presentedCoordinate k n) =
        qmk (CanonicalIdeal k n N d) z := by
  have hsurjective :=
    presentedCanonicalRightQuotient_rightMul_coordinate_surjective
      (k := k) n N hd
  obtain ⟨q, hq⟩ := hsurjective (qmk (CanonicalIdeal k n N d) z)
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
    (CanonicalIdeal k n N d) q
  refine ⟨y, ?_⟩
  rw [qmk_right_mul]
  exact hq

private theorem degree_eq_one_of_order_one_of_fibreOnly
    {n : ℕ} {P : SymbolRing k n} {m : PhaseVar n →₀ ℕ}
    (hm : P.coeff m ≠ 0)
    (hhom : MvPolynomial.IsWeightedHomogeneous (@orderWeight n) P 1)
    (hfibre : IsFibreOnly k P) :
    m.degree = 1 := by
  have horder : monomialWeight (@orderWeight n) m = 1 := by
    exact hhom hm
  rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply]
  simp only [smul_eq_mul, mul_one]
  rw [monomialWeight] at horder
  calc
    m.sum (fun _ e ↦ e) =
        m.sum (fun i e ↦ e * orderWeight i) := by
          apply Finsupp.sum_congr
          intro i hi
          rcases i with i | i
          · have hz := hfibre m hm i
            simp [hz, orderWeight, fibreWeight]
          · simp [orderWeight, fibreWeight]
    _ = 1 := horder

private theorem exponent_eq_selected_of_order_one_of_selected_ne_zero
    {n : ℕ} {P : SymbolRing k n} {m : PhaseVar n →₀ ℕ}
    (t : Fin n)
    (hm : P.coeff m ≠ 0)
    (hhom : MvPolynomial.IsWeightedHomogeneous (@orderWeight n) P 1)
    (hfibre : IsFibreOnly k P)
    (hmt : m (.inr t) ≠ 0) :
    m = Finsupp.single (.inr t) 1 := by
  have hdegree := degree_eq_one_of_order_one_of_fibreOnly k hm hhom hfibre
  have hdecomp := Finsupp.single_add_erase (.inr t) m
  have hdegdecomp := congrArg Finsupp.degree hdecomp
  rw [map_add Finsupp.degree] at hdegdecomp
  have hmtle := Finsupp.le_degree (.inr t) m
  rw [hdegree] at hmtle
  have hmt1 : m (.inr t) = 1 :=
    Nat.le_antisymm hmtle (Nat.one_le_iff_ne_zero.mpr hmt)
  have heraseDegree : (m.erase (.inr t)).degree = 0 := by
    simpa [hdegree, hmt1] using hdegdecomp
  have herase : m.erase (.inr t) = 0 :=
    (Finsupp.degree_eq_zero_iff _).mp heraseDegree
  rw [← hdecomp, hmt1, herase, add_zero]

/-- A fibre-only order-homogeneous linear symbol whose selected momentum
coefficient is one has selected partial derivative one. -/
theorem pderiv_eq_one_of_order_one_fibreOnly
    {n : ℕ} (t : Fin n) (P : SymbolRing k n)
    (hhom : MvPolynomial.IsWeightedHomogeneous (@orderWeight n) P 1)
    (hfibre : IsFibreOnly k P)
    (hcoeff : P.coeff (Finsupp.single (.inr t) 1) = 1) :
    MvPolynomial.pderiv (.inr t) P = 1 := by
  classical
  let Q := P - MvPolynomial.X (.inr t)
  have hQt : (.inr t : PhaseVar n) ∉ Q.vars := by
    intro ht
    rw [MvPolynomial.mem_vars] at ht
    obtain ⟨m, hmQ, htm⟩ := ht
    have hmQne : Q.coeff m ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hmQ
    have hmt : m (.inr t) ≠ 0 := Finsupp.mem_support_iff.mp htm
    by_cases hm : m = Finsupp.single (.inr t) 1
    · subst m
      dsimp [Q] at hmQne
      rw [MvPolynomial.coeff_sub, hcoeff, MvPolynomial.coeff_X] at hmQne
      simp at hmQne
    · have hPzero : P.coeff m = 0 := by
        by_contra hP
        exact hm
          (exponent_eq_selected_of_order_one_of_selected_ne_zero
            k t hP hhom hfibre hmt)
      have hXzero : (MvPolynomial.X (.inr t) : SymbolRing k n).coeff m = 0 := by
        rw [MvPolynomial.coeff_X]
        simp [Ne.symm hm]
      dsimp [Q] at hmQne
      rw [MvPolynomial.coeff_sub, hPzero, hXzero, sub_zero] at hmQne
      exact hmQne rfl
  have hQderiv : MvPolynomial.pderiv (.inr t : PhaseVar n) Q = 0 :=
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hQt
  have hdecomp : P = Q + MvPolynomial.X (.inr t) := by
    dsimp [Q]
    abel
  rw [hdecomp, map_add, hQderiv, MvPolynomial.pderiv_X_self, zero_add]

/-- In canonical Bernstein degree one, the selected coordinate commutator is
the scalar `-1`.  This is the strict low-order replacement for the missing
higher-order division estimate. -/
theorem coordinate_commutator_eq_neg_one_degree_one
    (n : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) 1 d) :
    Stafford.commutator (presentedCoordinate k n) d = -1 := by
  let P := presentedPrincipalComponent k (@orderWeight (n + 1)) 1 d
  have hdOrder : d ∈ orderPiece k (n + 1) 1 :=
    bernsteinPiece_le_orderPiece k (n + 1) 1 hd.1
  have hxOrder : presentedCoordinate k n ∈ orderPiece k (n + 1) 0 :=
    presentedCoordinate_mem_orderPiece_zero k n
  have hcommOrder :
      Stafford.commutator (presentedCoordinate k n) d ∈
        orderPiece k (n + 1) 0 := by
    simpa using commutator_mem_orderPiece_pred k hxOrder hdOrder
  have hhom : MvPolynomial.IsWeightedHomogeneous (@orderWeight (n + 1)) P 1 := by
    exact MvPolynomial.weightedHomogeneousComponent_mem _ _ _
  have hfibre : IsFibreOnly k P :=
    canonical_orderPrincipalComponent_isFibreOnly k n 1 hd
  have hcoeff :
      P.coeff (Finsupp.single (.inr (0 : Fin (n + 1))) 1) = 1 :=
    canonical_orderPrincipalComponent_pureMomentumCoefficient k n 1 hd
  have hpderiv :
      MvPolynomial.pderiv (.inr (0 : Fin (n + 1))) P = 1 :=
    pderiv_eq_one_of_order_one_fibreOnly k 0 P hhom hfibre hcoeff
  have hprincipal :
      presentedPrincipalComponent k (@orderWeight (n + 1)) 0
          (Stafford.commutator (presentedCoordinate k n) d) = -1 := by
    rw [principalComponent_coordinate_commutator_arbitrary]
    rw [Stafford38.WeylCommutatorSymbol.poissonBracket_newestCoordinate,
      hpderiv]
  have hnegOneOrder : (-1 : PresentedWeyl k (n + 1)) ∈
      orderPiece k (n + 1) 0 := by
    exact (orderPiece k (n + 1) 0).neg_mem
      (Stafford38.CharacteristicAssociatedGradedModule.orderPieceOne
        (n := n + 1) k).property
  have hdiffOrder :
      Stafford.commutator (presentedCoordinate k n) d - (-1) ∈
        orderPiece k (n + 1) 0 :=
    (orderPiece k (n + 1) 0).sub_mem hcommOrder hnegOneOrder
  have hdiffPrincipal :
      presentedPrincipalComponent k (@orderWeight (n + 1)) 0
          (Stafford.commutator (presentedCoordinate k n) d - (-1)) = 0 := by
    rw [map_sub, hprincipal]
    change -1 - presentedPrincipalComponent k orderWeight 0
      (-1 : PresentedWeyl k (n + 1)) = 0
    rw [map_neg]
    have honepc : presentedPrincipalComponent k orderWeight 0
        (1 : PresentedWeyl k (n + 1)) = 1 := by
      exact Stafford38.CharacteristicAssociatedGradedModule.presentedPrincipalComponent_orderPieceOne
        (n := n + 1) k
    rw [honepc]
    simp
  have hlower :=
    (presentedPrincipalComponent_eq_zero_iff_mem_strictLower
      k (@orderWeight (n + 1)) _ hdiffOrder).mp hdiffPrincipal
  have hdiff : Stafford.commutator (presentedCoordinate k n) d - (-1) = 0 := by
    simpa [presentedStrictLowerPiece] using hlower
  exact sub_eq_zero.mp hdiff

/-- Every canonical degree-one monic presentation is already the unit right
ideal.  Both terms in the commutator are literal right-ideal elements. -/
theorem canonicalRightIdeal_eq_top_degree_one
    (n : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) 1 d) :
    CanonicalIdeal k n 1 d = ⊤ := by
  apply top_unique
  intro z hz
  have hxd : presentedCoordinate k n * d ∈ CanonicalIdeal k n 1 d := by
    simpa using secondGenerator_mem (presentedCoordinate k n) d 1
  have hdx : d * presentedCoordinate k n ∈ CanonicalIdeal k n 1 d := by
    exact (CanonicalIdeal k n 1 d).smul_mem
      (MulOpposite.op (presentedCoordinate k n))
      (firstGenerator_mem (presentedCoordinate k n) d 1)
  have hneg : (-1 : PresentedWeyl k (n + 1)) ∈ CanonicalIdeal k n 1 d := by
    rw [← coordinate_commutator_eq_neg_one_degree_one k n hd]
    exact (CanonicalIdeal k n 1 d).sub_mem hxd hdx
  have hone : (1 : PresentedWeyl k (n + 1)) ∈ CanonicalIdeal k n 1 d := by
    simpa using (CanonicalIdeal k n 1 d).neg_mem hneg
  simpa using (CanonicalIdeal k n 1 d).smul_mem (MulOpposite.op z) hone

/-- The ordinary coordinate action on the degree-one canonical quotient is
injective.  This is the first half of the general filtered interface. -/
theorem canonical_quotient_coordinate_injective_degree_one
    (n : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) 1 d) :
    Function.Injective
      (rightMul (CanonicalIdeal k n 1 d) (presentedCoordinate k n)) := by
  intro q₁ q₂ hq
  obtain ⟨z₁, rfl⟩ := Submodule.Quotient.mk_surjective
    (CanonicalIdeal k n 1 d) q₁
  obtain ⟨z₂, rfl⟩ := Submodule.Quotient.mk_surjective
    (CanonicalIdeal k n 1 d) q₂
  apply (Submodule.Quotient.eq (CanonicalIdeal k n 1 d)).2
  rw [canonicalRightIdeal_eq_top_degree_one k n hd]
  exact Submodule.mem_top

/-- Strict lower-order coordinate preimages in degree one.  Together with
`canonical_quotient_coordinate_injective_degree_one`, this instantiates the
general filtered reduction and makes the unit-ideal case a reusable base
interface rather than an isolated shortcut. -/
theorem canonical_strictLowerCoordinatePreimages_degree_one
    (n : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) 1 d) :
    StrictLowerCoordinatePreimages k n 1 d := by
  intro m l hl
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  apply (Submodule.Quotient.eq (CanonicalIdeal k n 1 d)).2
  rw [canonicalRightIdeal_eq_top_degree_one k n hd]
  exact Submodule.mem_top

/-- The canonical order initial ideal is the unit ideal in degree one. -/
theorem canonical_orderInitialIdeal_eq_top_degree_one
    (n : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) 1 d) :
    orderInitialIdeal k (CanonicalIdeal k n 1 d) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).2
  have honeI : (1 : PresentedWeyl k (n + 1)) ∈ CanonicalIdeal k n 1 d := by
    rw [canonicalRightIdeal_eq_top_degree_one k n hd]
    exact Submodule.mem_top
  have hone := orderPrincipalComponent_mem_initialIdeal k
    (CanonicalIdeal k n 1 d) (1 : PresentedWeyl k (n + 1))
    (Stafford38.CharacteristicAssociatedGradedModule.orderPieceOne
      (n := n + 1) k).property honeI
  have honepc : presentedPrincipalComponent k orderWeight 0
      (1 : PresentedWeyl k (n + 1)) = 1 := by
    exact Stafford38.CharacteristicAssociatedGradedModule.presentedPrincipalComponent_orderPieceOne
      (n := n + 1) k
  rw [honepc] at hone
  exact hone

/-- **Concrete producer.** For every canonical Bernstein-monic operator of
degree one, the actual order initial ideal is saturated by the selected
coordinate symbol. -/
theorem canonical_orderInitialIdeal_coordinate_saturated_degree_one
    (n : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) 1 d) :
    (orderInitialIdeal k (CanonicalIdeal k n 1 d)).colon
        ({MvPolynomial.X (Sum.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1))) =
      orderInitialIdeal k (CanonicalIdeal k n 1 d) := by
  rw [canonical_orderInitialIdeal_eq_top_degree_one k n hd]
  apply le_antisymm le_top
  intro r hr
  rw [Submodule.mem_colon]
  intro p hp
  exact Submodule.mem_top

/-- The degree-one producer reaches the actual order-characteristic support. -/
theorem canonical_orderCharacteristicSupport_eq_empty_degree_one
    (n : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) 1 d) :
    orderCharacteristicSupport k
        (CanonicalIdeal k n 1 d) = ∅ := by
  apply (orderCharacteristicSupport_eq_empty_iff k
    (CanonicalIdeal k n 1 d)).2
  exact canonical_orderInitialIdeal_eq_top_degree_one k n hd

/-- The degree-one case yields the literal fixed-source Stafford certificate. -/
theorem exists_fixedSource_certificate_degree_one
    (n : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) 1 d) :
    ∃ R S : PresentedWeyl k (n + 1),
      (1 : PresentedWeyl k (n + 1)) =
        d * R + presentedCoordinate k n * d * S := by
  let I := CanonicalIdeal k n 1 d
  have hone : (1 : PresentedWeyl k (n + 1)) ∈ I := by
    change (1 : PresentedWeyl k (n + 1)) ∈
      CanonicalIdeal k n 1 d
    rw [canonicalRightIdeal_eq_top_degree_one k n hd]
    exact Submodule.mem_top
  change (1 : PresentedWeyl k (n + 1)) ∈
    canonicalRightIdeal (presentedCoordinate k n) d 1 at hone
  have hone' : (1 : PresentedWeyl k (n + 1)) ∈
    Submodule.span (PresentedWeyl k (n + 1))ᵐᵒᵖ
      ({d, presentedCoordinate k n * d} :
        Set (PresentedWeyl k (n + 1))) := by
    simpa [canonicalRightIdeal, pow_one] using hone
  rcases Submodule.mem_span_pair.mp hone' with ⟨r, s, hrs⟩
  refine ⟨r.unop, s.unop, ?_⟩
  simpa [op_smul_eq_mul] using hrs.symm

/-- Equivalent actual-graded formulation of the degree-one producer. -/
theorem canonical_graded_coordinateAction_injective_degree_one
    (n m : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) 1 d) :
    Function.Injective
      (canonicalGradedCoordinateAction k n 1 m d) := by
  exact
    canonical_graded_coordinateAction_injective_of_quotient_injective_of_strict_preimages
      k n 1 m d
      (canonical_quotient_coordinate_injective_degree_one k n hd)
      (canonical_strictLowerCoordinatePreimages_degree_one k n hd)


end

end Stafford38.CanonicalMonicSaturation
