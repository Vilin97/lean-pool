/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.UniversalAssembly
public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalUnitCoordinatePreimage
public import LeanPool.Stafford38.Stafford38.Geometry.ConormalAxisContradiction
public import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalDirection


/-!
# Conditional Laurent-direction skeleton for canonical support vanishing

This file retains a conditional Laurent-direction assembly between the literal
canonical quotient and `CanonicalSupportVanishing`. Its interfaces are
discharged downstream; they do not mark gaps in the unconditional theorem.
Over an algebraically
closed field, one order-zero coordinate predecessor of the unit supplies axis
avoidance, a Gabber/scalar-extension input makes the canonical fibre symbol
vanish on the Laurent equation-conormal locus, and the asymptotic producer supplies a
Laurent-generic conormal whose regular fibre residue is the forbidden pure
momentum direction. A fourth input explicitly isolates descent from algebraic
closure back to an arbitrary characteristic-zero field.

No finite phase-space limit is asserted: the Laurent base coordinates may have
poles, and only the fibre residue is specialized.
-/

@[expose] public section

namespace Stafford38.CanonicalSupportVanishingReduction

open Stafford38
open Stafford38.CanonicalAxisAvoidanceConsumer
open Stafford38.CanonicalUnitCoordinatePreimage
open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicHomogeneousChart
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.ConormalAxisContradiction
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylFiltration
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

/-- Universal production of the weakest filtered input used by terminal axis
avoidance: one order-zero coordinate predecessor of the quotient unit. -/
def CanonicalStrictUnitCoordinatePreimage : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    0 < N → IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
      StrictUnitCoordinatePreimage k n N d

/-- The pure momentum axis in the fibre-coordinate space. -/
def pureMomentumFibreAxis (k : Type u) [Field k] (n : ℕ) :
    Fin (n + 1) → k :=
  fun i ↦ if i = 0 then 1 else 0

/-- Packaged Laurent symbol control from Gabber, scalar extension, fibre-only
symbol extraction, and the checked conormal containment. -/
def CanonicalLaurentSymbolControl : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    0 < N → IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
      ∃ P : MvPolynomial (Fin (n + 1)) k,
        fibreLift P = presentedPrincipalComponent k orderWeight N d ∧
        ∀ q ∈ equationConormalLocus
            ((reducedOrderBaseIdeal k
              (canonicalRightIdeal (presentedCoordinate k n) d N)).map
                (scalarPolynomialMap
                  (k := k) (K := LaurentSeries k) (Fin (n + 1)))),
          MvPolynomial.eval₂ (algebraMap k (LaurentSeries k)) q
            (fibreLift P) = 0

/-- The remaining global geometric producer.  Its base coordinates stay in
Laurent series; only its regular fibre covector specializes to the pure
momentum axis. -/
def CanonicalAsymptoticLaurentProducer : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    0 < N → IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
    Disjoint
      (orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) →
    (orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N)).Nonempty →
    ∃ (y : Fin (n + 1) → LaurentSeries k)
      (xi : Fin (n + 1) → PowerSeries k),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) ∈
        equationConormalLocus
          ((reducedOrderBaseIdeal k
            (canonicalRightIdeal (presentedCoordinate k n) d N)).map
              (scalarPolynomialMap
                (k := k) (K := LaurentSeries k) (Fin (n + 1)))) ∧
      residueColumn xi = pureMomentumFibreAxis k n

/-- Canonical support vanishing restricted to algebraically closed
characteristic-zero fields. -/
def AlgebraicallyClosedCanonicalSupportVanishing : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    0 < N → IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
      orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N) = ∅

/-- The still-separate Weyl/base-change descent theorem.  This input must be
proved by transporting the canonical quotient and its initial ideal through
algebraic closure; geometric support descent alone does not supply it. -/
def CanonicalSupportDescent : Prop :=
  AlgebraicallyClosedCanonicalSupportVanishing.{u} →
    Stafford38.UniversalAssembly.CanonicalSupportVanishing.{u}

/-- The conditional contradiction skeleton over algebraically closed fields.
Its asymptotic input must be proved from divisor geometry without using the
desired support-vanishing conclusion. -/
theorem algebraicallyClosedCanonicalSupportVanishing_of_three_inputs
    (hunit : CanonicalStrictUnitCoordinatePreimage.{u})
    (hcontrol : CanonicalLaurentSymbolControl.{u})
    (hasymptotic : CanonicalAsymptoticLaurentProducer.{u}) :
    AlgebraicallyClosedCanonicalSupportVanishing.{u} := by
  intro k _ _ _ n N d hN hd
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  have hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) := by
    exact
      canonical_orderCharacteristicSupport_disjoint_coordinate_zeroLocus_of_strictUnit
        k n N (hunit k n N d hN hd)
  by_contra hsupp
  have hnonempty : (orderCharacteristicSupport k I).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hsupp
  rcases hcontrol k n N d hN hd with ⟨P, hP, hvanishes⟩
  rcases hasymptotic k n N d hN hd hdisjoint hnonempty with
    ⟨y, xi, hgeneric, hresidue⟩
  apply false_of_fibreOnly_symbol_one_on_residue_and_vanishes_on_laurentConormal
    (reducedOrderBaseIdeal k I) P (pureMomentumFibreAxis k n) y xi
    hgeneric hresidue hvanishes
  have hcanonical := canonical_orderPrincipalComponent_eval_pureMomentumAxis
    n N hd
  have hsplit : Sum.elim (fun _ : Fin (n + 1) ↦ (0 : k))
      (pureMomentumFibreAxis k n) =
      axisPoint k (.inr (0 : Fin (n + 1))) := by
    funext i
    rcases i with i | i
    · simp [axisPoint]
    · simp [axisPoint, pureMomentumFibreAxis]
  rw [← hP] at hcanonical
  have heval := eval₂_fibreLift (K := k) P
    (fun _ : Fin (n + 1) ↦ (0 : k)) (pureMomentumFibreAxis k n)
  rw [hsplit] at heval
  simpa only [← MvPolynomial.aeval_def, MvPolynomial.aeval_eq_eval] using
    heval.symm.trans hcanonical

/-- Consequently the exact Stafford statement follows from the three
algebraically closed inputs and the separate support-descent theorem. -/
theorem universalStatement_of_four_inputs
    (hunit : CanonicalStrictUnitCoordinatePreimage.{u})
    (hcontrol : CanonicalLaurentSymbolControl.{u})
    (hasymptotic : CanonicalAsymptoticLaurentProducer.{u})
    (hdescent : CanonicalSupportDescent.{u}) :
    Stafford38.UniversalStatement.{u} :=
  Stafford38.UniversalAssembly.universalStatement_of_canonicalSupportVanishing
    (hdescent
      (algebraicallyClosedCanonicalSupportVanishing_of_three_inputs
        hunit hcontrol hasymptotic))


end

end Stafford38.CanonicalSupportVanishingReduction
