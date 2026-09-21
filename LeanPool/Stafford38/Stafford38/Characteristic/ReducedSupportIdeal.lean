/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.BaseRelativePoisson
import LeanPool.Stafford38.Stafford38.Characteristic.InitialIdeal

/-!
# The reduced order-characteristic ideal

This file isolates the commutative ideal carried by the reduced order
characteristic support.  It also records its contraction to the base
polynomial ring.  These definitions make the remaining base-relative Gabber
statement concrete; no Poisson-closure theorem is asserted here.
-/

namespace Stafford38.Characteristic.ReducedSupportIdeal

open Stafford38.Characteristic
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section

variable (k : Type*) [Field k] {n : ℕ}

/-- The radical of the differential-order initial ideal. -/
def reducedOrderSupportIdeal
    (I : RightIdeal (PresentedWeyl k n)) : Ideal (SymbolRing k n) :=
  (orderInitialIdeal k I).radical

/-- The order initial ideal is contained in its reduced support ideal. -/
theorem orderInitialIdeal_le_reducedOrderSupportIdeal
    (I : RightIdeal (PresentedWeyl k n)) :
    orderInitialIdeal k I ≤ reducedOrderSupportIdeal k I :=
  Ideal.le_radical

/-- Membership in the reduced support ideal is witnessed by a power in the
order initial ideal. -/
theorem mem_reducedOrderSupportIdeal_iff
    (I : RightIdeal (PresentedWeyl k n)) (P : SymbolRing k n) :
    P ∈ reducedOrderSupportIdeal k I ↔
      ∃ m : ℕ, P ^ m ∈ orderInitialIdeal k I :=
  Iff.rfl

/-- The reduced support ideal is radical. -/
theorem reducedOrderSupportIdeal_isRadical
    (I : RightIdeal (PresentedWeyl k n)) :
    (reducedOrderSupportIdeal k I).IsRadical :=
  Ideal.radical_isRadical _

/-- Passing to the radical does not change the order characteristic support. -/
theorem orderCharacteristicSupport_eq_zeroLocus_reduced
    (I : RightIdeal (PresentedWeyl k n)) :
    orderCharacteristicSupport k I =
      PrimeSpectrum.zeroLocus (reducedOrderSupportIdeal k I) := by
  rw [orderCharacteristicSupport_eq_zeroLocus, reducedOrderSupportIdeal,
    PrimeSpectrum.zeroLocus_radical]

/-- The reduced support ideal is intrinsically the vanishing ideal of the
order characteristic support. -/
theorem vanishingIdeal_orderCharacteristicSupport
    (I : RightIdeal (PresentedWeyl k n)) :
    PrimeSpectrum.vanishingIdeal (orderCharacteristicSupport k I) =
      reducedOrderSupportIdeal k I := by
  rw [orderCharacteristicSupport_eq_zeroLocus, reducedOrderSupportIdeal,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]

/-- The contraction of the reduced support ideal along the base-coordinate
embedding.  This is the precise ideal denoted informally by
`E ∩ k[x₁, …, xₙ]`. -/
def reducedOrderBaseIdeal
    (I : RightIdeal (PresentedWeyl k n)) : Ideal (MvPolynomial (Fin n) k) :=
  (reducedOrderSupportIdeal k I).comap (baseLift :
    MvPolynomial (Fin n) k →ₐ[k] SymbolRing k n).toRingHom

/-- The base-coordinate lift really is an embedding, so the contraction above
is an honest intersection with the base polynomial subring. -/
theorem baseLift_injective :
    Function.Injective
      (baseLift : MvPolynomial (Fin n) k → SymbolRing k n) :=
  MvPolynomial.rename_injective Sum.inl Sum.inl_injective

/-- Base-ideal membership is exactly membership of the lifted polynomial in
the reduced support ideal. -/
theorem mem_reducedOrderBaseIdeal_iff
    (I : RightIdeal (PresentedWeyl k n)) (f : MvPolynomial (Fin n) k) :
    f ∈ reducedOrderBaseIdeal k I ↔
      baseLift f ∈ reducedOrderSupportIdeal k I :=
  Iff.rfl

/-- Contracting after reduction is the same as reducing the contracted order
initial ideal. -/
theorem reducedOrderBaseIdeal_eq_radical_comap
    (I : RightIdeal (PresentedWeyl k n)) :
    reducedOrderBaseIdeal k I =
      ((orderInitialIdeal k I).comap (baseLift :
        MvPolynomial (Fin n) k →ₐ[k] SymbolRing k n).toRingHom).radical := by
  simpa [reducedOrderBaseIdeal, reducedOrderSupportIdeal] using
    Ideal.comap_radical
      ((baseLift : MvPolynomial (Fin n) k →ₐ[k] SymbolRing k n).toRingHom)
      (orderInitialIdeal k I)

/-- The contracted base ideal is radical. -/
theorem reducedOrderBaseIdeal_isRadical
    (I : RightIdeal (PresentedWeyl k n)) :
    (reducedOrderBaseIdeal k I).IsRadical := by
  rw [reducedOrderBaseIdeal_eq_radical_comap]
  exact Ideal.radical_isRadical _

/-- The base contraction may be recovered directly from the characteristic
support, without reference to a chosen presentation of the radical. -/
theorem reducedOrderBaseIdeal_eq_comap_vanishingIdeal
    (I : RightIdeal (PresentedWeyl k n)) :
    reducedOrderBaseIdeal k I =
      (PrimeSpectrum.vanishingIdeal (orderCharacteristicSupport k I)).comap
        (baseLift : MvPolynomial (Fin n) k →ₐ[k] SymbolRing k n).toRingHom := by
  rw [vanishingIdeal_orderCharacteristicSupport]
  rfl

/-- A base polynomial lies in the contracted reduced ideal exactly when its
lift vanishes at every prime of the order characteristic support. -/
theorem mem_reducedOrderBaseIdeal_iff_forall_support
    (I : RightIdeal (PresentedWeyl k n)) (f : MvPolynomial (Fin n) k) :
    f ∈ reducedOrderBaseIdeal k I ↔
      ∀ p ∈ orderCharacteristicSupport k I, baseLift f ∈ p.asIdeal := by
  rw [reducedOrderBaseIdeal_eq_comap_vanishingIdeal, Ideal.mem_comap,
    PrimeSpectrum.mem_vanishingIdeal]
  rfl

/-- The remaining Gabber condition for the reduced characteristic ideal,
written entirely in terms of its base contraction.  This is a reformulation,
not a proof, of base-relative Poisson closure. -/
theorem isBaseRelativePoisson_reduced_iff
    (I : RightIdeal (PresentedWeyl k n)) :
    IsBaseRelativePoisson (reducedOrderSupportIdeal k I) ↔
      ∀ f ∈ reducedOrderBaseIdeal k I,
        ∀ g ∈ reducedOrderSupportIdeal k I,
          poissonBracket (baseLift f) g ∈ reducedOrderSupportIdeal k I := by
  rfl


end

end Stafford38.Characteristic.ReducedSupportIdeal
