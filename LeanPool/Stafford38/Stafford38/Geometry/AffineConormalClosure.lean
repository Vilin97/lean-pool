/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.Nullstellensatz
public import LeanPool.Stafford38.Stafford38.Geometry.AffineConormalSpan


/-!
# Algebraic closure of the equation-defined affine conormal locus

The equation-defined conormal locus over the contracted base zero set lies in
the reduced order support under the exact base-relative Gabber fragment. Since
that support is a polynomial zero locus, the algebraic closure hull of the
conormal locus lies there as well.

This file uses the closure operator `V(I(S))` on field-valued affine points.
It does not identify a smooth scheme-theoretic conormal bundle or prove the
asymptotic conormal theorem at infinity.
-/

@[expose] public section

namespace Stafford38.Geometry.AffineConormalClosure

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/-- Phase points whose base coordinate lies in `V(I)` and whose fibre
coordinate belongs to the equation-defined embedded conormal at that point. -/
def equationConormalLocus (I : Ideal (MvPolynomial (Fin n) k)) :
    Set (PhaseVar n → k) :=
  {q | (∀ f ∈ I,
      MvPolynomial.eval (fun i => q (Sum.inl i)) f = 0) ∧
    coordinateCovector (fun i => q (Sum.inr i)) ∈
      affineConormalSpace (fun i => q (Sum.inl i)) I}

/-- Algebraic closure hull of the equation-defined conormal locus. -/
def equationConormalClosure (I : Ideal (MvPolynomial (Fin n) k)) :
    Set (PhaseVar n → k) :=
  MvPolynomial.zeroLocus k
    (MvPolynomial.vanishingIdeal k (equationConormalLocus I))

/-- A subset of a polynomial zero locus has its algebraic closure hull in the
same zero locus. -/
theorem zeroLocus_vanishingIdeal_mono_of_subset_zeroLocus
    (S : Set (PhaseVar n → k)) (J : Ideal (SymbolRing k n))
    (h : S ⊆ MvPolynomial.zeroLocus k J) :
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k S) ⊆
      MvPolynomial.zeroLocus k J := by
  apply MvPolynomial.zeroLocus_anti_mono
  exact MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal.mp h

/-- Under the exact base-relative Gabber condition, every equation-defined
conormal point over the contracted base zero locus lies in the reduced order
support. -/
theorem equationConormalLocus_subset_reducedOrderSupport
    [CharZero k]
    (W : RightIdeal (PresentedWeyl k n))
    (hJ : IsBaseRelativePoisson (reducedOrderSupportIdeal k W)) :
    equationConormalLocus (reducedOrderBaseIdeal k W) ⊆
      MvPolynomial.zeroLocus k (reducedOrderSupportIdeal k W) := by
  intro q hq
  let y : Fin n → k := fun i => q (Sum.inl i)
  let ξ : Fin n → k := fun i => q (Sum.inr i)
  have hs := reducedOrderBaseZero_affineConormal_coordinatePoint_isCommonZero
    W hJ y hq.1 ξ hq.2
  have hsplit : Sum.elim y ξ = q := by
    funext i
    rcases i with i | i <;> rfl
  rw [← hsplit]
  exact hs

/-- The algebraic closure hull of the equation-defined conormal locus remains
inside the reduced order support. -/
theorem equationConormalClosure_subset_reducedOrderSupport
    [CharZero k]
    (W : RightIdeal (PresentedWeyl k n))
    (hJ : IsBaseRelativePoisson (reducedOrderSupportIdeal k W)) :
    equationConormalClosure (reducedOrderBaseIdeal k W) ⊆
      MvPolynomial.zeroLocus k (reducedOrderSupportIdeal k W) := by
  exact zeroLocus_vanishingIdeal_mono_of_subset_zeroLocus
    (equationConormalLocus (reducedOrderBaseIdeal k W))
    (reducedOrderSupportIdeal k W)
    (equationConormalLocus_subset_reducedOrderSupport W hJ)


end

end Stafford38.Geometry.AffineConormalClosure
