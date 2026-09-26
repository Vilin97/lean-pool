/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.IrreducibleOmnificIntegers
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.FiniteClassPrimality

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncationResidue

/-!
# Primality for finitely many support classes

Integer constants are primal in the bounded Hahn integer part. The generic finite-class theorem
then gives primality for omnific integers whose support meets finitely many Archimedean classes.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries

namespace HahnSeries.Nonpositive

variable {K G R : Type*} {κ : Cardinal}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R] [Fact (ℵ₀ < κ)]
variable (Z : Subring R) (hZ : ∀ r : R, r ∈ Z ↔ ∃ z : ℤ, (z : R) = r)
include hZ

/-- Every integer constant is primal in the bounded integer part over the integers. -/
theorem isPrimal_intCast [CharZero R] (z : ℤ) :
    IsPrimal (z : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) := by
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun z : ℤ ↦ IsPrimal
      (z : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)) z ?_ ?_ ?_
  · simpa using (isPrimal_zero : IsPrimal
      (0 : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z))
  · intro a ha
    exact (ha.map (Int.castRingHom _)).isPrimal
  · intro a p _ hp ha
    rw [Int.cast_mul]
    exact (prime_intCast Z hZ hp).isPrimal.mul ha

/-- A bounded integer-part series of order zero is an integer constant and hence primal. -/
theorem isPrimal_of_order_eq_zero [CharZero R]
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x :
      Nonpositive G R) : R⟦G⟧).order = 0) : IsPrimal x := by
  let xN := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x
  have hconstant : (xN : R⟦G⟧) = HahnSeries.C ((xN : R⟦G⟧).coeff 0) := by
    ext g
    by_cases hg : g = 0
    · subst g
      simp
    · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg]
      by_contra hcoeff
      have hgNonpos : g ≤ 0 := support_subset xN ((HahnSeries.mem_support _ _).mpr hcoeff)
      have hzeroLe : 0 ≤ g := horder ▸ HahnSeries.order_le_of_coeff_ne_zero hcoeff
      exact hg (le_antisymm hgNonpos hzeroLe)
  have hcoeffMem : (xN : R⟦G⟧).coeff 0 ∈ Z := by
    simpa only [xN, CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom] using
      ((mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2).2
  obtain ⟨z, hz⟩ := (hZ _).mp hcoeffMem
  have hxz : x = (z : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) := by
    apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective Z
    rw [map_intCast]
    apply Subtype.ext
    change (xN : R⟦G⟧) = HahnSeries.C (z : R)
    rw [hconstant, hz]
  rw [hxz]
  exact isPrimal_intCast Z hZ z

end HahnSeries.Nonpositive

namespace Surreal

universe u

/-- A bounded signed surreal integer-part series whose support meets only finitely many
Archimedean classes is primal. -/
theorem isPrimal_cardSuppLTTruncationIntegerPart_of_supportArchimedeanClasses_finite
    (a : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := Surreal.{u}) (R := ℝ) (κ := smallSupportCardinal.{u}) realIntegerSubring)
    (hfinite : (HahnSeries.Nonpositive.supportArchimedeanClasses
      (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
        realIntegerSubring a)).Finite) : IsPrimal a := by
  apply HahnSeries.Nonpositive.isPrimal_of_supportArchimedeanClasses_finite_of_reduced
    realIntegerSubring archimedeanStrata
  · exact HahnSeries.Nonpositive.isPrimal_of_order_eq_zero realIntegerSubring
      OmnificInteger.realIntegerSubring_mem_iff
  · intro y hyOrder hyReduced
    have hy0 : HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
        realIntegerSubring y ≠ 0 := by
      intro hyzero
      apply hyOrder
      rw [hyzero, Subring.coe_zero, HahnSeries.order_zero]
    let c := HahnSeries.Nonpositive.leadingClass
      (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
        realIntegerSubring y) hyOrder
    exact HahnSeries.Nonpositive.isPrimal_of_isReduced_of_leadingClass_orderIso_real
      archimedeanStrata realIntegerSubring y hy0 hyOrder hyReduced
        (assumptionA2AtFiniteClass realIntegerSubring c)
        (stratumOrderAddMonoidIsoReal archimedeanStrata c)
  · exact hfinite

/-- The finite-class endpoint stated directly using the underlying support image. -/
theorem isPrimal_cardSuppLTTruncationIntegerPart_of_image_mk_support_finite
    (a : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := Surreal.{u}) (R := ℝ) (κ := smallSupportCardinal.{u}) realIntegerSubring)
    (hfinite : (ArchimedeanClass.mk '' (a : ℝ⟦Surreal.{u}⟧).support).Finite) :
    IsPrimal a := by
  apply isPrimal_cardSuppLTTruncationIntegerPart_of_supportArchimedeanClasses_finite
  rw [HahnSeries.CardSuppLTTruncationIntegerPart.supportArchimedeanClasses_toNonpositiveRingHom]
  exact hfinite

end Surreal

namespace Surreal.OmnificInteger

universe u

open HahnSeries.Nonpositive

/-- Changing from Conway normal-form exponents to signed Hahn exponents preserves the set of
support classes, including the zero class. -/
theorem supportArchimedeanClasses_toSignedNonpositiveHahn (x : Surreal.OmnificInteger.{u}) :
    supportArchimedeanClasses x.toSignedNonpositiveHahn =
      ArchimedeanClass.mk '' (x : Surreal.{u}).support := by
  ext c
  rw [mem_supportArchimedeanClasses]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨-g, ?_, by simp⟩
    rw [coe_toSignedNonpositiveHahn] at hg
    exact Surreal.mem_support_toSignedFullHahnSeries.mp hg
  · rintro ⟨g, hg, rfl⟩
    refine ⟨-g, ?_, by simp⟩
    rw [coe_toSignedNonpositiveHahn, Surreal.mem_support_toSignedFullHahnSeries]
    simpa only [neg_neg] using hg

/-- An omnific integer whose support meets only finitely many Archimedean classes is primal.
The signed support includes exponent zero, whose class is `⊤`; sign reversal does not change
Archimedean classes. The conclusion also holds for zero. -/
@[blueprint "cor:omnific-finite-classes"
  (phase := "Surreal numbers and omnific integers")
  (title := "Primality for finitely many Archimedean classes")
  (statement := /--
    Every omnific integer whose normal-form exponents meet only finitely many
    Archimedean classes is primal in $\Oz$.
  -/)
  (proof := /--
    Pass to the signed Hahn presentation and induct on the finite set of
    occupied Archimedean classes.  A series of order zero is an integer
    constant.  Otherwise, split off its leading class.  The reduced factor is
    primal by \ref{cor:reduced-hahn-integer-part-primal}, using
    \ref{fact:surreal-archimedean-strata} for $(A1)_\sigma$ and
    \ref{fact:surreal-archimedean-ball-cofinality} for $(A2)_\sigma$; the lower truncation
    has fewer occupied classes and is primal by induction.  Their product is
    primal. By \ref{thm:signed-normal-form-omnific-integer-equivalence},
    signed normal form transfers primality back to the original omnific integer.
  -/)]
theorem isPrimal_of_supportArchimedeanClasses_finite (x : Surreal.OmnificInteger.{u})
    (hfinite : (supportArchimedeanClasses x.toSignedNonpositiveHahn).Finite) : IsPrimal x := by
  let b : SignedSmallSupportIntegerPart.{u} := toSignedSmallSupportIntegerPart x
  have himage : HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
      Surreal.realIntegerSubring b = x.toSignedNonpositiveHahn := by
    apply Subtype.ext
    rw [HahnSeries.CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom,
      coe_toSignedNonpositiveHahn]
    exact coe_toSignedSmallSupportIntegerPart x
  have hbPrimal : IsPrimal b := by
    apply Surreal.isPrimal_cardSuppLTTruncationIntegerPart_of_supportArchimedeanClasses_finite
    rwa [himage]
  let E : Surreal.OmnificInteger.{u} ≃+* SignedSmallSupportIntegerPart.{u} :=
    signedSmallSupportIntegerPartRingEquiv
  apply (RingEquiv.isPrimal_iff E x).mp
  simpa only [E, signedSmallSupportIntegerPartRingEquiv_apply, b] using hbPrimal

end Surreal.OmnificInteger
