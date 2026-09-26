/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.CardinalPrimalityTransfer
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CoefficientMap
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Ring.Hom.OfInjectiveComp

/-!
# Cardinal-bounded leading-class integer-part splitting

This module restricts LM24, Fact 2.4.2(5) to Hahn series with support cardinality less than
`κ`. The forward split always respects the bound on every inner coefficient. For the inverse,
regularity of `κ` ensures that flattening the countable outer support over the Archimedean
stratum, whose coefficients each have support smaller than `κ`, again has support smaller than
`κ`.

The regularity hypothesis records the exact set-sized cardinal closure used here. It is not folded
into the printed statement of LM24, where the intended omnific Hahn field has a proper-class
exponent group and every individual support remains a set.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass

namespace HahnSeries.Nonpositive

variable {K G R : Type*} {κ : Cardinal}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R] [Fact (ℵ₀ < κ)]

/-- Embed the bounded inner Hahn field into the full inner Hahn field. -/
def cardSuppLTInnerFieldSubtypeRingHom (c : FiniteArchimedeanClass G) :
    CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ) →+* R⟦ball K c⟧ :=
  (cardSuppLTSubfield (ball K c) R κ).subtype

/-- Forget the cardinal bound on every coefficient of an outer nonpositive Hahn series. -/
def forgetCardSuppLTInnerCoefficients
    (c : FiniteArchimedeanClass G) (u : HahnEmbedding.ArchimedeanStrata K G) :
    Nonpositive (u.stratum c)
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ)) →+*
      Nonpositive (u.stratum c) R⟦ball K c⟧ :=
  coefficientMapRingHom (cardSuppLTInnerFieldSubtypeRingHom c)

/-- Forgetting bounded inner coefficients preserves their underlying Hahn series. -/
@[simp]
theorem coeff_forgetCardSuppLTInnerCoefficients
    (c : FiniteArchimedeanClass G) (u : HahnEmbedding.ArchimedeanStrata K G)
    (y : Nonpositive (u.stratum c)
      (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) (s : u.stratum c) :
    (((forgetCardSuppLTInnerCoefficients c u y : Nonpositive
      (u.stratum c) R⟦ball K c⟧) : (R⟦ball K c⟧)⟦u.stratum c⟧).coeff s) =
      ((y : (CardSuppLTField (G := ↥(ball K c)) (R := R)
        (κ := κ))⟦u.stratum c⟧).coeff s : R⟦ball K c⟧) := by
  rw [forgetCardSuppLTInnerCoefficients, coe_coefficientMapRingHom,
    HahnSeries.coefficientMapRingHom_coeff]
  rfl

/-- Forget the inner cardinal bounds on a split truncation integer part. -/
def forgetSplitCardSuppLTIntegerPartRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) :
    truncationIntegerPart (u.stratum c)
        (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z) →+*
      truncationIntegerPart (u.stratum c)
        (innerIntegerPartSubring (K := K) (G := G) c Z) where
  toFun y := ⟨forgetCardSuppLTInnerCoefficients (K := K) (R := R) (κ := κ) c u y, by
    rw [mem_truncationIntegerPart]
    rw [mem_innerIntegerPartSubring_iff]
    have hy := (mem_truncationIntegerPart (Γ := u.stratum c)
      (R := CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))).mp y.2
    rw [coeff_forgetCardSuppLTInnerCoefficients (K := K) (R := R) (κ := κ)]
    exact (mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp hy⟩
  map_one' := Subtype.ext (map_one
    (forgetCardSuppLTInnerCoefficients (K := K) (R := R) (κ := κ) c u))
  map_mul' x y := Subtype.ext (map_mul
    (forgetCardSuppLTInnerCoefficients (K := K) (R := R) (κ := κ) c u)
      (x : Nonpositive (u.stratum c)
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) y)
  map_zero' := Subtype.ext (map_zero
    (forgetCardSuppLTInnerCoefficients (K := K) (R := R) (κ := κ) c u))
  map_add' x y := Subtype.ext (map_add
    (forgetCardSuppLTInnerCoefficients (K := K) (R := R) (κ := κ) c u)
      (x : Nonpositive (u.stratum c)
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) y)

/-- Forgetting the target bound acts by forgetting every inner coefficient. -/
@[simp]
theorem coe_forgetSplitCardSuppLTIntegerPartRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (y : truncationIntegerPart (u.stratum c)
      (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z)) :
    ((forgetSplitCardSuppLTIntegerPartRingHom u c Z y :
      truncationIntegerPart (u.stratum c) (innerIntegerPartSubring c Z)) :
        Nonpositive (u.stratum c) R⟦ball K c⟧) =
      forgetCardSuppLTInnerCoefficients (K := K) (R := R) (κ := κ) c u
        (y : Nonpositive (u.stratum c)
          (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) :=
  (rfl)

/-- Forgetting bounds after the bounded split recovers the full integer-part split. -/
theorem forget_splitTruncationCardSuppLTIntegerPart
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    forgetSplitCardSuppLTIntegerPartRingHom u c Z
        (splitTruncationCardSuppLTIntegerPart u c Z b) =
      splitIntegerPartRingHom u c Z
        (CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z b) := by
  apply Subtype.ext
  rw [coe_forgetSplitCardSuppLTIntegerPartRingHom, coe_splitIntegerPartRingHom]
  rw [coe_splitTruncationCardSuppLTIntegerPart]
  rw [CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom]
  apply Subtype.ext
  apply HahnSeries.ext
  funext s
  rw [coeff_forgetCardSuppLTInnerCoefficients]
  exact coe_coeff_splitTruncationCardSuppLT u c
    (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
    (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b) s

/-- Forgetting bounded inner coefficients is injective on the split integer part. -/
theorem forgetSplitCardSuppLTIntegerPartRingHom_injective
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) :
    Function.Injective
      (forgetSplitCardSuppLTIntegerPartRingHom (K := K) (R := R) (κ := κ) u c Z) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply HahnSeries.ext
  funext s
  apply Subtype.ext
  have hcoeff := congrArg (fun q : truncationIntegerPart (u.stratum c)
      (innerIntegerPartSubring (K := K) (G := G) c Z) ↦
        ((q : Nonpositive (u.stratum c) R⟦ball K c⟧) :
          (R⟦ball K c⟧)⟦u.stratum c⟧).coeff s) hxy
  simpa only [coe_forgetSplitCardSuppLTIntegerPartRingHom (K := K) (R := R) (κ := κ),
    coeff_forgetCardSuppLTInnerCoefficients (K := K) (R := R) (κ := κ)] using hcoeff

/-- The leading-class split as a ring homomorphism on cardinal-bounded integer parts. -/
def splitCardSuppLTIntegerPartRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z →+*
      truncationIntegerPart (u.stratum c)
        (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z) :=
  RingHom.ofInjectiveComp _ (forgetSplitCardSuppLTIntegerPartRingHom_injective u c Z)
    ((splitIntegerPartRingHom u c Z).comp
      (CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z))
    (splitTruncationCardSuppLTIntegerPart u c Z)
    (forget_splitTruncationCardSuppLTIntegerPart u c Z)

/-- The bounded split ring homomorphism applies by the bounded split construction. -/
@[simp]
theorem splitCardSuppLTIntegerPartRingHom_apply
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    splitCardSuppLTIntegerPartRingHom u c Z b =
      splitTruncationCardSuppLTIntegerPart u c Z b :=
  RingHom.ofInjectiveComp_apply _ _ _ _ _ b

/-- The bounded fixed integer part is the preimage of the full fixed integer part under the
bound-forgetting homomorphism. -/
def cardSuppLTFixedIntegerPartSubring
    (c : FiniteArchimedeanClass G) (Z : Subring R) :
    Subring (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :=
  (fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z).comap
    (CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z)

/-- Forget the cardinal bound on a bounded fixed integer-part element. -/
def forgetCardSuppLTFixedIntegerPartRingHom
    (c : FiniteArchimedeanClass G) (Z : Subring R) :
    cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) c Z →+*
      fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z where
  toFun x := ⟨CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z), x.2⟩
  map_one' := by
    apply Subtype.ext
    change CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom
      (G := G) (R := R) (κ := κ) Z (1 :
        cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) = 1
    rw [map_one]
  map_mul' x y := by
    apply Subtype.ext
    change CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z
      ((x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) *
        (y : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)) = _
    rw [map_mul]
    rfl
  map_zero' := by
    apply Subtype.ext
    change CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom
      (G := G) (R := R) (κ := κ) Z (0 :
        cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) = 0
    rw [map_zero]
  map_add' x y := by
    apply Subtype.ext
    change CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z
      ((x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) +
        (y : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)) = _
    rw [map_add]
    rfl

/-- Forgetting a bounded fixed element uses the underlying bound-forgetting homomorphism. -/
@[simp]
theorem coe_forgetCardSuppLTFixedIntegerPartRingHom
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) c Z) :
    (forgetCardSuppLTFixedIntegerPartRingHom c Z x : truncationIntegerPart G Z) =
      CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z
        (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :=
  (rfl)

/-- Forgetting the bound is injective on bounded fixed integer-part elements. -/
theorem forgetCardSuppLTFixedIntegerPartRingHom_injective
    (c : FiniteArchimedeanClass G) (Z : Subring R) :
    Function.Injective
      (forgetCardSuppLTFixedIntegerPartRingHom (K := K) (κ := κ) c Z) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have hraw := congrArg (fun q : fixedIntegerPartSubring
      (K := K) (G := G) (R := R) c Z ↦
        (((q : truncationIntegerPart G Z) : Nonpositive G R) : R⟦G⟧)) hxy
  simpa only [coe_forgetCardSuppLTFixedIntegerPartRingHom,
    CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom,
    CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom] using hraw

/-- Restrict the bounded split homomorphism to the bounded fixed integer part. -/
def splitCardSuppLTFixedIntegerPartRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) :
    cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) c Z →+*
      truncationIntegerPart (u.stratum c)
        (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z) :=
  (splitCardSuppLTIntegerPartRingHom u c Z).comp
    (cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) c Z).subtype

/-- The fixed bounded split is the unrestricted bounded split of the underlying element. -/
@[simp]
theorem splitCardSuppLTFixedIntegerPartRingHom_apply
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (x : cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) c Z) :
    splitCardSuppLTFixedIntegerPartRingHom u c Z x =
      splitCardSuppLTIntegerPartRingHom u c Z
        (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :=
  (rfl)

/-- Forgetting bounds commutes with the fixed integer-part split. -/
theorem forget_splitCardSuppLTFixedIntegerPartRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (x : cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) c Z) :
    forgetSplitCardSuppLTIntegerPartRingHom u c Z
        (splitCardSuppLTFixedIntegerPartRingHom u c Z x) =
      splitFixedIntegerPartRingHom u c Z
        (forgetCardSuppLTFixedIntegerPartRingHom c Z x) := by
  rw [splitCardSuppLTFixedIntegerPartRingHom_apply, splitCardSuppLTIntegerPartRingHom_apply,
    forget_splitTruncationCardSuppLTIntegerPart]
  apply Subtype.ext
  rw [coe_splitFixedIntegerPartRingHom, coe_splitIntegerPartRingHom]
  rw [coe_forgetCardSuppLTFixedIntegerPartRingHom,
    CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom]

/-- The full unsplit of a bounded outer integer-part element still has support smaller than a
regular `κ`. -/
theorem cardSupp_unsplit_forgetSplitCardSuppLTIntegerPart_lt
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (y : truncationIntegerPart (u.stratum c)
      (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z)) :
    ((((unsplitIntegerPart u c Z
      (forgetSplitCardSuppLTIntegerPartRingHom u c Z y) :
        truncationIntegerPart G Z) : Nonpositive G R) : R⟦G⟧).cardSupp) < κ := by
  let yBounded : Nonpositive (u.stratum c)
      (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ)) := y
  let yFull : Nonpositive (u.stratum c) R⟦ball K c⟧ :=
    forgetCardSuppLTInnerCoefficients c u yBounded
  have houter : ((yFull : (R⟦ball K c⟧)⟦u.stratum c⟧).cardSupp) < κ :=
    (HahnSeries.cardSupp_le_aleph0_of_archimedean
      (yFull : (R⟦ball K c⟧)⟦u.stratum c⟧)).trans_lt (Fact.out : ℵ₀ < κ)
  have hcoeff : ∀ s,
      (((yFull : (R⟦ball K c⟧)⟦u.stratum c⟧).coeff s).cardSupp) < κ := by
    intro s
    dsimp only [yFull]
    rw [coeff_forgetCardSuppLTInnerCoefficients]
    exact ((yBounded :
      (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))⟦u.stratum c⟧).coeff s).2
  have hflat : (HahnSeries.iterateRingEquiv
      (yFull : (R⟦ball K c⟧)⟦u.stratum c⟧)).cardSupp < κ :=
    HahnSeries.cardSupp_iterateRingEquiv_lt_of_isRegular Fact.out
      (yFull : (R⟦ball K c⟧)⟦u.stratum c⟧) houter hcoeff
  let zClosed := (HahnSeries.archimedeanSplitRingEquiv u c).symm
    (yFull : (R⟦ball K c⟧)⟦u.stratum c⟧)
  have hsplit : HahnSeries.archimedeanSplitRingEquiv u c zClosed =
      (yFull : (R⟦ball K c⟧)⟦u.stratum c⟧) :=
    (HahnSeries.archimedeanSplitRingEquiv u c).apply_symm_apply _
  have hiterate := iterateRingEquiv_archimedeanSplitRingEquiv u c zClosed
  rw [hsplit] at hiterate
  have hzClosed : zClosed.cardSupp < κ := by
    rw [← HahnSeries.cardSupp_embDomainRingEquiv
      (HahnEmbedding.ArchimedeanStrata.closedBallEquivStratumLexBall u c) zClosed]
    rw [← hiterate]
    exact hflat
  rw [coe_unsplitIntegerPart]
  rw [HahnSeries.cardSupp_embDomain]
  exact hzClosed

/-- Unsplit a bounded outer integer-part element and retain the support-cardinality witness. -/
def unsplitCardSuppLTIntegerPart
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (y : truncationIntegerPart (u.stratum c)
      (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z)) :
    cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) c Z := by
  let xFull := unsplitIntegerPart u c Z
    (forgetSplitCardSuppLTIntegerPartRingHom u c Z y)
  let xBounded : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z :=
    ⟨⟨((xFull : truncationIntegerPart G Z) : Nonpositive G R),
      cardSupp_unsplit_forgetSplitCardSuppLTIntegerPart_lt u c Z y⟩,
      by
        rw [mem_cardSuppLTTruncationIntegerPart]
        exact ⟨support_subset ((xFull : truncationIntegerPart G Z) : Nonpositive G R),
          (mem_truncationIntegerPart (Γ := G) (R := R)).mp
            (xFull : truncationIntegerPart G Z).2⟩⟩
  refine ⟨xBounded, ?_⟩
  change CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z xBounded ∈
    fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z
  have hx : CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z xBounded =
      (xFull : truncationIntegerPart G Z) := by
    apply Subtype.ext
    rw [CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom]
    apply Subtype.ext
    rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  rw [hx]
  exact xFull.2

/-- Forgetting the source bound after bounded unsplitting recovers the full unsplit. -/
theorem forget_unsplitCardSuppLTIntegerPart
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (y : truncationIntegerPart (u.stratum c)
      (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z)) :
    forgetCardSuppLTFixedIntegerPartRingHom c Z
        (unsplitCardSuppLTIntegerPart u c Z y) =
      unsplitIntegerPart u c Z
        (forgetSplitCardSuppLTIntegerPartRingHom u c Z y) := by
  apply Subtype.ext
  rw [coe_forgetCardSuppLTFixedIntegerPartRingHom]
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom]
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  rfl

/-- For regular `κ`, the bounded fixed integer part is equivalent to the outer integer part over
the bounded inner coefficient integer part. -/
def splitCardSuppLTFixedIntegerPartRingEquiv
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) :
    cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) c Z ≃+*
      truncationIntegerPart (u.stratum c)
        (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z) where
  toFun := splitCardSuppLTFixedIntegerPartRingHom u c Z
  invFun := unsplitCardSuppLTIntegerPart u c Z
  left_inv x := by
    apply forgetCardSuppLTFixedIntegerPartRingHom_injective c Z
    rw [forget_unsplitCardSuppLTIntegerPart,
      forget_splitCardSuppLTFixedIntegerPartRingHom]
    rw [← splitFixedIntegerPartRingEquiv_apply,
      ← splitFixedIntegerPartRingEquiv_symm_apply]
    exact (splitFixedIntegerPartRingEquiv u c Z).left_inv _
  right_inv y := by
    apply forgetSplitCardSuppLTIntegerPartRingHom_injective u c Z
    rw [forget_splitCardSuppLTFixedIntegerPartRingHom,
      forget_unsplitCardSuppLTIntegerPart]
    rw [← splitFixedIntegerPartRingEquiv_apply,
      ← splitFixedIntegerPartRingEquiv_symm_apply]
    exact (splitFixedIntegerPartRingEquiv u c Z).right_inv _
  map_mul' := (splitCardSuppLTFixedIntegerPartRingHom u c Z).map_mul
  map_add' := (splitCardSuppLTFixedIntegerPartRingHom u c Z).map_add

/-- The bounded fixed equivalence applies by the bounded split ring homomorphism. -/
@[simp]
theorem splitCardSuppLTFixedIntegerPartRingEquiv_apply
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (x : cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) c Z) :
    splitCardSuppLTFixedIntegerPartRingEquiv u c Z x =
      splitCardSuppLTFixedIntegerPartRingHom u c Z x :=
  (rfl)

/-- The inverse bounded fixed equivalence is the bounded unsplit construction. -/
@[simp]
theorem splitCardSuppLTFixedIntegerPartRingEquiv_symm_apply
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (y : truncationIntegerPart (u.stratum c)
      (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z)) :
    (splitCardSuppLTFixedIntegerPartRingEquiv u c Z).symm y =
      unsplitCardSuppLTIntegerPart u c Z y :=
  (rfl)

/-- Membership in the bounded fixed integer part is invariance under the closed-class cut. -/
theorem mem_cardSuppLTFixedIntegerPartSubring_iff
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    x ∈ cardSuppLTFixedIntegerPartSubring (K := K) c Z ↔
      T (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) =
        CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x := by
  change CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z x ∈
    fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z ↔ _
  rw [mem_fixedIntegerPartSubring_iff]
  rw [CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom]

end HahnSeries.Nonpositive
