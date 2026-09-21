/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncationResidue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.FiniteGermError

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Closed-class restrictions of cardinal-bounded Hahn series

Restriction to a closed Archimedean ball preserves a support-cardinality bound. Since the ball
contains zero, it also preserves the constant coefficient and hence every truncation integer part
defined by a coefficient subring.
-/

public noncomputable section

open scoped HahnSeries

universe u v

namespace HahnSeries

variable {G : Type u} {L : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field L] [Fact (Cardinal.aleph0 < κ)]

namespace CardSuppLTNonpositive

/-- Package a nonpositive Hahn series with an explicit support-cardinality bound. -/
def ofNonpositive (x : Nonpositive G L) (hx : (x : L⟦G⟧).cardSupp < κ) :
    CardSuppLTNonpositive (G := G) (L := L) (κ := κ) :=
  ⟨⟨x, (mem_cardSuppLTSubfield (Γ := G) (R := L) (κ := κ)).mpr hx⟩, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    exact ⟨x.2, Subring.mem_top _⟩⟩

/-- Forgetting the cardinal-bound package recovers the original nonpositive series. -/
@[simp]
theorem coe_ofNonpositive (x : Nonpositive G L) (hx : (x : L⟦G⟧).cardSupp < κ) :
    ((ofNonpositive x hx : CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) :
      L⟦G⟧) = (x : L⟦G⟧) :=
  (rfl)

/-- Forgetting the support bound from a packaged nonpositive series recovers that series. -/
@[simp]
theorem toNonpositiveRingHom_ofNonpositive
    (x : Nonpositive G L) (hx : (x : L⟦G⟧).cardSupp < κ) :
    CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring L)
      (ofNonpositive x hx) = x := by
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  exact coe_ofNonpositive x hx

/-- Forgetting a residue-subring presentation gives the same nonpositive series as forgetting
the original truncation integer part. -/
@[simp]
theorem toNonpositiveRingHom_truncationIntegerPartEquivResidueSubring
    (S : Subring L)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) :
    CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring L)
        ((truncationIntegerPartEquivResidueSubring S x :
          Subring.residueSubring constantCoeffAlgHom S) :
            CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) =
      CardSuppLTTruncationIntegerPart.toNonpositiveRingHom S x := by
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom,
    coe_truncationIntegerPartEquivResidueSubring,
    CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]

/-- Restrict a cardinal-bounded nonpositive series to a closed Archimedean ball. -/
def closedClassRestrict (q : FiniteArchimedeanClass G)
    (x : CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) :
    CardSuppLTNonpositive (G := G) (L := L) (κ := κ) := by
  let xN := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring L) x
  let xr := Nonpositive.closedClassRestrict q xN
  have hxcard : (x : L⟦G⟧).cardSupp < κ :=
    (mem_cardSuppLTSubfield (Γ := G) (R := L) (κ := κ)).mp x.1.2
  have hxNcard : (xN : L⟦G⟧).cardSupp < κ := by
    simpa only [xN, CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom] using hxcard
  exact ⟨⟨xr, (mem_cardSuppLTSubfield (Γ := G) (R := L) (κ := κ)).mpr
      ((cardSupp_mono (Nonpositive.support_closedClassRestrict_subset q xN)).trans_lt
        hxNcard)⟩, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    exact ⟨xr.2, Subring.mem_top _⟩⟩

/-- Forgetting the cardinal bound exposes the ordinary closed-class restriction. -/
@[simp]
theorem coe_closedClassRestrict (q : FiniteArchimedeanClass G)
    (x : CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) :
    ((closedClassRestrict q x : CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) :
      L⟦G⟧) =
      (Nonpositive.closedClassRestrict q
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring L) x) :
          Nonpositive G L) :=
  (rfl)

/-- Forgetting only the cardinal bound commutes with closed-class restriction. -/
theorem toNonpositiveRingHom_closedClassRestrict (q : FiniteArchimedeanClass G)
    (x : CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) :
    CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring L)
        (closedClassRestrict q x) =
      Nonpositive.closedClassRestrict q
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring L) x) := by
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  exact coe_closedClassRestrict q x

/-- Closed-class restriction is multiplicative on cardinal-bounded nonpositive series. -/
theorem closedClassRestrict_mul (q : FiniteArchimedeanClass G)
    (x y : CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) :
    closedClassRestrict q (x * y) =
      closedClassRestrict q x * closedClassRestrict q y := by
  apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective
    (⊤ : Subring L)
  rw [map_mul, toNonpositiveRingHom_closedClassRestrict,
    toNonpositiveRingHom_closedClassRestrict, toNonpositiveRingHom_closedClassRestrict,
    map_mul, Nonpositive.closedClassRestrict_mul]

/-- Restriction at a class met by the support of a bounded nonpositive series is nonzero. -/
theorem closedClassRestrict_ne_zero_of_mem_image_mk_support
    (q : FiniteArchimedeanClass G)
    (x : CardSuppLTNonpositive (G := G) (L := L) (κ := κ))
    (hq : q.1 ∈ ArchimedeanClass.mk '' (x : L⟦G⟧).support) :
    closedClassRestrict q x ≠ 0 := by
  intro hzero
  have hzero' : Nonpositive.closedClassRestrict q
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring L) x) = 0 := by
    apply Subtype.ext
    exact congrArg (fun z : CardSuppLTNonpositive (G := G) (L := L) (κ := κ) ↦
      (z : L⟦G⟧)) hzero
  apply Nonpositive.closedClassRestrict_ne_zero_of_mem_image_mk_support
    (c := q)
    (b := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring L) x)
  · simpa only [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom] using hq
  · exact hzero'

end CardSuppLTNonpositive

namespace CardSuppLTTruncationIntegerPart

/-- Restriction to a closed Archimedean ball preserves a cardinal-bounded truncation integer
part. -/
def closedClassRestrict (S : Subring L) (q : FiniteArchimedeanClass G)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) :
    cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S := by
  let xN := toNonpositiveRingHom S x
  let xr := Nonpositive.closedClassRestrict q xN
  have hxcard : (x : L⟦G⟧).cardSupp < κ :=
    (mem_cardSuppLTSubfield (Γ := G) (R := L) (κ := κ)).mp x.1.2
  have hxNcard : (xN : L⟦G⟧).cardSupp < κ := by
    simpa only [xN, coe_toNonpositiveRingHom] using hxcard
  have hxmem := (mem_cardSuppLTTruncationIntegerPart (Z := S)).mp x.2
  exact ⟨⟨xr, (mem_cardSuppLTSubfield (Γ := G) (R := L) (κ := κ)).mpr
      ((cardSupp_mono (Nonpositive.support_closedClassRestrict_subset q xN)).trans_lt
        hxNcard)⟩, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    refine ⟨xr.2, ?_⟩
    rw [Nonpositive.closedClassRestrict_coeff, ite_eq_left]
    · simpa only [xN, coe_toNonpositiveRingHom] using hxmem.2
    · exact (FiniteArchimedeanClass.closedBallAddSubgroup q).zero_mem⟩

/-- Forgetting the bound and residue condition exposes the ordinary closed-class restriction. -/
@[simp]
theorem coe_closedClassRestrict (S : Subring L) (q : FiniteArchimedeanClass G)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) :
    ((closedClassRestrict S q x :
        cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) : L⟦G⟧) =
      (Nonpositive.closedClassRestrict q (toNonpositiveRingHom S x) : Nonpositive G L) :=
  (rfl)

/-- Forgetting only the cardinal bound and residue condition commutes with closed-class
restriction. -/
theorem toNonpositiveRingHom_closedClassRestrict (S : Subring L)
    (q : FiniteArchimedeanClass G)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) :
    toNonpositiveRingHom S (closedClassRestrict S q x) =
      Nonpositive.closedClassRestrict q (toNonpositiveRingHom S x) := by
  apply Subtype.ext
  rw [coe_toNonpositiveRingHom]
  exact coe_closedClassRestrict S q x

/-- Restriction at a class met by the support of a cardinal-bounded integer part is nonzero. -/
theorem closedClassRestrict_ne_zero_of_mem_image_mk_support
    (S : Subring L) (q : FiniteArchimedeanClass G)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S)
    (hq : q.1 ∈ ArchimedeanClass.mk '' (x : L⟦G⟧).support) :
    closedClassRestrict S q x ≠ 0 := by
  intro hzero
  have hzero' : Nonpositive.closedClassRestrict q (toNonpositiveRingHom S x) = 0 := by
    rw [← toNonpositiveRingHom_closedClassRestrict]
    simpa only [map_zero] using congrArg (toNonpositiveRingHom S) hzero
  apply Nonpositive.closedClassRestrict_ne_zero_of_mem_image_mk_support
    (c := q) (b := toNonpositiveRingHom S x)
  · simpa only [coe_toNonpositiveRingHom] using hq
  · exact hzero'

/-- Closed-class restriction is multiplicative in every cardinal-bounded truncation integer
part. -/
theorem closedClassRestrict_mul (S : Subring L) (q : FiniteArchimedeanClass G)
    (x y : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) :
    closedClassRestrict S q (x * y) =
      closedClassRestrict S q x * closedClassRestrict S q y := by
  apply toNonpositiveRingHom_injective S
  rw [map_mul, toNonpositiveRingHom_closedClassRestrict,
    toNonpositiveRingHom_closedClassRestrict, toNonpositiveRingHom_closedClassRestrict,
    map_mul, Nonpositive.closedClassRestrict_mul]

/-- An exact closed-class refinement by bounded nonpositive factors can be normalized inside a
cardinal-bounded truncation integer part. -/
@[blueprint "lem:closed-class-refinement-normalization"
  (phase := "Refinement over Archimedean classes")
  (title := "Normalization of a closed-class refinement in a Hahn integer part")
  (statement := /--
    Let $S\subseteq L$ be a subring of a field, let $q$ be a nonzero
    Archimedean class of an ordered exponent group, and let
    $a,b,c,d\in S+L((G^{<0}))_\kappa$ satisfy $ab=cd$.  Assume the constant
    coefficient of $a$ is primal in $S$, every element of $L$ is a fraction of
    elements of $S$, and the closed-class restriction $a_q$ is nonzero.

    If the restrictions of $a,b,c,d$ admit a four-factor refinement by
    $\kappa$-bounded nonpositive Hahn series, then they admit such a refinement
    by elements of $S+L((G^{<0}))_\kappa$.
  -/)
  (proof := /--
    Regard the bounded Hahn integer part as the inverse image of $S$ under the
    constant-coefficient homomorphism on bounded nonpositive series.  The
    primality of the constant coefficient of $a$ and the fraction-field
    hypothesis allow a common scalar adjustment of the four ambient factors
    so that all four constant coefficients lie in $S$.  Transport the adjusted
    refinement back through this residue-subring presentation.
  -/)]
theorem exists_refinement_closedClassRestrict_of_ambient
    (S : Subring L) (q : FiniteArchimedeanClass G)
    (a b c d : cardSuppLTTruncationIntegerPart
      (G := G) (R := L) (κ := κ) S)
    (haS : IsPrimal (⟨(a : L⟦G⟧).coeff 0,
      ((mem_cardSuppLTTruncationIntegerPart (Z := S)).mp a.2).2⟩ : S))
    (hfrac : Subring.fracSubring S = ⊤)
    (ha0 : closedClassRestrict S q a ≠ 0) (habcd : a * b = c * d)
    (e f g h : Nonpositive G L)
    (hecard : (e : L⟦G⟧).cardSupp < κ)
    (hfcard : (f : L⟦G⟧).cardSupp < κ)
    (hgcard : (g : L⟦G⟧).cardSupp < κ)
    (hhcard : (h : L⟦G⟧).cardSupp < κ)
    (ha : Nonpositive.closedClassRestrict q (toNonpositiveRingHom S a) =
      Nonpositive.closedClassRestrict q e * Nonpositive.closedClassRestrict q f)
    (hb : Nonpositive.closedClassRestrict q (toNonpositiveRingHom S b) =
      Nonpositive.closedClassRestrict q g * Nonpositive.closedClassRestrict q h)
    (hc : Nonpositive.closedClassRestrict q (toNonpositiveRingHom S c) =
      Nonpositive.closedClassRestrict q e * Nonpositive.closedClassRestrict q g)
    (hd : Nonpositive.closedClassRestrict q (toNonpositiveRingHom S d) =
      Nonpositive.closedClassRestrict q f * Nonpositive.closedClassRestrict q h) :
    ∃ E F H₁ H₂ : cardSuppLTTruncationIntegerPart
        (G := G) (R := L) (κ := κ) S,
      closedClassRestrict S q a = E * F ∧
      closedClassRestrict S q b = H₁ * H₂ ∧
      closedClassRestrict S q c = E * H₁ ∧
      closedClassRestrict S q d = F * H₂ := by
  let eb := CardSuppLTNonpositive.closedClassRestrict q
    (CardSuppLTNonpositive.ofNonpositive e hecard)
  let fb := CardSuppLTNonpositive.closedClassRestrict q
    (CardSuppLTNonpositive.ofNonpositive f hfcard)
  let gb := CardSuppLTNonpositive.closedClassRestrict q
    (CardSuppLTNonpositive.ofNonpositive g hgcard)
  let hbnd := CardSuppLTNonpositive.closedClassRestrict q
    (CardSuppLTNonpositive.ofNonpositive h hhcard)
  have hea : ((CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring S
      (closedClassRestrict S q a) :
        Subring.residueSubring CardSuppLTNonpositive.constantCoeffAlgHom S) :
          CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) = eb * fb := by
    apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective
      (⊤ : Subring L)
    rw [map_mul,
      CardSuppLTNonpositive.toNonpositiveRingHom_truncationIntegerPartEquivResidueSubring,
      CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_ofNonpositive,
      CardSuppLTNonpositive.toNonpositiveRingHom_ofNonpositive]
    exact ha
  have heb : ((CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring S
      (closedClassRestrict S q b) :
        Subring.residueSubring CardSuppLTNonpositive.constantCoeffAlgHom S) :
          CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) = gb * hbnd := by
    apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective
      (⊤ : Subring L)
    rw [map_mul,
      CardSuppLTNonpositive.toNonpositiveRingHom_truncationIntegerPartEquivResidueSubring,
      CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_ofNonpositive,
      CardSuppLTNonpositive.toNonpositiveRingHom_ofNonpositive]
    exact hb
  have hec : ((CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring S
      (closedClassRestrict S q c) :
        Subring.residueSubring CardSuppLTNonpositive.constantCoeffAlgHom S) :
          CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) = eb * gb := by
    apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective
      (⊤ : Subring L)
    rw [map_mul,
      CardSuppLTNonpositive.toNonpositiveRingHom_truncationIntegerPartEquivResidueSubring,
      CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_ofNonpositive,
      CardSuppLTNonpositive.toNonpositiveRingHom_ofNonpositive]
    exact hc
  have hed : ((CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring S
      (closedClassRestrict S q d) :
        Subring.residueSubring CardSuppLTNonpositive.constantCoeffAlgHom S) :
          CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) = fb * hbnd := by
    apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective
      (⊤ : Subring L)
    rw [map_mul,
      CardSuppLTNonpositive.toNonpositiveRingHom_truncationIntegerPartEquivResidueSubring,
      CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_closedClassRestrict,
      CardSuppLTNonpositive.toNonpositiveRingHom_ofNonpositive,
      CardSuppLTNonpositive.toNonpositiveRingHom_ofNonpositive]
    exact hd
  have haS' : IsPrimal
      (⟨((closedClassRestrict S q a :
        cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) :
          L⟦G⟧).coeff 0,
        ((mem_cardSuppLTTruncationIntegerPart (Z := S)).mp
          (closedClassRestrict S q a).2).2⟩ : S) := by
    have hcoeff :
        ((closedClassRestrict S q a :
          cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) :
            L⟦G⟧).coeff 0 = (a : L⟦G⟧).coeff 0 := by
      rw [coe_closedClassRestrict, Nonpositive.closedClassRestrict_coeff, ite_eq_left]
      · exact congrArg (fun z : L⟦G⟧ ↦ z.coeff 0) (coe_toNonpositiveRingHom S a)
      · exact (FiniteArchimedeanClass.closedBallAddSubgroup q).zero_mem
    convert haS using 1
    apply Subtype.ext
    exact hcoeff
  have heq : closedClassRestrict S q a * closedClassRestrict S q b =
      closedClassRestrict S q c * closedClassRestrict S q d := by
    rw [← closedClassRestrict_mul, ← closedClassRestrict_mul,
      habcd]
  exact CardSuppLTNonpositive.exists_refinement_truncationIntegerPart_of_ambient
    S haS' hfrac ha0 heq hea heb hec hed

end CardSuppLTTruncationIntegerPart

end HahnSeries
