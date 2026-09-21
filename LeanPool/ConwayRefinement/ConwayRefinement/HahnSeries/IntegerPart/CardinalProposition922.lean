/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.CardinalIntegerPartSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.PrimalityTransfer

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# LM24 Proposition 9.2.2 for cardinal-bounded Hahn fields

This module proves the set-sized, cardinal-bounded form of LM24, Proposition 9.2.2. Closed-class
truncation preserves the bound directly. Its divisibility-localization converse stays bounded
because a quotient of two `< κ`-supported Hahn series again has support smaller than the
uncountable cardinal `κ`.

The bounded fixed-ring equivalence used later requires regularity of `κ`; that hypothesis records
the countable-union closure needed to flatten arbitrary bounded inner coefficients. The
hypothesis `(A2)_σ` is needed only in the zero-residue branch.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass

namespace HahnSeries.Nonpositive

variable {K G R : Type*} {κ : Cardinal}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R] [Fact (ℵ₀ < κ)]

/-- Closed-class truncation does not increase support cardinality. -/
theorem cardSupp_T_le (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    ((T (K := K) c x : Nonpositive G R) : R⟦G⟧).cardSupp ≤ (x : R⟦G⟧).cardSupp :=
  HahnSeries.cardSupp_mono (support_T_subset c x)

/-- Closed-class truncation restricted to a cardinal-bounded truncation integer part. -/
def TCardSuppLTIntegerPartRingHom
    (c : FiniteArchimedeanClass G) (Z : Subring R) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z →+*
      cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z where
  toFun x := by
    let xNP := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x
    let tx := T (K := K) c xNP
    refine ⟨⟨(tx : R⟦G⟧), (cardSupp_T_le c xNP).trans_lt
      (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z x)⟩, ?_⟩
    rw [mem_cardSuppLTTruncationIntegerPart]
    constructor
    · exact support_subset tx
    · rw [show (tx : R⟦G⟧).coeff 0 = (xNP : R⟦G⟧).coeff 0 by
        exact coeff_T_of_mem c xNP (zero_mem _)]
      rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
      exact (mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2 |>.2
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change (((T (K := K) c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z (1 :
        cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)) :
          Nonpositive G R) : R⟦G⟧)) = 1
    rw [map_one, map_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    change (((T (K := K) c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z (x * y)) :
        Nonpositive G R) : R⟦G⟧)) = _
    rw [map_mul, map_mul]
    rfl
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    change (((T (K := K) c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z (0 :
        cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)) :
          Nonpositive G R) : R⟦G⟧)) = 0
    rw [map_zero, map_zero]
    rfl
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    change (((T (K := K) c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z (x + y)) :
        Nonpositive G R) : R⟦G⟧)) = _
    rw [map_add, map_add]
    rfl

/-- The bounded truncation homomorphism has the expected underlying nonpositive series. -/
@[simp]
theorem toNonpositive_TCardSuppLTIntegerPartRingHom
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z
        (TCardSuppLTIntegerPartRingHom (K := K) c Z x) =
      T (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) := by
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  rfl

/-- Forgetting the cardinal bound commutes with closed-class truncation. -/
theorem toTruncationIntegerPart_TCardSuppLTIntegerPartRingHom
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z
        (TCardSuppLTIntegerPartRingHom (K := K) c Z x) =
      TIntegerPartRingHom (K := K) c Z
        (CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z x) := by
  apply Subtype.ext
  rw [coe_TIntegerPartRingHom,
    CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom]
  rw [toNonpositive_TCardSuppLTIntegerPartRingHom]
  rw [CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom]

/-- A bounded integer-part element is fixed by bounded truncation exactly when its underlying
nonpositive series is fixed. -/
theorem TCardSuppLTIntegerPartRingHom_eq_iff
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    TCardSuppLTIntegerPartRingHom (K := K) c Z x = x ↔
      T (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) =
        CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x := by
  constructor
  · intro h
    have h' := congrArg
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
        (G := G) (R := R) (κ := κ) Z) h
    rwa [toNonpositive_TCardSuppLTIntegerPartRingHom] at h'
  · intro h
    apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective Z
    rwa [toNonpositive_TCardSuppLTIntegerPartRingHom]

/-- Bounded closed-class truncation is idempotent. -/
@[simp]
theorem TCardSuppLTIntegerPartRingHom_TCardSuppLTIntegerPartRingHom
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    TCardSuppLTIntegerPartRingHom (K := K) c Z
        (TCardSuppLTIntegerPartRingHom (K := K) c Z x) =
      TCardSuppLTIntegerPartRingHom (K := K) c Z x := by
  apply (TCardSuppLTIntegerPartRingHom_eq_iff c Z _).mpr
  rw [toNonpositive_TCardSuppLTIntegerPartRingHom]
  exact T_T c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x)

/-- Divisibility by a nonzero fixed bounded integer-part element can be tested after closed-class
truncation, with the quotient remaining cardinal-bounded. -/
theorem dvd_iff_dvd_TCardSuppLTIntegerPart_of_fixed
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hb0 : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b ≠ 0)
    (hbFixed : T (K := K) c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) =
        CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    b ∣ x ↔ b ∣ TCardSuppLTIntegerPartRingHom (K := K) c Z x := by
  let f := CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom
    (G := G) (R := R) (κ := κ) Z
  have hbFixedBounded : TCardSuppLTIntegerPartRingHom (K := K) c Z b = b :=
    (TCardSuppLTIntegerPartRingHom_eq_iff c Z b).mpr hbFixed
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨TCardSuppLTIntegerPartRingHom (K := K) c Z q, ?_⟩
    calc
      TCardSuppLTIntegerPartRingHom (K := K) c Z x =
          TCardSuppLTIntegerPartRingHom (K := K) c Z (b * q) := congrArg _ hq
      _ = TCardSuppLTIntegerPartRingHom (K := K) c Z b *
          TCardSuppLTIntegerPartRingHom (K := K) c Z q := map_mul _ _ _
      _ = b * TCardSuppLTIntegerPartRingHom (K := K) c Z q := by rw [hbFixedBounded]
  · intro h
    have hFullT0 : f b ∣ f (TCardSuppLTIntegerPartRingHom (K := K) c Z x) :=
      map_dvd f h
    have hFullT : f b ∣ TIntegerPartRingHom (K := K) c Z (f x) := by
      rw [← toTruncationIntegerPart_TCardSuppLTIntegerPartRingHom]
      exact hFullT0
    have hbFull0 : (f b : Nonpositive G R) ≠ 0 := by
      rw [CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom]
      exact hb0
    have hbFullFixed : T (K := K) c (f b : Nonpositive G R) = f b := by
      rw [CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom]
      exact hbFixed
    have hFull : f b ∣ f x :=
      (dvd_iff_dvd_TIntegerPart_of_fixed c Z (f b) hbFull0 hbFullFixed (f x)).mpr hFullT
    obtain ⟨q, hq⟩ := hFull
    let bRaw : R⟦G⟧ := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b
    let xRaw : R⟦G⟧ := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x
    let qRaw : R⟦G⟧ := (q : Nonpositive G R)
    have hbRaw0 : bRaw ≠ 0 := by
      intro hzero
      apply hb0
      exact Subtype.ext hzero
    have hprod : xRaw = bRaw * qRaw := by
      have hraw := congrArg (fun z : truncationIntegerPart G Z ↦
        ((z : Nonpositive G R) : R⟦G⟧)) hq
      have hfx : (((f x : truncationIntegerPart G Z) : Nonpositive G R) : R⟦G⟧) =
          xRaw := by
        calc
          _ = (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x : R⟦G⟧) :=
            congrArg Subtype.val
              (CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom Z x)
          _ = xRaw := rfl
      have hfb : (((f b : truncationIntegerPart G Z) : Nonpositive G R) : R⟦G⟧) =
          bRaw := by
        calc
          _ = (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b : R⟦G⟧) :=
            congrArg Subtype.val
              (CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom Z b)
          _ = bRaw := rfl
      have hmul : ((((f b) * q : truncationIntegerPart G Z) : Nonpositive G R) : R⟦G⟧) =
          (((f b : truncationIntegerPart G Z) : Nonpositive G R) : R⟦G⟧) * qRaw :=
        (rfl)
      rw [hfx, hmul, hfb] at hraw
      exact hraw
    have hqDiv : qRaw = xRaw / bRaw := (eq_div_iff hbRaw0).mpr (by
      calc
        qRaw * bRaw = bRaw * qRaw := mul_comm _ _
        _ = xRaw := hprod.symm)
    have hbCard : bRaw.cardSupp < κ := by
      exact CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b
    have hxCard : xRaw.cardSupp < κ := by
      exact CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z x
    have hqCard : qRaw.cardSupp < κ := by
      rw [hqDiv]
      exact (HahnSeries.cardSupp_div_le xRaw bRaw).trans_lt
        (Cardinal.mul_lt_of_lt (Fact.out : ℵ₀ < κ).le hxCard
          (max_lt (Fact.out : ℵ₀ < κ) hbCard))
    let qBounded : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z :=
      ⟨⟨qRaw, hqCard⟩, by
        rw [mem_cardSuppLTTruncationIntegerPart]
        exact ⟨support_subset (q : Nonpositive G R),
          (mem_truncationIntegerPart (Γ := G) (R := R)).mp q.2⟩⟩
    refine ⟨qBounded, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hxval : ((x : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) =
        xRaw :=
      (CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom Z x).symm
    have hbval : ((b : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) =
        bRaw :=
      (CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom Z b).symm
    have hqval : ((qBounded : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) =
        qRaw :=
      (rfl)
    have hmul : (((b * qBounded :
        cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
          CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) =
        ((b : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) *
          ((qBounded : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) :=
      (rfl)
    rw [hxval, hmul, hbval, hqval]
    exact hprod

/-- Membership in the bounded fixed subring can be stated using the bundled bounded truncation
homomorphism. -/
theorem mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    x ∈ cardSuppLTFixedIntegerPartSubring (K := K) c Z ↔
      TCardSuppLTIntegerPartRingHom (K := K) c Z x = x :=
  (mem_cardSuppLTFixedIntegerPartSubring_iff c Z x).trans
    (TCardSuppLTIntegerPartRingHom_eq_iff c Z x).symm

/-- A nonconstant bounded integer-part element, regarded in the bounded subring fixed at its
leading Archimedean class. -/
def leadingCardSuppLTFixedIntegerPartElement
    (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      Nonpositive G R) : R⟦G⟧).order ≠ 0) :
    cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ)
      (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder) Z :=
  ⟨b, (mem_cardSuppLTFixedIntegerPartSubring_iff _ Z b).mpr
    (T_leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)⟩

/-- The leading bounded fixed element has the original bounded integer-part element as value. -/
@[simp]
theorem coe_leadingCardSuppLTFixedIntegerPartElement
    (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      Nonpositive G R) : R⟦G⟧).order ≠ 0) :
    (leadingCardSuppLTFixedIntegerPartElement (K := K) Z b horder :
      cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) = b :=
  (rfl)

/-- Primality of a nonzero nonconstant bounded integer-part element is unchanged when restricted
to the bounded subring fixed by truncation at its leading class. -/
theorem isPrimal_leadingCardSuppLTFixedIntegerPartElement_iff
    (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hb0 : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b ≠ 0)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      Nonpositive G R) : R⟦G⟧).order ≠ 0) :
    IsPrimal (leadingCardSuppLTFixedIntegerPartElement (K := K) Z b horder) ↔
      IsPrimal b := by
  let sigma := leadingClass
    (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder
  let t := TCardSuppLTIntegerPartRingHom (K := K) (R := R) (κ := κ) sigma Z
  have hbFixed : t b = b :=
    (TCardSuppLTIntegerPartRingHom_eq_iff sigma Z b).mpr
      (T_leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
  constructor
  · intro h x y hdvd
    obtain ⟨q, hq⟩ := hdvd
    have hdivLocal : leadingCardSuppLTFixedIntegerPartElement (K := K) Z b horder ∣
        ⟨t x, (mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT sigma Z _).mpr
          (TCardSuppLTIntegerPartRingHom_TCardSuppLTIntegerPartRingHom sigma Z x)⟩ *
        ⟨t y, (mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT sigma Z _).mpr
          (TCardSuppLTIntegerPartRingHom_TCardSuppLTIntegerPartRingHom sigma Z y)⟩ := by
      refine ⟨⟨t q, (mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT sigma Z _).mpr
        (TCardSuppLTIntegerPartRingHom_TCardSuppLTIntegerPartRingHom sigma Z q)⟩, ?_⟩
      apply Subtype.ext
      change t x * t y = b * t q
      rw [← map_mul]
      rw [show x * y = b * q from hq]
      rw [map_mul, hbFixed]
    obtain ⟨b₁, b₂, h₁, h₂, hprod⟩ := h hdivLocal
    have hprodSource : b =
        (b₁ : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) *
          (b₂ : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :=
      congrArg Subtype.val hprod
    have hb₁Ne : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z
        (b₁ : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) ≠ 0 := by
      intro hz
      apply hb0
      rw [show CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b =
        CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z
          ((b₁ : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) *
            (b₂ : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)) by
            exact congrArg _ hprodSource]
      rw [map_mul, hz, zero_mul]
    have hb₂Ne : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z
        (b₂ : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) ≠ 0 := by
      intro hz
      apply hb0
      rw [show CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b =
        CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z
          ((b₁ : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) *
            (b₂ : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)) by
            exact congrArg _ hprodSource]
      rw [map_mul, hz, mul_zero]
    have hfix₁ := (mem_cardSuppLTFixedIntegerPartSubring_iff sigma Z _).mp b₁.2
    have hfix₂ := (mem_cardSuppLTFixedIntegerPartSubring_iff sigma Z _).mp b₂.2
    have hiff₁ := dvd_iff_dvd_TCardSuppLTIntegerPart_of_fixed sigma Z b₁ hb₁Ne hfix₁ x
    have hiff₂ := dvd_iff_dvd_TCardSuppLTIntegerPart_of_fixed sigma Z b₂ hb₂Ne hfix₂ y
    have hmap₁ := map_dvd (cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) sigma Z).subtype h₁
    have hmap₂ := map_dvd (cardSuppLTFixedIntegerPartSubring (K := K) (κ := κ) sigma Z).subtype h₂
    exact ⟨_, _, hiff₁.mpr hmap₁, hiff₂.mpr hmap₂, hprodSource⟩
  · intro h x y hdvd
    have hdvdSource : b ∣
        (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) * y :=
      map_dvd (cardSuppLTFixedIntegerPartSubring
        (K := K) (κ := κ) sigma Z).subtype hdvd
    obtain ⟨b₁, b₂, h₁, h₂, hprod⟩ := h hdvdSource
    have hb₁Mem : t b₁ = b₁ :=
      (TCardSuppLTIntegerPartRingHom_eq_iff sigma Z b₁).mpr (by
        apply T_leadingClass_of_dvd
          (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) hb0 horder
        exact map_dvd (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
          (G := G) (R := R) (κ := κ) Z)
          (hprod.symm ▸ dvd_mul_right b₁ b₂))
    have hb₂Mem : t b₂ = b₂ :=
      (TCardSuppLTIntegerPartRingHom_eq_iff sigma Z b₂).mpr (by
        apply T_leadingClass_of_dvd
          (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) hb0 horder
        exact map_dvd (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
          (G := G) (R := R) (κ := κ) Z)
          (hprod.symm ▸ dvd_mul_left b₂ b₁))
    have hb₁Ne : b₁ ≠ 0 := by
      intro hz
      apply hb0
      rw [show b = b₁ * b₂ from hprod, hz, zero_mul, map_zero]
    have hb₂Ne : b₂ ≠ 0 := by
      intro hz
      apply hb0
      rw [show b = b₁ * b₂ from hprod, hz, mul_zero, map_zero]
    have hq₁Mem : t h₁.choose = h₁.choose := by
      apply mul_left_cancel₀ hb₁Ne
      calc
        b₁ * t h₁.choose = t b₁ * t h₁.choose := by rw [hb₁Mem]
        _ = t (b₁ * h₁.choose) := (map_mul t b₁ h₁.choose).symm
        _ = t (x : cardSuppLTTruncationIntegerPart
            (G := G) (R := R) (κ := κ) Z) := congrArg t h₁.choose_spec.symm
        _ = (x : cardSuppLTTruncationIntegerPart
            (G := G) (R := R) (κ := κ) Z) :=
          (mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT sigma Z _).mp x.2
        _ = b₁ * h₁.choose := h₁.choose_spec
    have hq₂Mem : t h₂.choose = h₂.choose := by
      apply mul_left_cancel₀ hb₂Ne
      calc
        b₂ * t h₂.choose = t b₂ * t h₂.choose := by rw [hb₂Mem]
        _ = t (b₂ * h₂.choose) := (map_mul t b₂ h₂.choose).symm
        _ = t (y : cardSuppLTTruncationIntegerPart
            (G := G) (R := R) (κ := κ) Z) := congrArg t h₂.choose_spec.symm
        _ = (y : cardSuppLTTruncationIntegerPart
            (G := G) (R := R) (κ := κ) Z) :=
          (mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT sigma Z _).mp y.2
        _ = b₂ * h₂.choose := h₂.choose_spec
    refine ⟨⟨b₁, (mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT sigma Z _).mpr hb₁Mem⟩,
      ⟨b₂, (mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT sigma Z _).mpr hb₂Mem⟩,
      ?_, ?_, ?_⟩
    · exact ⟨⟨h₁.choose,
        (mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT sigma Z _).mpr hq₁Mem⟩,
          Subtype.ext h₁.choose_spec⟩
    · exact ⟨⟨h₂.choose,
        (mem_cardSuppLTFixedIntegerPartSubring_iff_TCardSuppLT sigma Z _).mpr hq₂Mem⟩,
          Subtype.ext h₂.choose_spec⟩
    · exact Subtype.ext hprod

/-- Splitting the leading bounded fixed element gives the bounded split truncation integer-part
element. -/
theorem splitCardSuppLTFixedIntegerPartRingEquiv_leadingElement
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      Nonpositive G R) : R⟦G⟧).order ≠ 0) :
    splitCardSuppLTFixedIntegerPartRingEquiv u
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder) Z
        (leadingCardSuppLTFixedIntegerPartElement (K := K) Z b horder) =
      splitTruncationCardSuppLTIntegerPart u
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder) Z b := by
  rw [splitCardSuppLTFixedIntegerPartRingEquiv_apply,
    splitCardSuppLTFixedIntegerPartRingHom_apply,
    splitCardSuppLTIntegerPartRingHom_apply,
    coe_leadingCardSuppLTFixedIntegerPartElement]

/-- In the residue-one branch of LM24, Proposition 9.2.2, bounded source primality is equivalent
to ambient primality of the bounded split truncation, without `(A2)_σ`. -/
theorem isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_tau_eq_one
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hb0 : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b ≠ 0)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (htau : tauBall (K := K)
      (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) = 1) :
    IsPrimal b ↔
      IsPrimal (splitTruncationCardSuppLT u
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) := by
  let sigma := leadingClass
    (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder
  let bFixed := leadingCardSuppLTFixedIntegerPartElement (K := K) Z b horder
  let e := splitCardSuppLTFixedIntegerPartRingEquiv (R := R) (κ := κ) u sigma Z
  calc
    IsPrimal b ↔ IsPrimal bFixed :=
      (isPrimal_leadingCardSuppLTFixedIntegerPartElement_iff Z b hb0 horder).symm
    _ ↔ IsPrimal (e bFixed) := (RingEquiv.isPrimal_iff e bFixed).symm
    _ ↔ IsPrimal (splitTruncationCardSuppLTIntegerPart u sigma Z b) := by
      rw [show e bFixed = splitTruncationCardSuppLTIntegerPart u sigma Z b by
        exact splitCardSuppLTFixedIntegerPartRingEquiv_leadingElement u Z b horder]
    _ ↔ IsPrimal (splitTruncationCardSuppLT u sigma
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) :=
      isPrimal_splitTruncationCardSuppLTIntegerPart_iff_of_tau_eq_one
        u sigma Z b htau

/-- In the residue-zero branch of LM24, Proposition 9.2.2, exact assumption `(A2)_σ` supplies the
bounded inner fraction-field equality. -/
theorem isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_tau_eq_zero
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hb0 : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b ≠ 0)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (hA2 : LM24.AssumptionA2AtFiniteClass (K := K) κ Z
      (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder))
    (htau : tauBall (K := K)
      (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) = 0) :
    IsPrimal b ↔
      IsPrimal (splitTruncationCardSuppLT u
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) := by
  let sigma := leadingClass
    (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder
  let bFixed := leadingCardSuppLTFixedIntegerPartElement (K := K) Z b horder
  let e := splitCardSuppLTFixedIntegerPartRingEquiv (R := R) (κ := κ) u sigma Z
  calc
    IsPrimal b ↔ IsPrimal bFixed :=
      (isPrimal_leadingCardSuppLTFixedIntegerPartElement_iff Z b hb0 horder).symm
    _ ↔ IsPrimal (e bFixed) := (RingEquiv.isPrimal_iff e bFixed).symm
    _ ↔ IsPrimal (splitTruncationCardSuppLTIntegerPart u sigma Z b) := by
      rw [show e bFixed = splitTruncationCardSuppLTIntegerPart u sigma Z b by
        exact splitCardSuppLTFixedIntegerPartRingEquiv_leadingElement u Z b horder]
    _ ↔ IsPrimal (splitTruncationCardSuppLT u sigma
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) :=
      isPrimal_splitTruncationCardSuppLTIntegerPart_iff_of_tau_eq_zero
        u sigma Z hA2 b htau

/-- The set-sized cardinal-bounded core of LM24, Proposition 9.2.2, with `(A2)_σ` required only
when reduction places the leading residue in the zero branch. -/
@[blueprint "fact:leading-class-primality-transfer"
  (phase := "Finitely many Archimedean classes")
  (title := "Primality transfer at the leading Archimedean class")
  (statement := /--
    Let $\kappa$ be an uncountable regular cardinal, $K$ an Archimedean ordered
    division ring, $G$ a linearly ordered abelian group and ordered $K$-module,
    $R$ a field, and $Z$ a subring of $R$; choose the Archimedean splitting of
    $G$.  Let $b\in Z+R((G^{<0}))_\kappa$ be nonzero and reduced, with nonzero
    lowest exponent, and set $\sigma=[v(b)]$ and
    $L_\sigma=R((G_{\prec\sigma}))_\kappa$.  If $(A2)_\sigma$ holds whenever the
    coefficient of exponent $0$ in $\iota_\sigma(b)$ is zero, then $b$ is primal
    in $Z+R((G^{<0}))_\kappa$ if and only if $\iota_\sigma(b)$ is primal in
    $L_\sigma((H_\sigma^{\le 0}))$.  This is the set-sized $\kappa$-bounded form
    of [LM24, Prop. 9.2.2].
  -/)
  (proof := /--
    First restrict to the subring fixed by $T_\sigma$; this does not change the
    primality of $b$.  The splitting $\iota_\sigma$ identifies that subring with
    $S_\sigma+L_\sigma((H_\sigma^{<0}))$.  Reducedness says that the
    coefficient of exponent $0$ is either $0$ or $1$.  In the coefficient-one
    branch it is a unit, so the transfer lemma applies directly.  In the
    coefficient-zero branch, the cofinal alternative in $(A2)_\sigma$ and
    \ref{thm:bounded-hahn-integer-part-fraction-field} give
    $\operatorname{Frac}(S_\sigma)=L_\sigma$; the degenerate alternative gives
    the same equality directly.  The transfer lemma therefore applies in both
    cases.  Transport primality back through the splitting.  Regularity makes
    the split and unsplit support bounds compatible, while uncountability keeps
    quotient supports below $\kappa$.
  -/)]
theorem isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_isReduced_if_A2
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hb0 : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b ≠ 0)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (hbReduced : IsReduced (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b))
    (hA2 : tauBall (K := K)
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) = 0 →
      LM24.AssumptionA2AtFiniteClass (K := K) κ Z
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)) :
    IsPrimal b ↔
      IsPrimal (splitTruncationCardSuppLT u
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) := by
  rcases (isReduced_iff_tau_leadingClass_eq_zero_or_one (K := K)
    (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) hb0 horder).mp hbReduced with
    htau | htau
  · have htauBall : tauBall (K := K)
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) = 0 :=
      (tauBall_eq_zero_iff _ _).mpr htau
    exact isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_tau_eq_zero
      u Z b hb0 horder (hA2 htauBall) htauBall
  · have htauBall : tauBall (K := K)
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) = 1 :=
      tauBall_eq_one_of_tau_eq_one _ _ htau
    exact isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_tau_eq_one
      u Z b hb0 horder htauBall

/-- The unconditional-`(A2)_σ` specialization of the set-sized, `κ`-bounded form of LM24,
Proposition 9.2.2. -/
theorem isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_isReduced
    [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hb0 : CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b ≠ 0)
    (horder : ((CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b :
      Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (hbReduced : IsReduced (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b))
    (hA2 : LM24.AssumptionA2AtFiniteClass (K := K) κ Z
      (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)) :
    IsPrimal b ↔
      IsPrimal (splitTruncationCardSuppLT u
        (leadingClass (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) horder)
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) :=
  isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_isReduced_if_A2
    u Z b hb0 horder hbReduced (fun _ ↦ hA2)

end HahnSeries.Nonpositive
