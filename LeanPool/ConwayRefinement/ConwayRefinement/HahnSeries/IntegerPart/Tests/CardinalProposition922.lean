/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.CardinalProposition922

/-!
# API checks for cardinal-bounded LM24 Proposition 9.2.2

The reduced transfer requires `(A2)_σ` only at the leading Archimedean class. The bounded
fixed-ring equivalence exposes both directions under the explicit regularity hypothesis.
-/

universe u v

public noncomputable section

open Cardinal FiniteArchimedeanClass

namespace Tests

open HahnSeries HahnSeries.Nonpositive

theorem cardinalProposition922
    {K : Type*} {G : Type u} {R : Type v} {κ : Cardinal.{u}}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
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
  isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_isReduced
    u Z b hb0 horder hbReduced hA2

theorem cardinalProposition922_A2_only_if_zero
    {K : Type*} {G : Type u} {R : Type v} {κ : Cardinal.{u}}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R]
    [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
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
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) :=
  isPrimal_iff_isPrimal_splitTruncationCardSuppLT_of_isReduced_if_A2
    u Z b hb0 horder hbReduced hA2

end Tests
