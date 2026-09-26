/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.CardinalPrimalityTransfer

/-!
# API checks for cardinal-bounded local primality transfer

This separately compiled client exercises both reduced-residue branches after the leading-class
split. The zero branch consumes the exact finite-class form of `(A2)_σ`; the one branch does not.
-/

universe u v

public noncomputable section

open Cardinal FiniteArchimedeanClass

namespace Tests

open HahnSeries HahnSeries.Nonpositive

theorem cardinalPrimalityTransfer_residue_one
    {K : Type*} {G : Type u} {R : Type v} {κ : Cardinal.{u}}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R] [Fact (ℵ₀ < κ)]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (htau : tauBall (K := K) c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) = 1) :
    IsPrimal (splitTruncationCardSuppLTIntegerPart u c Z b) ↔
      IsPrimal (splitTruncationCardSuppLT u c
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) :=
  isPrimal_splitTruncationCardSuppLTIntegerPart_iff_of_tau_eq_one u c Z b htau

theorem cardinalPrimalityTransfer_residue_zero
    {K : Type*} {G : Type u} {R : Type v} {κ : Cardinal.{u}}
    [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Field R] [Fact (ℵ₀ < κ)]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) (hA2 : LM24.AssumptionA2AtFiniteClass (K := K) κ Z c)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (htau : tauBall (K := K) c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) = 0) :
    IsPrimal (splitTruncationCardSuppLTIntegerPart u c Z b) ↔
      IsPrimal (splitTruncationCardSuppLT u c
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) :=
  isPrimal_splitTruncationCardSuppLTIntegerPart_iff_of_tau_eq_zero
    u c Z hA2 b htau

end Tests
