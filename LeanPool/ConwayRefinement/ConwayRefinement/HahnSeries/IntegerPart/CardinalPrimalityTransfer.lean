/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.CardinalSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Assumptions
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.IntegerPartSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.TruncationIntegerPartPrimal

/-!
# Local primality transfer for cardinal-bounded Hahn series

This module applies LM24, Lemma 9.2.1 after the leading-class split has been bundled over the
bounded inner Hahn field. In the zero-residue branch, the exact nonzero-class specialization of
`(A2)_σ` supplies the fraction-field equality. In the residue-one branch no form of `(A2)_σ` is
used.

The remaining step toward LM24, Proposition 9.2.2 is the bounded restriction of the source-side
fixed-ring equivalence. It is kept separate from this local residue calculation.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass

namespace HahnSeries.Nonpositive

variable {K G R : Type*} {κ : Cardinal}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R] [Fact (ℵ₀ < κ)]

/-- The bounded split truncation in the outer integer part whose coefficient subring is the
bounded inner truncation integer part. -/
def splitTruncationCardSuppLTIntegerPart
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    truncationIntegerPart (u.stratum c)
      (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z) := by
  let bFull := CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom Z b
  let bNP := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b
  let hb := CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b
  let y := splitTruncationCardSuppLT u c bNP hb
  refine ⟨y, ?_⟩
  rw [mem_truncationIntegerPart]
  rw [← constantCoeff_apply]
  rw [show constantCoeff y = constantCoeff (splitTruncationCardSuppLT u c bNP hb) from rfl]
  rw [mem_cardSuppLTTruncationIntegerPart]
  constructor
  · rw [coe_constantCoeff_splitTruncationCardSuppLT]
    have htau := tauBall_mem_innerIntegerPartSubring (K := K) (G := G) c Z bFull
    rw [CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom] at htau
    exact (mem_innerIntegerPartSubring_iff (K := K) c Z _).mp htau |>.1
  · rw [coe_constantCoeff_splitTruncationCardSuppLT,
      coeff_zero_tauBall (K := K)]
    rw [show (bNP : R⟦G⟧) =
      (b : CardSuppLTField (G := G) (R := R) (κ := κ)) by
        exact CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom Z b]
    exact (mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp b.2 |>.2

/-- The bounded split integer-part element has the underlying bounded split truncation. -/
@[simp]
theorem coe_splitTruncationCardSuppLTIntegerPart
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    ((splitTruncationCardSuppLTIntegerPart u c Z b :
      truncationIntegerPart (u.stratum c)
        (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z)) :
      Nonpositive (u.stratum c)
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) =
      splitTruncationCardSuppLT u c
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b) :=
  (rfl)

/-- In the residue-one branch, primality in the split bounded integer part is ambient primality. -/
theorem isPrimal_splitTruncationCardSuppLTIntegerPart_iff_of_tau_eq_one
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (htau : tauBall (K := K) c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) = 1) :
    IsPrimal (splitTruncationCardSuppLTIntegerPart u c Z b) ↔
      IsPrimal (splitTruncationCardSuppLT u c
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) := by
  apply isPrimal_truncationIntegerPart_iff_of_constantCoeff_eq_one
    (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z)
  rw [constantCoeffAlgHom_apply]
  apply Subtype.ext
  rw [show ((splitTruncationCardSuppLTIntegerPart u c Z b :
      Nonpositive (u.stratum c)
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) :
      (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))⟦u.stratum c⟧).coeff 0 =
      ((splitTruncationCardSuppLT u c
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
          (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b) :
          Nonpositive (u.stratum c)
            (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) :
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))⟦u.stratum c⟧).coeff 0 from rfl]
  rw [coe_coeff_splitTruncationCardSuppLT]
  rw [← constantCoeff_apply, constantCoeff_splitTruncation, htau]
  rfl

/-- In the residue-zero branch, `(A2)_σ` identifies primality in the split bounded integer part
with ambient primality. -/
theorem isPrimal_splitTruncationCardSuppLTIntegerPart_iff_of_tau_eq_zero
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (hA2 : LM24.AssumptionA2AtFiniteClass (K := K) κ Z c)
    (b : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (htau : tauBall (K := K) c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b) = 0) :
    IsPrimal (splitTruncationCardSuppLTIntegerPart u c Z b) ↔
      IsPrimal (splitTruncationCardSuppLT u c
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b)) := by
  apply isPrimal_truncationIntegerPart_iff_of_constantCoeff_eq_zero
    (cardSuppLTTruncationIntegerPart (G := ↥(ball K c)) (R := R) (κ := κ) Z)
    (LM24.fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_assumptionA2AtFiniteClass
      Z c hA2)
  rw [constantCoeffAlgHom_apply]
  apply Subtype.ext
  rw [show ((splitTruncationCardSuppLTIntegerPart u c Z b :
      Nonpositive (u.stratum c)
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) :
      (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))⟦u.stratum c⟧).coeff 0 =
      ((splitTruncationCardSuppLT u c
        (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z b)
          (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z b) :
          Nonpositive (u.stratum c)
            (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) :
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))⟦u.stratum c⟧).coeff 0 from rfl]
  rw [coe_coeff_splitTruncationCardSuppLT]
  rw [← constantCoeff_apply, constantCoeff_splitTruncation]
  exact htau

end HahnSeries.Nonpositive
