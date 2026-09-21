/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Combinatorics.ProductOfChainsSperner

/-!
# Cardinality semantics of divisor-rank coefficients

This identifies the executable coefficient recurrence used by factorization
payloads with the actual rank layers of the divisor exponent box.
-/

namespace BGS.NumberTheory

/-- One rank layer in a divisor exponent box. -/
abbrev DivisorExponentLayer
    (factors : List PrimePowerFactor) (rank : ℕ) :=
  {exponentVector : DivisorExponentBox factors //
    divisorExponentRank factors exponentVector = rank}

private def divisorExponentLayerConsEquiv
    (factor : PrimePowerFactor) (factors : List PrimePowerFactor)
    (rank : ℕ) :
    DivisorExponentLayer (factor :: factors) rank ≃
      Σ exponent : Fin (min factor.exponent rank + 1),
        DivisorExponentLayer factors (rank - exponent) where
  toFun exponentVector := by
    have hexponentLeRank :
        (exponentVector.1.2 : ℕ) ≤ rank := by
      have hrank := exponentVector.2
      simp only [divisorExponentRank] at hrank
      omega
    have hexponentLeFactor :
        (exponentVector.1.2 : ℕ) ≤ factor.exponent :=
      Nat.le_of_lt_succ exponentVector.1.2.isLt
    let exponent : Fin (min factor.exponent rank + 1) :=
      ⟨exponentVector.1.2, Nat.lt_succ_iff.mpr
        (le_min hexponentLeFactor hexponentLeRank)⟩
    have htail :
        divisorExponentRank factors exponentVector.1.1 =
          rank - exponent := by
      have hrank := exponentVector.2
      simp only [divisorExponentRank] at hrank
      dsimp [exponent]
      omega
    exact ⟨exponent, ⟨exponentVector.1.1, htail⟩⟩
  invFun point := by
    have hexponentLeRank :
        (point.1 : ℕ) ≤ rank :=
      (Nat.le_of_lt_succ point.1.isLt).trans (min_le_right _ _)
    let exponent : Fin (factor.exponent + 1) :=
      ⟨point.1, Nat.lt_succ_iff.mpr
        ((Nat.le_of_lt_succ point.1.isLt).trans
          (min_le_left _ _))⟩
    have hrank :
        divisorExponentRank factors point.2.1 + exponent = rank := by
      have htail := point.2.2
      dsimp [exponent]
      omega
    exact ⟨(point.2.1, exponent), by
      simp only [divisorExponentRank]
      exact hrank⟩
  left_inv := by
    intro exponentVector
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl
  right_inv := by
    rintro ⟨exponent, tail⟩
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · apply heq_of_eq
      apply Subtype.ext
      rfl

/-- The executable recurrence is exactly the cardinality of the corresponding
rank layer of the exponent box. -/
theorem divisorExponentLayer_card_eq_divisorRankCoefficient
    (factors : List PrimePowerFactor) (rank : ℕ) :
    Fintype.card (DivisorExponentLayer factors rank) =
      divisorRankCoefficient factors rank := by
  induction factors generalizing rank with
  | nil =>
      cases rank with
      | zero =>
          let : Unique (DivisorExponentLayer [] 0) :=
            ⟨⟨PUnit.unit, rfl⟩, fun x ↦ Subtype.ext (Subsingleton.elim (α := PUnit) _ _)⟩
          exact Fintype.card_unique
      | succ rank =>
          change Fintype.card {v : PUnit // 0 = rank + 1} = 0
          exact Fintype.card_eq_zero_iff.mpr ⟨fun x ↦ Nat.noConfusion x.property⟩
  | cons factor factors ih =>
      calc
        Fintype.card
            (DivisorExponentLayer (factor :: factors) rank) =
            Fintype.card
              (Σ exponent :
                  Fin (min factor.exponent rank + 1),
                DivisorExponentLayer factors (rank - exponent)) :=
          Fintype.card_congr
            (divisorExponentLayerConsEquiv factor factors rank)
        _ = ∑ exponent :
              Fin (min factor.exponent rank + 1),
              Fintype.card
                (DivisorExponentLayer factors (rank - exponent)) :=
          Fintype.card_sigma
        _ = ∑ exponent :
              Fin (min factor.exponent rank + 1),
              divisorRankCoefficient factors (rank - exponent) := by
          apply Finset.sum_congr rfl
          intro exponent hexponent
          exact ih _
        _ = ∑ exponent ∈
              Finset.range (min factor.exponent rank + 1),
              divisorRankCoefficient factors (rank - exponent) := by
          exact
            Fin.sum_univ_eq_sum_range
              (fun exponent ↦
                divisorRankCoefficient factors (rank - exponent))
              (min factor.exponent rank + 1)
        _ = divisorRankCoefficient (factor :: factors) rank := by
          rfl

theorem centralDivisorRankCoefficient_eq_layer_card
    (factors : List PrimePowerFactor) :
    centralDivisorRankCoefficient factors =
      Fintype.card
        (DivisorExponentLayer factors
          (primePowerTotalExponent factors / 2)) := by
  rw [centralDivisorRankCoefficient]
  exact
    (divisorExponentLayer_card_eq_divisorRankCoefficient factors
      (primePowerTotalExponent factors / 2)).symm

end BGS.NumberTheory
