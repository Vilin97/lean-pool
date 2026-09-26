/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Sumset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Data.Finset.MulAntidiagonal

import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow
import Mathlib.Data.Sum.Order

/-!
# API check for order type of a sumset

This client embeds supports of order types `ω + 1` and `ω` into the lexicographically
ordered group `ℤ ×ₗ (ℤ ×ₗ ℤ)`. Their pointwise sum has order type `ω² + ω`, so the
Hessenberg-product bound of LM24, Fact 2.2.3(3), is attained. Ordinary ordinal multiplication
would instead give `(ω + 1) * ω = ω²`, which is too small.

The example therefore distinguishes the theorem from the plausible but false replacement of
Hessenberg multiplication by ordinary ordinal multiplication. Its auxiliary supports and order
isomorphisms are private.
-/

public noncomputable section

open Ordinal
open scoped Pointwise

namespace Tests

private instance : WellFoundedLT (ℕ ⊕ₗ Unit) :=
  (Sum.Lex.toLexRelIsoLT (α := ℕ) (β := Unit)).symm.toRelEmbedding.wellFounded'

private instance : WellFoundedLT ((ℕ ×ₗ ℕ) ⊕ₗ ℕ) :=
  (Sum.Lex.toLexRelIsoLT (α := ℕ ×ₗ ℕ) (β := ℕ)).symm.toRelEmbedding.wellFounded'

private abbrev SumsetExponentGroup := ℤ ×ₗ (ℤ ×ₗ ℤ)

private def triple (a b c : ℤ) : SumsetExponentGroup :=
  toLex (a, toLex (b, c))

private def leftMap (q : ℕ ⊕ₗ Unit) : SumsetExponentGroup :=
  match ofLex q with
  | Sum.inl n => triple 0 n 0
  | Sum.inr _ => triple 1 0 0

private def rightMap (m : ℕ) : SumsetExponentGroup :=
  triple 0 0 m

private def sumMap (q : (ℕ ×ₗ ℕ) ⊕ₗ ℕ) : SumsetExponentGroup :=
  match ofLex q with
  | Sum.inl p => triple 0 (ofLex p).1 (ofLex p).2
  | Sum.inr m => triple 1 0 m

private def leftSupport : Set SumsetExponentGroup :=
  Set.range leftMap

private def rightSupport : Set SumsetExponentGroup :=
  Set.range rightMap

private def sumSupport : Set SumsetExponentGroup :=
  Set.range sumMap

private theorem triple_add (a b c a' b' c' : ℤ) :
    triple a b c + triple a' b' c' = triple (a + a') (b + b') (c + c') := by
  rfl

private theorem leftMap_strictMono : StrictMono leftMap := by
  intro a b hab
  induction a using Lex.rec with
  | h a =>
      induction b using Lex.rec with
      | h b =>
          cases a with
          | inl n =>
              cases b with
              | inl m =>
                  simp only [Sum.Lex.toLex_lt_toLex, lt_self_iff_false,
                    Sum.lex_inl_inl, leftMap, ofLex_toLex, triple,
                    Prod.Lex.lt_iff, and_false, or_false, true_and,
                    false_or] at hab ⊢
                  exact_mod_cast hab
              | inr u =>
                  simp only [Sum.Lex.toLex_lt_toLex, lt_self_iff_false,
                    Sum.Lex.sep, leftMap, ofLex_toLex, triple,
                    Prod.Lex.lt_iff, zero_lt_one, zero_ne_one,
                    Int.natCast_eq_zero, and_false, or_false,
                    false_and] at hab ⊢
          | inr u =>
              cases b with
              | inl n =>
                  simp only [Sum.Lex.toLex_lt_toLex, lt_self_iff_false,
                    Sum.lex_inr_inl] at hab
              | inr v => simp only [lt_self_iff_false] at hab

private theorem rightMap_strictMono : StrictMono rightMap := by
  intro a b hab
  simpa [rightMap, triple, Prod.Lex.lt_iff] using hab

private theorem sumMap_strictMono : StrictMono sumMap := by
  intro a b hab
  induction a using Lex.rec with
  | h a =>
      induction b using Lex.rec with
      | h b =>
          cases a with
          | inl p =>
              cases b with
              | inl q =>
                  simp only [Sum.Lex.toLex_lt_toLex, Prod.Lex.lt_iff,
                    Sum.lex_inl_inl, sumMap, ofLex_toLex, triple,
                    lt_self_iff_false, true_and, false_or] at hab ⊢
                  exact_mod_cast hab
              | inr m =>
                  simp only [Sum.Lex.toLex_lt_toLex, Prod.Lex.lt_iff,
                    Sum.Lex.sep, sumMap, ofLex_toLex, triple,
                    zero_lt_one, zero_ne_one, Int.natCast_eq_zero,
                    false_and, or_false] at hab ⊢
          | inr m =>
              cases b with
              | inl p =>
                  simp only [Sum.Lex.toLex_lt_toLex, Prod.Lex.lt_iff,
                    Sum.lex_inr_inl] at hab
              | inr n =>
                  simp only [Sum.Lex.toLex_lt_toLex, Prod.Lex.lt_iff,
                    Sum.lex_inr_inr, sumMap, ofLex_toLex, triple,
                    lt_self_iff_false, true_and,
                    false_or] at hab ⊢
                  exact_mod_cast hab

private def leftOrderIso : (ℕ ⊕ₗ Unit) ≃o leftSupport where
  toEquiv := Equiv.ofInjective leftMap leftMap_strictMono.injective
  map_rel_iff' := leftMap_strictMono.le_iff_le

private def rightOrderIso : ℕ ≃o rightSupport where
  toEquiv := Equiv.ofInjective rightMap rightMap_strictMono.injective
  map_rel_iff' := rightMap_strictMono.le_iff_le

private def sumOrderIso : ((ℕ ×ₗ ℕ) ⊕ₗ ℕ) ≃o sumSupport where
  toEquiv := Equiv.ofInjective sumMap sumMap_strictMono.injective
  map_rel_iff' := sumMap_strictMono.le_iff_le

private theorem leftSupport_isPWO : leftSupport.IsPWO := by
  simpa [leftSupport] using
    (Set.IsPWO.of_linearOrder (Set.univ : Set (ℕ ⊕ₗ Unit))).image_of_monotone
      leftMap_strictMono.monotone

private theorem rightSupport_isPWO : rightSupport.IsPWO := by
  simpa [rightSupport] using
    (Set.IsPWO.of_linearOrder (Set.univ : Set ℕ)).image_of_monotone
      rightMap_strictMono.monotone

private theorem sumSupport_isPWO : sumSupport.IsPWO := by
  simpa [sumSupport] using
    (Set.IsPWO.of_linearOrder
      (Set.univ : Set ((ℕ ×ₗ ℕ) ⊕ₗ ℕ))).image_of_monotone
        sumMap_strictMono.monotone

private theorem add_supports : leftSupport + rightSupport = sumSupport := by
  ext z
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, rfl⟩
    induction a using Lex.rec with
    | h a =>
        cases a with
        | inl n =>
            refine ⟨Sum.inlₗ (toLex (n, b)), ?_⟩
            simp only [sumMap, leftMap, rightMap, ofLex_toLex]
            rw [triple_add]
            simp
        | inr u =>
            refine ⟨Sum.inrₗ b, ?_⟩
            simp only [sumMap, leftMap, rightMap, ofLex_toLex]
            rw [triple_add]
            simp
  · rintro ⟨q, rfl⟩
    induction q using Lex.rec with
    | h q =>
        cases q with
        | inl p =>
            apply Set.mem_add.mpr
            refine ⟨leftMap (Sum.inlₗ (ofLex p).1), ⟨_, rfl⟩,
              rightMap (ofLex p).2, ⟨_, rfl⟩, ?_⟩
            simp only [leftMap, rightMap, sumMap, ofLex_toLex]
            rw [triple_add]
            simp
        | inr m =>
            apply Set.mem_add.mpr
            refine ⟨leftMap (Sum.inrₗ ()), ⟨_, rfl⟩,
              rightMap m, ⟨_, rfl⟩, ?_⟩
            simp only [leftMap, rightMap, sumMap, ofLex_toLex]
            rw [triple_add]
            simp

private theorem left_orderType :
    leftSupport_isPWO.orderType = Ordinal.omega0 + 1 := by
  rw [Set.IsPWO.orderType_eq_typeLT_of_orderIso
    leftSupport_isPWO leftOrderIso.symm]
  calc
    typeLT (ℕ ⊕ₗ Unit) =
        Ordinal.type (Sum.Lex (· < · : ℕ → ℕ → Prop)
          (· < · : Unit → Unit → Prop)) :=
      (Sum.Lex.toLexRelIsoLT (α := ℕ) (β := Unit)).ordinalType_congr.symm
    _ = Ordinal.omega0 + 1 := by
      rw [Ordinal.type_sum_lex, Ordinal.type_nat_lt]
      simp

private theorem right_orderType :
    rightSupport_isPWO.orderType = Ordinal.omega0 := by
  rw [Set.IsPWO.orderType_eq_typeLT_of_orderIso
      rightSupport_isPWO rightOrderIso.symm,
    Ordinal.type_nat_lt]

private theorem sum_orderType :
    sumSupport_isPWO.orderType =
      Ordinal.omega0 ^ (2 : Ordinal) + Ordinal.omega0 := by
  rw [Set.IsPWO.orderType_eq_typeLT_of_orderIso
    sumSupport_isPWO sumOrderIso.symm]
  calc
    typeLT ((ℕ ×ₗ ℕ) ⊕ₗ ℕ) =
        typeLT (ℕ ×ₗ ℕ) + typeLT ℕ := by
      rw [← Ordinal.type_sum_lex]
      exact (Sum.Lex.toLexRelIsoLT (α := ℕ ×ₗ ℕ) (β := ℕ)).ordinalType_congr.symm
    _ = (typeLT ℕ) * (typeLT ℕ) + typeLT ℕ := by
      congr 1
    _ = Ordinal.omega0 * Ordinal.omega0 + Ordinal.omega0 := by
      rw [Ordinal.type_nat_lt]
    _ = Ordinal.omega0 ^ (2 : Ordinal) + Ordinal.omega0 := by
      have hsucc : (1 : Ordinal) + 1 = 2 := one_add_one_eq_two
      rw [← hsucc, Ordinal.opow_add_one, Ordinal.opow_one]

private theorem naturalProduct_value :
    (NatOrdinal.of (Ordinal.omega0 + 1) * NatOrdinal.of Ordinal.omega0).val =
      Ordinal.omega0 ^ (2 : Ordinal) + Ordinal.omega0 := by
  have homega : NatOrdinal.of Ordinal.omega0 = ω^ (1 : NatOrdinal) := by
    rw [NatOrdinal.wpow_def, NatOrdinal.val_one, Ordinal.opow_one]
  rw [NatOrdinal.of_add_one, homega, add_mul, one_mul,
    ← NatOrdinal.wpow_add, one_add_one_eq_two,
    NatOrdinal.wpow_add_wpow (show (1 : NatOrdinal) ≤ 2 by simp)]
  rw [NatOrdinal.val_of]
  change Ordinal.omega0 ^ (2 : Ordinal) +
    Ordinal.omega0 ^ (1 : Ordinal) = _
  rw [Ordinal.opow_one]

/-- The Hessenberg sumset bound is sharp when the corresponding ordinary ordinal product is too
small. -/
theorem naturalSumsetBound_distinguishes_ordinaryMul :
    ∃ (s t : Set (ℤ ×ₗ (ℤ ×ₗ ℤ))) (hs : s.IsPWO) (ht : t.IsPWO),
      (hs.add ht).orderType =
          (NatOrdinal.of hs.orderType * NatOrdinal.of ht.orderType).val ∧
        ¬(hs.add ht).orderType ≤ hs.orderType * ht.orderType := by
  let hs : leftSupport.IsPWO := leftSupport_isPWO
  let ht : rightSupport.IsPWO := rightSupport_isPWO
  refine ⟨leftSupport, rightSupport, hs, ht, ?_, ?_⟩
  · apply le_antisymm
    · exact Set.IsPWO.orderType_add_le_naturalMul hs ht
    · rw [Set.IsPWO.orderType_congr (hs.add ht)
          sumSupport_isPWO add_supports,
        sum_orderType, left_orderType, right_orderType]
      exact naturalProduct_value.le
  · rw [Set.IsPWO.orderType_congr (hs.add ht)
        sumSupport_isPWO add_supports,
      sum_orderType, left_orderType, right_orderType]
    have hordinary : (Ordinal.omega0 + 1) * Ordinal.omega0 =
        Ordinal.omega0 ^ (2 : Ordinal) := by
      rw [Ordinal.add_mul_of_isSuccLimit Ordinal.one_add_omega0
        Ordinal.isSuccLimit_omega0]
      have hsucc : (1 : Ordinal) + 1 = 2 := one_add_one_eq_two
      rw [← hsucc, Ordinal.opow_add_one, Ordinal.opow_one]
    rw [hordinary]
    exact not_le_of_gt (lt_add_of_pos_right _ Ordinal.omega0_pos)

end Tests
