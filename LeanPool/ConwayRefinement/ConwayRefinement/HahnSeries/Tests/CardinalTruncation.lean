/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation

/-!
# API checks for cardinal-bounded Hahn truncation integer parts

This separately compiled client exercises the support-cofinality and zero-exponent-group
fraction-field branches. These checks certify the public interfaces; the cofinality proof itself
provides the nondegenerate semantic content by constructing a monomial denominator for an
arbitrary bounded series.
-/

universe u v

public noncomputable section

open Cardinal

namespace Tests

open HahnSeries

theorem cardSuppLTTruncation_fraction_of_cofinality
    {G : Type u} {R : Type v} {κ : Cardinal.{u}}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field R]
    [Fact (ℵ₀ < κ)] (Z : Subring R) (hcof : κ ≤ Order.cof G) :
    Subring.fracSubring
      (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) = ⊤ :=
  fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_le_cof Z hcof

theorem cardSuppLTTruncation_fraction_of_zero_exponent_group
    {G : Type u} {R : Type v} {κ : Cardinal.{u}}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Subsingleton G] [Field R]
    [Fact (ℵ₀ < κ)] (Z : Subring R) (hfrac : Subring.fracSubring Z = ⊤) :
    Subring.fracSubring
      (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) = ⊤ :=
  fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_subsingleton Z hfrac

theorem zero_mem_cardSuppLTTruncationIntegerPart
    {G : Type u} {R : Type v} {κ : Cardinal.{u}}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field R]
    [Fact (ℵ₀ < κ)] (Z : Subring R) :
    (0 : CardSuppLTField (G := G) (R := R) (κ := κ)) ∈
      cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := by
  rw [mem_cardSuppLTTruncationIntegerPart]
  simp

end Tests
