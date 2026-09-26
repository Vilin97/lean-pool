/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.CardinalIntegerPart
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.DegreeTransfer

/-!
# Ordinary omnific integers

An omnific integer is ordinary when it is an integer. A non-ordinary omnific integer has nonzero
lowest exponent in the signed Hahn orientation, and conversely; these are the hypotheses under
which the LM24 leading-class transfer applies.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries NatOrdinal

namespace Surreal.OmnificInteger

universe u

/-- An omnific integer is ordinary when its underlying surreal is an integer. -/
def IsOrdinaryInteger (x : Surreal.OmnificInteger.{u}) : Prop :=
  ∃ z : ℤ, x.1 = (z : Surreal)

/-- Characterization of ordinary omnific integers by an integer witness. -/
theorem isOrdinaryInteger_iff (x : Surreal.OmnificInteger.{u}) :
    IsOrdinaryInteger x ↔ ∃ z : ℤ, x.1 = (z : Surreal) :=
  (Iff.rfl)

/-- A non-ordinary omnific integer has nonzero order in the signed Hahn orientation. -/
theorem signedFullHahnSeries_order_ne_zero_of_not_isOrdinaryInteger
    (x : Surreal.OmnificInteger.{u}) (hx : ¬ IsOrdinaryInteger x) :
    x.1.toSignedFullHahnSeries.order ≠ 0 := by
  intro horder
  have hsupport : x.1.toSignedFullHahnSeries.support ⊆ Set.Iic 0 := by
    intro g hg
    exact x.toSignedNonpositiveHahn.2 (by
      simpa only [coe_toSignedNonpositiveHahn] using hg)
  have hconstant : x.1.toSignedFullHahnSeries =
      HahnSeries.C (x.1.toSignedFullHahnSeries.coeff 0) := by
    ext g
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg]
      by_contra hcoeff
      exact hg (le_antisymm (hsupport hcoeff)
        (horder ▸ HahnSeries.order_le_of_coeff_ne_zero hcoeff))
  have hb := (HahnSeries.mem_cardSuppLTTruncationIntegerPart
    (Z := Surreal.realIntegerSubring)).mp (toSignedSmallSupportIntegerPart x).2
  have hcoeff : x.1.toSignedFullHahnSeries.coeff 0 ∈
      Surreal.realIntegerSubring := by
    rw [← coe_toSignedSmallSupportIntegerPart x]
    exact hb.2
  rw [Surreal.mem_realIntegerSubring] at hcoeff
  obtain ⟨z, hz⟩ := hcoeff
  apply hx
  rw [isOrdinaryInteger_iff]
  refine ⟨z, ?_⟩
  apply Surreal.toSignedFullHahnSeries_injective
  calc
    x.1.toSignedFullHahnSeries =
        HahnSeries.C (x.1.toSignedFullHahnSeries.coeff 0) := hconstant
    _ = HahnSeries.single 0 (x.1.toSignedFullHahnSeries.coeff 0) := by
      ext g
      rw [HahnSeries.C_apply]
    _ = HahnSeries.single 0 (z : ℝ) := by rw [hz]
    _ = ((z : Surreal).toSignedFullHahnSeries) := by
      simpa using (Surreal.toSignedFullHahnSeries_realCast (z : ℝ)).symm

/-- An omnific integer whose signed Conway normal form has nonzero order is not an ordinary
integer. -/
theorem not_isOrdinaryInteger_of_signedFullHahnSeries_order_ne_zero
    (x : Surreal.OmnificInteger.{u}) (horder : x.1.toSignedFullHahnSeries.order ≠ 0) :
    ¬ IsOrdinaryInteger x := by
  rintro ⟨z, hz⟩
  apply horder
  have hcast : x.1.toSignedFullHahnSeries = HahnSeries.single 0 (z : ℝ) := by
    rw [hz]
    simpa using Surreal.toSignedFullHahnSeries_realCast (z : ℝ)
  rw [hcast]
  rcases eq_or_ne (z : ℝ) 0 with hz0 | hz0
  · rw [hz0, HahnSeries.single_eq_zero, HahnSeries.order_zero]
  · exact HahnSeries.order_single hz0

/-- The bounded signed Hahn image of a non-ordinary omnific integer has nonzero order. -/
theorem boundedSignedHahn_order_ne_zero_of_not_isOrdinaryInteger
    (x : Surreal.OmnificInteger.{u}) (hx : ¬ IsOrdinaryInteger x) :
    ((HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
      Surreal.realIntegerSubring (toSignedSmallSupportIntegerPart x) :
        HahnSeries.Nonpositive Surreal ℝ) : HahnSeries Surreal ℝ).order ≠ 0 := by
  rw [HahnSeries.CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom,
    coe_toSignedSmallSupportIntegerPart]
  exact signedFullHahnSeries_order_ne_zero_of_not_isOrdinaryInteger x hx

end Surreal.OmnificInteger
