/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.CardinalIntegerPart

/-!
# Checks for the bounded omnific-integer correspondence

This separately compiled client checks both directions of the public additive equivalence and
the conditional ring-equivalence constructor. The generic raw-series equality exercises the
normal-form content; the two-term example excludes the zero and single-monomial degeneracies.
-/

universe u

public noncomputable section

namespace Tests

open Surreal

/-- The monomial `ω` as an omnific integer. -/
def omegaOmnific : Surreal.OmnificInteger.{u} :=
  ⟨ω^ (1 : Surreal.{u}), mem_omnificIntegers.mpr
    (isOmnificInteger_iff_normalForm.mpr ⟨by
      intro i hi
      rw [support_wpow, Set.mem_singleton_iff] at hi
      subst i
      simp, by
      rw [coeff_wpow]
      refine ⟨0, ?_⟩
      simp⟩)⟩

/-- The omnific integer `ω + 3`, with two distinct Conway exponents. -/
def omegaAddThree : Surreal.OmnificInteger.{u} :=
  omegaOmnific + 3

/-- The bounded image retains exactly the full Conway normal form. -/
theorem smallSupportIntegerPart_rawSeries
    (x : Surreal.OmnificInteger.{u}) :
    ((x.toSmallSupportIntegerPart :
      HahnSeries.CardSuppLTField (G := Surrealᵒᵈ) (R := ℝ)
        (κ := Surreal.smallSupportCardinal.{u})) : HahnSeries Surrealᵒᵈ ℝ) =
      x.1.toFullHahnSeries :=
  Surreal.OmnificInteger.coe_toSmallSupportIntegerPart x

/-- The nondegenerate two-term example survives the public round trip. -/
theorem omegaAddThree_smallSupport_roundTrip :
    Surreal.OmnificInteger.ofSmallSupportIntegerPart
        omegaAddThree.toSmallSupportIntegerPart = omegaAddThree :=
  Surreal.OmnificInteger.ofSmallSupportIntegerPart_toSmallSupportIntegerPart _

/-- The bounded Conway/Hahn correspondence preserves multiplication without an extra premise. -/
theorem smallSupportIntegerPart_map_mul
    (x y : Surreal.OmnificInteger.{u}) :
    Surreal.OmnificInteger.smallSupportIntegerPartRingEquiv (x * y) =
      Surreal.OmnificInteger.smallSupportIntegerPartRingEquiv x *
        Surreal.OmnificInteger.smallSupportIntegerPartRingEquiv y :=
  map_mul _ x y

/-- Signed exponent reindexing retains exactly the signed Conway normal form. -/
theorem signedSmallSupportIntegerPart_rawSeries
    (x : Surreal.OmnificInteger.{u}) :
    ((x.toSignedSmallSupportIntegerPart :
      HahnSeries.CardSuppLTField (G := Surreal) (R := ℝ)
        (κ := Surreal.smallSupportCardinal.{u})) : HahnSeries Surreal ℝ) =
      x.1.toSignedFullHahnSeries :=
  Surreal.OmnificInteger.coe_toSignedSmallSupportIntegerPart x

/-- The signed Conway/Hahn correspondence preserves multiplication without an extra premise. -/
theorem signedSmallSupportIntegerPart_map_mul
    (x y : Surreal.OmnificInteger.{u}) :
    Surreal.OmnificInteger.signedSmallSupportIntegerPartRingEquiv (x * y) =
      Surreal.OmnificInteger.signedSmallSupportIntegerPartRingEquiv x *
        Surreal.OmnificInteger.signedSmallSupportIntegerPartRingEquiv y :=
  map_mul _ x y

end Tests
