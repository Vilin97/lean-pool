/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.OneRowPrime
public import LeanPool.ConwayRefinement.ConwayRefinement.Examples.OmnificInteger.OneRowPrime

import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.ConwayNormalForm

/-!
# Proofs for Conway's one-row prime

The normal-form ring equivalence identifies the displayed series with the
cut-defined omnific integer whose irreducibility and primeness are proved from Berarducci's
theorem and the finite-degree primality theorem.
-/

public noncomputable section

namespace ConwayRefinement.Standalone.Oz.OneRowExample

/-- The independent displayed normal form agrees with the one used by the main proof. -/
private theorem normalForm_eq_main : OneRowExample.normalForm =
    Surreal.OmnificInteger.OneRowExample.normalForm := by
  rfl

namespace HasDisplayedCoefficients

/-- The concrete construction has the displayed coefficient function. -/
theorem proof : HasDisplayedCoefficients := by
  classical
  have hcoeff (i : Surreal) : oneRowOz.1.coeff i =
      if IsDisplayedExponent i then 1 else 0 := by
    rw [oneRowOz_val, normalForm_coeff]
    unfold coefficient IsDisplayedExponent
    congr 1
    apply propext
    constructor
    · rintro ⟨p, rfl⟩
      induction p using WithTop.recTopCoe with
      | top => exact Or.inl rfl
      | coe n => exact Or.inr ⟨n, by simp [exponentAtIndex]⟩
    · rintro (rfl | ⟨n, rfl⟩)
      · exact ⟨⊤, by simp [exponentAtIndex]⟩
      · exact ⟨(n : Index), by simp [exponentAtIndex, exponent_apply]⟩
  constructor
  · intro i hi
    rw [hcoeff, ite_eq_left hi]
  · intro i hi
    rw [hcoeff, ite_eq_right hi]

end HasDisplayedCoefficients

namespace HasExactSupportOrderType

/-- The displayed normal form has support order type `ω + 1`. -/
theorem proof : OneRowExample.HasExactSupportOrderType := by
  rw [OneRowExample.HasExactSupportOrderType, OneRowExample.oneRowOz_val]
  rw [normalForm_eq_main]
  rw [← Surreal.OmnificInteger.OneRowExample.oneRowOz_toHahnSeries,
    Surreal.length_toHahnSeries]
  exact Surreal.OmnificInteger.OneRowExample.oneRowOz_length

end HasExactSupportOrderType

private theorem normalFormRingEquiv_oneRowOz :
    ConwayRefinement.Standalone.Oz.normalFormRingEquiv
        OneRowExample.oneRowOz =
      Surreal.OmnificInteger.OneRowExample.oneRowOz := by
  apply Subtype.ext
  rw [← Surreal.toHahnSeries_inj]
  rw [ConwayRefinement.Standalone.Oz.toHahnSeries_normalFormRingEquiv,
    OneRowExample.oneRowOz_val,
    normalForm_eq_main,
    Surreal.OmnificInteger.OneRowExample.oneRowOz_toHahnSeries]

namespace IsPrime

/-- Conway's displayed one-row omnific integer is prime. -/
theorem proof : OneRowExample.IsPrime := by
  rw [OneRowExample.IsPrime]
  have hmap : Prime
      (ConwayRefinement.Standalone.Oz.normalFormRingEquiv
        OneRowExample.oneRowOz) := by
    rw [normalFormRingEquiv_oneRowOz]
    exact Surreal.OmnificInteger.OneRowExample.oneRowOz_prime
  exact (MulEquiv.prime_iff
    ConwayRefinement.Standalone.Oz.normalFormRingEquiv.toMulEquiv).mp hmap

end IsPrime

end ConwayRefinement.Standalone.Oz.OneRowExample
