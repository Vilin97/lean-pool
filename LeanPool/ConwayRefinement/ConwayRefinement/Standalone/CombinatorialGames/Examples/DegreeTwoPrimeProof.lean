/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.DegreeTwoPrime
public import LeanPool.ConwayRefinement.ConwayRefinement.Examples.OmnificInteger.DegreeTwoPrime

import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.ConwayNormalForm

/-!
# Proofs for the explicit degree-two prime

The normal-form ring equivalence identifies the displayed series with the reduced omnific
integer whose irreducibility and primeness follow from the PS06 criterion and the one-class
transfer.
-/

universe u

public noncomputable section

namespace ConwayRefinement.Standalone.Oz.DegreeTwoExample

/-- The independent displayed normal form agrees with the one used by the main proof. -/
private theorem normalForm_eq_main : DegreeTwoExample.normalForm.{u} =
    Surreal.OmnificInteger.DegreeTwoExample.normalForm := by
  rfl

namespace HasExactSupportOrderType

/-- The displayed normal form has support order type `ω ^ 2 + 1`. -/
theorem proof : DegreeTwoExample.HasExactSupportOrderType.{u} := by
  rw [DegreeTwoExample.HasExactSupportOrderType, DegreeTwoExample.degreeTwoOz_val]
  rw [normalForm_eq_main]
  rw [← Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz_toHahnSeries,
    Surreal.length_toHahnSeries]
  exact Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz_length

end HasExactSupportOrderType

private theorem normalFormRingEquiv_degreeTwoOz :
    ConwayRefinement.Standalone.Oz.normalFormRingEquiv
        DegreeTwoExample.degreeTwoOz.{u} =
      Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz := by
  apply Subtype.ext
  rw [← Surreal.toHahnSeries_inj]
  rw [ConwayRefinement.Standalone.Oz.toHahnSeries_normalFormRingEquiv,
    DegreeTwoExample.degreeTwoOz_val,
    normalForm_eq_main,
    Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz_toHahnSeries]

namespace IsPrime

/-- The displayed degree-two omnific integer is prime. -/
theorem proof : DegreeTwoExample.IsPrime.{u} := by
  rw [DegreeTwoExample.IsPrime]
  have hmap : Prime
      (ConwayRefinement.Standalone.Oz.normalFormRingEquiv
        DegreeTwoExample.degreeTwoOz) := by
    rw [normalFormRingEquiv_degreeTwoOz]
    exact Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz_prime
  exact (MulEquiv.prime_iff
    ConwayRefinement.Standalone.Oz.normalFormRingEquiv.toMulEquiv).mp hmap

end IsPrime

namespace FoilHasExactSupportOrderType

/-- The coefficient-doubled foil has the same exact support order type. -/
theorem proof : DegreeTwoExample.FoilHasExactSupportOrderType.{u} := by
  rw [DegreeTwoExample.FoilHasExactSupportOrderType]
  have hlength : DegreeTwoExample.degreeTwoFoil.1.length =
      DegreeTwoExample.degreeTwoOz.1.length := by
    apply le_antisymm
    · apply SurrealHahnSeries.length_mono
      rw [DegreeTwoExample.degreeTwoFoil_support]
    · apply SurrealHahnSeries.length_mono
      rw [DegreeTwoExample.degreeTwoFoil_support]
  exact hlength.trans HasExactSupportOrderType.proof.{u}

end FoilHasExactSupportOrderType

private theorem two_not_isUnit :
    ¬ IsUnit (2 : Oz.OmnificInteger.{u}) := by
  intro h
  have hmap : IsUnit
      (Oz.integerConstantCoeffRingHom (2 : Oz.OmnificInteger)) :=
    h.map Oz.integerConstantCoeffRingHom
  have heq : Oz.integerConstantCoeffRingHom
      (2 : Oz.OmnificInteger) = 2 :=
    map_natCast Oz.integerConstantCoeffRingHom 2
  rw [heq, Int.isUnit_iff] at hmap
  omega

namespace FoilHasNontrivialFactorization

/-- The displayed factorisation has the nonunits `2` and `degreeTwoOz`. -/
theorem proof : DegreeTwoExample.FoilHasNontrivialFactorization.{u} := by
  rw [DegreeTwoExample.FoilHasNontrivialFactorization]
  exact ⟨2, DegreeTwoExample.degreeTwoOz, rfl, two_not_isUnit,
    IsPrime.proof.not_unit⟩

end FoilHasNontrivialFactorization

namespace FoilIsCoefficientDouble

/-- The foil's defining equation is `degreeTwoFoil = 2 * degreeTwoOz`. -/
theorem proof : DegreeTwoExample.FoilIsCoefficientDouble.{u} := rfl

end FoilIsCoefficientDouble

namespace HasDisplayedCoefficients

/-- The concrete construction has the displayed coefficient function. -/
theorem proof : HasDisplayedCoefficients.{u} := by
  classical
  have hcoeff (i : Surreal.{u}) : degreeTwoOz.{u}.1.coeff i =
      if IsDisplayedExponent i then 1 else 0 := by
    rw [degreeTwoOz_val, normalForm_coeff]
    unfold coefficient IsDisplayedExponent
    congr 1
    apply propext
    constructor
    · rintro ⟨p, rfl⟩
      induction p using WithTop.recTopCoe with
      | top => exact Or.inl rfl
      | coe p => exact Or.inr ⟨(ofLex p).1, (ofLex p).2, by simp [exponentAtIndex]⟩
    · rintro (rfl | ⟨m, n, rfl⟩)
      · exact ⟨⊤, by simp [exponentAtIndex]⟩
      · exact ⟨((toLex (m, n) : Lex (ℕ × ℕ)) : Index),
          by simp [exponentAtIndex, exponent_apply]⟩
  constructor
  · intro i hi
    rw [hcoeff, if_pos hi]
  · intro i hi
    rw [hcoeff, if_neg hi]

end HasDisplayedCoefficients

end ConwayRefinement.Standalone.Oz.DegreeTwoExample
