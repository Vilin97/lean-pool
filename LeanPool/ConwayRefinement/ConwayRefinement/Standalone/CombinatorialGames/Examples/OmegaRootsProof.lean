/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.OmegaRoots

/-! # Omega Roots Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.Oz.OmegaRoots.OmegaHasRootsOfEveryPositiveOrder

universe u

/-- The exponent identity `(ω^(1/n))^n = ω` gives the roots; the zero constant coefficient
prevents them from being units. -/
theorem proof : OmegaHasRootsOfEveryPositiveOrder.{u} := by
  intro n hn
  constructor
  · intro hunit
    have hcoeff : Oz.integerConstantCoeff (nthRoot n) = 0 := by
      apply Int.cast_injective (α := ℝ)
      rw [Oz.coe_integerConstantCoeff]
      rw [coe_nthRoot, SurrealHahnSeries.coeff_single_of_ne]
      · simp
      · exact inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne')
    have := hunit.map Oz.integerConstantCoeffRingHom
    rw [Oz.integerConstantCoeffRingHom_apply, hcoeff] at this
    exact not_isUnit_zero this
  · apply Subtype.ext
    change (nthRoot n).1 ^ n = omega.1
    rw [coe_nthRoot, coe_omega]
    rw [Oz.single_one_pow]
    congr 2
    simp [nsmul_eq_mul, Nat.cast_ne_zero.mpr hn.ne']

end ConwayRefinement.Standalone.Oz.OmegaRoots.OmegaHasRootsOfEveryPositiveOrder
