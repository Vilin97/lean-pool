/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinementProof
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.ConwayNormalForm
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Ordinal

/-!
# Checks for the native Conway target

The cut-defined carrier excludes one half, separating it from the entire surreal field.
The public equivalence exposes native subring divisibility. The zero-input certificate ensures
that the standalone statement does not silently exclude the cancellation boundary.
-/

public noncomputable section

universe u

namespace Tests.Conway

open ConwayRefinement.Standalone.Oz

/-- The target's carrier is not the whole field of surreal numbers. -/
theorem half_not_in_carrier : ¬ IsConwayOmnificInteger ((2 : Surreal.{u})⁻¹) := by
  rw [isConwayOmnificInteger_iff_mem]
  exact Surreal.two_inv_not_mem_omnificIntegers

/-- The carrier includes an actual infinite omnific integer, so it is not just the integers. -/
theorem omega_in_carrier :
    IsConwayOmnificInteger (NatOrdinal.of Ordinal.omega0).toSurreal ∧
      ∀ n : ℕ, (n : Surreal.{u}) < (NatOrdinal.of Ordinal.omega0).toSurreal := by
  refine ⟨isConwayOmnificInteger_iff_mem.mpr (NatOrdinal.toSurreal_mem_omnificIntegers _), ?_⟩
  intro n
  rw [← NatOrdinal.toSurreal_natCast n]
  exact NatOrdinal.toSurreal.strictMono (NatOrdinal.natCast_lt_omega0 n)

/-- The endpoint uses divisibility in the actual omnific subring. -/
theorem native_endpoint (h : ConwayConjecture.{u}) (b : Surreal.OmnificInteger.{u}) :
    IsPrimal b := conwayConjecture_iff_forall_isPrimal.mp h b

/-- A zero top row remains within the standalone conjecture's quantifiers. -/
theorem zero_row (h : ConwayConjecture.{u}) :
    ∃ e f g h : Surreal.{u},
      IsConwayOmnificInteger e ∧ IsConwayOmnificInteger f ∧
      IsConwayOmnificInteger g ∧ IsConwayOmnificInteger h ∧
      0 = e * f ∧ 3 = g * h ∧ 0 = e * g ∧ 2 = f * h := by
  have hz : IsConwayOmnificInteger (0 : Surreal.{u}) :=
    isConwayOmnificInteger_iff_mem.mpr (Subring.zero_mem _)
  exact h 0 3 0 2 hz
    (isConwayOmnificInteger_iff_mem.mpr ((3 : Surreal.OmnificInteger).2)) hz
    (isConwayOmnificInteger_iff_mem.mpr ((2 : Surreal.OmnificInteger).2)) (by simp)

end Tests.Conway
