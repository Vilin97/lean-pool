/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.RealModule
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Pow

/-!
# API checks for the ordered real module structure on surreal numbers

The first check identifies scalar multiplication with the standard real embedding. The second
uses the genuinely non-real surreal `ω` and confirms that multiplication by a positive real is
strictly monotone on it.
-/

public noncomputable section

namespace Tests

theorem surreal_real_smul (r : ℝ) (x : Surreal) :
    r • x = (r : Surreal) * x :=
  Surreal.real_smul_def r x

theorem surreal_real_smul_omega_strictMono :
    StrictMono (fun r : ℝ ↦ r • (ω^ (0 : Surreal))) := by
  intro r s hrs
  change r • (ω^ (0 : Surreal)) < s • (ω^ (0 : Surreal))
  rw [Surreal.real_smul_def, Surreal.real_smul_def]
  exact mul_lt_mul_of_pos_right (Real.toSurreal_lt_iff.mpr hrs) (Surreal.wpow_pos 0)

end Tests
