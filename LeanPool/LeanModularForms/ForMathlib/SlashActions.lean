/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.ModularForms.SlashActions


/- This is from the Sphere Pack project, so might not actually be for mathlib.-/

-- Maybe this belongs in NumberTheory/ModularForms/SlashActions.lean, next to ModularForm.mul_slash

/-! # SlashActions -/


local notation "GL(" n ", " R ")" "⁺" => @Matrix.GLPos (Fin n) R (instDecidableEqFin n)
  (Fin.fintype n) Real.linearOrderedCommRing

open ModularForm MatrixGroups UpperHalfPlane

/- Looks like the way to fix the errors is to replace each GL(n, ℝ)⁺ with
  `@Matrix.GLPos (Fin 2) ℝ (instDecidableEqFin 2) (Fin.fintype 2) Real.linearOrderedCommRing :
  Subgroup (GL (Fin 2) ℝ)`... but it's just so ugly!
-/

/-- Slash action under -I₂ as a GL(n, ℝ)⁺ matrix. See `ModularForm.slash_neg_one'` for the SL(2, ℤ)
version. -/
theorem ModularForm.slash_neg_one {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : (GL (Fin 2) ℝ)) =
    f ∣[k] (1 : (GL (Fin 2) ℝ)) := by simp [slash_def, denom, hk.neg_one_zpow, Matrix.det_neg, σ]

/-- Slash action under -I₂ as a SL(2, ℤ) matrix. See `ModularForm.slash_neg_one` for the GL(n, ℝ)⁺
version. -/
theorem ModularForm.slash_neg_one' {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : SL(2, ℤ)) = f ∣[k] (1 : SL(2, ℤ)) := by simp [SL_slash_def, denom, hk.neg_one_zpow]

/-- See `ModularForm.slash_neg'` for the version where `g` is a SL(2, ℤ) matrix. -/
theorem ModularForm.slash_neg {k : ℤ} (g : GL (Fin 2) ℝ) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [← neg_one_mul, SlashAction.slash_mul, slash_neg_one f hk, SlashAction.slash_one]

/-- See `ModularForm.slash_neg` for the version where `g` is a GL(n, ℝ)⁺ matrix. -/
theorem ModularForm.slash_neg' {k : ℤ} (g : SL(2, ℤ)) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [SL_slash, ← slash_neg _ _ hk]
  congr
  ext
  simp
