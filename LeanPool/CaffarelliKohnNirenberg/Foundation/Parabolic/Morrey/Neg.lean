/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# Neg

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory
open scoped ENNReal


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- Negation leaves the parabolic Morrey seminorm invariant. -/
theorem morreyNorm_neg (p q : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (fun z => -f z) = morreyNorm p q f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

/-- Absolute value leaves the parabolic Morrey seminorm invariant. -/
theorem morreyNorm_abs (p q : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (fun z => |f z|) = morreyNorm p q f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_abs]

end CKN.Foundation.Parabolic.Morrey
