/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Time Partial

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Factor-wise time derivative on the ordinary product space described in docs/DESIGN_NOTES.md. -/
@[expose]
def timePartial (g : ParabolicPoint → ℝ) (z : ParabolicPoint) : ℝ :=
  (fderiv ℝ (fun s : ℝ => g (z.1, s)) z.2) 1

end CKN
