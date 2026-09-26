/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis

/-!
# Spatial Partial

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Factor-wise spatial derivative on the ordinary product space described in
  docs/DESIGN_NOTES.md. -/
@[expose]
def spatialPartial (g : ParabolicPoint → ℝ) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  (fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) (basisVec i)

end CKN
