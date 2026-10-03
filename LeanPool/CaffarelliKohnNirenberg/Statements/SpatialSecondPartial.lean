/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial

/-!
# Spatial Second Partial

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- The iterated spatial derivative used in the local energy inequality. -/
@[expose]
def spatialSecondPartial (g : ParabolicPoint → ℝ) (i j : Fin 3)
    (z : ParabolicPoint) : ℝ :=
  spatialPartial (fun w => spatialPartial g i w) j z

end CKN
