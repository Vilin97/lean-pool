/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.Alpha
public import LeanPool.CaffarelliKohnNirenberg.Statements.Beta
public import LeanPool.CaffarelliKohnNirenberg.Statements.Delta

/-!
# Theta

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open CKN.Foundation.Parabolic

namespace CKN

/-- The iteration quantity θ from the manuscript, `eq:theta`. -/
noncomputable def theta (κ : ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  alpha u z r + beta u Du z r + κ ^ (-4 : ℝ) * (delta p z r) ^ (2 : ℕ)

end CKN
