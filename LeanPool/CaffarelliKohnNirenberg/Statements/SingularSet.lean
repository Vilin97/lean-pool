/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint

/-!
# Singular Set

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open Set


open CKN.Foundation.Parabolic

namespace CKN

/-- The singular set from paper label `def:regular`. -/
@[expose]
def SingularSet (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3) :
    Set ParabolicPoint :=
  {z | z ∈ spaceTimeSet Ω I ∧ ¬ IsRegularPoint Ω I u z}

end CKN
