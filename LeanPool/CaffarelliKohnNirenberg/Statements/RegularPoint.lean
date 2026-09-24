/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecOn
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Regular Point

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- The regular-point predicate from paper label `def:regular`, with the Hölder representative
  convention of docs/DESIGN_NOTES.md. -/
def IsRegularPoint (Ω : Set Vec3) (I : Set ℝ)
    (u : ParabolicPoint → Vec3) (z₀ : ParabolicPoint) : Prop :=
  z₀ ∈ spaceTimeSet Ω I ∧
    ∃ N : Set ParabolicPoint, IsOpen N ∧ z₀ ∈ N ∧
      N ⊆ spaceTimeSet Ω I ∧ ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict N] u ∧ ParabolicHolderVecOn N w γ

end CKN
