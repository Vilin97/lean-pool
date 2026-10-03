/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Space Time Test Function

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open Set
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- The smooth compactly supported test-function class on `Ω × I` from paper label `def:sws`; its
  ordinary product space follows the test-function convention of docs/DESIGN_NOTES.md. -/
@[expose]
def spaceTimeTestFunction {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Ω : Set Vec3) (I : Set ℝ) : Set (Vec3 × ℝ → V) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ spaceTimeSet Ω I}

end CKN
