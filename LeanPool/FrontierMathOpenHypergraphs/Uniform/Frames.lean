/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameDefs
import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameBoosters
import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameExact
import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameResidues
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Finite frame bank
-/

@[expose] public section

namespace HypergraphLowerBound

/-- Every exact small frame, booster, and residue gadget listed in the appendices
    satisfies the stated frame inequalities. -/
theorem finite_bank_valid :
    (∀ spec ∈ exactSmallFrames, spec.IsValid) ∧
    (∀ spec ∈ boosters, spec.IsValid) ∧
    (∀ spec ∈ residueGadgets, spec.IsValid) := by
  exact ⟨exactSmallFrames_valid, boosters_valid, residueGadgets_valid⟩

end HypergraphLowerBound
