/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/

import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameExact
import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameBoosters
import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameResidues

/-!
# Finite frame bank
-/

namespace HypergraphLowerBound

/-- Every exact small frame, booster, and residue gadget listed in the appendices
    satisfies the stated frame inequalities. -/
theorem finite_bank_valid :
    (∀ spec ∈ exactSmallFrames, spec.IsValid) ∧
    (∀ spec ∈ boosters, spec.IsValid) ∧
    (∀ spec ∈ residueGadgets, spec.IsValid) := by
  exact ⟨exactSmallFrames_valid, boosters_valid, residueGadgets_valid⟩

end HypergraphLowerBound
