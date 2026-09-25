/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CubeFold

/-! # The cube contribution of a forest index

Defines `ForestIndex.cubeContribution`, the ordinary cube contribution
attached to an abstract forest index — the integral over `[0,1]^{E(F)}` of
the forest mixed partial at the interpolated point — realized through a
canonical grown forest and independent of the active-extension choice
system used to realize it.  This is the right-hand side of the flagship
form of the BKAR forest interpolation formula (see `BKAR.Formula`).
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace ForestIndex

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The ordinary cube contribution attached to an abstract forest index.

The value is independent of the active-extension choice system used to realize
the support as a `Forest` representative; if no such system is available, this definition
uses `0` as a harmless fallback. The public BKAR theorem will remove that
fallback by constructing a global choice system.
-/
def cubeContribution (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  by
    classical
    exact
      if hchoices : Nonempty (Forest.ActiveExtensionChoice V) then
        (Forest.canonicalGrownForestForSupport (Classical.choice hchoices) I)
          |>.cubeContribution ρ
      else
        0

/--
Any concrete active-extension choice system realizes the same abstract
forest-index cube contribution.
-/
theorem cubeContribution_eq_canonicalGrownForestForSupport
    (I : ForestIndex V) (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    I.cubeContribution ρ =
      (Forest.canonicalGrownForestForSupport choices I).cubeContribution ρ := by
  classical
  unfold cubeContribution
  rw [dite_eq_left ⟨choices⟩]
  exact
    Forest.canonicalGrownForestForSupport_cubeContribution_eq_of_choices
      (Classical.choice ⟨choices⟩) choices I ρ hρ

end ForestIndex

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
