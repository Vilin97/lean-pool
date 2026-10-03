/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import LeanPool.NavierStokesAndEuler.ForMathlib.ElaborationShortcuts

/-!
# Continuity of addition on bounded continuous functions

For bounded continuous functions with values in a normed ring, such as the continuous linear
endomorphisms of a normed space, instance resolution derives `ContinuousAdd (α →ᵇ β)` from the
topological ring structure. The addition in that instance is the one of the ring, while a space of
continuous linear maps out of `C(K, α →ᵇ β)` is stated with the addition of the additive group, so
every declaration mentioning such a space makes the kernel compare the two additions.

The instance below derives the continuity from the additive group, for every seminormed group of
values, and is tried first.
-/

public section

namespace NavierStokesAndEuler

open scoped BoundedContinuousFunction

variable {α β : Type*} [TopologicalSpace α] [SeminormedAddCommGroup β]

instance (priority := high) BoundedContinuousFunctionShortcut.instContinuousAdd :
    ContinuousAdd (α →ᵇ β) := inferInstance

end NavierStokesAndEuler

end
