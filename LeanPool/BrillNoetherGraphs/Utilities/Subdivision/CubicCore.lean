/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ExplicitPotential

/-!
# Cubic ordered cores

Occurrence-sensitive incidence degree for an ordered explicit core.  Parallel
slots are counted separately, and a loop contributes twice.  Looplessness is
an independent property.
-/

@[expose] public section

namespace Utilities.Certificate.ExplicitPotential.Core

open Finset

/-- Incidence degree, counting every ordered slot endpoint. -/
def incidenceDegree {n p : ℕ} (core : ExplicitPotential.Core n p)
    (vertex : Fin n) : ℕ :=
  ∑ edge : Fin p,
    ((if core.tail edge = vertex then 1 else 0) +
      (if core.head edge = vertex then 1 else 0))

/-- Every vertex has exactly three incident slot endpoints. -/
def Cubic {n p : ℕ} (core : ExplicitPotential.Core n p) : Prop :=
  ∀ vertex : Fin n, core.incidenceDegree vertex = 3

end Utilities.Certificate.ExplicitPotential.Core
