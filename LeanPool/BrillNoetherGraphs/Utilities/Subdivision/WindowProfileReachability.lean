/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.WindowProfile
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.StrongSeparator

/-!
# Reachability consequences of signed window profiles

The endpoint formula for a compatible window profile can be used directly as
a linear-equivalence witness.  These lemmas package that use for winnability
and one-chip reachability without imposing restrictions on the profile slopes.
-/

namespace Utilities.Certificate.WindowProfile.Data
open Utilities.Certificate

open Utilities

open Finset
open SubdivisionGraph

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p}

/-- The signed sum of the start and stop endpoint divisors of a profile. -/
def endpointDivisors (data : Data spec) : CFDiv spec.graph :=
  ∑ edge : Fin p,
    data.slope edge •
      (one_chip (G := spec.graph)
          (spec.pathVertex edge (data.startPosition edge)) -
        one_chip (G := spec.graph)
          (spec.pathVertex edge (data.stopPosition edge)))

/-- Adding the signed endpoint divisor of a compatible window profile is a
linear equivalence. -/
theorem linearEquiv_add_endpointDivisors (data : Data spec)
    (D : CFDiv spec.graph) :
    linear_equiv spec.graph D (D + data.endpointDivisors) := by
  rw [endpointDivisors, ← data.prin_script_eq_endpointDivisors]
  exact StrongSeparator.linearEquiv_add_prin D data.script

/-- Winnability is unchanged by adding the signed endpoint divisor of a
compatible window profile. -/
theorem winnable_add_endpointDivisors_iff (data : Data spec)
    (D : CFDiv spec.graph) :
    winnable spec.graph (D + data.endpointDivisors) ↔ winnable spec.graph D := by
  constructor
  · intro hWinnable
    exact winnable_equiv_winnable spec.graph _ _ hWinnable
      (data.linearEquiv_add_endpointDivisors D).symm
  · intro hWinnable
    exact winnable_equiv_winnable spec.graph _ _ hWinnable
      (data.linearEquiv_add_endpointDivisors D)

/-- If removing one chip and adding the signed endpoint divisor gives an
effective divisor, then the original divisor reaches that vertex. -/
theorem reaches_of_effective_endpointDivisors
    (data : Data spec) {D : CFDiv spec.graph} {v : spec.Vertex}
    (hEffective : effective (D - one_chip v + data.endpointDivisors)) :
    StrongSeparator.Reaches spec.graph D v := by
  unfold StrongSeparator.Reaches winnable
  refine ⟨D - one_chip v + data.endpointDivisors, hEffective, ?_⟩
  exact data.linearEquiv_add_endpointDivisors (D - one_chip v)

end Utilities.Certificate.WindowProfile.Data
