/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.SphereTopology.SimplyConnectedP1
import LeanPool.JacobianDiffgeo.SphereTopology.GlobalPrimitive

/-!
# The backward headline: `X ≃ₜ S² ⇒ genus X = 0` (CC-sphere-topology, design §4)

Unit: sphere-topology (`docs/design/sphere-topology.md` §4). Assembles the topological fact
(`SimplyConnectedP1.lean`: any space homeomorphic to `OnePoint ℂ`, in particular to the challenge
sphere, is simply connected) with the analytic fact (`GlobalPrimitive.lean`: a simply connected
compact Riemann surface has genus `0`) into the exact backward-headline signature consumed by
`genus-zero-headline`.

Main declaration: `RS.SphereTopology.genus_eq_zero_of_homeo_sphere`.
-/

open scoped ContDiff Manifold

namespace RS.SphereTopology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The backward headline half (consumed by `genus-zero-headline` alongside Riemann–Roch's
forward half). Only `X`'s TOPOLOGY is used to get `SimplyConnectedSpace X`; `genus X = 0` then
uses `X`'s OWN complex structure via `GlobalPrimitive.lean` — consistent, since `Form1 X`/
`genus X` are defined from `X`'s own atlas, not from the sphere's. -/
theorem genus_eq_zero_of_homeo_sphere
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) : genus X = 0 := by
  obtain ⟨e⟩ := h
  have : SimplyConnectedSpace X :=
    simplyConnectedSpace_of_homeoOnePoint (e.trans RS.P1.homeoSphere.symm)
  exact genus_eq_zero_of_simplyConnectedSpace

end RS.SphereTopology
