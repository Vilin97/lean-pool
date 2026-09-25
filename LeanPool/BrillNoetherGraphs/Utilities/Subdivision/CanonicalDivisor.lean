/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.CycleRigidity
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CubicCore
import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch

/-!
# Canonical divisors on positive subdivisions

The canonical coefficient at a core vertex is its incidence degree minus
two; every subdivision-interior coefficient is zero. Thus leaflessness can
be checked on the finite core. Degree and rank depend only on the numbers
of core vertices and slots. In particular a connected specification with
one more slot than core vertices has a canonical divisor of degree two and
rank one.

The valence calculations are reused from `Utilities.Gluing.CycleRigidity`.
All statements here concern positive `SubdivisionGraph.Spec` objects, not
contracted zero-length faces.
-/

namespace Utilities

/-- Riemann--Roch gives the canonical divisor rank on every connected graph. -/
theorem rank_canonical_divisor_eq_genus_sub_one {G : CFGraph}
    (hConnected : graphConnected G) :
    rank G (canonicalDivisor G) = genus G - 1 := by
  have hRR := riemann_roch_for_graphs hConnected (canonicalDivisor G)
  rw [sub_self, zero_divisor_rank, sub_zero, degree_of_canonical_divisor] at hRR
  linarith

namespace Certificate.SubdivisionGraph.Spec

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- The graph valence of a core vertex is its occurrence-sensitive incidence
degree. Parallel slots are counted separately. -/
theorem vertex_degree_coreVertex_eq_incidenceDegree (v : Fin n) :
    vertexDegree spec.graph (spec.coreVertex v) =
      (spec.core.incidenceDegree v : ℤ) := by
  rw [spec.vertex_degree_coreVertex_eq_incidentSlots]
  simp [ExplicitPotential.Core.incidenceDegree]

@[simp] theorem canonical_divisor_coreVertex (v : Fin n) :
    canonicalDivisor spec.graph (spec.coreVertex v) =
      (spec.core.incidenceDegree v : ℤ) - 2 := by
  change vertexDegree spec.graph (spec.coreVertex v) - 2 = _
  rw [spec.vertex_degree_coreVertex_eq_incidenceDegree]

@[simp] theorem canonical_divisor_interiorVertex (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    canonicalDivisor spec.graph (spec.interiorVertex edge offset) = 0 := by
  change vertexDegree spec.graph (spec.interiorVertex edge offset) - 2 = 0
  rw [spec.vertex_degree_interiorVertex_eq_two]
  norm_num

/-- An effective canonical divisor on a positive subdivision is exactly the
condition that every core incidence degree is at least two. -/
theorem canonical_divisor_effective_iff :
    effective (canonicalDivisor spec.graph) ↔
      ∀ v : Fin n, 2 ≤ spec.core.incidenceDegree v := by
  constructor
  · intro h v
    have hv := h (spec.coreVertex v)
    rw [spec.canonical_divisor_coreVertex] at hv
    omega
  · intro h vertex
    rcases vertex with v | ⟨edge, offset⟩
    · change 0 ≤ canonicalDivisor spec.graph (spec.coreVertex v)
      rw [spec.canonical_divisor_coreVertex]
      have hv := h v
      omega
    · change 0 ≤ canonicalDivisor spec.graph (spec.interiorVertex edge offset)
      rw [spec.canonical_divisor_interiorVertex]

/-- Core leaflessness makes the canonical divisor effective, uniformly in
all positive edge lengths. -/
theorem canonical_divisor_effective
    (hLeafless : ∀ v : Fin n, 2 ≤ spec.core.incidenceDegree v) :
    effective (canonicalDivisor spec.graph) :=
  spec.canonical_divisor_effective_iff.mpr hLeafless

/-- The canonical degree is determined by the finite core counts. -/
@[simp] theorem deg_canonical_divisor :
    deg (canonicalDivisor spec.graph) = 2 * ((p : ℤ) - (n : ℤ)) := by
  rw [degree_of_canonical_divisor, spec.genus_graph]
  ring

/-- On a connected positive subdivision, the canonical rank is determined
by the finite core counts. -/
theorem rank_canonical_divisor (hConnected : graphConnected spec.graph) :
    rank spec.graph (canonicalDivisor spec.graph) = (p : ℤ) - (n : ℤ) := by
  rw [rank_canonical_divisor_eq_genus_sub_one hConnected, spec.genus_graph]
  omega

/-- One more slot than core vertices gives canonical degree two. -/
theorem deg_canonical_divisor_eq_two (hGenusTwo : p = n + 1) :
    deg (canonicalDivisor spec.graph) = 2 := by
  rw [spec.deg_canonical_divisor]
  omega

/-- The canonical divisor of a connected genus-two subdivision has rank
one, including every connected `Spec 4 5`. -/
theorem rank_canonical_divisor_eq_one
    (hConnected : graphConnected spec.graph) (hGenusTwo : p = n + 1) :
    rank spec.graph (canonicalDivisor spec.graph) = 1 := by
  rw [spec.rank_canonical_divisor hConnected]
  omega

/-- Package the effective canonical pencil needed for a leafless genus-two
factor in a gluing construction. -/
theorem effective_canonical_pencil
    (hConnected : graphConnected spec.graph) (hGenusTwo : p = n + 1)
    (hLeafless : ∀ v : Fin n, 2 ≤ spec.core.incidenceDegree v) :
    effective (canonicalDivisor spec.graph) ∧
      deg (canonicalDivisor spec.graph) = 2 ∧
      rank spec.graph (canonicalDivisor spec.graph) ≥ 1 := by
  refine ⟨spec.canonical_divisor_effective hLeafless,
    spec.deg_canonical_divisor_eq_two hGenusTwo, ?_⟩
  exact le_of_eq (spec.rank_canonical_divisor_eq_one hConnected hGenusTwo).symm

end Certificate.SubdivisionGraph.Spec

end Utilities
