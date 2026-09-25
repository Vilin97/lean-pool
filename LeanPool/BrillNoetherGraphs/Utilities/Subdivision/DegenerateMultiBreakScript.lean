/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateInterpolation
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.MultiBreakScript
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.StrongSeparator

/-!
# Multi-break firing scripts on the closed length orthant

This is the closed-face counterpart of the concrete part of
`MultiBreakScript.lean`. A row leaf first evaluates its named break positions,
then supplies the resulting concrete lists here. A zero-length slot has no
steps; `BreakData.balance` consequently forces its endpoint potential to agree.
-/

namespace Utilities.Certificate.DegenerateSpec
open Utilities.Certificate

open Utilities

open Finset
open ExplicitPotential

namespace DegSpec

variable {n p : ℕ} (d : DegSpec n p)

/-- Effectivity on a contracted subdivision reduces to its quotient-core and
interior summands.  This is the closed-face counterpart of the positive
multi-break helper, and is the assembly point a row leaf uses after W4/W5. -/
theorem effective_of_cases {D : CFDiv d.graph}
    (hcore : ∀ c : d.Class, 0 ≤ D (Sum.inl c))
    (hint : ∀ (edge : Fin p) (offset : Fin (d.length edge - 1)),
      0 ≤ D (d.interiorVertex edge offset)) : effective D := by
  intro vertex
  rcases vertex with core | interior
  · exact hcore core
  · exact hint interior.1 interior.2

/-- An effective representative carrying a chip at a target vertex witnesses
reachability there.  It works verbatim on closed faces, including when core
vertices have merged. -/
theorem reaches_of_script (D : CFDiv d.graph) (script : firingScript d.graph)
    (q : d.graph.V) (hEffective : effective (D + prin d.graph script))
    (hChip : 1 ≤ (D + prin d.graph script) q) :
    StrongSeparator.Reaches d.graph D q := by
  refine StrongSeparator.reaches_of_effective_representative ?_ hEffective hChip
  unfold linearEquiv
  rw [principal_iff_eq_prin]
  exact ⟨script, by abel⟩

/-- Path values of a closed-face multi-break script. -/
def breakValue (potential : Fin n → ℤ) (breaks : Fin p → List (ℕ × ℤ)) :
    Fin p → ℕ → ℤ :=
  fun edge k =>
    potential (d.core.tail edge) +
      ∑ j ∈ Finset.range k, SubdivisionGraph.Spec.breakSlope (breaks edge) j

/-- The concrete multi-break firing script on a contracted subdivision. -/
def breakScript (potential : Fin n → ℤ) (breaks : Fin p → List (ℕ × ℤ)) :
    firingScript d.graph :=
  d.slotValueScript potential (d.breakValue potential breaks)

/-- Closing condition for a multi-break script, including zero slots. -/
structure BreakData (potential : Fin n → ℤ) (breaks : Fin p → List (ℕ × ℤ)) :
    Prop where
  balance : ∀ edge : Fin p,
    potential (d.core.head edge) = potential (d.core.tail edge) +
      ∑ j ∈ Finset.range (d.length edge),
        SubdivisionGraph.Spec.breakSlope (breaks edge) j

variable {d}
variable {potential : Fin n → ℤ} {breaks : Fin p → List (ℕ × ℤ)}

@[simp] theorem breakValue_zero (edge : Fin p) :
    d.breakValue potential breaks edge 0 = potential (d.core.tail edge) := by
  simp [breakValue]

theorem slotValueCompatible_breakValue (hInv : d.RepInvariant potential)
    (hData : d.BreakData potential breaks) :
    d.SlotValueCompatible potential (d.breakValue potential breaks) where
  tail := fun edge => by
    rw [breakValue_zero]
    exact (hInv _).symm
  head := fun edge => by
    simp only [breakValue]
    rw [← hData.balance edge]
    exact (hInv _).symm

/-- The unit-step slopes are the decoded break slopes. Vanishing slots impose
no condition because their step type is empty. -/
theorem isStepSlope_breakScript (hInv : d.RepInvariant potential)
    (hData : d.BreakData potential breaks) :
    d.IsStepSlope (d.breakScript potential breaks)
      fun edge k => SubdivisionGraph.Spec.breakSlope (breaks edge) k := by
  intro edge offset
  have hStep := d.isStepSlope_slotValueScript
    (slotValueCompatible_breakValue hInv hData) edge offset
  have hValue :
      d.breakValue potential breaks edge (offset.val + 1) -
          d.breakValue potential breaks edge offset.val =
        SubdivisionGraph.Spec.breakSlope (breaks edge) offset.val := by
    simp [breakValue, Finset.sum_range_succ]
  exact hStep.trans hValue

/-- At a contracted core class, the Laplacian is the endpoint sum over every
original slot, including vanishing slots (which cancel in the generic formula). -/
theorem prin_breakScript_coreVertex (hInv : d.RepInvariant potential)
    (hData : d.BreakData potential breaks)
    (vertex : Fin n) :
    prin d.graph (d.breakScript potential breaks) (d.coreVertex vertex) =
      ∑ edge : Fin p,
        ((if d.rep (d.core.tail edge) = d.rep vertex then
            SubdivisionGraph.Spec.breakSlope (breaks edge) 0 else 0) +
          (if d.rep (d.core.head edge) = d.rep vertex then
            -SubdivisionGraph.Spec.breakSlope (breaks edge) (d.length edge - 1)
          else 0)) :=
  d.prin_coreVertex_eq_endpointSum (isStepSlope_breakScript hInv hData) vertex

/-- At a surviving interior vertex, the Laplacian is the jump of the break slope. -/
theorem prin_breakScript_interiorVertex (hInv : d.RepInvariant potential)
    (hData : d.BreakData potential breaks)
    (edge : Fin p) (offset : Fin (d.length edge - 1)) :
    prin d.graph (d.breakScript potential breaks) (d.interiorVertex edge offset) =
      SubdivisionGraph.Spec.breakSlope (breaks edge) (offset.val + 1) -
        SubdivisionGraph.Spec.breakSlope (breaks edge) offset.val :=
  d.prin_interiorVertex_eq_slopeDifference (isStepSlope_breakScript hInv hData) edge offset

/-- The principal divisor vanishes away from named break positions. -/
theorem prin_breakScript_interiorVertex_eq_zero
    (hInv : d.RepInvariant potential) (hData : d.BreakData potential breaks) (edge : Fin p)
    (offset : Fin (d.length edge - 1))
    (hNoBreak : ∀ entry ∈ breaks edge, entry.1 ≠ offset.val + 1) :
    prin d.graph (d.breakScript potential breaks) (d.interiorVertex edge offset) = 0 := by
  rw [prin_breakScript_interiorVertex hInv hData edge offset,
    SubdivisionGraph.Spec.breakSlope_succ_of_notMem (breaks edge) offset.val hNoBreak]
  ring

end DegSpec

end Utilities.Certificate.DegenerateSpec
