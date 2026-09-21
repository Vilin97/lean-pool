/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSlopeScript
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ValidClosed

/-!
# Canonical integer interpolation on the CLOSED length orthant

This is the `DegSpec` counterpart of the interpolated layer of
`Certificate/SubdivisionGraph.lean` (`coreRise`, `pathValue`,
`interpolatedScript`) together with the two exact Laplacian formulas that
`Certificate/ExplicitPotentialRankOne.lean` derives from it
(`prin_interpolatedScript_core_eq_endpointSum`,
`prin_interpolatedScript_interior_eq_stepDifference`).

Nothing in `SubdivisionGraph.Spec` is touched; these are separate statements
about `DegSpec.graph`.

## The one genuinely new hypothesis: `RepInvariant`

`DegSpec.interpolatedScript` has to be a function on the **contracted** vertex
set, whose core summand is `DegSpec.Class`, not `Fin n`.  Its value at the
class of `v` can only be `potential v` if `potential` is constant on classes.
That is `RepInvariant`, and it is genuinely an extra input:

* on the interior it is free (`repInvariant_of_pos`, since `rep = id` there);
* along a *single* collapsed slot it is free for a certificate potential, by
  `ValidClosed`'s shared `lowerForm`/`upperForm` rows
  (`ExplicitPotential.Certificate.potential_eq_of_segment_eval_zero`);
* on a whole class it is exactly the statement that `rep` merges only vertices
  joined by chains of collapsed slots.  The `forest` field does not imply this
  (see the caveat in the design note), so it is supplied, and
  `repInvariant_evaluatedPotential_of_zeroReach` in
  `Certificate/DegenerateRankOne.lean` discharges it from such a chain.

Note that `coreRise` below is defined **without** `rep`, exactly as on a
`Spec`.  That is deliberate: it keeps `coreRise (evaluatedPotential …) = riseValue`
definitionally, so the certificate's endpoint bounds apply verbatim.  Under
`RepInvariant` the two readings agree anyway
(`coreRise_eq_zero_of_length_zero`).
-/

namespace Utilities.Certificate.DegenerateSpec
open Utilities.Certificate

open Utilities

open Finset ExplicitPotential

namespace DegSpec

variable {n p : ℕ} (d : DegSpec n p)

/-! ## Potentials constant on the contracted classes -/

/-- A core potential that is constant on every contracted class. -/
def RepInvariant (potential : Fin n → ℤ) : Prop :=
  ∀ v : Fin n, potential (d.rep v) = potential v

/-- On the interior of the orthant `rep` is the identity, so every potential is
rep-invariant: the hypothesis costs nothing where the strictly positive layer
already applies. -/
theorem repInvariant_of_pos (hpos : ∀ e : Fin p, 0 < d.length e)
    (potential : Fin n → ℤ) : d.RepInvariant potential := by
  intro v
  rw [d.rep_eq_self_of_pos hpos v]

/-! ## Rise, path value, interpolated script -/

/-- Rise of a core potential along an oriented edge slot.  Verbatim the `Spec`
definition; no `rep` appears. -/
def coreRise (potential : Fin n → ℤ) (e : Fin p) : ℤ :=
  potential (d.core.head e) - potential (d.core.tail e)

/-- A collapsed slot has zero rise, for any rep-invariant potential.  This is
what makes the arithmetic interpolator well behaved at `length = 0`, where
`SubdivisionArithmetic.potential_zero` is unavailable. -/
theorem coreRise_eq_zero_of_length_zero {potential : Fin n → ℤ}
    (hInv : d.RepInvariant potential) {e : Fin p} (hzero : d.length e = 0) :
    d.coreRise potential e = 0 := by
  have hHead : potential (d.core.head e) = potential (d.rep (d.core.head e)) :=
    (hInv _).symm
  have hTail : potential (d.core.tail e) = potential (d.rep (d.core.tail e)) :=
    (hInv _).symm
  unfold coreRise
  rw [hHead, hTail, d.rep_zero e hzero, sub_self]

/-- The interpolator of a zero rise is identically zero up to the slot length.
Needed at `length = 0`, where `potential_zero` and `potential_length` both
require positivity. -/
theorem arith_potential_zero_rise (L i : ℕ) (hi : i ≤ L) :
    SubdivisionArithmetic.potential L 0 i = 0 := by
  have hcast : (i : ℤ) ≤ (L : ℤ) := by exact_mod_cast hi
  simp only [SubdivisionArithmetic.potential, SubdivisionArithmetic.quotient,
    SubdivisionArithmetic.remainder, SubdivisionArithmetic.bend,
    Int.zero_ediv, Int.zero_emod, sub_zero, zero_mul, zero_add]
  exact max_eq_left (by omega)

/-- Normalization at the tail endpoint, valid on the **closed** orthant. -/
theorem arith_potential_first {potential : Fin n → ℤ}
    (hInv : d.RepInvariant potential) (e : Fin p) :
    SubdivisionArithmetic.potential (d.length e) (d.coreRise potential e) 0 = 0 := by
  by_cases hpos : 0 < d.length e
  · exact SubdivisionArithmetic.potential_zero _ hpos
  · have hzero : d.length e = 0 := by omega
    rw [d.coreRise_eq_zero_of_length_zero hInv hzero]
    exact arith_potential_zero_rise _ 0 (Nat.zero_le _)

/-- Realization of the rise at the head endpoint, valid on the **closed**
orthant. -/
theorem arith_potential_last {potential : Fin n → ℤ}
    (hInv : d.RepInvariant potential) (e : Fin p) :
    SubdivisionArithmetic.potential (d.length e) (d.coreRise potential e)
        (d.length e) = d.coreRise potential e := by
  by_cases hpos : 0 < d.length e
  · exact SubdivisionArithmetic.potential_length _ hpos
  · have hzero : d.length e = 0 := by omega
    rw [d.coreRise_eq_zero_of_length_zero hInv hzero, hzero]
    exact arith_potential_zero_rise 0 0 le_rfl

/-- Value at a numerical path offset, normalized by the tail potential. -/
def pathValue (potential : Fin n → ℤ) (e : Fin p) (k : ℕ) : ℤ :=
  potential (d.core.tail e) +
    SubdivisionArithmetic.potential (d.length e) (d.coreRise potential e) k

/-- Extend a rep-invariant core potential over every surviving slot by the
canonical convex interpolation.  Collapsed slots contribute nothing: they carry
no interior vertex and their two endpoints are already one class. -/
def interpolatedScript (potential : Fin n → ℤ) : firing_script d.graph :=
  d.slotValueScript potential (d.pathValue potential)

@[simp] theorem interpolatedScript_coreVertex (potential : Fin n → ℤ)
    (v : Fin n) :
    d.interpolatedScript potential (d.coreVertex v) = potential (d.rep v) := rfl

@[simp] theorem interpolatedScript_interiorVertex (potential : Fin n → ℤ)
    (e : Fin p) (o : Fin (d.length e - 1)) :
    d.interpolatedScript potential (d.interiorVertex e o) =
      d.pathValue potential e (o.val + 1) := rfl

/-- The interpolated path values are compatible with the core potential at both
endpoints of **every** slot, collapsed ones included. -/
theorem slotValueCompatible_pathValue {potential : Fin n → ℤ}
    (hInv : d.RepInvariant potential) :
    d.SlotValueCompatible potential (d.pathValue potential) where
  tail := by
    intro e
    unfold pathValue
    rw [d.arith_potential_first hInv e, add_zero, hInv]
  head := by
    intro e
    unfold pathValue
    rw [d.arith_potential_last hInv e]
    unfold coreRise
    rw [hInv]
    ring

theorem interpolatedScript_stepLeft {potential : Fin n → ℤ}
    (hInv : d.RepInvariant potential) (e : Fin p) (o : Fin (d.length e)) :
    d.interpolatedScript potential (d.stepLeft e o) =
      d.pathValue potential e o.val :=
  d.slotValueScript_stepLeft (d.slotValueCompatible_pathValue hInv) e o

theorem interpolatedScript_stepRight {potential : Fin n → ℤ}
    (hInv : d.RepInvariant potential) (e : Fin p) (o : Fin (d.length e)) :
    d.interpolatedScript potential (d.stepRight e o) =
      d.pathValue potential e (o.val + 1) :=
  d.slotValueScript_stepRight (d.slotValueCompatible_pathValue hInv) e o

/-- The script difference across a unit edge is the arithmetic interpolator's
step slope. -/
theorem isStepSlope_interpolatedScript {potential : Fin n → ℤ}
    (hInv : d.RepInvariant potential) :
    d.IsStepSlope (d.interpolatedScript potential)
      (fun e k => SubdivisionArithmetic.step (d.length e)
        (d.coreRise potential e) k) := by
  intro e o
  rw [d.interpolatedScript_stepRight hInv e o,
    d.interpolatedScript_stepLeft hInv e o]
  simp only [pathValue, SubdivisionArithmetic.step]
  ring

/-! ## The two exact Laplacian formulas -/

/-- **Core-class formula.**  At a contracted class only the first and last unit
steps of the incident slots contribute, and the sum runs over *every* slot of
the uncontracted core — collapsed ones cancel by `zero_slot_cancels`. -/
theorem prin_interpolatedScript_coreVertex_eq_endpointSum
    {potential : Fin n → ℤ} (hInv : d.RepInvariant potential) (r : Fin n) :
    prin d.graph (d.interpolatedScript potential) (d.coreVertex r) =
      ∑ e : Fin p,
        ((if d.rep (d.core.tail e) = d.rep r then
            SubdivisionArithmetic.step (d.length e)
              (d.coreRise potential e) 0 else 0) +
          (if d.rep (d.core.head e) = d.rep r then
            -SubdivisionArithmetic.step (d.length e)
              (d.coreRise potential e) (d.length e - 1) else 0)) :=
  d.prin_coreVertex_eq_endpointSum (d.isStepSlope_interpolatedScript hInv) r

/-- **The reuse mechanism, for the interpolated layer.**  The Laplacian at a
contracted class is the sum, over the members of that class, of the strictly
positive per-core-vertex endpoint formula. -/
theorem prin_interpolatedScript_coreVertex_eq_classSum
    {potential : Fin n → ℤ} (hInv : d.RepInvariant potential) (r : Fin n) :
    prin d.graph (d.interpolatedScript potential) (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
        ∑ e : Fin p,
          ((if d.core.tail e = v then
              SubdivisionArithmetic.step (d.length e)
                (d.coreRise potential e) 0 else 0) +
            (if d.core.head e = v then
              -SubdivisionArithmetic.step (d.length e)
                (d.coreRise potential e) (d.length e - 1) else 0)) :=
  d.prin_coreVertex_eq_classSum (d.isStepSlope_interpolatedScript hInv) r

/-- **Interior formula.**  Unchanged in shape: an interior vertex exists only on
a slot of length at least two. -/
theorem prin_interpolatedScript_interiorVertex_eq_stepDifference
    {potential : Fin n → ℤ} (hInv : d.RepInvariant potential)
    (e : Fin p) (o : Fin (d.length e - 1)) :
    prin d.graph (d.interpolatedScript potential) (d.interiorVertex e o) =
      SubdivisionArithmetic.step (d.length e) (d.coreRise potential e)
          (o.val + 1) -
        SubdivisionArithmetic.step (d.length e) (d.coreRise potential e)
          o.val :=
  d.prin_interiorVertex_eq_slopeDifference
    (d.isStepSlope_interpolatedScript hInv) e o

/-- Convexity of the interpolator: the interior Laplacian coefficient is
non-negative. -/
theorem prin_interpolatedScript_interiorVertex_nonneg
    {potential : Fin n → ℤ} (hInv : d.RepInvariant potential)
    (e : Fin p) (o : Fin (d.length e - 1)) :
    0 ≤ prin d.graph (d.interpolatedScript potential) (d.interiorVertex e o) := by
  rw [d.prin_interpolatedScript_interiorVertex_eq_stepDifference hInv e o,
    sub_nonneg]
  exact SubdivisionArithmetic.step_mono (Nat.le_succ o.val)

/-! ## Path positions from numerical offsets

`SubdivisionGraph.Spec.pathPosition` lives in `Certificate/MovingPosition.lean`;
this is its `DegSpec` counterpart, needed by the affine position decoder.  The
consumer-facing difference is the trichotomy: `pathVertex_zero`,
`pathVertex_length` and `pathVertex_interior` are three separate cases, and at a
collapsed slot the first two coincide. -/

/-- The path position at a numerical offset known not to pass the head. -/
def pathPosition (e : Fin p) (offset : ℕ) (hOffset : offset ≤ d.length e) :
    d.PathPosition e := ⟨offset, by omega⟩

@[simp] theorem pathPosition_val (e : Fin p) (offset : ℕ)
    (hOffset : offset ≤ d.length e) :
    (d.pathPosition e offset hOffset).val = offset := rfl

theorem pathVertex_pathPosition_zero (e : Fin p)
    (hOffset : (0 : ℕ) ≤ d.length e) :
    d.pathVertex e (d.pathPosition e 0 hOffset) =
      d.coreVertex (d.core.tail e) := d.pathVertex_zero e

theorem pathVertex_pathPosition_length (e : Fin p)
    (hOffset : d.length e ≤ d.length e) :
    d.pathVertex e (d.pathPosition e (d.length e) hOffset) =
      d.coreVertex (d.core.head e) := d.pathVertex_length e

theorem pathVertex_pathPosition_interior (e : Fin p) (offset : ℕ)
    (hOffset : offset ≤ d.length e) (hZero : offset ≠ 0)
    (hLast : offset ≠ d.length e) :
    d.pathVertex e (d.pathPosition e offset hOffset) =
      d.interiorVertex e ⟨offset - 1, by omega⟩ := by
  rw [d.pathVertex_interior e (d.pathPosition e offset hOffset) hZero hLast]
  rfl

/-- **The trichotomy, in one statement.**  On the closed orthant a numerical
path offset lands on the tail class, the head class, or an interior vertex —
the positive-world two-case split (`offset = 0` versus `offset > 0 ⟹ interior`)
has no case for `offset = length`. -/
theorem pathVertex_pathPosition_trichotomy (e : Fin p) (offset : ℕ)
    (hOffset : offset ≤ d.length e) :
    d.pathVertex e (d.pathPosition e offset hOffset) =
        d.coreVertex (d.core.tail e) ∨
      d.pathVertex e (d.pathPosition e offset hOffset) =
        d.coreVertex (d.core.head e) ∨
      ∃ o : Fin (d.length e - 1),
        d.pathVertex e (d.pathPosition e offset hOffset) =
          d.interiorVertex e o := by
  by_cases hZero : offset = 0
  · subst hZero
    exact Or.inl (d.pathVertex_zero e)
  · by_cases hLast : offset = d.length e
    · subst hLast
      exact Or.inr (Or.inl (d.pathVertex_length e))
    · exact Or.inr (Or.inr ⟨⟨offset - 1, by omega⟩,
        d.pathVertex_pathPosition_interior e offset hOffset hZero hLast⟩)

end DegSpec

end Utilities.Certificate.DegenerateSpec
