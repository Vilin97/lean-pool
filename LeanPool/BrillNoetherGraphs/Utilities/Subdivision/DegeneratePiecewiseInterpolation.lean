/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateInterpolation

/-!
# Canonical piecewise interpolation on closed subdivision faces

A `PiecewiseData` describes a path potential by its successive block ends and
the total rise of each block.  The slope *inside* a block is not supplied by a
certificate: it is the canonical integer interpolation slope for that block's
length and rise.  Thus the only interior coefficients which a leaf needs to
check separately are the block boundaries.

The data deliberately uses a selector rather than a list traversal.  A lowerer
can decode its finite block list into `blockAt`; `covers` is the small,
arithmetic statement that the selected block contains every surviving unit
step.  This formulation is also meaningful on a closed face: a zero-length
slot has no selected step, and `balance` then forces its two endpoint values to
coincide.
-/

namespace Utilities.Certificate.DegenerateSpec
open Utilities.Certificate

open Utilities

open Finset ExplicitPotential

namespace DegSpec

variable {n p : ℕ} (d : DegSpec n p)

/-- The left endpoint of a block.  Block zero starts at the tail; every later
block starts where its predecessor ended. -/
def blockStart (blockEnd : Fin p → ℕ → ℕ) (e : Fin p) (block : ℕ) : ℕ :=
  if block = 0 then 0 else blockEnd e (block - 1)

/-- The canonical slope at a unit step, selected from its containing block. -/
def blockSlope (blockAt blockEnd : Fin p → ℕ → ℕ) (blockRise : Fin p → ℕ → ℤ)
    (e : Fin p) (k : ℕ) : ℤ :=
  let block := blockAt e k
  SubdivisionArithmetic.step
    (blockEnd e block - blockStart blockEnd e block)
    (blockRise e block)
    (k - blockStart blockEnd e block)

/-- Block-end/rise data for a canonically interpolated piecewise script.

`blockEnd e j` is the right endpoint of block `j`; the preceding endpoint is
`blockStart e j`.  `blockAt` selects the block containing a surviving step.
The latter is intentionally a semantic finite-data interface: list indexing,
ordering, and affine endpoint decoding belong in the lowering layer, while the
proof below only needs the displayed containment inequalities. -/
structure PiecewiseData (potential : Fin n → ℤ) where
  blockAt : Fin p → ℕ → ℕ
  blockEnd : Fin p → ℕ → ℕ
  blockRise : Fin p → ℕ → ℤ
  covers : ∀ e k, k < d.length e →
    blockStart blockEnd e (blockAt e k) ≤ k ∧
      k < blockEnd e (blockAt e k)
  ownsInterval : ∀ e block k,
    blockStart blockEnd e block ≤ k → k < blockEnd e block →
      blockAt e k = block
  balance : ∀ e : Fin p,
    potential (d.core.head e) = potential (d.core.tail e) +
      ∑ k ∈ Finset.range (d.length e),
        blockSlope blockAt blockEnd blockRise e k

variable {d}
variable {potential : Fin n → ℤ} {data : d.PiecewiseData potential}

/-- Inside a declared block, the selected slope is exactly that block's
canonical interpolation slope.  This is the direct W2-facing reading of a
block endpoint/rise pair. -/
theorem blockSlope_eq_of_mem (edge : Fin p) (block k : ℕ)
    (hStart : blockStart data.blockEnd edge block ≤ k)
    (hEnd : k < data.blockEnd edge block) :
    blockSlope data.blockAt data.blockEnd data.blockRise edge k =
      SubdivisionArithmetic.step
        (data.blockEnd edge block - blockStart data.blockEnd edge block)
        (data.blockRise edge block) (k - blockStart data.blockEnd edge block) := by
  unfold blockSlope
  rw [data.ownsInterval edge block k hStart hEnd]

/-- W2 bounds on the total rise of the selected nonempty block bound every
canonical unit slope of its integer interpolation.  This is the precise
bridge used by a rich leaf's W4 boundary residual: it does not assume that
the endpoint list has no repeated entries. -/
theorem lower_le_blockSlope_of_mul_le (edge : Fin p) (k : ℕ) (lo : ℤ)
    (hk : k < d.length edge)
    (hLower : lo *
      ↑(data.blockEnd edge (data.blockAt edge k) -
        blockStart data.blockEnd edge (data.blockAt edge k)) ≤
      data.blockRise edge (data.blockAt edge k)) :
    lo ≤ blockSlope data.blockAt data.blockEnd data.blockRise edge k := by
  have hCover := data.covers edge k hk
  rw [blockSlope_eq_of_mem edge (data.blockAt edge k) k hCover.1 hCover.2]
  apply SubdivisionArithmetic.lower_le_step_of_mul_le
  · omega
  · exact hLower

/-- The upper-half of the selected canonical slope bound. -/
theorem blockSlope_le_upper_of_le_mul (edge : Fin p) (k : ℕ) (hi : ℤ)
    (hk : k < d.length edge)
    (hUpper : data.blockRise edge (data.blockAt edge k) ≤ hi *
      ↑(data.blockEnd edge (data.blockAt edge k) -
        blockStart data.blockEnd edge (data.blockAt edge k))) :
    blockSlope data.blockAt data.blockEnd data.blockRise edge k ≤ hi := by
  have hCover := data.covers edge k hk
  rw [blockSlope_eq_of_mem edge (data.blockAt edge k) k hCover.1 hCover.2]
  apply SubdivisionArithmetic.step_le_upper_of_le_mul
  · omega
  · omega
  · exact hUpper

/-- The path values obtained by accumulating the canonical selected slopes. -/
def piecewiseValue (data : d.PiecewiseData potential) : Fin p → ℕ → ℤ :=
  fun e k => potential (d.core.tail e) +
    ∑ j ∈ Finset.range k, blockSlope data.blockAt data.blockEnd data.blockRise e j

/-- The resulting firing script on the contracted subdivision. -/
def piecewiseScript (data : d.PiecewiseData potential) : firingScript d.graph :=
  d.slotValueScript potential (d.piecewiseValue data)

@[simp] theorem piecewiseValue_zero (e : Fin p) :
    d.piecewiseValue data e 0 = potential (d.core.tail e) := by
  simp [piecewiseValue]

theorem slotValueCompatible_piecewiseValue (hInv : d.RepInvariant potential) :
    d.SlotValueCompatible potential (d.piecewiseValue data) where
  tail := fun e => by rw [piecewiseValue_zero]; exact (hInv _).symm
  head := fun e => by
    simp only [piecewiseValue]
    rw [← data.balance e]
    exact (hInv _).symm

theorem isStepSlope_piecewiseScript (hInv : d.RepInvariant potential) :
    d.IsStepSlope (d.piecewiseScript data)
      (fun e k => blockSlope data.blockAt data.blockEnd data.blockRise e k) := by
  intro e offset
  have hStep := d.isStepSlope_slotValueScript
    (d.slotValueCompatible_piecewiseValue (data := data) hInv) e offset
  have hValue :
      d.piecewiseValue data e (offset.val + 1) - d.piecewiseValue data e offset.val =
        blockSlope data.blockAt data.blockEnd data.blockRise e offset.val := by
    simp [piecewiseValue, Finset.sum_range_succ]
  exact hStep.trans hValue

/-- Exact endpoint formula at a contracted core class.  In particular this
retains all collapsed slots; their two displayed endpoint terms cancel. -/
theorem prin_piecewiseScript_coreVertex (hInv : d.RepInvariant potential)
    (vertex : Fin n) :
    prin d.graph (d.piecewiseScript data) (d.coreVertex vertex) =
      ∑ edge : Fin p,
        ((if d.rep (d.core.tail edge) = d.rep vertex then
            blockSlope data.blockAt data.blockEnd data.blockRise edge 0 else 0) +
          (if d.rep (d.core.head edge) = d.rep vertex then
            -blockSlope data.blockAt data.blockEnd data.blockRise edge
              (d.length edge - 1) else 0)) :=
  d.prin_coreVertex_eq_endpointSum (d.isStepSlope_piecewiseScript hInv) vertex

/-- The quotient-core version of the endpoint formula.  It expands a
contracted class into its original core vertices, which is the form needed to
combine W5's per-anchor residuals with chips that have slid onto a face. -/
theorem prin_piecewiseScript_coreVertex_eq_classSum (hInv : d.RepInvariant potential)
    (vertex : Fin n) :
    prin d.graph (d.piecewiseScript data) (d.coreVertex vertex) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep vertex),
        ∑ edge : Fin p,
          ((if d.core.tail edge = v then
              blockSlope data.blockAt data.blockEnd data.blockRise edge 0 else 0) +
            (if d.core.head edge = v then
              -blockSlope data.blockAt data.blockEnd data.blockRise edge
                (d.length edge - 1) else 0)) :=
  d.prin_coreVertex_eq_classSum (d.isStepSlope_piecewiseScript hInv) vertex

/-- Exact interior formula: the coefficient is the jump of the two selected
canonical block slopes. -/
theorem prin_piecewiseScript_interiorVertex (hInv : d.RepInvariant potential)
    (edge : Fin p) (offset : Fin (d.length edge - 1)) :
    prin d.graph (d.piecewiseScript data) (d.interiorVertex edge offset) =
      blockSlope data.blockAt data.blockEnd data.blockRise edge (offset.val + 1) -
        blockSlope data.blockAt data.blockEnd data.blockRise edge offset.val :=
  d.prin_interiorVertex_eq_slopeDifference
    (d.isStepSlope_piecewiseScript hInv) edge offset

/-- Away from a block boundary the two adjacent unit steps are selected from
the same canonical interpolator, hence the interior coefficient is
non-negative.  W4 need only check the omitted boundary case. -/
theorem prin_piecewiseScript_interiorVertex_nonneg_of_sameBlock
    (hInv : d.RepInvariant potential) (edge : Fin p)
    (offset : Fin (d.length edge - 1))
    (hSame : data.blockAt edge (offset.val + 1) = data.blockAt edge offset.val) :
    0 ≤ prin d.graph (d.piecewiseScript data) (d.interiorVertex edge offset) := by
  rw [d.prin_piecewiseScript_interiorVertex hInv edge offset]
  rw [sub_nonneg]
  unfold blockSlope
  rw [hSame]
  let block := data.blockAt edge offset.val
  have hCover := data.covers edge offset.val (by omega)
  have hStart : blockStart data.blockEnd edge block ≤ offset.val := by
    simpa [block] using hCover.1
  change SubdivisionArithmetic.step _ _
      (offset.val - blockStart data.blockEnd edge block) ≤
    SubdivisionArithmetic.step _ _
      (offset.val + 1 - blockStart data.blockEnd edge block)
  apply SubdivisionArithmetic.step_mono
  omega

end DegSpec

end Utilities.Certificate.DegenerateSpec
