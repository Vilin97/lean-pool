/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegeneratePiecewiseInterpolation

/-!
# Finite block-end decoding

The rich RPF leaf records a finite (weakly ordered) list of block endpoints.
This file supplies the one semantic operation the interpolation layer needs:
for every surviving unit step, choose the first endpoint strictly to its
right.  Repeated endpoints are intentional -- they represent zero-length
blocks -- and are skipped by the selector.

The small `FiniteBlockEnds` interface keeps list bookkeeping out of the
closed-face soundness proof.  The lowerer/checker bridge proves its three
displayed facts from a concrete RPF block list.
-/

@[expose] public section

namespace MarkedGraphs.Certificate
open Utilities.Certificate

open Utilities

open Utilities.Certificate.DegenerateSpec

/-- A finite, weakly ordered endpoint list ending at `L`.

`cover` is deliberately bounded by `ends.length`: although `endAt` has the
convenient default `L` out of bounds, no phantom block may be selected. -/
structure FiniteBlockEnds (L : ℕ) where
  /-- The nonempty, weakly ordered list of block endpoints ending at `L`, covering every unit
  step below `L`. -/
  ends : List ℕ
  nonempty : 0 < ends.length
  last : ends.getD (ends.length - 1) L = L
  ordered : ∀ i : ℕ, ends.getD i L ≤ ends.getD (i + 1) L
  cover : ∀ k : ℕ, k < L → ∃ i < ends.length, k < ends.getD i L

namespace FiniteBlockEnds

variable {L : ℕ} (b : FiniteBlockEnds L)

/-- A nonempty weakly ordered list whose final endpoint is `L` automatically
covers every unit step below `L`: the final block is always a possible owner.
This is the form produced directly by the W1 checks of a rich row leaf. -/
def ofOrderedLast (ends : List ℕ) (hNonempty : 0 < ends.length)
    (hLast : ends.getD (ends.length - 1) L = L)
    (hOrdered : ∀ i : ℕ, ends.getD i L ≤ ends.getD (i + 1) L) :
    FiniteBlockEnds L where
  ends := ends
  nonempty := hNonempty
  last := hLast
  ordered := hOrdered
  cover := by
    intro k hk
    refine ⟨ends.length - 1, by omega, ?_⟩
    rw [hLast]
    exact hk

/-- The endpoint at a block index, defaulting to the total length. -/
def endAt (i : ℕ) : ℕ := b.ends.getD i L

/-- The left endpoint of a block. -/
def startAt (i : ℕ) : ℕ := if i = 0 then 0 else b.endAt (i - 1)

/-- The first (finite) block ending strictly after `k`; its arbitrary value
outside `[0,L)` is never used by the interpolation interface. -/
def blockAt (k : ℕ) : ℕ :=
  if hk : k < L then Nat.find (b.cover k hk) else 0

@[simp] theorem endAt_def (i : ℕ) : b.endAt i = b.ends.getD i L := rfl

theorem endAt_mono {i j : ℕ} (hij : i ≤ j) : b.endAt i ≤ b.endAt j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact ih.trans (b.ordered j)

/-- Every actual listed endpoint lies at or before the total path length. -/
theorem endAt_le_length (i : ℕ) (hi : i < b.ends.length) : b.endAt i ≤ L := by
  have hLastIndex : i ≤ b.ends.length - 1 := by omega
  have hMono := b.endAt_mono hLastIndex
  change b.endAt i ≤ b.ends.getD (b.ends.length - 1) L at hMono
  rw [b.last] at hMono
  exact hMono

/-- If the endpoint of block `s` is strictly beyond the tail, every endpoint
at the tail occurs strictly before `s`.  This remains valid when earlier
blocks have length zero and hence have repeated endpoints. -/
theorem lt_of_endAt_eq_zero_of_endAt_pos {i s : ℕ}
    (hZero : b.endAt i = 0) (hPos : 0 < b.endAt s) : i < s := by
  by_contra hNot
  have hSI : s ≤ i := Nat.le_of_not_gt hNot
  have hMono := b.endAt_mono hSI
  rw [hZero] at hMono
  omega

/-- Dually, if the endpoint of block `s` is strictly before the head, every
endpoint at the total length occurs strictly after `s`.  Repeated endpoints
at the head are therefore an allowed suffix, never an interior run. -/
theorem lt_of_endAt_lt_length_of_endAt_eq_length {i s : ℕ}
    (hLength : b.endAt i = L) (hLt : b.endAt s < L) : s < i := by
  by_contra hNot
  have hIS : i ≤ s := Nat.le_of_not_gt hNot
  have hMono := b.endAt_mono hIS
  rw [hLength] at hMono
  omega

theorem blockAt_spec (k : ℕ) (hk : k < L) : k < b.endAt (b.blockAt k) := by
  rw [blockAt, dite_eq_left hk]
  exact (Nat.find_spec (b.cover k hk)).2

theorem blockAt_lt_length (k : ℕ) (hk : k < L) : b.blockAt k < b.ends.length := by
  rw [blockAt, dite_eq_left hk]
  rcases b.cover k hk with ⟨i, hi, hEnd⟩
  exact lt_of_le_of_lt (Nat.find_min' (b.cover k hk) ⟨hi, hEnd⟩) hi

/-- Once the endpoint of a block lies at or before a surviving step, the
first-endpoint selector must have moved strictly past that block.  This is the
basic boundary fact used to turn a selector change into a run of coincident
finite endpoints. -/
theorem lt_blockAt_of_endAt_le (k i : ℕ) (hk : k < L)
    (hEnd : b.endAt i ≤ k) : i < b.blockAt k := by
  by_contra hNot
  have hLE : b.blockAt k ≤ i := Nat.le_of_not_gt hNot
  have hMono : b.endAt (b.blockAt k) ≤ b.endAt i := b.endAt_mono hLE
  have hContr : b.endAt (b.blockAt k) ≤ k := hMono.trans hEnd
  exact (not_le_of_gt (b.blockAt_spec k hk)) hContr

/-- Conversely, every block strictly before the selected one has already
ended.  Together with `lt_blockAt_of_endAt_le`, this characterizes the
selector by the endpoint inequalities, including repeated (zero-length)
endpoints. -/
theorem endAt_le_of_lt_blockAt (k i : ℕ) (hk : k < L)
    (hIndex : i < b.blockAt k) : b.endAt i ≤ k := by
  by_contra hNot
  have hEnd : k < b.endAt i := by omega
  have hFinite : i < b.ends.length :=
    lt_trans hIndex (b.blockAt_lt_length k hk)
  have hMin : b.blockAt k ≤ i := by
    rw [blockAt, dite_eq_left hk]
    exact Nat.find_min' (b.cover k hk) ⟨hFinite, hEnd⟩
  omega

/-- When the selector changes between adjacent surviving steps, every listed
endpoint from the old selected block through the block immediately before the
new selection is exactly their common boundary.  This is the finite
``collapsed run'' decoded by W4. -/
theorem endAt_eq_succ_of_selector_lt (k i j t : ℕ) (hk : k + 1 < L)
    (hi : i = b.blockAt k) (hj : j = b.blockAt (k + 1))
    (hChange : i < j) (hRun : i ≤ t) (ht : t < j) : b.endAt t = k + 1 := by
  have hk0 : k < L := by omega
  have hOld : k < b.endAt i := by simpa [hi] using b.blockAt_spec k hk0
  have hNew : b.endAt i ≤ k + 1 := by
    apply b.endAt_le_of_lt_blockAt (k + 1) i hk
    simpa [hi, hj] using hChange
  have hI : b.endAt i = k + 1 := by omega
  have hLower : b.endAt i ≤ b.endAt t := b.endAt_mono hRun
  have hUpper : b.endAt t ≤ k + 1 :=
    b.endAt_le_of_lt_blockAt (k + 1) t hk (by simpa [hj] using ht)
  omega

/-- The first-endpoint selector is monotone along a slot.  Thus two adjacent
surviving steps either belong to the same canonical interpolator or form the
forward collapsed-boundary situation handled by W4. -/
theorem blockAt_mono {k l : ℕ} (hk : k < L) (hl : l < L) (hkl : k ≤ l) :
    b.blockAt k ≤ b.blockAt l := by
  by_contra hNot
  have hLK : b.blockAt l < b.blockAt k := Nat.lt_of_not_ge hNot
  have hEnded : b.endAt (b.blockAt l) ≤ k :=
    b.endAt_le_of_lt_blockAt k (b.blockAt l) hk hLK
  have hLive : l < b.endAt (b.blockAt l) := b.blockAt_spec l hl
  omega

private theorem endAt_pred_le (i k : ℕ) (hi : 0 < i) (hFinite : i < b.ends.length)
    (hMin : ∀ m, m < b.ends.length → k < b.endAt m → i ≤ m) : b.endAt (i - 1) ≤ k := by
  by_contra h
  have hlt : k < b.endAt (i - 1) := by omega
  have hPred : i - 1 < b.ends.length := by omega
  have hle := hMin (i - 1) hPred hlt
  omega

/-- The selected block contains the step. -/
theorem covers (k : ℕ) (hk : k < L) :
    b.startAt (b.blockAt k) ≤ k ∧ k < b.endAt (b.blockAt k) := by
  constructor
  · unfold startAt
    split_ifs with hzero
    · omega
    · have hPos : 0 < b.blockAt k := by omega
      apply b.endAt_pred_le (b.blockAt k) k hPos (b.blockAt_lt_length k hk)
      intro m hmFinite hm
      rw [blockAt, dite_eq_left hk]
      exact Nat.find_min' (b.cover k hk) ⟨hmFinite, hm⟩
  · exact b.blockAt_spec k hk

/-- Any nonempty block interval has a unique owner: the first endpoint to its
right is exactly that block.  This is the `PiecewiseData.ownsInterval` law. -/
theorem ownsInterval (block k : ℕ)
    (hStart : b.startAt block ≤ k) (hEnd : k < b.endAt block) :
    b.blockAt k = block := by
  have hk : k < L := by
    by_cases hBlock : block < b.ends.length
    · have hLastIndex : block ≤ b.ends.length - 1 := by omega
      have hLE : b.endAt block ≤ b.endAt (b.ends.length - 1) :=
        b.endAt_mono hLastIndex
      change b.ends.getD block L ≤ b.ends.getD (b.ends.length - 1) L at hLE
      rw [b.last] at hLE
      exact lt_of_lt_of_le hEnd hLE
    · have hDefault : b.endAt block = L := by
        unfold endAt
        rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hBlock)]
      rw [hDefault] at hEnd
      exact hEnd
  have hFinite : block < b.ends.length := by
    by_contra hNot
    have hLength : b.ends.length ≤ block := Nat.le_of_not_gt hNot
    have hPos : 0 < block := lt_of_lt_of_le b.nonempty hLength
    have hPred : b.ends.length - 1 ≤ block - 1 := by omega
    have hMono := b.endAt_mono hPred
    have hStartL : L ≤ b.startAt block := by
      unfold startAt
      rw [ite_eq_right (by omega : block ≠ 0)]
      change L ≤ b.ends.getD (block - 1) L
      simpa only [endAt, b.last] using hMono
    omega
  apply Nat.le_antisymm
  · rw [blockAt, dite_eq_left hk]
    exact Nat.find_min' (b.cover k hk) ⟨hFinite, hEnd⟩
  · by_cases hzero : block = 0
    · subst block
      exact Nat.zero_le _
    · have hPos : 0 < block := by omega
      unfold startAt at hStart
      rw [ite_eq_right hzero] at hStart
      by_contra hlt
      have hle : b.blockAt k ≤ block - 1 := by omega
      have hMono := b.endAt_mono hle
      have hContr : b.endAt (b.blockAt k) ≤ k := hMono.trans hStart
      exact (not_le_of_gt (b.blockAt_spec k hk)) hContr

/-- The nonempty block intervals partition the surviving unit steps.  This
is stated for integer-valued functions because it is used to concatenate the
canonical interpolation slopes. -/
theorem sum_range_eq_sum_blocks (f : ℕ → ℤ) :
    (∑ k ∈ Finset.range L, f k) =
      ∑ i ∈ Finset.range b.ends.length,
        ∑ j ∈ Finset.range (b.endAt i - b.startAt i), f (b.startAt i + j) := by
  classical
  rw [Finset.sum_sigma']
  symm
  apply Finset.sum_bij (fun x _ => b.startAt x.1 + x.2)
  · intro x hx
    rcases Finset.mem_sigma.1 hx with ⟨hIndex, hOffset⟩
    have hOffset' : x.2 < b.endAt x.1 - b.startAt x.1 := Finset.mem_range.1 hOffset
    have hEnd : b.startAt x.1 + x.2 < b.endAt x.1 := by
      omega
    exact Finset.mem_range.2 (lt_of_lt_of_le hEnd (b.endAt_le_length x.1 (Finset.mem_range.1 hIndex)))
  · rintro ⟨xi, xj⟩ hx ⟨yi, yj⟩ hy hxy
    rcases Finset.mem_sigma.1 hx with ⟨hxIndex, hxOffset⟩
    rcases Finset.mem_sigma.1 hy with ⟨hyIndex, hyOffset⟩
    have hxOffset' : xj < b.endAt xi - b.startAt xi :=
      Finset.mem_range.1 hxOffset
    have hyOffset' : yj < b.endAt yi - b.startAt yi :=
      Finset.mem_range.1 hyOffset
    change b.startAt xi + xj = b.startAt yi + yj at hxy
    have hxEnd : b.startAt xi + xj < b.endAt xi := by
      omega
    have hyEnd : b.startAt yi + yj < b.endAt yi := by
      omega
    have hxi : b.blockAt (b.startAt xi + xj) = xi :=
      b.ownsInterval xi _ (Nat.le_add_right _ _) hxEnd
    have hyi : b.blockAt (b.startAt yi + yj) = yi :=
      b.ownsInterval yi _ (Nat.le_add_right _ _) hyEnd
    rw [hxy] at hxi
    have hIndex : xi = yi := hxi.symm.trans hyi
    subst yi
    apply Sigma.mk.inj_iff.mpr
    constructor
    · rfl
    exact heq_of_eq (by omega)
  · intro k hk
    have hkL : k < L := Finset.mem_range.1 hk
    have hi : b.blockAt k < b.ends.length := b.blockAt_lt_length k hkL
    have hCover := b.covers k hkL
    have hj : k - b.startAt (b.blockAt k) <
        b.endAt (b.blockAt k) - b.startAt (b.blockAt k) := by
      omega
    refine ⟨⟨b.blockAt k, k - b.startAt (b.blockAt k)⟩,
      Finset.mem_sigma.2 ⟨Finset.mem_range.2 hi, Finset.mem_range.2 hj⟩, ?_⟩
    exact Nat.add_sub_of_le hCover.1
  · intro x hx
    rfl

/-- Concatenating the canonical interpolation on the selected blocks realizes
the sum of the rises of exactly the nonempty blocks.  Repeated endpoints
represent zero-length blocks and therefore contribute zero independently of
their (irrelevant) stored rise. -/
theorem sum_selected_steps_eq_sum_rises (rises : ℕ → ℤ) :
    (∑ k ∈ Finset.range L,
      SubdivisionArithmetic.step
        (b.endAt (b.blockAt k) - b.startAt (b.blockAt k))
        (rises (b.blockAt k)) (k - b.startAt (b.blockAt k))) =
      ∑ i ∈ Finset.range b.ends.length,
        if b.startAt i < b.endAt i then rises i else 0 := by
  rw [b.sum_range_eq_sum_blocks]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hNonempty : b.startAt i < b.endAt i
  · rw [ite_eq_left hNonempty]
    have hLength : 0 < b.endAt i - b.startAt i := Nat.sub_pos_of_lt hNonempty
    have hOwner : ∀ j ∈ Finset.range (b.endAt i - b.startAt i),
        b.blockAt (b.startAt i + j) = i := by
      intro j hj
      apply b.ownsInterval i
      · exact Nat.le_add_right _ _
      · have hj' : j < b.endAt i - b.startAt i := Finset.mem_range.1 hj
        omega
    calc
      _ = ∑ j ∈ Finset.range (b.endAt i - b.startAt i),
          SubdivisionArithmetic.step (b.endAt i - b.startAt i) (rises i) j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hOwner j hj]
        rw [Nat.add_sub_cancel_left]
      _ = rises i := SubdivisionArithmetic.sum_steps_eq_rise (rises i) hLength
  · rw [ite_eq_right hNonempty]
    have hEmpty : b.endAt i - b.startAt i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hNonempty)
    rw [hEmpty]
    simp

/-- W2 makes the rise of an empty block zero.  Under exactly that condition,
the nonempty-block sum used by canonical interpolation is the full declared
rise sum. -/
theorem sum_rises_eq_sum_nonempty (rises : ℕ → ℤ)
    (hEmpty : ∀ i, b.endAt i ≤ b.startAt i → rises i = 0) :
    (∑ i ∈ Finset.range b.ends.length, rises i) =
      ∑ i ∈ Finset.range b.ends.length,
        if b.startAt i < b.endAt i then rises i else 0 := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hNonempty : b.startAt i < b.endAt i
  · rw [ite_eq_left hNonempty]
  · have hLE : b.endAt i ≤ b.startAt i := Nat.le_of_not_gt hNonempty
    rw [ite_eq_right hNonempty, hEmpty i hLE]

/-- The canonical selected slopes realize every declared rise once W2 has
discharged the zero-length blocks. -/
theorem sum_selected_steps_eq_total_rises (rises : ℕ → ℤ)
    (hEmpty : ∀ i, b.endAt i ≤ b.startAt i → rises i = 0) :
    (∑ k ∈ Finset.range L,
      SubdivisionArithmetic.step
        (b.endAt (b.blockAt k) - b.startAt (b.blockAt k))
        (rises (b.blockAt k)) (k - b.startAt (b.blockAt k))) =
      ∑ i ∈ Finset.range b.ends.length, rises i := by
  rw [b.sum_selected_steps_eq_sum_rises]
  exact (b.sum_rises_eq_sum_nonempty rises hEmpty).symm

end FiniteBlockEnds

end MarkedGraphs.Certificate

namespace Utilities.Certificate.DegenerateSpec.DegSpec

open MarkedGraphs.Certificate
open Utilities

variable {n p : ℕ} (d : DegSpec n p)

/-- Decode one finite endpoint list per slot into the selector portion of a
`PiecewiseData`.  Endpoint rises and the endpoint balance are supplied by the
rich leaf separately. -/
def decodePiecewiseData (potential : Fin n → ℤ)
    (blocks : (e : Fin p) → FiniteBlockEnds (d.length e))
    (rises : Fin p → ℕ → ℤ)
    (balance : ∀ e : Fin p,
      potential (d.core.head e) = potential (d.core.tail e) +
        ∑ k ∈ Finset.range (d.length e),
          blockSlope (fun e k => (blocks e).blockAt k)
            (fun e k => (blocks e).endAt k) rises e k) :
    d.PiecewiseData potential where
  blockAt := fun e k => (blocks e).blockAt k
  blockEnd := fun e k => (blocks e).endAt k
  blockRise := rises
  covers := by
    intro e k hk
    simpa [blockStart, FiniteBlockEnds.startAt] using (blocks e).covers k hk
  ownsInterval := by
    intro e block k hStart hEnd
    exact (blocks e).ownsInterval block k (by simpa [blockStart, FiniteBlockEnds.startAt] using hStart) hEnd
  balance := balance

end Utilities.Certificate.DegenerateSpec.DegSpec
