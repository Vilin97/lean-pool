/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness
import LeanPool.TwoColoringOneRound.LowerBound.OverlapType

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskComplete
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000MaskComplete

open Distributed2Coloring.LowerBound.N1000000StructureConstants
open Distributed2Coloring.LowerBound.N1000000Witness

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Distributed2Coloring.LowerBound.Mask
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

instance : DecidablePred IsPartialPermMask := by
  intro m
  unfold IsPartialPermMask
  infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def partialPermMasks : Finset Mask :=
  (Finset.range (1 <<< 9)).filter IsPartialPermMask

private theorem mem_masks_block0 {m : Mask} (hhi : m < 32)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block1 {m : Mask} (hlo : 32 ≤ m) (hhi : m < 64)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block2 {m : Mask} (hlo : 64 ≤ m) (hhi : m < 96)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block3 {m : Mask} (hlo : 96 ≤ m) (hhi : m < 128)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block4 {m : Mask} (hlo : 128 ≤ m) (hhi : m < 160)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block5 {m : Mask} (hlo : 160 ≤ m) (hhi : m < 192)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block6 {m : Mask} (hlo : 192 ≤ m) (hhi : m < 224)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block7 {m : Mask} (hlo : 224 ≤ m) (hhi : m < 256)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block8 {m : Mask} (hlo : 256 ≤ m) (hhi : m < 288)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block9 {m : Mask} (hlo : 288 ≤ m) (hhi : m < 320)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block10 {m : Mask} (hlo : 320 ≤ m) (hhi : m < 352)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block11 {m : Mask} (hlo : 352 ≤ m) (hhi : m < 384)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block12 {m : Mask} (hlo : 384 ≤ m) (hhi : m < 416)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block13 {m : Mask} (hlo : 416 ≤ m) (hhi : m < 448)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block14 {m : Mask} (hlo : 448 ≤ m) (hhi : m < 480)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

private theorem mem_masks_block15 {m : Mask} (hlo : 480 ≤ m) (hhi : m < 512)
    (hperm : IsPartialPermMask m) :
    m ∈ (masks.toList.toFinset : Finset Mask) := by
  interval_cases m <;> first | decide | exfalso; revert hperm; decide

theorem mem_masks_toFinset_of_isPartialPermMask {m : Mask} (hm : m < (1 <<< 9))
    (hperm : IsPartialPermMask m) : m ∈ (masks.toList.toFinset : Finset Mask) := by
  have hm' : m < 512 := by simpa using hm
  by_cases h0 : m < 32
  · exact mem_masks_block0 h0 hperm
  by_cases h1 : m < 64
  · exact mem_masks_block1 (le_of_not_gt h0) h1 hperm
  by_cases h2 : m < 96
  · exact mem_masks_block2 (le_of_not_gt h1) h2 hperm
  by_cases h3 : m < 128
  · exact mem_masks_block3 (le_of_not_gt h2) h3 hperm
  by_cases h4 : m < 160
  · exact mem_masks_block4 (le_of_not_gt h3) h4 hperm
  by_cases h5 : m < 192
  · exact mem_masks_block5 (le_of_not_gt h4) h5 hperm
  by_cases h6 : m < 224
  · exact mem_masks_block6 (le_of_not_gt h5) h6 hperm
  by_cases h7 : m < 256
  · exact mem_masks_block7 (le_of_not_gt h6) h7 hperm
  by_cases h8 : m < 288
  · exact mem_masks_block8 (le_of_not_gt h7) h8 hperm
  by_cases h9 : m < 320
  · exact mem_masks_block9 (le_of_not_gt h8) h9 hperm
  by_cases h10 : m < 352
  · exact mem_masks_block10 (le_of_not_gt h9) h10 hperm
  by_cases h11 : m < 384
  · exact mem_masks_block11 (le_of_not_gt h10) h11 hperm
  by_cases h12 : m < 416
  · exact mem_masks_block12 (le_of_not_gt h11) h12 hperm
  by_cases h13 : m < 448
  · exact mem_masks_block13 (le_of_not_gt h12) h13 hperm
  by_cases h14 : m < 480
  · exact mem_masks_block14 (le_of_not_gt h13) h14 hperm
  exact mem_masks_block15 (le_of_not_gt h14) hm' hperm

theorem maskAt_injective : Function.Injective (maskAt : DirIdx → Mask) := by decide

theorem exists_dirIdx_of_isPartialPermMask {m : Mask} (hm : m < (1 <<< 9))
    (hperm : IsPartialPermMask m) : ∃ d : DirIdx, maskAt d = m := by
  classical
  -- Convert membership in `toFinset` back to membership in the list.
  have hmemFinset : m ∈ (masks.toList.toFinset : Finset Mask) :=
    mem_masks_toFinset_of_isPartialPermMask (m := m) hm hperm
  have hmemList : m ∈ masks.toList := by simpa [List.mem_toFinset] using hmemFinset
  -- Extract an index `i` with `masks.toList[i] = m`.
  rcases (List.mem_iff_get).1 hmemList with ⟨i, hi⟩
  have hiLt : i.1 < masks.size := by exact i.2
  have hList : masks.toList[i.1] = m := by simpa [List.get_eq_getElem] using hi
  have hToList : masks.toList[i.1] = masks[i.1] :=
    Array.getElem_toList (xs := masks) (i := i.1) hiLt
  have hArr : masks[i.1] = m := by exact hToList.symm.trans hList
  refine ⟨⟨i.1, hiLt⟩, ?_⟩
  simpa [maskAt, hiLt] using hArr

end N1000000MaskComplete

end Distributed2Coloring.LowerBound
