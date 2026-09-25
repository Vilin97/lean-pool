/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.FlagEnum
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.IndexPerm
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockAlign

/-!
# The sorted-position key

The block enumeration is sorted under the sigma-position key, so
the canonical index permutation's sign is the key-sortSign of the
pair enumeration alone.
-/

@[expose] public section

namespace RS

open Finset

variable {k ℓ : ℕ}

/-- The sorted-position key of a flag. -/
noncomputable def sortKey (W : ClosedFragment) (f : W.Flag) :
    Fin (ds W).sum :=
  sortEquiv (starAssignEnum W) (starFlagEnum W f)

/-- The key is injective. -/
theorem sortKey_injective (W : ClosedFragment) :
    Function.Injective (sortKey W) := fun _ _ h =>
  (starFlagEnum W).injective
    ((sortEquiv (starAssignEnum W)).injective h)

/-- The key of a block flag is its sigma position. -/
theorem sortKey_blockFlag (W : ClosedFragment)
    (v : Fin (ds W).length) (j : Fin ((ds W).get v)) :
    sortKey W (blockFlag W v j) =
      blockSigmaEquiv (ds W) ⟨v, j⟩ := by
  rw [sortKey, starFlagEnum_blockFlag]
  exact _root_.Equiv.apply_symm_apply _ _

open Classical in
/-- The block enumeration is sorted under the key. -/
theorem blockOddFlagList_key_sorted (W : ClosedFragment)
    (F : EdgeSubset W) (v : Fin (ds W).length) :
    List.Pairwise (· ≤ ·)
      ((blockOddFlagList W F v).map
        (fun f => sortKey W f.val)) := by
  have hgen : ∀ (l : List (Fin ((ds W).get v)))
      (H : ∀ j ∈ l, j ∈ oddSlots W F v),
      (l.pmap (fun j hj => (⟨blockFlag W v j,
          (mem_oddSlots j).mp hj⟩ :
            {f : W.Flag // f ∈ F.flags})) H).map
        (fun f => sortKey W f.val) =
      l.map (fun j => sortKey W (blockFlag W v j)) := by
    intro l
    induction l with
    | nil => intro H; rfl
    | cons a t ih =>
      intro H
      rw [List.pmap_cons, List.map_cons, List.map_cons, ih]
  rw [blockOddFlagList, hgen]
  have hsorted := Finset.pairwise_sort
    (r := (· ≤ ·)) (s := oddSlots W F v)
  refine List.Pairwise.map _ ?_ hsorted
  intro a b hab
  rw [sortKey_blockFlag, sortKey_blockFlag]
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact le_of_lt (blockSigmaEquiv_strictMono (ds W) v hlt)
  · rw [heq]

open Classical in
/-- The enumerations have equal length. -/
theorem blockOddFlagList_length_eq (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (v : Fin (ds W).length) :
    (blockOddFlagList W F v).length =
      (pairFlagList (F := F) o (blockVertex W v)).length :=
  length_eq_of_nodup_mem _ _ (blockOddFlagList_nodup W F v)
    (pairFlagList_nodup o (blockVertex W v))
    (mem_blockOddFlagList_iff_pairFlagList W F o v)

open Classical in
/-- **The per-vertex reindexing sign is the key-sortSign of the
pair enumeration.** -/
theorem sortSign_pairFlagList_key (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (v : Fin (ds W).length) :
    sortSign ((pairFlagList (F := F) o
        (blockVertex W v)).map (fun f => sortKey W f.val)) =
      (Equiv.Perm.sign (listIndexPerm
        (blockOddFlagList W F v)
        (pairFlagList (F := F) o (blockVertex W v))
        (blockOddFlagList_nodup W F v)
        (pairFlagList_nodup o (blockVertex W v))
        (mem_blockOddFlagList_iff_pairFlagList W F o v)
        (blockOddFlagList_length_eq W F o v)) : ℤ) := by
  rw [sortSign_map_listIndexPerm (blockOddFlagList W F v)
    (pairFlagList (F := F) o (blockVertex W v))
    (blockOddFlagList_nodup W F v)
    (pairFlagList_nodup o (blockVertex W v))
    (mem_blockOddFlagList_iff_pairFlagList W F o v)
    (blockOddFlagList_length_eq W F o v)
    (fun f => sortKey W f.val)
    (List.Nodup.map
      (fun a b h => Subtype.ext (sortKey_injective W h))
      (blockOddFlagList_nodup W F v))]
  rw [sortSign_eq_one_of_sorted _
    (blockOddFlagList_key_sorted W F v), mul_one]

end RS
