/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockOddList
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TauKey

/-!
# The per-vertex sign collapse

The product of the two per-vertex sorting signs is the
key-sortSign of the pair enumeration: both lists are value maps
of the two flag enumerations, so the reindexing sign transports
between them, and the block enumeration is key-sorted.
-/

@[expose] public section

namespace RS

open Finset

variable {k ℓ : ℕ}

-- Two sorting signs are matched with the key sign of
-- the pair enumeration, so all three sorts unfold together.
open Classical in
/-- **The per-vertex sign collapse**: the block and Definition 5
sorting signs multiply to the key-sortSign of the pair
enumeration. -/
theorem vertex_sign_collapse (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length)
    (hnd : (F.oddListAt o φ (blockVertex W v)).Nodup) :
    (sortSign (oddListOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
      (sortSign (F.oddListAt o φ (blockVertex W v)) : ℂ) =
    (sortSign ((pairFlagList (F := F) o
        (blockVertex W v)).map
      (fun f => sortKey W f.val)) : ℂ) := by
  have hblock := oddListOf_blockRestrict_eq_map W F o ψ φ v
  have hpair := oddListAt_eq_map (F := F) o φ
    (blockVertex W v)
  have hnd_map : ((blockOddFlagList W F v).map
      (defFiveValue o φ)).Nodup := by
    rw [← hblock]
    exact (oddListOf_blockRestrict_nodup_iff W F o ψ φ
      v).mpr hnd
  have htrans := sortSign_map_listIndexPerm
    (blockOddFlagList W F v)
    (pairFlagList (F := F) o (blockVertex W v))
    (blockOddFlagList_nodup W F v)
    (pairFlagList_nodup o (blockVertex W v))
    (mem_blockOddFlagList_iff_pairFlagList W F o v)
    (blockOddFlagList_length_eq W F o v)
    (defFiveValue o φ) hnd_map
  have hkey := sortSign_pairFlagList_key W F o v
  -- htrans : sortSign (pairList.map dFV) =
  --   sign τ * sortSign (blockList.map dFV)
  -- hkey   : sortSign (pairList.map key) = (sign τ : ℤ)
  rw [hblock, hpair]
  have hsq : (sortSign ((blockOddFlagList W F v).map
      (defFiveValue o φ)) : ℂ) *
      (sortSign ((blockOddFlagList W F v).map
        (defFiveValue o φ)) : ℂ) = 1 := sortSign_sq _
  have h1 : (sortSign ((pairFlagList (F := F) o
      (blockVertex W v)).map (defFiveValue o φ)) : ℂ) =
      ((Equiv.Perm.sign (listIndexPerm
        (blockOddFlagList W F v)
        (pairFlagList (F := F) o (blockVertex W v))
        (blockOddFlagList_nodup W F v)
        (pairFlagList_nodup o (blockVertex W v))
        (mem_blockOddFlagList_iff_pairFlagList W F o v)
        (blockOddFlagList_length_eq W F o v)) : ℤ) : ℂ) *
      (sortSign ((blockOddFlagList W F v).map
        (defFiveValue o φ)) : ℂ) := by
    rw [htrans]
    push_cast
    ring
  have h2 : ((Equiv.Perm.sign (listIndexPerm
      (blockOddFlagList W F v)
      (pairFlagList (F := F) o (blockVertex W v))
      (blockOddFlagList_nodup W F v)
      (pairFlagList_nodup o (blockVertex W v))
      (mem_blockOddFlagList_iff_pairFlagList W F o v)
      (blockOddFlagList_length_eq W F o v)) : ℤ) : ℂ) =
      (sortSign ((pairFlagList (F := F) o
        (blockVertex W v)).map
        (fun f => sortKey W f.val)) : ℂ) := by
    rw [← hkey]
  calc (sortSign ((blockOddFlagList W F v).map
        (defFiveValue o φ)) : ℂ) *
      (sortSign ((pairFlagList (F := F) o
        (blockVertex W v)).map (defFiveValue o φ)) : ℂ)
      = (sortSign ((blockOddFlagList W F v).map
          (defFiveValue o φ)) : ℂ) *
        (((Equiv.Perm.sign (listIndexPerm
          (blockOddFlagList W F v)
          (pairFlagList (F := F) o (blockVertex W v))
          (blockOddFlagList_nodup W F v)
          (pairFlagList_nodup o (blockVertex W v))
          (mem_blockOddFlagList_iff_pairFlagList W F o v)
          (blockOddFlagList_length_eq W F o v)) : ℤ) : ℂ) *
        (sortSign ((blockOddFlagList W F v).map
          (defFiveValue o φ)) : ℂ)) := by
        rw [← h1]
    _ = ((Equiv.Perm.sign (listIndexPerm
          (blockOddFlagList W F v)
          (pairFlagList (F := F) o (blockVertex W v))
          (blockOddFlagList_nodup W F v)
          (pairFlagList_nodup o (blockVertex W v))
          (mem_blockOddFlagList_iff_pairFlagList W F o v)
          (blockOddFlagList_length_eq W F o v)) : ℤ) : ℂ) := by
        calc _ = (((sortSign ((blockOddFlagList W F v).map
              (defFiveValue o φ)) : ℂ) *
            (sortSign ((blockOddFlagList W F v).map
              (defFiveValue o φ)) : ℂ)) *
            ((Equiv.Perm.sign (listIndexPerm
              (blockOddFlagList W F v)
              (pairFlagList (F := F) o (blockVertex W v))
              (blockOddFlagList_nodup W F v)
              (pairFlagList_nodup o (blockVertex W v))
              (mem_blockOddFlagList_iff_pairFlagList W F o v)
              (blockOddFlagList_length_eq W F o v)) : ℤ)
              : ℂ)) := by ring
          _ = _ := by rw [hsq, one_mul]
    _ = (sortSign ((pairFlagList (F := F) o
          (blockVertex W v)).map
        (fun f => sortKey W f.val)) : ℂ) := h2

end RS
