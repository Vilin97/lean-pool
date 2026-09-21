/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.VertexValue
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.FlagEnum

/-!
# The block odd list, order-exactly

The odd list of a block of the flipped data colouring is the
Definition 5 value map over the block-slot flag enumeration,
entry by entry.
-/

namespace RS

open Classical Finset

variable {k ℓ : ℕ}

-- Raised budget: the block's odd list is matched with the sorted
-- slot enumeration order-exactly, so the flip, the sort and the
-- block restriction are all unfolded together.
open Classical in
/-- **The block odd list is the value map of the block
enumeration** (order-exact). -/
theorem oddListOf_blockRestrict_eq_map (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length) :
    oddListOf (blockRestrict (ds W)
      (cSorted W (colouringOfFlip W F o ψ φ)) v) =
    (blockOddFlagList W F v).map (defFiveValue o φ) := by
  set b := blockRestrict (ds W)
    (cSorted W (colouringOfFlip W F o ψ φ)) v with hb
  set L := (oddSlots W F v).sort (· ≤ ·) with hL
  have hLmem : ∀ j, j ∈ L ↔ j ∈ oddSlots W F v := by
    intro j
    rw [hL, Finset.mem_sort]
  have hpwlt : List.Pairwise (· < ·) L := by
    have h1 : List.Pairwise (· ≤ ·) L :=
      Finset.pairwise_sort (r := (· ≤ ·))
        (s := oddSlots W F v)
    have h2 : L.Nodup := Finset.sort_nodup _ _
    refine List.Pairwise.imp ?_ (List.Pairwise.and h1 h2)
    intro a c hac
    exact lt_of_le_of_ne hac.1 hac.2
  have hps : StrictMono (fun t : Fin L.length => L.get t) := by
    intro t₁ t₂ ht
    exact List.pairwise_iff_getElem.mp hpwlt t₁.val t₂.val
      t₁.isLt t₂.isLt ht
  have hmemflag : ∀ t : Fin L.length,
      blockFlag W v (L.get t) ∈ F.flags := by
    intro t
    exact (mem_oddSlots (L.get t)).mp
      ((hLmem (L.get t)).mp (L.get_mem t))
  have hvals : ∀ t : Fin L.length,
      Sum.getRight? (b (L.get t)) =
      some (defFiveValue o φ ⟨blockFlag W v (L.get t),
        hmemflag t⟩) := by
    intro t
    rw [hb, blockRestrict_colouringOfFlip_mem W F o ψ φ v
      (L.get t) (hmemflag t)]
    rfl
  have hnone : ∀ q : Fin ((ds W).get v),
      (∀ t : Fin L.length, L.get t ≠ q) →
      Sum.getRight? (b q) = none := by
    intro q hq
    have hqL : q ∉ L := by
      intro hmem
      obtain ⟨t, ht⟩ := List.mem_iff_get.mp hmem
      exact hq t ht
    have hqodd : blockFlag W v q ∉ F.flags := by
      intro hmem
      exact hqL ((hLmem q).mpr ((mem_oddSlots q).mpr hmem))
    rw [hb, blockRestrict_colouringOfFlip_not_mem W F o ψ φ
      v q hqodd]
    rfl
  have hmain : oddListOf b = List.ofFn
      (fun t : Fin L.length => defFiveValue o φ
        ⟨blockFlag W v (L.get t), hmemflag t⟩) := by
    rw [oddListOf]
    exact filterMap_ofFn_sorted hps hvals hnone
  rw [hmain]
  rw [show blockOddFlagList W F v = L.pmap
      (fun j hj => (⟨blockFlag W v j,
        (mem_oddSlots j).mp hj⟩ :
          {f : W.Flag // f ∈ F.flags}))
      (fun _ hj => (Finset.mem_sort _).mp hj) from rfl]
  rw [List.map_pmap]
  refine List.ext_getElem ?_ ?_
  · rw [List.length_ofFn, List.length_pmap]
  · intro i hi₁ hi₂
    rw [List.getElem_ofFn, List.getElem_pmap]
    refine congrArg (defFiveValue o φ) (Subtype.ext ?_)
    rfl

end RS
