/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockData
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RepFlag
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddFlip

/-!
# The block alignment

Flipping the odd colouring on the edges whose representative is
outgoing aligns the block values of the data colouring with the
Definition 5 per-flag values: outgoing flags carry the partner of
their colour, incoming flags the colour itself.
-/

@[expose] public section

namespace RS

open Finset

variable {k ℓ : ℕ}

/-- The flipped data colouring of an orientation. -/
noncomputable def colouringOfFlip (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    MixedColouring k ℓ (edgeCount W + edgeCount W) :=
  colouringOf W F ψ
    (EdgeSubset.OddColouring.flip F (outRepSet W F o)
      (outRepSet_pairing_mem W F o) φ)

/-- The slot half of a block flag is the slot half of its
embedded slot. -/
theorem starFlagEnum_blockFlag (W : ClosedFragment)
    (v : Fin (ds W).length) (j : Fin ((ds W).get v)) :
    starFlagEnum W (blockFlag W v j) = slotEmbed W v j :=
  _root_.Equiv.apply_symm_apply _ _

/-- **The four-case alignment**: the block value of the flipped
data colouring at a participating slot is the Definition 5
per-flag value of its flag. -/
theorem blockRestrict_colouringOfFlip_mem (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length)
    (j : Fin ((ds W).get v))
    (h : blockFlag W v j ∈ F.flags) :
    blockRestrict (ds W)
      (cSorted W (colouringOfFlip W F o ψ φ)) v j =
    Sum.inr (if o.isOut (blockFlag W v j) = true
      then oddPartner ℓ (φ.val ⟨blockFlag W v j, h⟩)
      else φ.val ⟨blockFlag W v j, h⟩) := by
  rw [colouringOfFlip,
    blockRestrict_colouringOf_mem W F _ _ v j h]
  congr 1
  by_cases hlow : (slotEmbed W v j).val < edgeCount W
  · rw [ite_eq_left hlow]
    have hrep : repFlag W (blockFlag W v j) =
        blockFlag W v j :=
      repFlag_low W _ (by
        rw [starFlagEnum_blockFlag]
        exact hlow)
    by_cases hout : o.isOut (blockFlag W v j) = true
    · have hT : blockFlag W v j ∈ outRepSet W F o :=
        (mem_outRepSet_iff W F o _ h).mpr (by
          rw [hrep]
          exact hout)
      rw [EdgeSubset.OddColouring.flip_val_mem F _ _ φ
        ⟨blockFlag W v j, h⟩ hT, ite_eq_left hout]
    · have hT : blockFlag W v j ∉ outRepSet W F o :=
        fun hmem => hout (by
          have h2 := (mem_outRepSet_iff W F o _ h).mp hmem
          rw [hrep] at h2
          exact h2)
      rw [EdgeSubset.OddColouring.flip_val_not_mem F _ _ φ
        ⟨blockFlag W v j, h⟩ hT, ite_eq_right hout]
  · rw [ite_eq_right hlow]
    have hnotlow :
        ¬ (starFlagEnum W (blockFlag W v j)).val <
          edgeCount W := by
      rw [starFlagEnum_blockFlag]
      exact hlow
    have hrep : repFlag W (blockFlag W v j) =
        W.pairing (blockFlag W v j) :=
      repFlag_high W _ hnotlow
    have hpair := o.pairing_flip _ h
    by_cases hout : o.isOut (blockFlag W v j) = true
    · have hT : blockFlag W v j ∉ outRepSet W F o :=
        fun hmem => by
          have h2 := (mem_outRepSet_iff W F o _ h).mp hmem
          rw [hrep, hpair, hout] at h2
          exact Bool.noConfusion h2
      rw [EdgeSubset.OddColouring.flip_val_not_mem F _ _ φ
        ⟨blockFlag W v j, h⟩ hT, ite_eq_left hout]
    · have hof : o.isOut (blockFlag W v j) = false := by
        cases hb : o.isOut (blockFlag W v j)
        · rfl
        · exact absurd hb hout
      have hT : blockFlag W v j ∈ outRepSet W F o :=
        (mem_outRepSet_iff W F o _ h).mpr (by
          rw [hrep, hpair, hof]
          rfl)
      rw [EdgeSubset.OddColouring.flip_val_mem F _ _ φ
        ⟨blockFlag W v j, h⟩ hT, oddPartner_invol,
        ite_eq_right hout]

/-- Non-participating block values are unchanged by the flip. -/
theorem blockRestrict_colouringOfFlip_not_mem
    (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ)
    (v : Fin (ds W).length) (j : Fin ((ds W).get v))
    (h : blockFlag W v j ∉ F.flags) :
    blockRestrict (ds W)
      (cSorted W (colouringOfFlip W F o ψ φ)) v j =
    Sum.inl (ψ.val ⟨blockFlag W v j, h⟩) :=
  blockRestrict_colouringOf_not_mem W F ψ _ v j h

end RS
