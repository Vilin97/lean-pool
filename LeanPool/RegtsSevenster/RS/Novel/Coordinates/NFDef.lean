/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockCanon

/-!
# The h-generic normal form

The master-sum analogue where an arbitrary mixed functional `h` is
evaluated at the colour-data extractors of the sorted blocks: the
per-vertex factor carries a Nodup guard mirroring `evalOdd`.

This is the first stage of discharging the Eulerian-independence
interface: the normal form is manifestly independent of the
transition system and orientation.
-/

@[expose] public section

namespace RS

open Finset

variable {k ℓ : ℕ}

/-! ## The h-generic master summand -/

-- Raised budget: the definition names the sorted colouring, its
-- block restrictions and their odd lists, so the whole star
-- enumeration elaborates here.
open Classical in
/-- The h-generic master summand: mirrors `masterSummand` but
replaces `starCoord` with the `h`-evaluation at the block's
colour-data extractors, guarded by the Nodup condition. -/
noncomputable def hMaster (h : MixedFunctional k ℓ)
    (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W)) : ℂ :=
  ((-1 : ℂ) ^ oddInversions (sortSplitPerm W)
      (c ∘ finCongr (degList_sum (starAssignEnum W))) *
    ∏ v, (if (oddListOf (blockRestrict
          (degList (starAssignEnum W))
          (((c ∘ finCongr (degList_sum (starAssignEnum W))) ∘
            sortSplitPerm W)) v)).Nodup then
        (sortSign (oddListOf (blockRestrict
          (degList (starAssignEnum W))
          (((c ∘ finCongr (degList_sum (starAssignEnum W))) ∘
            sortSplitPerm W)) v)) : ℂ) *
          h (evenMultisetOf (blockRestrict
            (degList (starAssignEnum W))
            (((c ∘ finCongr (degList_sum (starAssignEnum W))) ∘
              sortSplitPerm W)) v))
            (oddFinsetOf (blockRestrict
              (degList (starAssignEnum W))
              (((c ∘ finCongr (degList_sum
                (starAssignEnum W))) ∘ sortSplitPerm W)) v))
      else 0)) *
  betaDiag (edgeCount W) c

/-! ## Per-vertex value lemmas -/

-- Raised budget: the block factor is matched with the vertex
-- factor, unfolding the sorted colouring and its restriction.
open Classical in
/-- **The per-vertex value** (duplicate-free case): the h-generic
block factor equals the block sorting sign times the
sign-normalised Definition 5 vertex factor. -/
theorem hMaster_vertex_nodup (h : MixedFunctional k ℓ)
    (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ)
    (v : Fin (ds W).length)
    (hnd : (F.oddListAt o φ (blockVertex W v)).Nodup) :
    (if (oddListOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v)).Nodup then
      (sortSign (oddListOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
        h (evenMultisetOf (blockRestrict (ds W)
          (cSorted W (colouringOfFlip W F o ψ φ)) v))
          (oddFinsetOf (blockRestrict (ds W)
            (cSorted W (colouringOfFlip W F o ψ φ)) v))
    else 0) =
    (sortSign (oddListOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
      ((sortSign (F.oddListAt o φ (blockVertex W v)) : ℂ) *
        h.evalOdd (F.evenColoursAt ψ (blockVertex W v))
          (F.oddListAt o φ (blockVertex W v))) := by
  have hnd_b : (oddListOf (blockRestrict (ds W)
      (cSorted W (colouringOfFlip W F o ψ φ)) v)).Nodup :=
    (oddListOf_blockRestrict_nodup_iff W F o ψ φ v).mpr hnd
  rw [ite_eq_left hnd_b]
  rw [evenMultisetOf_blockRestrict W F o ψ φ v]
  rw [oddFinsetOf_blockRestrict W F o ψ φ v]
  rw [MixedFunctional.evalOdd, ite_eq_left hnd]
  set A := (sortSign (oddListOf (blockRestrict (ds W)
      (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ)
  set B := (sortSign (F.oddListAt o φ (blockVertex W v)) : ℂ)
  set hval := h (F.evenColoursAt ψ (blockVertex W v))
    (F.oddListAt o φ (blockVertex W v)).toFinset
  have hB : B * B = 1 := sortSign_sq _
  calc A * hval = A * ((B * B) * hval) := by rw [hB, one_mul]
    _ = A * (B * (B * hval)) := by ring

-- As for the duplicate-free case, on the vanishing branch.
open Classical in
/-- **The per-vertex vanishing** (repeated case): a repeated odd
value kills the h-generic block factor. -/
theorem hMaster_vertex_not_nodup (h : MixedFunctional k ℓ)
    (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ)
    (v : Fin (ds W).length)
    (hnd : ¬ (F.oddListAt o φ (blockVertex W v)).Nodup) :
    (if (oddListOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v)).Nodup then
      (sortSign (oddListOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
        h (evenMultisetOf (blockRestrict (ds W)
          (cSorted W (colouringOfFlip W F o ψ φ)) v))
          (oddFinsetOf (blockRestrict (ds W)
            (cSorted W (colouringOfFlip W F o ψ φ)) v))
    else 0) = 0 := by
  have hnd_b : ¬ (oddListOf (blockRestrict (ds W)
      (cSorted W (colouringOfFlip W F o ψ φ)) v)).Nodup :=
    fun hn => hnd
      ((oddListOf_blockRestrict_nodup_iff W F o ψ φ v).mp hn)
  exact ite_eq_right hnd_b

/-! ## The normal form -/

open Classical in
/-- The h-generic normal form for the Definition 5 summand:
the sum over even/odd colourings of the h-generic master
summand at the data colouring. -/
noncomputable def defFiveNF (h : MixedFunctional k ℓ)
    (W : ClosedFragment) (F : EdgeSubset W) : ℂ :=
  ∑ ψ : F.EvenColouring k, ∑ φ : F.OddColouring ℓ,
    hMaster h W (colouringOf W F ψ φ)

open Classical in
/-- **The flip-reindex step**: the normal form equals the sum
over the flipped data colouring at any orientation. -/
theorem defFiveNF_eq_flip (h : MixedFunctional k ℓ)
    (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    defFiveNF h W F = ∑ ψ, ∑ φ,
      hMaster h W (colouringOfFlip W F o ψ φ) := by
  unfold defFiveNF
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  set T := outRepSet W F o
  set hTc := outRepSet_pairing_mem W F o
  have heq : ∀ φ : F.OddColouring ℓ,
      hMaster h W (colouringOfFlip W F o ψ φ) =
      hMaster h W (colouringOf W F ψ
        (EdgeSubset.OddColouring.flip F T hTc φ)) := fun _ => rfl
  simp_rw [heq]
  exact (EdgeSubset.OddColouring.sum_flip F T hTc _).symm

end RS
