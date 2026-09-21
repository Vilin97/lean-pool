/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.Reindex

/-!
# Block parity dictionary

The parity bridge between vertex blocks of the sorted colouring
and flag-degrees of the colouring's pattern: the v-th block of the
sorted colouring is even iff the pattern-flags at the
corresponding vertex have even count.  Corollary: the master
summand vanishes whenever any block is odd-parity.
-/

namespace RS

open Classical Finset

variable {k ℓ : ℕ}

/-- The vertex corresponding to the v-th block of the sorted
colouring: applying the vertex enumeration to the block index. -/
noncomputable def blockVertex (W : ClosedFragment)
    (v : Fin (degList (starAssignEnum W)).length) : W.Vertex :=
  (Fintype.equivFin W.Vertex).symm
    (finCongr (degList_length (starAssignEnum W)) v)

/-- The degree list of the star assignment: one entry per vertex,
recording how many slots it carries. -/
noncomputable abbrev ds (W : ClosedFragment) :=
  degList (starAssignEnum W)

/-- A colouring read in block order: slot `j` of block `v` gets the
colour the original colouring gave that vertex's `j`th flag. -/
noncomputable abbrev cSorted
    (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W)) :
    MixedColouring k ℓ (ds W).sum :=
  (c ∘ finCongr (degList_sum (starAssignEnum W))) ∘
    sortSplitPerm W

/-- The slot a block position occupies in the unsorted colouring. -/
noncomputable def slotEmbed (W : ClosedFragment)
    (v : Fin (ds W).length) (j : Fin ((ds W).get v)) :
    Fin (edgeCount W + edgeCount W) :=
  (sortEquiv (starAssignEnum W)).symm
    (blockSigmaEquiv (ds W) ⟨v, j⟩)

/-- The sorted colouring at a block position equals the original
colouring at the unsorted slot. -/
theorem blockRestrict_val (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (v : Fin (ds W).length)
    (j : Fin ((ds W).get v)) :
    blockRestrict (ds W) (cSorted W c) v j =
      c (slotEmbed W v j) := by
  -- Both sides apply c to the same Fin value
  apply congrArg c
  -- Need: finCongr _ (sortSplitPerm W x) = (sortEquiv _).symm x
  -- By sortEquiv_symm_split: (sortEquiv _).symm = (sortSplitPerm W).trans
  --   (finCongr _)
  -- So (sortEquiv _).symm x = finCongr _ (sortSplitPerm W x)
  suffices h : (sortEquiv (starAssignEnum W)).symm
      (blockSigmaEquiv (ds W) ⟨v, j⟩) =
    finCongr (degList_sum (starAssignEnum W))
      ((sortSplitPerm W) (blockSigmaEquiv (ds W) ⟨v, j⟩)) from
    h.symm
  exact congrFun (congrArg _root_.Equiv.toFun
    (sortEquiv_symm_split W)) _

/-- The assignment at an embedded slot equals the block index
(up to `finCongr`). -/
theorem assign_slotEmbed (W : ClosedFragment)
    (v : Fin (ds W).length) (j : Fin ((ds W).get v)) :
    starAssignEnum W (slotEmbed W v j) =
      finCongr (degList_length (starAssignEnum W)) v := by
  have h1 := blockAssign_sortEquiv (starAssignEnum W)
    (slotEmbed W v j)
  have h2 : sortEquiv (starAssignEnum W) (slotEmbed W v j) =
      blockSigmaEquiv (ds W) ⟨v, j⟩ :=
    _root_.Equiv.apply_symm_apply _ _
  rw [h2, blockAssign_blockSigmaEquiv] at h1
  -- h1 : v = finCongr (degList_length _).symm (starAssignEnum W _)
  apply Fin.ext
  rw [finCongr_apply_coe]
  exact (congrArg Fin.val h1).symm

/-- The vertex at an embedded slot is the block's vertex. -/
theorem vertexOf_slotEmbed (W : ClosedFragment)
    (v : Fin (ds W).length) (j : Fin ((ds W).get v)) :
    ClosedFragment.vertexOf W
      ((starFlagEnum W).symm (slotEmbed W v j)) =
    blockVertex W v := by
  -- vertexOf at (starFlagEnum).symm s is starAssign W s by def
  -- starAssign W s = (equivFin).symm (starAssignEnum W s) by def
  apply (Fintype.equivFin W.Vertex).injective
  -- Goal: equivFin (vertexOf W ((starFlagEnum W).symm (slotEmbed W v j)))
  --     = equivFin (blockVertex W v)
  show starAssignEnum W (slotEmbed W v j) =
    (Fintype.equivFin W.Vertex) (blockVertex W v)
  rw [assign_slotEmbed, blockVertex, _root_.Equiv.apply_symm_apply]

/-- The slot embedding is injective in its block-offset
argument. -/
theorem slotEmbed_injective (W : ClosedFragment)
    (v : Fin (ds W).length) :
    Function.Injective (slotEmbed W v) := by
  intro j₁ j₂ h
  have h1 : blockSigmaEquiv (ds W) ⟨v, j₁⟩ =
      blockSigmaEquiv (ds W) ⟨v, j₂⟩ :=
    _root_.Equiv.injective (sortEquiv (starAssignEnum W)).symm h
  have h2 : (⟨v, j₁⟩ : Σ _w : Fin (ds W).length,
      Fin ((ds W).get _w)) = ⟨v, j₂⟩ :=
    _root_.Equiv.injective (blockSigmaEquiv (ds W)) h1
  rw [Sigma.mk.injEq] at h2
  exact eq_of_heq h2.2

/-- The slot embedding recovers the original slot from the
sigma decomposition. -/
theorem slotEmbed_recover (W : ClosedFragment)
    (v : Fin (ds W).length)
    (s : Fin (edgeCount W + edgeCount W))
    (jw : Fin ((ds W).get v))
    (hq : (⟨v, jw⟩ : Σ _w : Fin (ds W).length,
        Fin ((ds W).get _w)) =
      sortSigma (starAssignEnum W) s) :
    slotEmbed W v jw = s := by
  show (sortEquiv (starAssignEnum W)).symm
    (blockSigmaEquiv (ds W) ⟨v, jw⟩) = s
  have hbe : blockSigmaEquiv (ds W) ⟨v, jw⟩ =
      sortEquiv (starAssignEnum W) s := by
    show blockSigmaEquiv (ds W) ⟨v, jw⟩ =
      ((sortSigma (starAssignEnum W)).trans
        (blockSigmaEquiv (ds W))) s
    rw [_root_.Equiv.trans_apply, ← hq]
  rw [hbe, _root_.Equiv.symm_apply_apply]

/-- **Block parity**: the v-th block of the sorted colouring has
the same odd-set cardinality as the pattern-flags at the
corresponding vertex. -/
theorem blockRestrict_oddSet_card (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (v : Fin (ds W).length) :
    (blockRestrict (ds W) (cSorted W c) v).oddSet.card =
    ((colourFlags W c).filter
      (fun g => ClosedFragment.vertexOf W g =
        blockVertex W v)).card := by
  refine Finset.card_bij
    (fun j _hj => (starFlagEnum W).symm (slotEmbed W v j))
    ?mem ?inj ?surj
  case mem =>
    intro j hj
    simp only [mem_filter]
    constructor
    · -- the flag is in colourFlags W c
      rw [colourFlags, Finset.mem_image]
      refine ⟨slotEmbed W v j, ?_, rfl⟩
      simp only [MixedColouring.oddSet, mem_filter, mem_univ,
        true_and] at hj ⊢
      rwa [blockRestrict_val] at hj
    · exact vertexOf_slotEmbed W v j
  case inj =>
    intro j₁ _hj₁ j₂ _hj₂ h
    exact slotEmbed_injective W v
      (_root_.Equiv.injective (starFlagEnum W).symm h)
  case surj =>
    intro g hg
    simp only [mem_filter] at hg
    obtain ⟨hcf, hvtx⟩ := hg
    -- g ∈ colourFlags W c: extract the slot s
    rw [colourFlags, Finset.mem_image] at hcf
    obtain ⟨s, hs, hsg⟩ := hcf
    -- s ∈ oddSet c, and (starFlagEnum W).symm s = g
    -- The assignment of s matches block v
    have hassign : starAssignEnum W s =
        finCongr (degList_length (starAssignEnum W)) v := by
      show (Fintype.equivFin W.Vertex) (starAssign W s) = _
      have hv : starAssign W s = blockVertex W v := by
        show ClosedFragment.vertexOf W
          ((starFlagEnum W).symm s) = blockVertex W v
        rw [hsg, hvtx]
      rw [hv, blockVertex, _root_.Equiv.apply_symm_apply]
    -- sortSigma has first component v
    have hfst : (sortSigma (starAssignEnum W) s).1 = v := by
      rw [sortSigma_fst, hassign]; exact Fin.ext rfl
    -- Decompose the sigma and substitute to get j in the right
    -- type
    set q := sortSigma (starAssignEnum W) s with hq_def
    obtain ⟨w, jw⟩ := q
    simp only at hfst
    -- hfst : w = v; eliminate w
    rcases hfst with rfl
    -- After rcases: v is replaced by w throughout
    -- jw : Fin ((ds W).get w), hq_def : ⟨w, jw⟩ = sortSigma ...
    refine ⟨jw, ?_, ?_⟩
    · -- jw ∈ oddSet (blockRestrict ...)
      simp only [MixedColouring.oddSet, mem_filter, mem_univ,
        true_and, blockRestrict_val]
      rw [slotEmbed_recover W w s jw hq_def]
      simp only [MixedColouring.oddSet, mem_filter, mem_univ,
        true_and] at hs
      exact hs
    · -- the map sends jw to g
      show (starFlagEnum W).symm (slotEmbed W w jw) = g
      rw [slotEmbed_recover W w s jw hq_def, hsg]

/-- **Block parity dictionary**: the v-th block of the sorted
colouring is even iff the pattern-flags at the corresponding
vertex have even count. -/
theorem blockRestrict_parity (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (v : Fin (ds W).length) :
    MixedColouring.IsEven
      (blockRestrict (ds W) (cSorted W c) v) ↔
    Even ((colourFlags W c).filter
      (fun g => ClosedFragment.vertexOf W g =
        blockVertex W v)).card := by
  unfold MixedColouring.IsEven
  rw [blockRestrict_oddSet_card]

/-- **Master summand vanishing**: if any block of the sorted
colouring is odd-parity, the master summand is zero, since the
star coordinate vanishes on odd-parity colourings and the product
absorbs the zero. -/
theorem masterSummand_vanish_of_block_odd
    {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)
    (W : ClosedFragment)
    (c : MixedColouring k ℓ (edgeCount W + edgeCount W))
    (v : Fin (degList (starAssignEnum W)).length)
    (hodd : ¬ MixedColouring.IsEven
      (blockRestrict (degList (starAssignEnum W))
        ((c ∘ finCongr (degList_sum (starAssignEnum W))) ∘
          sortSplitPerm W) v)) :
    masterSummand f P e' W c = 0 := by
  unfold masterSummand
  have hzero : starCoord f P e'
      ((degList (starAssignEnum W)).get v)
      (blockRestrict (degList (starAssignEnum W))
        ((c ∘ finCongr (degList_sum (starAssignEnum W))) ∘
          sortSplitPerm W) v) = 0 :=
    starCoord_odd f P e' _ _ hodd
  rw [Finset.prod_eq_zero (Finset.mem_univ v) hzero, mul_zero,
    zero_mul]

end RS
