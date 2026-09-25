/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaFlip
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.VertexSign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TauCount
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ConcatSign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SignPair
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RiffleSign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RegroupSign

/-!
# The core and grand parities

The two parity counts the extraction's sign bookkeeping rests on:
the parity of the core slots' pairing and the parity of the whole
slot list.
-/

namespace RS

open CategoryTheory MonoidalCategory Finset
open Functor.LaxMonoidal Functor.OplaxMonoidal


variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

private theorem core_out_card (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    Fintype.card
      {f : {g : W.Flag // g ∈ F.flags} //
        o.isOut f.val = true} =
    (edgeIndexSet W F).card := by
  classical
  have hcard2 : F.flags.card =
      2 * (edgeIndexSet W F).card := by
    have h1 : Fintype.card {f : W.Flag // f ∈ F.flags} =
        F.flags.card := Fintype.card_coe _
    have h2 : (Finset.univ :
        Finset {f : W.Flag // f ∈ F.flags}) =
        (edgePairList W F).toFinset := by
      ext x
      simp only [Finset.mem_univ, List.mem_toFinset,
        true_iff]
      exact mem_edgePairList W F x
    have h3 : Fintype.card {f : W.Flag // f ∈ F.flags} =
        (edgePairList W F).length := by
      rw [← Finset.card_univ, h2]
      exact List.toFinset_card_of_nodup (edgePairList_nodup W F)
    have h4 : (edgePairList W F).length =
        2 * (edgeIndexSet W F).card := by
      rw [edgePairList, List.length_flatMap]
      have h5 : (((partEdges W F).attachWith
          (· ∈ edgeIndexSet W F)
          (fun _ hi => (Finset.mem_sort _).mp hi)).map
          (fun i => ([⟨(starFlagEnum W).symm
              (Fin.castAdd (edgeCount W) i.val),
            repMem_of_partEdge i.prop⟩,
            ⟨(starFlagEnum W).symm
              (Fin.natAdd (edgeCount W) i.val),
            partnerMem_of_partEdge i.prop⟩] :
            List {f : W.Flag // f ∈ F.flags}).length)) =
          List.replicate (((partEdges W F).attachWith
            (· ∈ edgeIndexSet W F)
            (fun _ hi => (Finset.mem_sort _).mp hi)).length)
            2 := by
        refine Eq.trans (List.map_congr_left
          (fun i _ => (rfl : _ = 2))) ?_
        exact List.map_const'
      rw [h5, List.sum_replicate, smul_eq_mul,
        List.length_attachWith]
      rw [show (partEdges W F).length =
        (edgeIndexSet W F).card from Finset.length_sort (· ≤ ·)]
      ring
    omega
  have hout_card : Fintype.card
      {f : {g : W.Flag // g ∈ F.flags} //
        o.isOut f.val = true} =
      (edgeIndexSet W F).card := by
    have h1 := card_out_eq_fintype W F o
    have h2 := card_in_eq_card_out W F o
    have h3 := Finset.card_filter_add_card_filter_not
      (s := F.flags) (p := fun f => o.isOut f = true)
    have h4 : F.flags.filter
        (fun f => ¬ (o.isOut f = true)) =
        F.flags.filter (fun f => o.isOut f = false) :=
      Finset.filter_congr (fun f _ => by
        cases h : o.isOut f <;> simp)
    rw [h4] at h3
    omega
  exact hout_card

/-- **The core parity identity**: the pattern,
crossing and representative signs against the pair-enumeration
key signs compose to the circuit and outgoing signs. -/
theorem core_parity (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    ((-1 : ℂ) ^ patternOddInv W F) *
      ((-1 : ℂ) ^ (Finset.univ.filter
        (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
          p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
          p.2 ∈ edgeIndexSet W F)).card *
        (-1 : ℂ) ^ inRepCount W F o) *
      ∏ v : Fin (ds W).length,
        (sortSign ((pairFlagList (F := F) o
            (blockVertex W v)).map
          (fun f => sortKey W f.val)) : ℂ) =
    (-1 : ℂ) ^ κ.circuitCount := by
  classical
  -- ═══════ STAGE 1: THE FIVE LISTS AGREE AS SETS ═══════
  -- Nodup, membership and length for the slot, edge-pair, oriented,
  -- matched and global lists, so that the index permutations between
  -- consecutive lists are defined and compose.
  have nA := globalSlotList_nodup W F
  have nB := edgePairList_nodup W F
  have nC := orientedPairList_nodup W F o
  have nM := matchedPairList_nodup' W F o
  have nD := globalPairList_nodup W F o
  have mAB : ∀ x, x ∈ globalSlotList W F ↔
      x ∈ edgePairList W F := fun x =>
    ⟨fun _ => mem_edgePairList W F x,
     fun _ => mem_globalSlotList W F x⟩
  have mBC : ∀ x, x ∈ edgePairList W F ↔
      x ∈ orientedPairList W F o := fun x =>
    ⟨fun _ => mem_orientedPairList W F o x,
     fun _ => mem_edgePairList W F x⟩
  have mCM : ∀ x, x ∈ orientedPairList W F o ↔
      x ∈ matchedPairList W F o := fun x =>
    ⟨fun _ => mem_matchedPairList' W F o x,
     fun _ => mem_orientedPairList W F o x⟩
  have mMD : ∀ x, x ∈ matchedPairList W F o ↔
      x ∈ globalPairList W F o := fun x =>
    ⟨fun _ => mem_globalPairList W F o x,
     fun _ => mem_matchedPairList' W F o x⟩
  have mAD : ∀ x, x ∈ globalSlotList W F ↔
      x ∈ globalPairList W F o := fun x =>
    ⟨fun _ => mem_globalPairList W F o x,
     fun _ => mem_globalSlotList W F x⟩
  have lAB := length_eq_of_nodup_mem _ _ nA nB mAB
  have lBC := length_eq_of_nodup_mem _ _ nB nC mBC
  have lCM := length_eq_of_nodup_mem _ _ nC nM mCM
  have lMD := length_eq_of_nodup_mem _ _ nM nD mMD
  have lAD := length_eq_of_nodup_mem _ _ nA nD mAD
  -- ═══════ STAGE 2: THE CHAIN OF INDEX PERMUTATIONS ═══════
  -- the chained sign
  have hchain :
      Equiv.Perm.sign (listIndexPerm (globalSlotList W F)
        (globalPairList W F o) nA nD mAD lAD) =
      Equiv.Perm.sign (listIndexPerm (globalSlotList W F)
          (edgePairList W F) nA nB mAB lAB) *
        (Equiv.Perm.sign (listIndexPerm (edgePairList W F)
            (orientedPairList W F o) nB nC mBC lBC) *
          (Equiv.Perm.sign (listIndexPerm
              (orientedPairList W F o)
              (matchedPairList W F o) nC nM mCM lCM) *
            Equiv.Perm.sign (listIndexPerm
              (matchedPairList W F o)
              (globalPairList W F o) nM nD mMD lMD))) := by
    have t1 := sign_listIndexPerm_trans
      (globalSlotList W F) (edgePairList W F)
      (globalPairList W F o) nA nB nD mAB
      (fun x => (mBC x).trans ((mCM x).trans (mMD x)))
      lAB (lBC.trans (lCM.trans lMD))
    have t2 := sign_listIndexPerm_trans
      (edgePairList W F) (orientedPairList W F o)
      (globalPairList W F o) nB nC nD mBC
      (fun x => (mCM x).trans (mMD x))
      lBC (lCM.trans lMD)
    have t3 := sign_listIndexPerm_trans
      (orientedPairList W F o) (matchedPairList W F o)
      (globalPairList W F o) nC nM nD mCM mMD lCM lMD
    exact t1.trans (by rw [t2, t3])
  -- the four link values
  have hAB := sign_listIndexPerm_slot_edge W F
  have hBC := sign_listIndexPerm_edge_oriented W F o
  have hCM := sign_listIndexPerm_oriented_matched W F o
  have hMD := sign_listIndexPerm_matched_global W F o
  -- ═══════ STAGE 3: THE FLAG-COUNT BRIDGE ═══════
  -- the flag-count bridge
  have hout_card := core_out_card W F o
  -- ═══════ STAGE 4: THE TWO ENDPOINTS OF THE CHAIN ═══════
  -- endpoints: the two key sortSigns pair to the chained sign
  have hpair := sortSign_key_pair
    (fun f : {f : W.Flag // f ∈ F.flags} =>
      sortKey W f.val)
    (fun a b h => Subtype.ext (sortKey_injective W h))
    (globalSlotList W F) (globalPairList W F o)
    nA nD mAD lAD
  -- the pattern sign is the A-end key sortSign
  have hA : ((-1 : ℂ) ^ patternOddInv W F) =
      (sortSign ((globalSlotList W F).map
        (fun f => sortKey W f.val)) : ℂ) := by
    rw [patternOddInv_eq_inversions W F, sortSign]
    push_cast
    ring
  -- the vertex product is the D-end key sortSign
  rw [show (∏ v : Fin (ds W).length,
      (sortSign ((pairFlagList (F := F) o
          (blockVertex W v)).map
        (fun f => sortKey W f.val)) : ℂ)) =
    (sortSign ((globalPairList W F o).map
      (fun f => sortKey W f.val)) : ℂ) from
    (sortSign_globalPairList W F o).symm]
  rw [hA]
  -- ═══════ ASSEMBLY: THE NUMERIC LEDGER ═══════
  -- close over the numeric ledger
  have hs := card_out_add_card_in_edges W F o
  have hG := κ.neg_one_pow_circuitCount (o := o)
  -- assemble in ℂ
  have hADval : ((Equiv.Perm.sign (listIndexPerm
      (globalSlotList W F) (globalPairList W F o)
      nA nD mAD lAD) : ℤ) : ℂ) =
      ((-1 : ℂ) ^ (Finset.univ.filter
        (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
          p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
          p.2 ∈ edgeIndexSet W F)).card) *
      ((-1 : ℂ) ^ ((edgeIndexSet W F).filter (fun i =>
        o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)) = true)).card) *
      ((Equiv.Perm.sign (κ.outPerm o) : ℤ) : ℂ) := by
    rw [hchain]
    rw [hCM, hMD, mul_one]
    push_cast [hAB, hBC]
    ring
  calc (sortSign ((globalSlotList W F).map
        (fun f => sortKey W f.val)) : ℂ) *
      ((-1 : ℂ) ^ (Finset.univ.filter
        (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
          p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
          p.2 ∈ edgeIndexSet W F)).card *
        (-1 : ℂ) ^ inRepCount W F o) *
      (sortSign ((globalPairList W F o).map
        (fun f => sortKey W f.val)) : ℂ)
      = ((sortSign ((globalSlotList W F).map
          (fun f => sortKey W f.val)) : ℂ) *
        (sortSign ((globalPairList W F o).map
          (fun f => sortKey W f.val)) : ℂ)) *
        ((-1 : ℂ) ^ (Finset.univ.filter
          (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
            p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
            p.2 ∈ edgeIndexSet W F)).card *
          (-1 : ℂ) ^ inRepCount W F o) := by ring
    _ = (((-1 : ℂ) ^ (Finset.univ.filter
          (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
            p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
            p.2 ∈ edgeIndexSet W F)).card) *
        ((-1 : ℂ) ^ ((edgeIndexSet W F).filter (fun i =>
          o.isOut ((starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i)) = true)).card) *
        ((Equiv.Perm.sign (κ.outPerm o) : ℤ) : ℂ)) *
        ((-1 : ℂ) ^ (Finset.univ.filter
          (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
            p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
            p.2 ∈ edgeIndexSet W F)).card *
          (-1 : ℂ) ^ inRepCount W F o) := by
        rw [hpair, hADval]
    _ = ((-1 : ℂ) ^ (((edgeIndexSet W F).filter (fun i =>
          o.isOut ((starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i)) = true)).card +
          inRepCount W F o)) *
        ((Equiv.Perm.sign (κ.outPerm o) : ℤ) : ℂ) := by
        have hxx : ((-1 : ℂ) ^ (Finset.univ.filter
            (fun p : Fin (edgeCount W) ×
                Fin (edgeCount W) =>
              p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
              p.2 ∈ edgeIndexSet W F)).card) *
            ((-1 : ℂ) ^ (Finset.univ.filter
            (fun p : Fin (edgeCount W) ×
                Fin (edgeCount W) =>
              p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
              p.2 ∈ edgeIndexSet W F)).card) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]
          norm_num
        rw [pow_add]
        calc ((-1 : ℂ) ^ (Finset.univ.filter
            (fun p : Fin (edgeCount W) ×
                Fin (edgeCount W) =>
              p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
              p.2 ∈ edgeIndexSet W F)).card *
            (-1 : ℂ) ^ ((edgeIndexSet W F).filter (fun i =>
              o.isOut ((starFlagEnum W).symm
                (Fin.castAdd (edgeCount W) i)) =
                true)).card *
            ((Equiv.Perm.sign (κ.outPerm o) : ℤ) : ℂ)) *
            ((-1 : ℂ) ^ (Finset.univ.filter
              (fun p : Fin (edgeCount W) ×
                  Fin (edgeCount W) =>
                p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
                p.2 ∈ edgeIndexSet W F)).card *
              (-1 : ℂ) ^ inRepCount W F o)
            = (((-1 : ℂ) ^ (Finset.univ.filter
                (fun p : Fin (edgeCount W) ×
                    Fin (edgeCount W) =>
                  p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
                  p.2 ∈ edgeIndexSet W F)).card) *
              ((-1 : ℂ) ^ (Finset.univ.filter
                (fun p : Fin (edgeCount W) ×
                    Fin (edgeCount W) =>
                  p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
                  p.2 ∈ edgeIndexSet W F)).card)) *
              (((-1 : ℂ) ^ ((edgeIndexSet W F).filter
                (fun i => o.isOut ((starFlagEnum W).symm
                  (Fin.castAdd (edgeCount W) i)) =
                  true)).card *
                (-1 : ℂ) ^ inRepCount W F o) *
              ((Equiv.Perm.sign (κ.outPerm o) : ℤ) : ℂ)) := by
              ring
          _ = ((-1 : ℂ) ^ ((edgeIndexSet W F).filter
              (fun i => o.isOut ((starFlagEnum W).symm
                (Fin.castAdd (edgeCount W) i)) =
                true)).card *
              (-1 : ℂ) ^ inRepCount W F o) *
              ((Equiv.Perm.sign (κ.outPerm o) : ℤ) : ℂ) := by
              rw [hxx, one_mul]
          _ = _ := by ring
    _ = (-1 : ℂ) ^ κ.circuitCount := by
        rw [hs, ← hout_card, hG]

-- Raised budget: four sign families — pattern, crossing,
-- representative and per-vertex sorting — are combined in one
-- identity, so all four definitions unfold together.
/-- **The grand parity identity**: the pattern, crossing,
representative and per-vertex sorting signs compose to the
circuit sign. -/
theorem grand_parity (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ)
    (hnd : ∀ v : Fin (ds W).length,
      (F.oddListAt o φ (blockVertex W v)).Nodup) :
    ((-1 : ℂ) ^ patternOddInv W F) *
      ((-1 : ℂ) ^ (Finset.univ.filter
        (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
          p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
          p.2 ∈ edgeIndexSet W F)).card *
        (-1 : ℂ) ^ inRepCount W F o) *
      ∏ v : Fin (ds W).length,
        ((sortSign (oddListOf (blockRestrict (ds W)
            (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
          (sortSign (F.oddListAt o φ
            (blockVertex W v)) : ℂ)) =
    (-1 : ℂ) ^ κ.circuitCount := by
  have hsplit : (∏ v : Fin (ds W).length,
      ((sortSign (oddListOf (blockRestrict (ds W)
          (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
        (sortSign (F.oddListAt o φ
          (blockVertex W v)) : ℂ))) =
    ∏ v : Fin (ds W).length,
      (sortSign ((pairFlagList (F := F) o
          (blockVertex W v)).map
        (fun f => sortKey W f.val)) : ℂ) :=
    Finset.prod_congr rfl (fun v _ =>
      vertex_sign_collapse W F o ψ φ v (hnd v))
  rw [hsplit]
  exact core_parity W F o

end RS
