/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagCode
/-!
# The maximal-flag code-to-simplex bridge

This file completes the explicit bridge left open by `MaximalFlagCode`.

For a code `z = (bottom, removal, top)` and a stage `j`, the retained bars are those whose
removal time is at least `j`.  They determine an ordered block number for every label.  The rank
inside the stage cell is the ordinal rank of the lexicographic key

```
(stage block, final top rank).
```

Thus stage zero has the bottom singleton order, the final stage has the top order, and every
intermediate stage orders its blocks from left to right while using the final top permutation
inside each current block.  This is the finite construction used by the exact regression checker.

The two internal pairings act transparently on this model:

* the bottom partner changes only stage zero, because its transposed labels lie on opposite sides
  of the first bar and that bar has disappeared at every later stage;
* the removal partner changes only the one intermediate stage between the two swapped removal
  times.

Consequently the paired maximal flags have literally equal deleted faces.
-/

namespace NRR

open scoped BigOperators

variable {p : Nat}

namespace FoxNeuwirthOrderComplex
namespace MaximalFlagCode

/-- Bars already removed before stage `j`. -/
def removedBefore (z : Code p) (j : Fin p) : Finset (Fin (p - 1)) :=
  Finset.univ.filter fun r => (z.removal.symm r).1 < j.1

/-- Bars still present at stage `j`. -/
def retainedBars (z : Code p) (j : Fin p) : Finset (Fin (p - 1)) :=
  Finset.univ \ removedBefore z j

@[simp] theorem mem_retainedBars_iff
    (z : Code p) (j : Fin p) (r : Fin (p - 1)) :
    r ∈ retainedBars z j ↔ j.1 ≤ (z.removal.symm r).1 := by
  simp [retainedBars, removedBefore]

/-- Zero-based block number at one stage, computed in the bottom singleton order. -/
def stageBlock (z : Code p) (j : Fin p) (x : Fin p) : Nat :=
  ((retainedBars z j).filter fun r => r.1 < (z.bottom x).1).card

/-- Lexicographic key used to order labels at a stage. -/
def stageKey (z : Code p) (j : Fin p) (x : Fin p) : Nat ×ₗ Nat :=
  toLex (stageBlock z j x, (z.top x).1)

/-- The stage key is injective because its second coordinate is a permutation rank. -/
theorem stageKey_injective (z : Code p) (j : Fin p) :
    Function.Injective (stageKey z j) := by
  intro x y h
  apply z.top.injective
  apply Fin.ext
  exact congrArg (fun k => (ofLex k).2) h

/-- Ordinal rank of a key in a finite linear order. -/
def ordinalRankNat (key : Fin p → Nat ×ₗ Nat) (x : Fin p) : Nat :=
  (Finset.univ.filter fun y => key y < key x).card

/-- An ordinal rank is strictly smaller than the size of the finite type. -/
theorem ordinalRankNat_lt (key : Fin p → Nat ×ₗ Nat) (x : Fin p) :
    ordinalRankNat key x < p := by
  have hssub :
      (Finset.univ.filter fun y : Fin p => key y < key x) ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro hEq
    have hx : x ∈ (Finset.univ.filter fun y : Fin p => key y < key x) := by
      rw [hEq]
      simp
    simpa using hx
  simpa [ordinalRankNat] using Finset.card_lt_card hssub

/-- Fin-valued ordinal rank. -/
def ordinalRankFin (key : Fin p → Nat ×ₗ Nat) (x : Fin p) : Fin p :=
  ⟨ordinalRankNat key x, ordinalRankNat_lt key x⟩

/-- Strictly ordered keys have strictly ordered ordinal ranks. -/
theorem ordinalRankFin_lt_of_lt
    {key : Fin p → Nat ×ₗ Nat} {x y : Fin p}
    (hxy : key x < key y) :
    ordinalRankFin key x < ordinalRankFin key y := by
  have hssub :
      (Finset.univ.filter fun z : Fin p => key z < key x) ⊂
        (Finset.univ.filter fun z : Fin p => key z < key y) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact lt_trans hz hxy
    · intro hEq
      have hxRight : x ∈ (Finset.univ.filter fun z : Fin p => key z < key y) := by
        simp [hxy]
      have hxLeft : x ∉ (Finset.univ.filter fun z : Fin p => key z < key x) := by
        simp
      rw [← hEq] at hxRight
      exact hxLeft hxRight
  exact Finset.card_lt_card hssub

/-- For injective keys, ordinal rank is injective. -/
theorem ordinalRankFin_injective
    {key : Fin p → Nat ×ₗ Nat} (hkey : Function.Injective key) :
    Function.Injective (ordinalRankFin key) := by
  intro x y hxy
  by_contra hne
  have hkeyne : key x ≠ key y := by
    intro h
    exact hne (hkey h)
  rcases lt_or_gt_of_ne hkeyne with hlt | hgt
  · exact (Fin.ne_of_lt (ordinalRankFin_lt_of_lt hlt)) hxy
  · exact (Fin.ne_of_lt (ordinalRankFin_lt_of_lt hgt)) hxy.symm

/-- The ordinal-rank permutation associated with a code stage. -/
noncomputable def stageRank (z : Code p) (j : Fin p) : Equiv.Perm (Fin p) :=
  Equiv.ofBijective (ordinalRankFin (stageKey z j)) (by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨ordinalRankFin_injective (stageKey_injective z j), by simp⟩)

@[simp] theorem stageRank_apply (z : Code p) (j : Fin p) (x : Fin p) :
    (stageRank z j x).1 = ordinalRankNat (stageKey z j) x :=
  rfl

/-- Ordinal rank reflects the lexicographic key order. -/
theorem stageRank_lt_iff
    (z : Code p) (j : Fin p) (x y : Fin p) :
    (stageRank z j x).1 < (stageRank z j y).1 ↔
      stageKey z j x < stageKey z j y := by
  constructor
  · intro hrank
    rcases lt_trichotomy (stageKey z j x) (stageKey z j y) with hxy | hEq | hyx
    · exact hxy
    · have hlabel : x = y := stageKey_injective z j hEq
      subst y
      exact (Nat.lt_irrefl _ hrank).elim
    · have hrev : (stageRank z j y).1 < (stageRank z j x).1 :=
        ordinalRankFin_lt_of_lt hyx
      omega
  · intro h
    exact ordinalRankFin_lt_of_lt h

/-- Prefix of bottom positions ending at a cut. -/
def bottomPrefix (z : Code p) (r : Fin (p - 1)) : Finset (Fin p) :=
  Finset.univ.filter fun x => (z.bottom x).1 ≤ r.1

/-- A bottom prefix has the expected cardinality. -/
theorem card_bottomPrefix (z : Code p) (r : Fin (p - 1)) :
    (bottomPrefix z r).card = r.1 + 1 := by
  classical
  have hbij : (bottomPrefix z r).card
      = (Finset.univ.filter (fun y : Fin p => y.1 ≤ r.1)).card := by
    apply Finset.card_nbij' (i := z.bottom) (j := z.bottom.symm)
    · intro x hx
      simp only [bottomPrefix, Finset.coe_filter, Set.mem_ofPred_eq,
        Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro y hy
      simp only [bottomPrefix, Finset.coe_filter, Set.mem_ofPred_eq,
        Finset.mem_univ, true_and] at hy ⊢
      simpa using hy
    · intro x hx; simp
    · intro y hy; simp
  rw [hbij]
  have hset : (Finset.univ.filter (fun y : Fin p => y.1 ≤ r.1))
       = Finset.Iic (⟨r.1, by omega⟩ : Fin p) := by
    ext y; simp [Finset.mem_Iic, Fin.le_def]
  rw [hset, Fin.card_Iic]

/-- A retained cut separates stage block numbers strictly. -/
theorem stageBlock_lt_of_bottom_le_cut_lt
    (z : Code p) (j : Fin p) (r : Fin (p - 1))
    (hr : r ∈ retainedBars z j) (x y : Fin p)
    (hx : (z.bottom x).1 ≤ r.1) (hy : r.1 < (z.bottom y).1) :
    stageBlock z j x < stageBlock z j y := by
  unfold stageBlock
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, lt_trans hq.2 (lt_of_le_of_lt hx hy)⟩
  · intro hEq
    have hrRight : r ∈ (retainedBars z j).filter
        (fun q => q.1 < (z.bottom y).1) := by
      simp [hr, hy]
    have hrLeft : r ∉ (retainedBars z j).filter
        (fun q => q.1 < (z.bottom x).1) := by
      simp [hr, not_lt_of_ge hx]
    rw [← hEq] at hrRight
    exact hrLeft hrRight

/-- A retained cut occurs before a stage rank exactly when it occurs before the bottom rank. -/
theorem retainedCut_lt_stageRank_iff
    (z : Code p) (j : Fin p) (r : Fin (p - 1))
    (hr : r ∈ retainedBars z j) (x : Fin p) :
    r.1 < (stageRank z j x).1 ↔ r.1 < (z.bottom x).1 := by
  constructor
  · intro hrank
    by_contra hbottom
    have hx : (z.bottom x).1 ≤ r.1 := Nat.le_of_not_gt hbottom
    let lower := Finset.univ.filter fun y : Fin p => stageKey z j y < stageKey z j x
    have hsub : lower ⊂ bottomPrefix z r := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro y hy
        simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simp only [bottomPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hyr
        have hsep := stageBlock_lt_of_bottom_le_cut_lt z j r hr x y hx
          (Nat.lt_of_not_ge hyr)
        have hnot : ¬ stageKey z j y < stageKey z j x := by
          unfold stageKey
          rw [Prod.Lex.toLex_lt_toLex]
          omega
        exact hnot hy
      · intro hEq
        have hxPrefix : x ∈ bottomPrefix z r := by simp [bottomPrefix, hx]
        have hxLower : x ∉ lower := by simp [lower]
        rw [← hEq] at hxPrefix
        exact hxLower hxPrefix
    have hcard := Finset.card_lt_card hsub
    rw [card_bottomPrefix z r] at hcard
    simp only [stageRank_apply, ordinalRankNat] at hrank
    change lower.card < r.1 + 1 at hcard
    change r.1 < lower.card at hrank
    omega
  · intro hbottom
    let lower := Finset.univ.filter fun y : Fin p => stageKey z j y < stageKey z j x
    have hsub : bottomPrefix z r ⊆ lower := by
      intro y hy
      simp only [bottomPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and]
      have hblock := stageBlock_lt_of_bottom_le_cut_lt z j r hr y x hy hbottom
      change stageKey z j y < stageKey z j x
      unfold stageKey
      exact Prod.Lex.left _ _ hblock
    have hcard := Finset.card_le_card hsub
    rw [card_bottomPrefix z r] at hcard
    simp only [stageRank_apply, ordinalRankNat]
    change r.1 + 1 ≤ lower.card at hcard
    change r.1 < lower.card
    omega

/-- The stage cell represented by a maximal-flag code. -/
noncomputable def stageCell (z : Code p) (j : Fin p) : BarredPermutation p where
  rank := stageRank z j
  bars := retainedBars z j

/-- The stage-cell block index is the block number used in its construction. -/
theorem stageCell_blockIndex
    (z : Code p) (j : Fin p) (x : Fin p) :
    (stageCell z j).blockIndex x = stageBlock z j x := by
  classical
  unfold BarredPermutation.blockIndex stageCell stageBlock
  congr 1
  ext r
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hr, hlt⟩
    exact ⟨hr, (retainedCut_lt_stageRank_iff z j r hr x).1 hlt⟩
  · rintro ⟨hr, hlt⟩
    exact ⟨hr, (retainedCut_lt_stageRank_iff z j r hr x).2 hlt⟩

/-- Retained bars decrease with the stage. -/
theorem retainedBars_mono
    (z : Code p) {i j : Fin p} (hij : i ≤ j) :
    retainedBars z j ⊆ retainedBars z i := by
  intro r hr
  rw [mem_retainedBars_iff] at hr ⊢
  exact le_trans hij hr

/-- Stage blocks are monotone in the bottom position. -/
theorem stageBlock_mono
    (z : Code p) (j : Fin p) {x y : Fin p}
    (hxy : (z.bottom x).1 ≤ (z.bottom y).1) :
    stageBlock z j x ≤ stageBlock z j y := by
  unfold stageBlock
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter] at hr ⊢
  exact ⟨hr.1, lt_of_lt_of_le hr.2 hxy⟩

/-- Equality of blocks persists after further bar removals. -/
theorem stageBlock_eq_of_le_of_eq
    (z : Code p) {i j : Fin p} (hij : i ≤ j) {x y : Fin p}
    (hxy : stageBlock z i x = stageBlock z i y) :
    stageBlock z j x = stageBlock z j y := by
  classical
  wlog hpos : (z.bottom x).1 ≤ (z.bottom y).1 generalizing x y
  · exact (this hxy.symm (Nat.le_of_not_ge hpos)).symm
  have hset :
      (retainedBars z i).filter (fun r => r.1 < (z.bottom x).1) =
      (retainedBars z i).filter (fun r => r.1 < (z.bottom y).1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      simp only [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, lt_of_lt_of_le hr.2 hpos⟩
    · simpa [stageBlock] using Nat.le_of_eq hxy.symm
  unfold stageBlock
  congr 1
  ext r
  constructor
  · intro hr
    simp only [Finset.mem_filter] at hr ⊢
    refine ⟨hr.1, ?_⟩
    have hri : r ∈ retainedBars z i := retainedBars_mono z hij hr.1
    have hmem : r ∈ (retainedBars z i).filter
        (fun q => q.1 < (z.bottom x).1) := Finset.mem_filter.mpr ⟨hri, hr.2⟩
    rw [hset] at hmem
    exact (Finset.mem_filter.mp hmem).2
  · intro hr
    simp only [Finset.mem_filter] at hr ⊢
    refine ⟨hr.1, ?_⟩
    have hri : r ∈ retainedBars z i := retainedBars_mono z hij hr.1
    have hmem : r ∈ (retainedBars z i).filter
        (fun q => q.1 < (z.bottom y).1) := Finset.mem_filter.mpr ⟨hri, hr.2⟩
    rw [← hset] at hmem
    exact (Finset.mem_filter.mp hmem).2

/-- Ordered blocks at an earlier stage remain ordered after further removals. -/
theorem stageBlock_order_preserved
    (z : Code p) {i j : Fin p} (hij : i ≤ j) {x y : Fin p}
    (hxy : stageBlock z i x ≤ stageBlock z i y) :
    stageBlock z j x ≤ stageBlock z j y := by
  by_cases hpos : (z.bottom x).1 ≤ (z.bottom y).1
  · exact stageBlock_mono z j hpos
  · have hrev := stageBlock_mono z i (Nat.le_of_not_ge hpos)
    have heq : stageBlock z i x = stageBlock z i y := Nat.le_antisymm hxy hrev
    exact Nat.le_of_eq (stageBlock_eq_of_le_of_eq z hij heq)

/-- A genuinely later stage has strictly fewer retained bars. -/
theorem retainedBars_ssubset
    (z : Code p) {i j : Fin p} (hij : i < j) :
    retainedBars z j ⊂ retainedBars z i := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨retainedBars_mono z (Nat.le_of_lt hij), ?_⟩
  intro hEq
  have hiBound : i.1 < p - 1 := by omega
  let step : Fin (p - 1) := ⟨i.1, hiBound⟩
  let r : Fin (p - 1) := z.removal step
  have hri : r ∈ retainedBars z i := by
    rw [mem_retainedBars_iff]
    simp [r, step]
  have hrj : r ∉ retainedBars z j := by
    rw [mem_retainedBars_iff]
    simp [r, step]
    omega
  rw [hEq] at hrj
  exact hrj hri

/-- Consecutive code stages form a strict Fox--Neuwirth face chain. -/
theorem stageCell_properFace
    (hp : Nat.Prime p) (z : Code p) {i j : Fin p} (hij : i < j) :
    ProperFace (stageCell z i) (stageCell z j) := by
  have hle : i ≤ j := Nat.le_of_lt hij
  have hdim : (stageCell z i).dualDimension < (stageCell z j).dualDimension := by
    rw [BarredPermutation.dualDimension_eq _ hp.pos,
      BarredPermutation.dualDimension_eq _ hp.pos]
    have hcard := Finset.card_lt_card (retainedBars_ssubset z hij)
    have hiCard : (retainedBars z i).card ≤ p - 1 := by
      simpa [stageCell] using BarredPermutation.bars_card_le (stageCell z i)
    have hjCard : (retainedBars z j).card ≤ p - 1 := by
      simpa [stageCell] using BarredPermutation.bars_card_le (stageCell z j)
    simp only [stageCell]
    omega
  refine ⟨?_, hdim⟩
  refine ⟨?_, ?_, Nat.le_of_lt hdim⟩
  · intro x y hxy
    rw [stageCell_blockIndex, stageCell_blockIndex] at hxy ⊢
    exact stageBlock_order_preserved z hle hxy
  · intro x y hsame
    rw [BarredPermutation.SameBlock, stageCell_blockIndex,
      stageCell_blockIndex] at hsame
    have hlater := stageBlock_eq_of_le_of_eq z hle hsame
    simp only [stageCell]
    rw [stageRank_lt_iff, stageRank_lt_iff]
    unfold stageKey
    rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex]
    omega

/-- Cast a maximal-simplex vertex index to the stage index `Fin p`. -/
def stageIndex (hp : Nat.Prime p) (i : Fin (p - 1 + 1)) : Fin p :=
  FoxNeuwirthChain.maximalIndexCast hp i

/-- Explicit strict flag associated with a maximal-flag code. -/
noncomputable def toSimplex (hp : Nat.Prime p) (z : Code p) : Simplex p (p - 1) :=
  ⟨fun i => stageCell z (stageIndex hp i), by
    intro i j hij
    apply stageCell_properFace hp z
    change i.1 < j.1
    exact hij⟩

@[simp] theorem toSimplex_apply
    (hp : Nat.Prime p) (z : Code p) (i : Fin (p - 1 + 1)) :
    toSimplex hp z i = stageCell z (stageIndex hp i) :=
  rfl

/-- A stage cell is determined by its retained bars, block numbers, and final permutation. -/
theorem stageCell_ext
    {z w : Code p} {i j : Fin p}
    (hbars : retainedBars z i = retainedBars w j)
    (hblock : ∀ x, stageBlock z i x = stageBlock w j x)
    (htop : z.top = w.top) :
    stageCell z i = stageCell w j := by
  apply BarredPermutation.ext
  · apply Equiv.ext
    intro x
    apply Fin.ext
    simp [stageCell, stageRank, ordinalRankFin, ordinalRankNat, stageKey,
      hblock, htop]
    rfl
  · exact hbars

/-- The first removed bar is absent from every positive stage. -/
theorem firstCut_not_mem_retained
    (hp : Nat.Prime p) (z : Code p) {j : Fin p} (hj : 0 < j.1) :
    z.removal (firstRemovalStep hp) ∉ retainedBars z j := by
  rw [mem_retainedBars_iff]
  simp [firstRemovalStep]
  omega

/-- Swapping the two labels around the first removed cut preserves all positive-stage blocks. -/
theorem stageBlock_bottomPartner
    (hp : Nat.Prime p) (z : Code p) {j : Fin p} (hj : 0 < j.1) (x : Fin p) :
    stageBlock (bottomPartner hp z) j x = stageBlock z j x := by
  classical
  unfold stageBlock
  congr 1
  ext r
  simp only [Finset.mem_filter]
  have hbars : retainedBars (bottomPartner hp z) j = retainedBars z j := by
    rfl
  rw [hbars]
  have hcast : ((ePp hp) (z.removal (firstRemovalStep hp)).castSucc).1
      = (z.removal (firstRemovalStep hp)).1 := rfl
  have hsucc : ((ePp hp) (z.removal (firstRemovalStep hp)).succ).1
      = (z.removal (firstRemovalStep hp)).1 + 1 := rfl
  constructor <;> rintro ⟨hr, hlt⟩ <;> refine ⟨hr, ?_⟩
  · by_cases hxL : x = firstCutLeftLabel hp z
    · subst x
      have hrne : r.1 ≠ (z.removal (firstRemovalStep hp)).1 := fun h =>
        firstCut_not_mem_retained hp z hj (Fin.ext h ▸ hr)
      simp [bottomPartner, firstCutLeftLabel, firstCutRightLabel] at hlt ⊢
      omega
    · by_cases hxR : x = firstCutRightLabel hp z
      · subst x
        simp [bottomPartner, firstCutLeftLabel, firstCutRightLabel] at hlt ⊢
        omega
      · simpa [bottomPartner, Equiv.swap_apply_of_ne_of_ne hxL hxR] using hlt
  · by_cases hxL : x = firstCutLeftLabel hp z
    · subst x
      simp [bottomPartner, firstCutLeftLabel, firstCutRightLabel] at hlt ⊢
      omega
    · by_cases hxR : x = firstCutRightLabel hp z
      · subst x
        have hrne : r.1 ≠ (z.removal (firstRemovalStep hp)).1 := fun h =>
          firstCut_not_mem_retained hp z hj (Fin.ext h ▸ hr)
        simp [bottomPartner, firstCutLeftLabel, firstCutRightLabel] at hlt ⊢
        omega
      · simpa [bottomPartner, Equiv.swap_apply_of_ne_of_ne hxL hxR] using hlt

/-- The bottom partner gives the same cell at every positive stage. -/
theorem stageCell_bottomPartner
    (hp : Nat.Prime p) (z : Code p) {j : Fin p} (hj : 0 < j.1) :
    stageCell (bottomPartner hp z) j = stageCell z j := by
  apply stageCell_ext
  · rfl
  · exact stageBlock_bottomPartner hp z hj
  · rfl

/-- Swapping adjacent removal times preserves every prefix except the intermediate one. -/
theorem retainedBars_removalPartner
    (hp : Nat.Prime p) (i : Fin (p - 2)) (z : Code p) (j : Fin p)
    (hj : j.1 ≠ i.1 + 1) :
    retainedBars (removalPartner hp i z) j = retainedBars z j := by
  classical
  ext r
  simp only [mem_retainedBars_iff]
  change j.1 ≤ (((Equiv.swap (eQ hp i.castSucc) (eQ hp i.succ)).trans z.removal).symm r).1 ↔
    j.1 ≤ (z.removal.symm r).1
  simp only [Equiv.symm_trans_apply, Equiv.symm_swap]
  have hL : (eQ hp i.castSucc).1 = i.1 := by simp [eQ]
  have hR : (eQ hp i.succ).1 = i.1 + 1 := by simp [eQ]
  set q := z.removal.symm r with hqdef
  by_cases hq0 : q = eQ hp i.castSucc
  · rw [hq0, Equiv.swap_apply_left]; omega
  · by_cases hq1 : q = eQ hp i.succ
    · rw [hq1, Equiv.swap_apply_right]; omega
    · rw [Equiv.swap_apply_of_ne_of_ne hq0 hq1]

/-- The removal partner gives the same cell away from its one changed intermediate stage. -/
theorem stageCell_removalPartner
    (hp : Nat.Prime p) (i : Fin (p - 2)) (z : Code p) (j : Fin p)
    (hj : j.1 ≠ i.1 + 1) :
    stageCell (removalPartner hp i z) j = stageCell z j := by
  have hbars := retainedBars_removalPartner hp i z j hj
  apply stageCell_ext hbars
  · intro x
    unfold stageBlock
    rw [hbars]
    rfl
  · rfl

/- Face-compatibility bridge proofs certifying the `BottomFaceCompatibility` /
`RemovalFaceCompatibility` predicates, consumed by `MaximalFlagSourceCancellation`. -/

theorem bottomFaceCompatibility (hp : Nat.Prime p) :
    BottomFaceCompatibility hp (toSimplex hp) := by
  intro z
  apply Simplex.ext
  intro i
  simp only [Simplex.restrict_apply, toSimplex_apply]
  apply stageCell_bottomPartner hp z
  set k : Fin (p - 1 + 1) :=
    Fin.cast (by have := hp.two_le; omega) (bottomDeletionIndex hp) with hkdef
  have h0 : k.1 = 0 := rfl
  have hne :
      k.succAbove (Fin.cast (show p - 2 + 1 = p - 1 by have := hp.two_le; omega) i) ≠ k :=
    Fin.succAbove_ne _ _
  refine Nat.pos_of_ne_zero (fun hcontra => ?_)
  apply hne
  apply Fin.ext
  rw [h0]
  exact hcontra

theorem removalFaceCompatibility (hp : Nat.Prime p) :
    RemovalFaceCompatibility hp (toSimplex hp) := by
  intro i z
  apply Simplex.ext
  intro q
  simp only [Simplex.restrict_apply, toSimplex_apply]
  apply stageCell_removalPartner hp i z
  set k : Fin (p - 1 + 1) :=
    Fin.cast (by have := hp.two_le; omega) i.succ.castSucc with hkdef
  have hk1 : k.1 = i.1 + 1 := rfl
  have hne :
      k.succAbove (Fin.cast (show p - 2 + 1 = p - 1 by have := hp.two_le; omega) q) ≠ k :=
    Fin.succAbove_ne _ _
  intro hcontra
  apply hne
  apply Fin.ext
  rw [hk1]
  exact hcontra

end MaximalFlagCode
end FoxNeuwirthOrderComplex

namespace AAK

/- Unused: the maximal-flag code-to-simplex compatibility bridge packaging (see note above).

theorem simplestRoute_maximalFlagBridge_complete :
    ∀ {p : Nat} (hp : Nat.Prime p),
      FoxNeuwirthOrderComplex.MaximalFlagCode.BottomFaceCompatibility hp
        (FoxNeuwirthOrderComplex.MaximalFlagCode.toSimplex hp) ∧
      FoxNeuwirthOrderComplex.MaximalFlagCode.RemovalFaceCompatibility hp
        (FoxNeuwirthOrderComplex.MaximalFlagCode.toSimplex hp) := by
  intro p hp
  exact ⟨
    FoxNeuwirthOrderComplex.MaximalFlagCode.bottomFaceCompatibility hp,
    FoxNeuwirthOrderComplex.MaximalFlagCode.removalFaceCompatibility hp⟩
-/

end AAK

end NRR
