/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagEncodingStepOne

/-!
# Classification of maximal Fox--Neuwirth flags

This file proves the surjectivity theorem for maximal-flag codes.  The central observation is that
if `a.IsFace b`, then every prefix cut defined by a bar of `b` contains exactly the same labels in
`a` and `b`.  Hence `b.bars ⊆ a.bars`.  Along a maximal strict flag the dual dimension at vertex
`i` is exactly `i`, so consecutive bar sets differ by one element.  Those unique removed bars form
a permutation of `Fin (p - 1)`.

The first and last ranks, together with this removal permutation, reconstruct every intermediate
cell: the bottom rank fixes the block order and the final rank fixes the order inside each block.
This yields the explicit inverse `simplexToCode` and proves that `toSimplex` is bijective.
-/

@[expose] public section

namespace NRR

variable {p : Nat}

namespace BarredPermutation

/-- Rank-prefix labels through position `r`. -/
def rankPrefix (c : BarredPermutation p) (r : Fin (p - 1)) : Finset (Fin p) :=
  Finset.univ.filter fun x => (c.rank x).1 ≤ r.1

theorem mem_rankPrefix {c : BarredPermutation p} {r : Fin (p - 1)} {x : Fin p} :
    x ∈ rankPrefix c r ↔ (c.rank x).1 ≤ r.1 := by
  simp only [rankPrefix, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The displayed position immediately to the left of a bar.

Using an explicit constructor avoids relying on the non-definitional arithmetic identity
`p - 1 + 1 = p`. -/
def barLeft (r : Fin (p - 1)) : Fin p :=
  ⟨r.1, by have := r.2; omega⟩

/-- The displayed position immediately to the right of a bar. -/
def barRight (r : Fin (p - 1)) : Fin p :=
  ⟨r.1 + 1, by have := r.2; omega⟩

@[simp] theorem barLeft_val (r : Fin (p - 1)) : (barLeft r).1 = r.1 := rfl
@[simp] theorem barRight_val (r : Fin (p - 1)) : (barRight r).1 = r.1 + 1 := rfl

/-- Every rank prefix has its evident size. -/
theorem card_rankPrefix (c : BarredPermutation p) (r : Fin (p - 1)) :
    (rankPrefix c r).card = r.1 + 1 := by
  classical
  let e : {x : Fin p // x ∈ rankPrefix c r} ≃ Fin (r.1 + 1) :=
    { toFun := fun x => ⟨(c.rank x.1).1, by
        have hx : (c.rank x.1).1 ≤ r.1 := mem_rankPrefix.mp x.2
        omega⟩
      invFun := fun q =>
        ⟨c.rank.symm ⟨q.1, by have := r.2; have := q.2; omega⟩, by
          simp only [mem_rankPrefix, Equiv.apply_symm_apply]
          omega⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun q => by
        apply Fin.ext
        simp }
  simpa using Fintype.card_congr e

/-- Block indices are monotone in the displayed rank. -/
theorem blockIndex_mono_rank
    (c : BarredPermutation p) {x y : Fin p}
    (hxy : (c.rank x).1 ≤ (c.rank y).1) :
    c.blockIndex x ≤ c.blockIndex y := by
  unfold blockIndex
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter] at hr ⊢
  exact ⟨hr.1, lt_of_lt_of_le hr.2 hxy⟩

/-- A bar separates every label on its left from every label on its right. -/
theorem blockIndex_lt_of_rank_le_bar_lt
    (c : BarredPermutation p) (r : Fin (p - 1)) (hr : r ∈ c.bars)
    {x y : Fin p} (hx : (c.rank x).1 ≤ r.1)
    (hy : r.1 < (c.rank y).1) :
    c.blockIndex x < c.blockIndex y := by
  unfold blockIndex
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, by omega⟩
  · intro hEq
    have hrRight : r ∈ c.bars.filter (fun q => q.1 < (c.rank y).1) := by
      simp [hr, hy]
    have hrLeft : r ∉ c.bars.filter (fun q => q.1 < (c.rank x).1) := by
      simp [hr, not_lt_of_ge hx]
    rw [hEq] at hrLeft
    exact hrLeft hrRight

/-- A bar is characterized by a strict block jump between its two adjacent displayed positions. -/
theorem mem_bars_iff_adjacent_blockIndex_lt
    (c : BarredPermutation p) (r : Fin (p - 1)) :
    r ∈ c.bars ↔
      c.blockIndex (c.rank.symm (barLeft r)) <
        c.blockIndex (c.rank.symm (barRight r)) := by
  constructor
  · intro hr
    apply blockIndex_lt_of_rank_le_bar_lt c r hr
    · simp
    · simp
  · intro hlt
    by_contra hr
    unfold blockIndex at hlt
    have heq :
        c.bars.filter (fun q => q.1 < (c.rank (c.rank.symm (barLeft r))).1) =
        c.bars.filter (fun q => q.1 < (c.rank (c.rank.symm (barRight r))).1) := by
      ext q
      by_cases hqr : q = r
      · subst q
        simp [hr]
      · simp
        omega
    simp only [Equiv.apply_symm_apply] at heq hlt
    rw [heq] at hlt
    exact (Nat.lt_irrefl _ hlt)

/-- Across a bar of a coarser face, all prefix labels precede all complementary labels in every
refinement. -/
theorem rank_lt_of_mem_prefix_of_not_mem_prefix
    {a b : BarredPermutation p} (hface : a.IsFace b)
    (r : Fin (p - 1)) (hr : r ∈ b.bars)
    {x y : Fin p} (hx : x ∈ rankPrefix b r)
    (hy : y ∉ rankPrefix b r) :
    (a.rank x).1 < (a.rank y).1 := by
  have hxb : (b.rank x).1 ≤ r.1 := by simpa [rankPrefix] using hx
  have hyb : r.1 < (b.rank y).1 := by
    simpa [rankPrefix] using hy
  have hblock : b.blockIndex x < b.blockIndex y :=
    blockIndex_lt_of_rank_le_bar_lt b r hr hxb hyb
  by_contra hxy
  have hyx : (a.rank y).1 < (a.rank x).1 := by
    have hne : x ≠ y := by
      intro h
      subst y
      exact hy hx
    have hrankne : a.rank x ≠ a.rank y := fun h => hne (a.rank.injective h)
    omega
  have hale : a.blockIndex y ≤ a.blockIndex x :=
    blockIndex_mono_rank a (Nat.le_of_lt hyx)
  have hble : b.blockIndex y ≤ b.blockIndex x := hface.1 y x hale
  omega

/-- A face relation preserves the label set lying in every bar-defined rank prefix of the coarser
cell. -/
theorem rankPrefix_eq_of_isFace
    {a b : BarredPermutation p} (hface : a.IsFace b)
    (r : Fin (p - 1)) (hr : r ∈ b.bars) :
    rankPrefix a r = rankPrefix b r := by
  classical
  let A := rankPrefix a r
  let B := rankPrefix b r
  have hcard : A.card = B.card := by
    simp [A, B, card_rankPrefix]
  apply Finset.eq_of_subset_of_card_le
  · intro x hxA
    by_contra hxB
    have hnotBA : ¬ B ⊆ A := by
      intro hBA
      have hEq : B = A := Finset.eq_of_subset_of_card_le hBA (by omega)
      exact hxB (by simpa [A, B, hEq] using hxA)
    obtain ⟨y, hyB, hyA⟩ := Finset.not_subset.mp hnotBA
    have hyx := rank_lt_of_mem_prefix_of_not_mem_prefix hface r hr hyB hxB
    have hxrank : (a.rank x).1 ≤ r.1 := mem_rankPrefix.mp hxA
    have hyrank : r.1 < (a.rank y).1 := by
      by_contra hcon
      exact hyA (mem_rankPrefix.mpr (by omega))
    omega
  · simp [card_rankPrefix]

/-- Bars can only disappear when passing to a coarser face. -/
theorem bars_subset_of_isFace
    {a b : BarredPermutation p} (hface : a.IsFace b) :
    b.bars ⊆ a.bars := by
  intro r hr
  let x : Fin p := a.rank.symm (barLeft r)
  let y : Fin p := a.rank.symm (barRight r)
  have hprefix := rankPrefix_eq_of_isFace hface r hr
  have hxB : x ∈ rankPrefix b r := by
    rw [← hprefix]
    simp [rankPrefix, x]
  have hyB : y ∉ rankPrefix b r := by
    rw [← hprefix]
    simp [rankPrefix, y]
  have hxb : (b.rank x).1 ≤ r.1 := by simpa [rankPrefix] using hxB
  have hyb : r.1 < (b.rank y).1 := by simpa [rankPrefix] using hyB
  have hbxy : b.blockIndex x < b.blockIndex y :=
    blockIndex_lt_of_rank_le_bar_lt b r hr hxb hyb
  have haxy_le : a.blockIndex x ≤ a.blockIndex y := by
    apply blockIndex_mono_rank
    simp [x, y]
  have haxy_ne : a.blockIndex x ≠ a.blockIndex y := by
    intro heq
    have h1 := hface.1 x y (Nat.le_of_eq heq)
    have h2 := hface.1 y x (Nat.le_of_eq heq.symm)
    omega
  apply (mem_bars_iff_adjacent_blockIndex_lt a r).2
  simpa [x, y] using lt_of_le_of_ne haxy_le haxy_ne

/-- Along a face, the coarser block index counts the bars lying before the finer cell's rank.

The first-stage vertex is the intended finer cell, but only the face relation is needed. -/
theorem blockIndex_eq_barCount_before_vertexRank
    {a b : BarredPermutation p} (hface : a.IsFace b)
    (x : Fin p) :
    b.blockIndex x =
      (b.bars.filter fun r => r.1 < (a.rank x).1).card := by
  unfold blockIndex
  congr 1
  ext r
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hr, hlt⟩
    refine ⟨hr, ?_⟩
    have hprefix := rankPrefix_eq_of_isFace hface r hr
    by_contra hnot
    have hxa : x ∈ rankPrefix a r := mem_rankPrefix.mpr (by omega)
    have hxb : x ∈ rankPrefix b r := by rw [← hprefix]; exact hxa
    have hle := mem_rankPrefix.mp hxb
    omega
  · rintro ⟨hr, hlt⟩
    refine ⟨hr, ?_⟩
    have hprefix := rankPrefix_eq_of_isFace hface r hr
    by_contra hnot
    have hxb : x ∈ rankPrefix b r := mem_rankPrefix.mpr (by omega)
    have hxa : x ∈ rankPrefix a r := by rw [hprefix]; exact hxb
    have hle := mem_rankPrefix.mp hxa
    omega

end BarredPermutation

namespace FoxNeuwirthOrderComplex

namespace Simplex

/-- Dual dimension as an order isomorphism along a maximal strict flag. -/
noncomputable def maximalDimensionOrderIso
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) : Fin p ≃o Fin p := by
  classical
  have hbound : ∀ i : Fin p,
      (s (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm i)).dualDimension < p := by
    intro i
    have hle := TopFlagSubdivision.dualDimension_le_top hp.pos
      (s (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm i))
    have := hp.pos; omega
  set f : Fin p → Fin p := fun i =>
    ⟨(s (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm i)).dualDimension, hbound i⟩
    with hf
  have hmono : StrictMono f := by
    intro i j hlt
    have hpf := s.properFace
      (show (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm i)
          < (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm j) by
        rw [Fin.lt_def]; simpa using hlt)
    exact Fin.lt_def.mpr hpf.2
  exact
    { toEquiv := Equiv.ofBijective f (by
        rw [Fintype.bijective_iff_injective_and_card]
        exact ⟨hmono.injective, rfl⟩)
      map_rel_iff' := hmono.le_iff_le }

/-- The dual dimension of vertex `i` in a maximal strict flag is exactly `i`. -/
theorem maximal_dualDimension
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) (i : Fin p) :
    (s (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm i)).dualDimension = i.1 := by
  have h := Fin.coe_orderIso_apply (maximalDimensionOrderIso hp s) i
  exact h

/-- Bar cardinality at a maximal-flag stage. -/
theorem maximal_bars_card
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) (i : Fin p) :
    (s (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm i)).bars.card =
      p - 1 - i.1 := by
  have hdim := maximal_dualDimension hp s i
  rw [BarredPermutation.dualDimension_eq _ hp.pos] at hdim
  have hle := BarredPermutation.bars_card_le
    (s (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm i))
  omega

/-- The initial vertex of a maximal strict flag is all-singleton. -/
theorem maximal_zero_isVertex
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    (s (MaximalFlagCode.simplexIndex hp (MaximalFlagCode.firstStage hp))).IsVertex := by
  have h := maximal_bars_card hp s (MaximalFlagCode.firstStage hp)
  have hfs : (MaximalFlagCode.firstStage hp).1 = 0 := rfl
  unfold BarredPermutation.IsVertex
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  have hcard : (Finset.univ : Finset (Fin (p - 1))).card = p - 1 := by simp
  rw [hcard]
  simp only [MaximalFlagCode.simplexIndex]
  omega

/-- The final vertex of a maximal strict flag is top-dimensional. -/
theorem maximal_last_isTop
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    (s (MaximalFlagCode.simplexIndex hp (MaximalFlagCode.lastStage hp))).IsTop := by
  exact TopFlagSubdivision.isTop_of_dualDimension_eq_top hp.pos _
    (by simpa [MaximalFlagCode.simplexIndex, MaximalFlagCode.lastStage] using
      maximal_dualDimension hp s (MaximalFlagCode.lastStage hp))

end Simplex

namespace MaximalFlagCode

/-- The bar difference between two consecutive maximal-flag stages is a singleton. -/
theorem consecutive_sdiff_card
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) (q : Fin (p - 1)) :
    ((s (simplexIndex hp (stageIndex hp q.castSucc))).bars \
        (s (simplexIndex hp (stageIndex hp q.succ))).bars).card = 1 := by
  have hstep :
      simplexIndex hp (stageIndex hp q.castSucc) <
        simplexIndex hp (stageIndex hp q.succ) := by
    apply Fin.lt_def.mpr
    change q.1 < q.1 + 1
    omega
  have hsub : (s (simplexIndex hp (stageIndex hp q.succ))).bars ⊆
      (s (simplexIndex hp (stageIndex hp q.castSucc))).bars :=
    BarredPermutation.bars_subset_of_isFace (s.properFace hstep).1
  rw [Finset.card_sdiff_of_subset hsub]
  have ha := Simplex.maximal_bars_card hp s (stageIndex hp q.castSucc)
  have hb := Simplex.maximal_bars_card hp s (stageIndex hp q.succ)
  have hqc : (stageIndex hp q.castSucc).1 = q.1 := rfl
  have hqs : (stageIndex hp q.succ).1 = q.1 + 1 := rfl
  have hq2 : q.1 < p - 1 := q.2
  simp only [simplexIndex] at ha hb ⊢
  rw [ha, hb, hqc, hqs]
  omega

/-- The unique bar removed between two consecutive stages of a maximal strict flag. -/
noncomputable def removedBarAt
    (hp : Nat.Prime p) (s : Simplex p (p - 1))
    (q : Fin (p - 1)) : Fin (p - 1) :=
  Classical.choose (Finset.card_eq_one.mp (consecutive_sdiff_card hp s q))

/-- The defining singleton difference for `removedBarAt`. -/
theorem removedBarAt_spec
    (hp : Nat.Prime p) (s : Simplex p (p - 1))
    (q : Fin (p - 1)) :
    (s (simplexIndex hp (stageIndex hp q.castSucc))).bars \
        (s (simplexIndex hp (stageIndex hp q.succ))).bars = {removedBarAt hp s q} := by
  exact Classical.choose_spec
    (Finset.card_eq_one.mp (consecutive_sdiff_card hp s q))

/-- Bar sets are nested along any two stages of a maximal flag. -/
theorem maximal_bars_mono
    (hp : Nat.Prime p) (s : Simplex p (p - 1))
    {i j : Fin p} (hij : i ≤ j) :
    (s (simplexIndex hp j)).bars ⊆ (s (simplexIndex hp i)).bars := by
  by_cases hEq : i = j
  · subst j
    exact Finset.Subset.rfl
  · have hij' : i < j := lt_of_le_of_ne hij hEq
    exact BarredPermutation.bars_subset_of_isFace
      (s.properFace (by
        apply Fin.lt_def.mpr
        change i.1 < j.1
        exact Fin.lt_def.mp hij')).1

/-- Distinct removal steps remove distinct bars. -/
theorem removedBarAt_injective
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    Function.Injective (removedBarAt hp s) := by
  intro i j hij
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this hij.symm (fun h => hne h.symm)
      (lt_of_le_of_ne (not_lt.mp hlt) (fun h => hne h.symm))
  have hiMem : removedBarAt hp s i ∈
      (s (simplexIndex hp (stageIndex hp i.castSucc))).bars := by
    have h : removedBarAt hp s i ∈
        (s (simplexIndex hp (stageIndex hp i.castSucc))).bars \
          (s (simplexIndex hp (stageIndex hp i.succ))).bars := by
      rw [removedBarAt_spec hp s i]; simp
    exact (Finset.mem_sdiff.mp h).1
  have hiNot : removedBarAt hp s i ∉
      (s (simplexIndex hp (stageIndex hp i.succ))).bars := by
    have h : removedBarAt hp s i ∈
        (s (simplexIndex hp (stageIndex hp i.castSucc))).bars \
          (s (simplexIndex hp (stageIndex hp i.succ))).bars := by
      rw [removedBarAt_spec hp s i]; simp
    exact (Finset.mem_sdiff.mp h).2
  have hjMem : removedBarAt hp s j ∈
      (s (simplexIndex hp (stageIndex hp j.castSucc))).bars := by
    have h : removedBarAt hp s j ∈
        (s (simplexIndex hp (stageIndex hp j.castSucc))).bars \
          (s (simplexIndex hp (stageIndex hp j.succ))).bars := by
      rw [removedBarAt_spec hp s j]; simp
    exact (Finset.mem_sdiff.mp h).1
  rw [← hij] at hjMem
  have hsub := maximal_bars_mono hp s
    (show stageIndex hp i.succ ≤ stageIndex hp j.castSucc by
      change i.1 + 1 ≤ j.1
      omega)
  exact hiNot (hsub hjMem)

/-- Canonical removal permutation recovered from a maximal strict flag. -/
noncomputable def decodedRemoval
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    Equiv.Perm (Fin (p - 1)) :=
  Equiv.ofBijective (removedBarAt hp s) (by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨removedBarAt_injective hp s, by simp⟩)

@[simp] theorem decodedRemoval_apply
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) (q : Fin (p - 1)) :
    decodedRemoval hp s q = removedBarAt hp s q :=
  rfl

/-- Canonical code extracted from an arbitrary maximal strict flag. -/
noncomputable def simplexToCode
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) : Code p where
  bottom := (s (simplexIndex hp (firstStage hp))).rank
  removal := decodedRemoval hp s
  top := (s (simplexIndex hp (lastStage hp))).rank

/-- Cardinality of the removed-before set for any removal permutation. -/
theorem card_removedBefore
    (z : Code p) (j : Fin p) :
    (removedBefore z j).card = j.1 := by
  classical
  let e : {r : Fin (p - 1) // r ∈ removedBefore z j} ≃ Fin j.1 :=
    { toFun := fun r => ⟨(z.removal.symm r.1).1, by
        have h := r.2
        simp only [removedBefore, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h⟩
      invFun := fun q => ⟨z.removal ⟨q.1, lt_of_lt_of_le q.2 (by omega)⟩, by
        simp only [removedBefore, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.symm_apply_apply]
        exact q.2⟩
      left_inv := fun r => by ext; simp
      right_inv := fun q => by ext; simp }
  simpa using Fintype.card_congr e

/-- Cardinality of the retained-bar set at one coded stage. -/
theorem card_retainedBars
    (z : Code p) (j : Fin p) :
    (retainedBars z j).card = p - 1 - j.1 := by
  rw [retainedBars, Finset.card_sdiff_of_subset (Finset.subset_univ _), card_removedBefore]
  simp

/-- The recovered removal schedule has exactly the original stage bar sets. -/
theorem retainedBars_simplexToCode
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) (j : Fin p) :
    retainedBars (simplexToCode hp s) j =
      (s (simplexIndex hp j)).bars := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    rw [mem_retainedBars_iff] at hr
    let q := (decodedRemoval hp s).symm r
    have hqrem : removedBarAt hp s q = r := by
      rw [← decodedRemoval_apply hp s q]
      exact (decodedRemoval hp s).apply_symm_apply r
    have hqmem : r ∈ (s (simplexIndex hp (stageIndex hp q.castSucc))).bars := by
      rw [← hqrem]
      exact (Finset.mem_sdiff.mp (by
        rw [removedBarAt_spec hp s q]
        simp)).1
    have hsub :
        (s (simplexIndex hp (stageIndex hp q.castSucc))).bars ⊆
          (s (simplexIndex hp j)).bars :=
      maximal_bars_mono hp s (by
        change j.1 ≤ q.1
        simpa [q, simplexToCode] using hr)
    exact hsub hqmem
  · rw [card_retainedBars]
    have h := Simplex.maximal_bars_card hp s j
    simp only [simplexIndex]
    omega

/-- The stage block number reconstructed from the bottom vertex equals the original block index. -/
theorem stageBlock_simplexToCode
    (hp : Nat.Prime p) (s : Simplex p (p - 1))
    (j : Fin p) (x : Fin p) :
    stageBlock (simplexToCode hp s) j x =
      (s (simplexIndex hp j)).blockIndex x := by
  have hbars := retainedBars_simplexToCode hp s j
  have hface :
      (s (simplexIndex hp (firstStage hp))).IsFace (s (simplexIndex hp j)) := by
    by_cases hj0 : j = firstStage hp
    · subst j
      exact BarredPermutation.isFace_refl _
    · exact (s.properFace (by
        apply Fin.lt_def.mpr
        have hjval : j.1 ≠ 0 := by
          intro hzero
          apply hj0
          apply Fin.ext
          simpa [firstStage] using hzero
        change 0 < j.1
        omega)).1
  unfold stageBlock
  rw [hbars]
  simp only [simplexToCode]
  exact (BarredPermutation.blockIndex_eq_barCount_before_vertexRank
      hface x).symm

/-- A cell rank is lexicographically determined by its block index and the final top rank. -/
theorem rank_lt_iff_blockIndex_topRank
    (hp : Nat.Prime p) (s : Simplex p (p - 1))
    (j : Fin p) (x y : Fin p) :
    ((s (simplexIndex hp j)).rank x).1 <
        ((s (simplexIndex hp j)).rank y).1 ↔
      (toLex ((s (simplexIndex hp j)).blockIndex x,
          ((s (simplexIndex hp (lastStage hp))).rank x).1) : Nat ×ₗ Nat) <
        toLex ((s (simplexIndex hp j)).blockIndex y,
          ((s (simplexIndex hp (lastStage hp))).rank y).1) := by
  let c := s (simplexIndex hp j)
  let t := s (simplexIndex hp (lastStage hp))
  have hct : c.IsFace t := by
    by_cases hj : j = lastStage hp
    · subst j
      exact BarredPermutation.isFace_refl _
    · exact (s.properFace (by
        apply Fin.lt_def.mpr
        have hjval : j.1 ≠ p - 1 := by
          intro hlast
          apply hj
          apply Fin.ext
          simpa [lastStage] using hlast
        change j.1 < p - 1
        have := j.2
        omega)).1
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · intro hxy
    have hle := BarredPermutation.blockIndex_mono_rank c (Nat.le_of_lt hxy)
    by_cases heq : c.blockIndex x = c.blockIndex y
    · have hsame : c.SameBlock x y := heq
      have htop := (hct.2.1 x y hsame).1 hxy
      exact Or.inr ⟨heq, htop⟩
    · exact Or.inl (lt_of_le_of_ne hle heq)
  · intro hkey
    rcases hkey with hblock | ⟨hblock, htop⟩
    · by_contra hnot
      have hyx : (s (simplexIndex hp j)).blockIndex y ≤ (s (simplexIndex hp j)).blockIndex x :=
        BarredPermutation.blockIndex_mono_rank c (Nat.le_of_not_lt hnot)
      omega
    · have hsame : c.SameBlock x y := hblock
      exact (hct.2.1 x y hsame).2 htop

/-- Every reconstructed stage cell is the original simplex vertex. -/
theorem stageCell_simplexToCode
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) (j : Fin p) :
    stageCell (simplexToCode hp s) j = s (simplexIndex hp j) := by
  apply BarredPermutation.ext
  · apply perm_eq_of_lt_iff
    intro x y
    simp only [Fin.lt_def, stageCell]
    rw [stageRank_lt_iff]
    simp only [stageKey, stageBlock_simplexToCode]
    simp only [simplexToCode]
    exact (rank_lt_iff_blockIndex_topRank hp s j x y).symm
  · exact retainedBars_simplexToCode hp s j

/-- The canonical inverse reconstructs every maximal strict flag. -/
@[simp] theorem toSimplex_simplexToCode
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    toSimplex hp (simplexToCode hp s) = s := by
  apply Simplex.ext
  intro i
  rw [toSimplex_apply, stageCell_simplexToCode hp s (stageIndex hp i)]
  rfl

/-- The canonical inverse also recovers every explicit code. -/
@[simp] theorem simplexToCode_toSimplex
    (hp : Nat.Prime p) (z : Code p) :
    simplexToCode hp (toSimplex hp z) = z := by
  apply toSimplex_injective hp
  exact toSimplex_simplexToCode hp _

/-- Every maximal strict flag is encoded by the explicit stage construction. -/
theorem everyMaximalFlagEncoded (hp : Nat.Prime p) :
    EveryMaximalFlagEncoded hp := by
  intro s
  exact ⟨simplexToCode hp s, toSimplex_simplexToCode hp s⟩

/-- The explicit code map is bijective onto all maximal strict flags. -/
theorem toSimplex_bijective (hp : Nat.Prime p) :
    Function.Bijective (toSimplex hp : Code p → Simplex p (p - 1)) :=
  ⟨toSimplex_injective hp, everyMaximalFlagEncoded hp⟩

/-- Unconditional equivalence between maximal-flag codes and all maximal strict flags. -/
noncomputable def maximalFlagEquiv
    (hp : Nat.Prime p) : Code p ≃ Simplex p (p - 1) where
  toFun := toSimplex hp
  invFun := simplexToCode hp
  left_inv := simplexToCode_toSimplex hp
  right_inv := toSimplex_simplexToCode hp

end MaximalFlagCode
end FoxNeuwirthOrderComplex

namespace AAK

/-- Step 1 of the simplest route: maximal flags are unconditionally classified by explicit codes. -/
theorem simplestRoute_maximalFlagEncoding_complete :
    ∀ {p : Nat} (hp : Nat.Prime p),
      FoxNeuwirthOrderComplex.MaximalFlagCode.EveryMaximalFlagEncoded hp :=
  fun hp => FoxNeuwirthOrderComplex.MaximalFlagCode.everyMaximalFlagEncoded hp

end AAK

end NRR
