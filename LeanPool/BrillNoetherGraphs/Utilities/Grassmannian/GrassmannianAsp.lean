/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.OnceMarked
public import LeanPool.BrillNoetherGraphs.Demazure.InvSet

/-!
# Grassmannian ASP permutations from Young diagrams

This file begins the permutation-side half of the once-marked/transmission
dictionary.  A Young diagram `lambda` determines the finite Ferrers inversion
set

`{(m,n) : n >= 0, -lambda_n <= m < 0}`.

We prove directly that this is an `AspSet`, then use the reconstruction theorem
from `Demazure.InvSet` with shift zero.  Consequently the advertised inversion
set and shift are kernel-checked facts, not fields supplied by a generator.

The exact slipface/corner-envelope theorem is completed in
`GrassmannianEnvelope`, using the concrete row and column formulas established
below.
-/

@[expose] public section

namespace Utilities

/-- The length of the integer-indexed row of a Young diagram, extended by zero
on negative indices. -/
def grassmannianRowLen (lambda : YoungDiagram) (n : ℤ) : ℕ :=
  if 0 ≤ n then lambda.rowLen n.toNat else 0

@[simp] theorem grassmannianRowLen_of_nonneg
    (lambda : YoungDiagram) {n : ℤ} (hn : 0 ≤ n) :
    grassmannianRowLen lambda n = lambda.rowLen n.toNat := by
  simp [grassmannianRowLen, hn]

@[simp] theorem grassmannianRowLen_of_neg
    (lambda : YoungDiagram) {n : ℤ} (hn : n < 0) :
    grassmannianRowLen lambda n = 0 := by
  simp [grassmannianRowLen, not_le.mpr hn]

/-- Integer-indexed row lengths are weakly decreasing on nonnegative indices. -/
theorem grassmannianRowLen_anti (lambda : YoungDiagram)
    {m n : ℤ} (hm : 0 ≤ m) (hmn : m ≤ n) :
    grassmannianRowLen lambda n ≤ grassmannianRowLen lambda m := by
  have hn : 0 ≤ n := hm.trans hmn
  rw [grassmannianRowLen_of_nonneg lambda hm,
    grassmannianRowLen_of_nonneg lambda hn]
  exact lambda.rowLen_anti m.toNat n.toNat (Int.toNat_le_toNat hmn)

/-- Rows beyond the positive row list have length zero. -/
theorem rowLen_eq_zero_of_rowLens_length_le (lambda : YoungDiagram)
    {n : ℕ} (hn : lambda.rowLens.length ≤ n) :
    lambda.rowLen n = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hcell : (n, 0) ∈ lambda :=
    YoungDiagram.mem_iff_lt_rowLen.mpr hpos
  have hnlt : n < lambda.colLen 0 :=
    YoungDiagram.mem_iff_lt_colLen.mp hcell
  rw [← YoungDiagram.length_rowLens] at hnlt
  omega

/-- The finite Ferrers inversion diagram of the Grassmannian permutation. -/
def grassmannianInvSet (lambda : YoungDiagram) : Set (ℤ × ℤ) :=
  {p | 0 ≤ p.2 ∧ -(grassmannianRowLen lambda p.2 : ℤ) ≤ p.1 ∧ p.1 < 0}

@[simp] theorem mem_grassmannianInvSet (lambda : YoungDiagram) (m n : ℤ) :
    (m, n) ∈ grassmannianInvSet lambda ↔
      0 ≤ n ∧ -(grassmannianRowLen lambda n : ℤ) ≤ m ∧ m < 0 :=
  Iff.rfl

/-- The Ferrers diagram satisfies the inversion-set axioms. -/
theorem grassmannianInvSet_prop (lambda : YoungDiagram) :
    AspSet_prop (grassmannianInvSet lambda) := by
  constructor
  · intro m n hmn
    change 0 ≤ n ∧ -(grassmannianRowLen lambda n : ℤ) ≤ m ∧ m < 0 at hmn
    exact lt_of_lt_of_le hmn.2.2 hmn.1
  · intro u v w huv hvw
    change 0 ≤ v ∧ -(grassmannianRowLen lambda v : ℤ) ≤ u ∧ u < 0 at huv
    change 0 ≤ w ∧ -(grassmannianRowLen lambda w : ℤ) ≤ v ∧ v < 0 at hvw
    omega
  · intro u v w huv hvw huvNot hvwNot huw
    change 0 ≤ w ∧ -(grassmannianRowLen lambda w : ℤ) ≤ u ∧ u < 0 at huw
    by_cases hv : 0 ≤ v
    · apply huvNot
      change 0 ≤ v ∧ -(grassmannianRowLen lambda v : ℤ) ≤ u ∧ u < 0
      refine ⟨hv, ?_, huw.2.2⟩
      have hRows := grassmannianRowLen_anti lambda hv hvw.le
      omega
    · apply hvwNot
      change 0 ≤ w ∧ -(grassmannianRowLen lambda w : ℤ) ≤ v ∧ v < 0
      have hvneg : v < 0 := lt_of_not_ge hv
      exact ⟨huw.1, by omega, hvneg⟩
  · intro u
    refine Set.Finite.subset (Set.finite_Ico (0 : ℤ)
      (lambda.rowLens.length : ℤ)) ?_
    intro v huv
    change 0 ≤ v ∧ -(grassmannianRowLen lambda v : ℤ) ≤ u ∧ u < 0 at huv
    have hvnonneg : 0 ≤ v := huv.1
    have hvlt : v < (lambda.rowLens.length : ℤ) := by
      by_contra hnot
      have hlenInt : (lambda.rowLens.length : ℤ) ≤ (v.toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hvnonneg]
        exact le_of_not_gt hnot
      have hlen : lambda.rowLens.length ≤ v.toNat := by
        exact_mod_cast hlenInt
      have hzero : lambda.rowLen v.toNat = 0 :=
        rowLen_eq_zero_of_rowLens_length_le lambda hlen
      rw [grassmannianRowLen_of_nonneg lambda hvnonneg, hzero] at huv
      omega
    exact ⟨hvnonneg, hvlt⟩
  · intro v
    refine Set.Finite.subset
      (Set.finite_Ico (-(grassmannianRowLen lambda v : ℤ)) 0) ?_
    intro u huv
    change 0 ≤ v ∧ -(grassmannianRowLen lambda v : ℤ) ≤ u ∧ u < 0 at huv
    exact ⟨huv.2.1, huv.2.2⟩

/-- The abstract ASP inversion set associated to a Young diagram. -/
def grassmannianAspSet (lambda : YoungDiagram) : AspSet where
  I := grassmannianInvSet lambda
  prop := grassmannianInvSet_prop lambda

/-- The shift-zero Grassmannian ASP permutation associated to a Young diagram. -/
noncomputable def grassmannianPermOfYoungDiagram
    (lambda : YoungDiagram) : AspPerm :=
  (grassmannianAspSet lambda).toAspPerm 0

@[simp] theorem grassmannianPerm_chi (lambda : YoungDiagram) :
    (grassmannianPermOfYoungDiagram lambda).χ = 0 := by
  exact AspSet.chi_of_toAspPerm (grassmannianAspSet lambda) 0

/-- The reconstructed permutation has exactly the Ferrers inversion set. -/
theorem inv_set_grassmannianPerm (lambda : YoungDiagram) :
    invSet (grassmannianPermOfYoungDiagram lambda) =
      grassmannianInvSet lambda := by
  exact AspSet.invSet_of_toAspPerm (grassmannianAspSet lambda) 0

/-- No nonnegative index is the first coordinate of a Grassmannian inversion. -/
theorem grassmannianAspSet_outset_eq_empty (lambda : YoungDiagram)
    {n : ℤ} (hn : 0 ≤ n) :
    (grassmannianAspSet lambda).outset n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  rw [AspSet.mem_outset] at hm
  exact (not_lt_of_ge hn hm.2.2).elim

/-- The inset at a nonnegative row is the corresponding integer interval. -/
theorem grassmannianAspSet_inset_eq_Ico (lambda : YoungDiagram)
    {n : ℤ} (hn : 0 ≤ n) :
    (grassmannianAspSet lambda).inset n =
      Finset.Ico (-(lambda.rowLen n.toNat : ℤ)) 0 := by
  ext m
  rw [AspSet.mem_inset]
  simp [grassmannianAspSet, grassmannianInvSet, hn]

/-- At a negative input, the outset is indexed by one column of the Young
diagram. -/
theorem grassmannianAspSet_outset_eq_Ico (lambda : YoungDiagram)
    {m : ℤ} (hm : m < 0) :
    (grassmannianAspSet lambda).outset m =
      Finset.Ico 0 (lambda.colLen (-m - 1).toNat : ℤ) := by
  ext n
  rw [AspSet.mem_outset]
  simp only [Finset.mem_Ico]
  change (0 ≤ n ∧ -(grassmannianRowLen lambda n : ℤ) ≤ m ∧ m < 0) ↔
    0 ≤ n ∧ n < (lambda.colLen (-m - 1).toNat : ℤ)
  constructor
  · rintro ⟨hn, hLower, _⟩
    refine ⟨hn, ?_⟩
    rw [grassmannianRowLen_of_nonneg lambda hn] at hLower
    have hjNonneg : 0 ≤ -m - 1 := by omega
    have hColumnInt : ((-m - 1).toNat : ℤ) <
        (lambda.rowLen n.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hjNonneg]
      omega
    have hColumn : (-m - 1).toNat < lambda.rowLen n.toNat := by
      exact_mod_cast hColumnInt
    have hCell : (n.toNat, (-m - 1).toNat) ∈ lambda :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hColumn
    have hRowBound : n.toNat < lambda.colLen (-m - 1).toNat :=
      YoungDiagram.mem_iff_lt_colLen.mp hCell
    have hnCast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    rw [← hnCast]
    exact_mod_cast hRowBound
  · rintro ⟨hn, hUpper⟩
    refine ⟨hn, ?_, hm⟩
    have hnCast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    have hRowBound : n.toNat < lambda.colLen (-m - 1).toNat := by
      have hUpper' : (n.toNat : ℤ) <
          (lambda.colLen (-m - 1).toNat : ℤ) := by
        simpa [hnCast] using hUpper
      exact_mod_cast hUpper'
    have hCell : (n.toNat, (-m - 1).toNat) ∈ lambda :=
      YoungDiagram.mem_iff_lt_colLen.mpr hRowBound
    have hColumn : (-m - 1).toNat < lambda.rowLen n.toNat :=
      YoungDiagram.mem_iff_lt_rowLen.mp hCell
    rw [grassmannianRowLen_of_nonneg lambda hn]
    have hjNonneg : 0 ≤ -m - 1 := by omega
    have hjCast : ((-m - 1).toNat : ℤ) = -m - 1 :=
      Int.toNat_of_nonneg hjNonneg
    have hColumnInt : ((-m - 1).toNat : ℤ) <
        (lambda.rowLen n.toNat : ℤ) := by
      exact_mod_cast hColumn
    rw [hjCast] at hColumnInt
    omega

/-- On nonnegative indices the reconstructed permutation has the usual
Grassmannian formula `n - lambda_n`. -/
theorem grassmannianPerm_apply_of_nonneg (lambda : YoungDiagram)
    {n : ℤ} (hn : 0 ≤ n) :
    grassmannianPermOfYoungDiagram lambda n =
      n - (lambda.rowLen n.toNat : ℤ) := by
  rw [show grassmannianPermOfYoungDiagram lambda n =
      n + ((grassmannianAspSet lambda).outset n).card -
        ((grassmannianAspSet lambda).inset n).card - 0 by rfl]
  rw [grassmannianAspSet_outset_eq_empty lambda hn,
    grassmannianAspSet_inset_eq_Ico lambda hn]
  simp only [Finset.card_empty, Nat.cast_zero, add_zero, sub_zero,
    Int.card_Ico]
  have hnonneg : 0 ≤ (lambda.rowLen n.toNat : ℤ) := by omega
  rw [show (0 - -(lambda.rowLen n.toNat : ℤ)).toNat =
      lambda.rowLen n.toNat by
        simp]

/-- On negative indices the complementary increasing enumeration is described
by column lengths of the Young diagram. -/
theorem grassmannianPerm_apply_of_neg (lambda : YoungDiagram)
    {m : ℤ} (hm : m < 0) :
    grassmannianPermOfYoungDiagram lambda m =
      m + (lambda.colLen (-m - 1).toNat : ℤ) := by
  rw [show grassmannianPermOfYoungDiagram lambda m =
      m + ((grassmannianAspSet lambda).outset m).card -
        ((grassmannianAspSet lambda).inset m).card - 0 by rfl]
  have hInset : (grassmannianAspSet lambda).inset m = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    rw [AspSet.mem_inset] at hn
    change 0 ≤ m ∧ -(grassmannianRowLen lambda m : ℤ) ≤ n ∧ n < 0 at hn
    omega
  rw [grassmannianAspSet_outset_eq_Ico lambda hm, hInset]
  simp

/-- The Grassmannian permutation is strictly increasing on its nonnegative
input ray. -/
theorem grassmannianPerm_strictMono_nonnegative (lambda : YoungDiagram)
    {m n : ℤ} (hm : 0 ≤ m) (hmn : m < n) :
    grassmannianPermOfYoungDiagram lambda m <
      grassmannianPermOfYoungDiagram lambda n := by
  have hn : 0 ≤ n := hm.trans hmn.le
  rw [grassmannianPerm_apply_of_nonneg lambda hm,
    grassmannianPerm_apply_of_nonneg lambda hn]
  have hmnNat : m.toNat ≤ n.toNat := Int.toNat_le_toNat hmn.le
  have hRows := lambda.rowLen_anti m.toNat n.toNat hmnNat
  have hmCast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  have hnCast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  omega

/-- On a nonnegative input ray, a nonempty southeast set is the entire integer
interval from its lower endpoint through its maximum. -/
theorem grassmannianPerm_se_finset_eq_Icc_max
    (lambda : YoungDiagram) {a b : ℤ} (hb : 0 ≤ b)
    (hNonempty : ((grassmannianPermOfYoungDiagram lambda).seFinset a b).Nonempty) :
    (grassmannianPermOfYoungDiagram lambda).seFinset a b =
      Finset.Icc b
        (((grassmannianPermOfYoungDiagram lambda).seFinset a b).max' hNonempty) := by
  let S := (grassmannianPermOfYoungDiagram lambda).seFinset a b
  let top := S.max' hNonempty
  have hTop : top ∈ S := S.max'_mem hNonempty
  have hTopData : b ≤ top ∧ grassmannianPermOfYoungDiagram lambda top < a := by
    simpa [S] using (AspPerm.mem_se
      (grassmannianPermOfYoungDiagram lambda) a b top).mp hTop
  ext n
  constructor
  · intro hn
    have hnData := (AspPerm.mem_se
      (grassmannianPermOfYoungDiagram lambda) a b n).mp (by simpa [S] using hn)
    exact Finset.mem_Icc.mpr ⟨hnData.1, S.le_max' n hn⟩
  · intro hn
    have hnBounds := Finset.mem_Icc.mp hn
    apply (AspPerm.mem_se
      (grassmannianPermOfYoungDiagram lambda) a b n).mpr
    refine ⟨hnBounds.1, ?_⟩
    rcases hnBounds.2.eq_or_lt with rfl | hlt
    · exact hTopData.2
    · exact (grassmannianPerm_strictMono_nonnegative lambda
        (hb.trans hnBounds.1) hlt).trans hTopData.2

/-- The last element of a nonempty nonnegative southeast set is determined by
its cardinality. -/
theorem grassmannianPerm_se_card_last_mem
    (lambda : YoungDiagram) {a b : ℤ} (hb : 0 ≤ b)
    (hNonempty : ((grassmannianPermOfYoungDiagram lambda).seFinset a b).Nonempty) :
    b + (((grassmannianPermOfYoungDiagram lambda).seFinset a b).card : ℤ) - 1 ∈
      (grassmannianPermOfYoungDiagram lambda).seFinset a b := by
  let S := (grassmannianPermOfYoungDiagram lambda).seFinset a b
  let top := S.max' hNonempty
  have hEq := grassmannianPerm_se_finset_eq_Icc_max lambda hb hNonempty
  have hTop : top ∈ S := S.max'_mem hNonempty
  have hbtop : b ≤ top :=
    ((AspPerm.mem_se (grassmannianPermOfYoungDiagram lambda) a b top).mp
      (by simpa [S] using hTop)).1
  have hEq' : S = Finset.Icc b top := by
    simpa [S, top] using hEq
  have hCard : (S.card : ℤ) = top + 1 - b := by
    rw [hEq', Int.card_Icc]
    rw [Int.toNat_of_nonneg (by omega)]
  have hLast : b + (S.card : ℤ) - 1 = top := by omega
  rw [show (grassmannianPermOfYoungDiagram lambda).seFinset a b = S by rfl,
    hLast]
  exact hTop

/-- At the row threshold of `i`, the southeast set is exactly the first
`i+1` nonnegative integers. -/
theorem grassmannianPerm_se_finset_at_row (lambda : YoungDiagram) (i : ℕ) :
    (grassmannianPermOfYoungDiagram lambda).seFinset
        ((i : ℤ) + 1 - (lambda.rowLen i : ℤ)) 0 =
      Finset.Ico 0 ((i : ℤ) + 1) := by
  ext n
  rw [AspPerm.mem_se]
  simp only [Finset.mem_Ico]
  constructor
  · rintro ⟨hn, hValue⟩
    have hApply := grassmannianPerm_apply_of_nonneg lambda hn
    rw [hApply] at hValue
    refine ⟨hn, ?_⟩
    by_contra hnot
    have hiInt : (i : ℤ) ≤ (n.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hn]
      omega
    have hi : i ≤ n.toNat := by
      exact_mod_cast hiInt
    have hRows := lambda.rowLen_anti i n.toNat hi
    omega
  · rintro ⟨hn, hnlt⟩
    have hApply := grassmannianPerm_apply_of_nonneg lambda hn
    rw [hApply]
    have hnInt : (n.toNat : ℤ) ≤ (i : ℤ) := by
      rw [Int.toNat_of_nonneg hn]
      omega
    have hni : n.toNat ≤ i := by
      exact_mod_cast hnInt
    have hRows := lambda.rowLen_anti n.toNat i hni
    omega

/-- The row threshold has the exact essential slipface value `i+1`. -/
theorem grassmannianPerm_s_at_row (lambda : YoungDiagram) (i : ℕ) :
    (grassmannianPermOfYoungDiagram lambda).s
        ((i : ℤ) + 1 - (lambda.rowLen i : ℤ)) 0 = (i : ℤ) + 1 := by
  rw [AspPerm.s_eq_se_card, grassmannianPerm_se_finset_at_row]
  simp

/-- A Young-diagram cell, placed in the negative/nonnegative Ferrers
quadrant used for the Grassmannian inversion set. -/
def grassmannianCellEmbedding (cell : ℕ × ℕ) : ℤ × ℤ :=
  (-(cell.2 : ℤ) - 1, (cell.1 : ℤ))

theorem grassmannianCellEmbedding_injective :
    Function.Injective grassmannianCellEmbedding := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  apply Prod.ext
  · have hSecond := congrArg Prod.snd h
    dsimp [grassmannianCellEmbedding] at hSecond
    exact_mod_cast hSecond
  · have hFirst := congrArg Prod.fst h
    dsimp [grassmannianCellEmbedding] at hFirst
    have : (j : ℤ) = (j' : ℤ) := by omega
    exact_mod_cast this

/-- The Ferrers inversion set is literally the image of the cells of the
Young diagram. -/
theorem grassmannianInvSet_eq_image_cells (lambda : YoungDiagram) :
    grassmannianInvSet lambda =
      grassmannianCellEmbedding '' (lambda.cells : Set (ℕ × ℕ)) := by
  ext ⟨m, n⟩
  constructor
  · intro h
    change 0 ≤ n ∧ -(grassmannianRowLen lambda n : ℤ) ≤ m ∧ m < 0 at h
    let i : ℕ := n.toNat
    let j : ℕ := (-m - 1).toNat
    have hnCast : (i : ℤ) = n := by
      exact Int.toNat_of_nonneg h.1
    have hjNonneg : 0 ≤ -m - 1 := by omega
    have hjCast : (j : ℤ) = -m - 1 := by
      exact Int.toNat_of_nonneg hjNonneg
    have hRowRewrite : grassmannianRowLen lambda n = lambda.rowLen i := by
      rw [grassmannianRowLen_of_nonneg lambda h.1]
    have hjLtInt : (j : ℤ) < (lambda.rowLen i : ℤ) := by
      rw [hjCast]
      rw [hRowRewrite] at h
      omega
    have hjLt : j < lambda.rowLen i := by
      exact_mod_cast hjLtInt
    refine ⟨(i, j), YoungDiagram.mem_iff_lt_rowLen.mpr hjLt, ?_⟩
    apply Prod.ext
    · dsimp [grassmannianCellEmbedding]
      rw [hjCast]
      omega
    · simpa [grassmannianCellEmbedding] using hnCast
  · rintro ⟨⟨i, j⟩, hij, hImage⟩
    have hj : j < lambda.rowLen i :=
      YoungDiagram.mem_iff_lt_rowLen.mp hij
    have hFirst := congrArg Prod.fst hImage
    have hSecond := congrArg Prod.snd hImage
    dsimp [grassmannianCellEmbedding] at hFirst hSecond
    change 0 ≤ n ∧ -(grassmannianRowLen lambda n : ℤ) ≤ m ∧ m < 0
    have hn : 0 ≤ n := by omega
    have hRow : grassmannianRowLen lambda n = lambda.rowLen i := by
      rw [grassmannianRowLen_of_nonneg lambda hn]
      have hi : n.toNat = i := by
        apply Int.ofNat_inj.mp
        rw [Int.toNat_of_nonneg hn]
        omega
      rw [hi]
    rw [hRow]
    constructor
    · exact hn
    · constructor <;> omega

/-- The inversion set is finite, with no appeal to the ASP reconstruction. -/
theorem grassmannianInvSet_finite (lambda : YoungDiagram) :
    (grassmannianInvSet lambda).Finite := by
  rw [grassmannianInvSet_eq_image_cells]
  exact (lambda.cells.finite_toSet.image grassmannianCellEmbedding)

/-- The inversion number of the Grassmannian permutation is the number of
boxes of its Young diagram. -/
theorem ncard_inv_set_grassmannianPerm (lambda : YoungDiagram) :
    (invSet (grassmannianPermOfYoungDiagram lambda)).ncard = lambda.card := by
  rw [inv_set_grassmannianPerm, grassmannianInvSet_eq_image_cells,
    Set.ncard_image_of_injective _ grassmannianCellEmbedding_injective]
  rw [Set.ncard_coe_finset]

/-- Every row stored by `onceMarkedCorners` records the true slipface value of
the reconstructed Grassmannian permutation. -/
theorem grassmannianPerm_onceMarkedCorner_threshold
    (lambda : YoungDiagram) :
    ∀ c ∈ onceMarkedCorners lambda,
      c.2.2 = (grassmannianPermOfYoungDiagram lambda).s (c.1 + 1) 0 - 1 := by
  unfold onceMarkedCorners
  simp only [List.forall_mem_map, List.forall_mem_zipIdx']
  intro i hi
  rw [YoungDiagram.get_rowLens]
  have hRow := grassmannianPerm_s_at_row lambda i
  rw [show (i : ℤ) - (lambda.rowLen i : ℤ) + 1 =
      (i : ℤ) + 1 - (lambda.rowLen i : ℤ) by ring, hRow]
  omega

/-- The once-marked rows dominate every transmission test whose second
coordinate is nonnegative.  This is the direct initial-segment half of the
Grassmannian corner-envelope theorem. -/
theorem grassmannianPerm_cornersDominate_of_nonnegative_b
    (lambda : YoungDiagram) (a b : ℤ) (hb : 0 ≤ b) :
    (grassmannianPermOfYoungDiagram lambda).s (a + 1) b - 1 < 0 ∨
    (grassmannianPermOfYoungDiagram lambda).s (a + 1) b - 1 ≤
      (grassmannianPermOfYoungDiagram lambda).χ + a - b ∨
    ∃ c ∈ onceMarkedCorners lambda,
      (grassmannianPermOfYoungDiagram lambda).s (a + 1) b - 1 ≤
        cornerBound c a b := by
  let tau := grassmannianPermOfYoungDiagram lambda
  let S := tau.seFinset (a + 1) b
  have hSlip : tau.s (a + 1) b = (S.card : ℤ) := by
    simpa [S] using AspPerm.s_eq_se_card tau (a + 1) b
  rw [hSlip]
  by_cases hTrivial : (S.card : ℤ) - 1 < 0
  · exact Or.inl hTrivial
  by_cases hRiemann : (S.card : ℤ) - 1 ≤ a - b
  · exact Or.inr (Or.inl (by simpa [tau] using hRiemann))
  right
  right
  have hCardPos : 0 < S.card := by omega
  have hNonempty : S.Nonempty := Finset.card_pos.mp hCardPos
  let position : ℤ := b + (S.card : ℤ) - 1
  have hPositionMem : position ∈ S := by
    simpa [tau, S, position] using
      (grassmannianPerm_se_card_last_mem lambda (a := a + 1) hb hNonempty)
  have hPositionData : b ≤ position ∧ tau position < a + 1 := by
    exact (AspPerm.mem_se tau (a + 1) b position).mp
      (by simpa [S] using hPositionMem)
  have hPositionNonneg : 0 ≤ position := hb.trans hPositionData.1
  let i : ℕ := position.toNat
  have hiCast : (i : ℤ) = position := Int.toNat_of_nonneg hPositionNonneg
  have hApply := grassmannianPerm_apply_of_nonneg lambda hPositionNonneg
  change tau position = position - (lambda.rowLen position.toNat : ℤ) at hApply
  have hRowPositive : 0 < lambda.rowLen i := by
    by_contra hnot
    have hzero : lambda.rowLen i = 0 := Nat.eq_zero_of_not_pos hnot
    have hiEq : position.toNat = i := rfl
    rw [hiEq, hzero] at hApply
    have : (S.card : ℤ) - 1 ≤ a - b := by
      rw [hApply] at hPositionData
      dsimp [position] at hiCast hPositionData
      omega
    exact hRiemann this
  have hiLength : i < lambda.rowLens.length := by
    rw [YoungDiagram.length_rowLens]
    apply YoungDiagram.mem_iff_lt_colLen.mp
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    exact hRowPositive
  let c : Corner :=
    ((i : ℤ) - (lambda.rowLens[i] : ℤ), 0, (i : ℤ))
  refine ⟨c, ?_, ?_⟩
  · unfold onceMarkedCorners
    apply List.mem_map.mpr
    have hExists : ∃ p ∈ lambda.rowLens.zipIdx,
        p = (lambda.rowLens[i], i) := by
      apply (List.exists_mem_zipIdx').2
      exact ⟨i, hiLength, rfl⟩
    obtain ⟨p, hp, rfl⟩ := hExists
    exact ⟨(lambda.rowLens[i], i), hp, rfl⟩
  · have hAi : (i : ℤ) - (lambda.rowLen i : ℤ) ≤ a := by
      rw [hApply] at hPositionData
      rw [hiCast]
      exact Int.lt_add_one_iff.mp hPositionData.2
    unfold cornerBound
    dsimp [c]
    rw [YoungDiagram.get_rowLens]
    rw [max_eq_left (by omega)]
    simp only [sub_zero]
    rw [max_eq_right hb]
    dsimp [position] at hiCast
    omega

/-- Once corner domination is established, all the remaining fields of the
Grassmannian partition profile follow from the explicit constructor.  This
isolates the exact envelope theorem still required for the full dictionary. -/
theorem grassmannianPartitionProfile_of_cornersDominate
    (lambda : YoungDiagram)
    (hDom : CornersDominate (grassmannianPermOfYoungDiagram lambda)
      (onceMarkedCorners lambda)) :
    GrassmannianPartitionProfile (grassmannianPermOfYoungDiagram lambda)
      lambda := by
  exact ⟨grassmannianPerm_chi lambda, hDom,
    fun c hc => (grassmannianPerm_onceMarkedCorner_threshold lambda c hc).le⟩

end Utilities
