/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.GrassmannianAsp

/-!
# The remaining negative-side Grassmannian envelope

`GrassmannianAsp` proves that the ordinary Young-diagram corners dominate all
rows with `b ≥ 0`.  This module isolates the complementary half without
silently replacing it by a finite experiment.  The only extra datum is the
cardinality of a finite interval of *negative* inputs; for a Grassmannian
permutation its membership predicate is the explicit column-length formula.

The Young-diagram counting inequality is proved below, so the resulting
corner envelope and once-marked dictionary are unconditional facts about the
explicitly reconstructed ASP permutation.
-/

@[expose] public section

namespace Utilities

/-! ## The cut determined by the zero-row slipface -/

/-- On the nonnegative ray, the inputs below a fixed output threshold form
the initial interval whose length is the zero-cut slipface value. -/
theorem grassmannianPerm_se_finset_zero_eq_Ico_s
    (lambda : YoungDiagram) (a : ℤ) :
    (grassmannianPermOfYoungDiagram lambda).seFinset (a + 1) 0 =
      Finset.Ico 0
        ((grassmannianPermOfYoungDiagram lambda).s (a + 1) 0) := by
  let tau := grassmannianPermOfYoungDiagram lambda
  let S := tau.seFinset (a + 1) 0
  change S = Finset.Ico 0 (tau.s (a + 1) 0)
  have hSlip : tau.s (a + 1) 0 = (S.card : ℤ) := by
    simpa [S] using tau.s_eq_se_card (a + 1) 0
  by_cases hEmpty : S = ∅
  · have hZero : tau.s (a + 1) 0 = 0 := by simp [hSlip, hEmpty]
    simp [S, hEmpty, hZero]
  · have hNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    let top := S.max' hNonempty
    have hTopMem : top ∈ S := S.max'_mem hNonempty
    have hTopNonneg : 0 ≤ top := by
      have hData := (tau.mem_se (a + 1) 0 top).mp (by simpa [S] using hTopMem)
      exact hData.1
    have hInterval : S = Finset.Icc 0 top := by
      simpa [tau, S, top] using
        (grassmannianPerm_se_finset_eq_Icc_max lambda
          (a := a + 1) (b := 0) (by omega) hNonempty)
    have hCard : (S.card : ℤ) = top + 1 := by
      rw [hInterval, Int.card_Icc]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hTopEq : tau.s (a + 1) 0 = top + 1 := by omega
    rw [hInterval]
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    rw [hTopEq]
    omega

/-- If `r = s(a+1,0)`, then the first row omitted from the initial segment
has length at most `r-a-1`. -/
theorem grassmannianRowLen_at_zeroCut_le
    (lambda : YoungDiagram) (a : ℤ) :
    let r := (grassmannianPermOfYoungDiagram lambda).s (a + 1) 0
    (lambda.rowLen r.toNat : ℤ) ≤ r - a - 1 := by
  let tau := grassmannianPermOfYoungDiagram lambda
  let r := tau.s (a + 1) 0
  change (lambda.rowLen r.toNat : ℤ) ≤ r - a - 1
  have hr : 0 ≤ r := tau.s_nonneg (a + 1) 0
  have hCut := grassmannianPerm_se_finset_zero_eq_Ico_s lambda a
  have hNotMem : r ∉ tau.seFinset (a + 1) 0 := by
    rw [show tau.seFinset (a + 1) 0 = Finset.Ico 0 r by
      simpa [tau, r] using hCut]
    simp
  have hValue : a + 1 ≤ tau r := by
    by_contra hnot
    have hlt : tau r < a + 1 := lt_of_not_ge hnot
    exact hNotMem ((tau.mem_se (a + 1) 0 r).mpr ⟨hr, hlt⟩)
  have hApply := grassmannianPerm_apply_of_nonneg lambda hr
  change tau r = r - (lambda.rowLen r.toNat : ℤ) at hApply
  omega

/-- When the zero-cut is nonempty, its last included row has length at least
`r-a-1`, where `r` is the slipface value. -/
theorem grassmannianRowLen_before_zeroCut_ge
    (lambda : YoungDiagram) (a : ℤ)
    (hr : 0 < (grassmannianPermOfYoungDiagram lambda).s (a + 1) 0) :
    let r := (grassmannianPermOfYoungDiagram lambda).s (a + 1) 0
    r - a - 1 ≤ (lambda.rowLen (r - 1).toNat : ℤ) := by
  let tau := grassmannianPermOfYoungDiagram lambda
  let r := tau.s (a + 1) 0
  change r - a - 1 ≤ (lambda.rowLen (r - 1).toNat : ℤ)
  have hr' : 0 < r := by simpa [tau, r] using hr
  have hrm1 : 0 ≤ r - 1 := by omega
  have hCut := grassmannianPerm_se_finset_zero_eq_Ico_s lambda a
  have hMem : r - 1 ∈ tau.seFinset (a + 1) 0 := by
    rw [show tau.seFinset (a + 1) 0 = Finset.Ico 0 r by
      simpa [tau, r] using hCut]
    simp only [Finset.mem_Ico]
    omega
  have hValue : tau (r - 1) < a + 1 :=
    ((tau.mem_se (a + 1) 0 (r - 1)).mp hMem).2
  have hApply := grassmannianPerm_apply_of_nonneg lambda hrm1
  change tau (r - 1) =
    r - 1 - (lambda.rowLen (r - 1).toNat : ℤ) at hApply
  omega

/-- The negative ray crosses the output threshold exactly at the conjugate
column determined by the zero-cut.  This is the row/column-conjugacy heart of
the negative envelope. -/
theorem grassmannianPerm_apply_neg_lt_iff_le_zeroCut
    (lambda : YoungDiagram) (a n : ℤ) (hn : n < 0) :
    grassmannianPermOfYoungDiagram lambda n < a + 1 ↔
      n ≤ a - (grassmannianPermOfYoungDiagram lambda).s (a + 1) 0 := by
  let tau := grassmannianPermOfYoungDiagram lambda
  let r := tau.s (a + 1) 0
  let j : ℕ := (-n - 1).toNat
  change tau n < a + 1 ↔ n ≤ a - r
  have hr : 0 ≤ r := tau.s_nonneg (a + 1) 0
  have hnIndex : 0 ≤ -n - 1 := by omega
  have hjCast : (j : ℤ) = -n - 1 := Int.toNat_of_nonneg hnIndex
  have hrCast : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr
  have hApply := grassmannianPerm_apply_of_neg lambda hn
  change tau n = n + (lambda.colLen j : ℤ) at hApply
  constructor
  · intro hValue
    by_contra hnot
    have hnLarge : a - r < n := lt_of_not_ge hnot
    by_cases hrZero : r = 0
    · have hColNonneg : 0 ≤ (lambda.colLen j : ℤ) := by omega
      rw [hApply] at hValue
      omega
    · have hrPos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrZero)
      have hRow : r - a - 1 ≤
          (lambda.rowLen (r - 1).toNat : ℤ) := by
        simpa [tau, r] using
          (grassmannianRowLen_before_zeroCut_ge lambda a (by
            simpa [tau, r] using hrPos))
      have hrm1Nonneg : 0 ≤ r - 1 := by omega
      have hrm1Cast : ((r - 1).toNat : ℤ) = r - 1 :=
        Int.toNat_of_nonneg hrm1Nonneg
      have hjLtInt : (j : ℤ) <
          (lambda.rowLen (r - 1).toNat : ℤ) := by
        rw [hjCast]
        omega
      have hjLt : j < lambda.rowLen (r - 1).toNat := by
        exact_mod_cast hjLtInt
      have hCell : ((r - 1).toNat, j) ∈ lambda :=
        YoungDiagram.mem_iff_lt_rowLen.mpr hjLt
      have hCol : (r - 1).toNat < lambda.colLen j :=
        YoungDiagram.mem_iff_lt_colLen.mp hCell
      have hColInt : r ≤ (lambda.colLen j : ℤ) := by
        have hColInt' : ((r - 1).toNat : ℤ) <
            (lambda.colLen j : ℤ) := by
          exact_mod_cast hCol
        rw [hrm1Cast] at hColInt'
        omega
      rw [hApply] at hValue
      omega
  · intro hnSmall
    have hRow : (lambda.rowLen r.toNat : ℤ) ≤ r - a - 1 := by
      simpa [tau, r] using grassmannianRowLen_at_zeroCut_le lambda a
    have hjLargeInt : (lambda.rowLen r.toNat : ℤ) ≤ (j : ℤ) := by
      rw [hjCast]
      omega
    have hjLarge : lambda.rowLen r.toNat ≤ j := by
      exact_mod_cast hjLargeInt
    have hNotCell : (r.toNat, j) ∉ lambda := by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      omega
    have hCol : lambda.colLen j ≤ r.toNat := by
      rw [← not_lt]
      intro hlt
      exact hNotCell (YoungDiagram.mem_iff_lt_colLen.mpr hlt)
    have hColInt : (lambda.colLen j : ℤ) ≤ r := by
      rw [← hrCast]
      exact_mod_cast hCol
    rw [hApply]
    omega

/-- The finite negative-input contribution when a transmission row is moved
from the cut `b = 0` to `b < 0`. -/
noncomputable def grassmannianNegativeContribution
    (lambda : YoungDiagram) (a b : ℤ) : ℤ :=
  (((Finset.Ico b 0).filter fun n : ℤ =>
    n + (lambda.colLen (-n - 1).toNat : ℤ) < a + 1).card : ℤ)

/-- Moving a Grassmannian row from a negative second coordinate to zero adds
exactly the displayed finite column-length count. -/
theorem grassmannianPerm_negative_row_formula
    (lambda : YoungDiagram) (a b : ℤ) (hb : b ≤ 0) :
    (grassmannianPermOfYoungDiagram lambda).s (a + 1) b - 1 =
      (grassmannianPermOfYoungDiagram lambda).s (a + 1) 0 - 1 +
        grassmannianNegativeContribution lambda a b := by
  let tau := grassmannianPermOfYoungDiagram lambda
  have hMove := tau.b_move_up (a + 1) b 0 hb
  have hFilter :
      (Finset.Ico b 0).filter (tau · < a + 1) =
        (Finset.Ico b 0).filter fun n : ℤ =>
          n + (lambda.colLen (-n - 1).toNat : ℤ) < a + 1 := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨hn, hValue⟩
      have hnNeg : n < 0 := hn.2
      rw [grassmannianPerm_apply_of_neg lambda hnNeg] at hValue
      exact ⟨hn, hValue⟩
    · rintro ⟨hn, hValue⟩
      have hnNeg : n < 0 := hn.2
      rw [grassmannianPerm_apply_of_neg lambda hnNeg]
      exact ⟨hn, hValue⟩
  unfold grassmannianNegativeContribution
  rw [hFilter] at hMove
  dsimp [tau] at hMove
  linarith

/-- The negative contribution is the length of a single terminal interval.
Here `r = s(a+1,0)`, so its first contributing column is `r-a-1`. -/
theorem grassmannianNegativeContribution_eq
    (lambda : YoungDiagram) (a b : ℤ) :
    let r := (grassmannianPermOfYoungDiagram lambda).s (a + 1) 0
    grassmannianNegativeContribution lambda a b =
      if b ≤ a - r then a - r - b + 1 else 0 := by
  let tau := grassmannianPermOfYoungDiagram lambda
  let r := tau.s (a + 1) 0
  change grassmannianNegativeContribution lambda a b =
    if b ≤ a - r then a - r - b + 1 else 0
  have hRiemann := tau.s_ge (a + 1) 0
  have hrLower : a + 1 ≤ r := by
    rw [show tau.χ = 0 by simp [tau, grassmannianPerm_chi]] at hRiemann
    omega
  have hCutNeg : a - r < 0 := by omega
  have hPred : ∀ n : ℤ, n < 0 →
      (n + (lambda.colLen (-n - 1).toNat : ℤ) < a + 1 ↔
        n ≤ a - r) := by
    intro n hn
    rw [← grassmannianPerm_apply_of_neg lambda hn]
    simpa [tau, r] using
      (grassmannianPerm_apply_neg_lt_iff_le_zeroCut lambda a n hn)
  by_cases hStart : b ≤ a - r
  · rw [if_pos hStart]
    have hFilter :
        (Finset.Ico b 0).filter (fun n : ℤ =>
          n + (lambda.colLen (-n - 1).toNat : ℤ) < a + 1) =
        Finset.Icc b (a - r) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hbn, hn0⟩, hnValue⟩
        exact ⟨hbn, (hPred n hn0).mp hnValue⟩
      · rintro ⟨hbn, hnCut⟩
        have hn0 : n < 0 := hnCut.trans_lt hCutNeg
        exact ⟨⟨hbn, hn0⟩, (hPred n hn0).mpr hnCut⟩
    unfold grassmannianNegativeContribution
    rw [hFilter, Int.card_Icc]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  · rw [if_neg hStart]
    have hFilter :
        (Finset.Ico b 0).filter (fun n : ℤ =>
          n + (lambda.colLen (-n - 1).toNat : ℤ) < a + 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      have hnCut := (hPred n hn.1.2).mp hn.2
      exact hStart (hn.1.1.trans hnCut)
    unfold grassmannianNegativeContribution
    rw [hFilter]
    simp

/-- At a negative cut, the Grassmannian slipface is forced onto one of two
lines: it is unchanged from `b=0`, or it lies exactly on the Riemann line. -/
theorem grassmannianPerm_negative_row_dichotomy
    (lambda : YoungDiagram) (a b : ℤ) (hb : b < 0) :
    let r := (grassmannianPermOfYoungDiagram lambda).s (a + 1) 0
    (grassmannianPermOfYoungDiagram lambda).s (a + 1) b - 1 = r - 1 ∨
      (grassmannianPermOfYoungDiagram lambda).s (a + 1) b - 1 = a - b := by
  let tau := grassmannianPermOfYoungDiagram lambda
  let r := tau.s (a + 1) 0
  change tau.s (a + 1) b - 1 = r - 1 ∨
    tau.s (a + 1) b - 1 = a - b
  have hMove := grassmannianPerm_negative_row_formula lambda a b hb.le
  have hContribution := grassmannianNegativeContribution_eq lambda a b
  by_cases hStart : b ≤ a - r
  · right
    rw [show grassmannianNegativeContribution lambda a b =
        a - r - b + 1 by
      simpa [tau, r, hStart] using hContribution] at hMove
    dsimp [tau, r] at hMove ⊢
    omega
  · left
    rw [show grassmannianNegativeContribution lambda a b = 0 by
      simpa [tau, r, hStart] using hContribution] at hMove
    dsimp [tau, r] at hMove ⊢
    omega

/-- The precise residual Young-diagram inequality needed on the negative side
of the corner envelope.  It contains no ASP-set or reconstruction predicate:
only a finite interval count using column lengths remains. -/
def GrassmannianNegativeEnvelope (lambda : YoungDiagram) : Prop :=
  ∀ a b : ℤ, b < 0 →
    let t := (grassmannianPermOfYoungDiagram lambda).s (a + 1) 0 - 1 +
      grassmannianNegativeContribution lambda a b
    t < 0 ∨ t ≤ a - b ∨
      ∃ c ∈ onceMarkedCorners lambda, t ≤ cornerBound c a 0

/-- The negative Ferrers-count envelope holds for every Young diagram.  The
proof uses the dichotomy above: either moving below `b=0` adds no inputs, or
the resulting slipface value is exactly the Riemann bound. -/
theorem grassmannianNegativeEnvelope (lambda : YoungDiagram) :
    GrassmannianNegativeEnvelope lambda := by
  intro a b hb
  dsimp only
  let tau := grassmannianPermOfYoungDiagram lambda
  let r := tau.s (a + 1) 0
  change r - 1 + grassmannianNegativeContribution lambda a b < 0 ∨
    r - 1 + grassmannianNegativeContribution lambda a b ≤ a - b ∨
      ∃ c ∈ onceMarkedCorners lambda,
        r - 1 + grassmannianNegativeContribution lambda a b ≤
          cornerBound c a 0
  have hMove : tau.s (a + 1) b - 1 =
      r - 1 + grassmannianNegativeContribution lambda a b := by
    simpa [tau, r] using
      (grassmannianPerm_negative_row_formula lambda a b hb.le)
  have hDichotomy : tau.s (a + 1) b - 1 = r - 1 ∨
      tau.s (a + 1) b - 1 = a - b := by
    simpa [tau, r] using
      (grassmannianPerm_negative_row_dichotomy lambda a b hb)
  rcases hDichotomy with hUnchanged | hRiemann
  · have hTarget :
        r - 1 + grassmannianNegativeContribution lambda a b = r - 1 := by
      omega
    have hAtZero : r - 1 < 0 ∨ r - 1 ≤ tau.χ + a ∨
        ∃ c ∈ onceMarkedCorners lambda, r - 1 ≤ cornerBound c a 0 := by
      simpa [tau, r] using
        (grassmannianPerm_cornersDominate_of_nonnegative_b lambda a 0 (by omega))
    rcases hAtZero with hTrivial | hRiemannZero | ⟨c, hc, hCorner⟩
    · exact Or.inl (by omega)
    · right
      left
      have hChi : tau.χ = 0 := by simp [tau, grassmannianPerm_chi]
      omega
    · right
      right
      exact ⟨c, hc, by omega⟩
  · right
    left
    omega

/-- A negative-side Young-diagram envelope, together with the already-proved
nonnegative theorem, gives the full ASP corner envelope. -/
theorem grassmannianPerm_cornersDominate_of_negativeEnvelope
    (lambda : YoungDiagram) (hNegative : GrassmannianNegativeEnvelope lambda) :
    CornersDominate (grassmannianPermOfYoungDiagram lambda)
      (onceMarkedCorners lambda) := by
  intro a b
  by_cases hb : 0 ≤ b
  · exact grassmannianPerm_cornersDominate_of_nonnegative_b lambda a b hb
  · have hbNeg : b < 0 := lt_of_not_ge hb
    specialize hNegative a b hbNeg
    dsimp only at hNegative
    rw [grassmannianPerm_negative_row_formula lambda a b hbNeg.le]
    rcases hNegative with hTrivial | hRiemann | ⟨c, hc, hCorner⟩
    · exact Or.inl hTrivial
    · right
      left
      simpa [grassmannianPerm_chi] using hRiemann
    · right
      right
      refine ⟨c, hc, ?_⟩
      have hCornerB : cornerBound c a b = cornerBound c a 0 := by
        unfold cornerBound
        have hcB : c.2.1 = 0 := by
          rw [onceMarkedCorners, List.mem_map] at hc
          obtain ⟨p, _hp, rfl⟩ := hc
          rfl
        rw [hcB]
        have hMaxB : max 0 b = 0 := max_eq_left (by omega)
        simp [hMaxB]
      rw [hCornerB]
      exact hCorner

/-- Unconditional full corner domination for the Grassmannian permutation of
an arbitrary Young diagram. -/
theorem grassmannianPerm_cornersDominate (lambda : YoungDiagram) :
    CornersDominate (grassmannianPermOfYoungDiagram lambda)
      (onceMarkedCorners lambda) :=
  grassmannianPerm_cornersDominate_of_negativeEnvelope lambda
    (grassmannianNegativeEnvelope lambda)

/-- The explicit Grassmannian constructor has a partition profile as soon as
the finite negative-side Young-diagram envelope is supplied. -/
theorem grassmannianPartitionProfile_of_negativeEnvelope
    (lambda : YoungDiagram) (hNegative : GrassmannianNegativeEnvelope lambda) :
    GrassmannianPartitionProfile (grassmannianPermOfYoungDiagram lambda)
      lambda :=
  grassmannianPartitionProfile_of_cornersDominate lambda
    (grassmannianPerm_cornersDominate_of_negativeEnvelope lambda hNegative)

/-- Every explicit Grassmannian permutation has the partition profile of its
defining Young diagram. -/
theorem grassmannianPartitionProfile (lambda : YoungDiagram) :
    GrassmannianPartitionProfile (grassmannianPermOfYoungDiagram lambda)
      lambda :=
  grassmannianPartitionProfile_of_cornersDominate lambda
    (grassmannianPerm_cornersDominate lambda)

/-- Factored form of the full Grassmannian/once-marked dictionary, useful when
reusing a separately supplied negative-envelope proof. -/
theorem transmissionExists_grassmannianPerm_iff_onceMarkedBNExists_of_negativeEnvelope
    {G : CFGraph} (hG : graphConnected G) (u v : G.V)
    (lambda : YoungDiagram) (hNegative : GrassmannianNegativeEnvelope lambda) :
    TransmissionExists G u v (grassmannianPermOfYoungDiagram lambda) ↔
      OnceMarkedBNExists G u lambda :=
  transmissionExists_iff_onceMarkedBNExists hG u v
    (grassmannianPermOfYoungDiagram lambda) lambda
    (grassmannianPartitionProfile_of_negativeEnvelope lambda hNegative)

/-- Unconditional Grassmannian/once-marked existence dictionary. -/
theorem transmissionExists_grassmannianPerm_iff_onceMarkedBNExists
    {G : CFGraph} (hG : graphConnected G) (u v : G.V)
    (lambda : YoungDiagram) :
    TransmissionExists G u v (grassmannianPermOfYoungDiagram lambda) ↔
      OnceMarkedBNExists G u lambda :=
  transmissionExists_iff_onceMarkedBNExists hG u v
    (grassmannianPermOfYoungDiagram lambda) lambda
    (grassmannianPartitionProfile lambda)

end Utilities
