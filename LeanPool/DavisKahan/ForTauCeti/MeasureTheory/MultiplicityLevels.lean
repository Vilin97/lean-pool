/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.LpSliceSum
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorUnitaryEquiv
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Multiplicity normal form for a countable family of measures

A countable family of finite measures on `X` is brought into **level-set form** in two moves,
both of them pure measure theory.

1. **Domination.**  The weighted sum `ρ := ∑ₙ 2⁻ⁿ (‖μₙ‖ + 1)⁻¹ μₙ` is a finite measure
   dominating every member, so `μₙ` is equivalent to `ρ` restricted to the support `Sₙ` of its
   Radon--Nikodym derivative.  Every member of the family is now a restriction of *one* measure.

2. **Rearrangement.**  Set `rank S x n := #{m < n | x ∈ Sₘ}` and

   ```text
   levelPiece S n k := Sₙ ∩ {x | rank S x n = k},      levelSet S k := ⋃ₙ levelPiece S n k.
   ```

   For fixed `n` the pieces partition `Sₙ` as `k` varies; for fixed `k` they partition
   `levelSet S k` as `n` varies.  So the fibrewise relabelling `(x, n) ↦ (x, rank S x n)` carries
   the slice sum of the `ρ|_{Sₙ}` onto the slice sum of the `ρ|_{levelSet S k}`, and it is
   invertible almost everywhere because `k` determines `n` on a level set.

   `levelSet` is **antitone**, so `k ↦ levelSet S k` is the sequence of super-level sets of the
   multiplicity function `x ↦ #{n | x ∈ Sₙ}`.  That antitonicity is what makes the resulting
   datum a multiplicity function rather than an arbitrary family, and it comes out of a
   three-line induction: if `rank S x n = k + 1` then some earlier index has rank `k`.

The relabelling fixes the first coordinate, so it commutes with multiplication by any symbol of
the form `g ∘ Prod.fst`; combined with the Radon--Nikodym unitary this gives the main result,
`TauCeti.exists_multiplicityLevels`.

## Main results

* `TauCeti.dominatingMeasure`: the finite dominating measure.
* `TauCeti.rank`, `TauCeti.levelPiece`, `TauCeti.levelSet`: the combinatorics.
* `TauCeti.antitone_levelSet`: the level sets decrease.
* `TauCeti.map_rankMap_sliceSum`: the relabelling identity between slice sums.
* `TauCeti.exists_multiplicityLevels`: **the normal form.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

section Dominating

variable {X : Type*} [MeasurableSpace X]

/-- The weight attached to the `n`-th member when forming a dominating measure: small enough
that the total mass converges, and nonzero so that no member is lost. -/
noncomputable def domWeight (μ : ℕ → Measure X) (n : ℕ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞)⁻¹) ^ n * (μ n Set.univ + 1)⁻¹

/-- The weights are nonzero, which is what keeps the dominating measure from losing a member of
the family. -/
theorem domWeight_ne_zero (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] (n : ℕ) :
    domWeight μ n ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ ?_) ?_
  · simp
  · rw [ne_eq, ENNReal.inv_eq_zero]
    exact (ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, ENNReal.one_lt_top⟩).ne

/-- Each weighted member contributes at most `2⁻ⁿ` of total mass, which is what makes the
dominating measure finite. -/
theorem domWeight_mul_le (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] (n : ℕ) :
    domWeight μ n * μ n Set.univ ≤ ((2 : ℝ≥0∞)⁻¹) ^ n := by
  have hcancel : (μ n Set.univ + 1)⁻¹ * (μ n Set.univ + 1) = 1 :=
    ENNReal.inv_mul_cancel (by simp)
      (ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, ENNReal.one_lt_top⟩).ne
  calc domWeight μ n * μ n Set.univ
      = ((2 : ℝ≥0∞)⁻¹) ^ n * ((μ n Set.univ + 1)⁻¹ * μ n Set.univ) := by
        rw [domWeight, mul_assoc]
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ n * ((μ n Set.univ + 1)⁻¹ * (μ n Set.univ + 1)) := by
        gcongr
        exact le_self_add
    _ = ((2 : ℝ≥0∞)⁻¹) ^ n := by rw [hcancel, mul_one]

/-- **A finite measure dominating every member of a countable family of finite measures.** -/
noncomputable def dominatingMeasure (μ : ℕ → Measure X) : Measure X :=
  Measure.sum fun n => domWeight μ n • μ n

/-- The dominating measure, evaluated: a weighted countable sum of the members. -/
theorem dominatingMeasure_apply (μ : ℕ → Measure X) {s : Set X} (hs : MeasurableSet s) :
    dominatingMeasure μ s = ∑' n, domWeight μ n * μ n s := by
  rw [dominatingMeasure, Measure.sum_apply _ hs]
  exact tsum_congr fun n => Measure.smul_apply _ _ _

/-- **The dominating measure is finite**, by comparison with a geometric series. -/
instance isFiniteMeasure_dominatingMeasure (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] :
    IsFiniteMeasure (dominatingMeasure μ) := by
  refine ⟨?_⟩
  rw [dominatingMeasure_apply _ MeasurableSet.univ]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (domWeight_mul_le μ)) ?_
  rw [ENNReal.tsum_geometric_two]
  exact ENNReal.ofNat_lt_top

/-- **Every member is absolutely continuous with respect to the dominating measure**, because its
weight is nonzero and a countable sum in `ℝ≥0∞` vanishes only when every term does. -/
theorem absolutelyContinuous_dominatingMeasure (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)]
    (n : ℕ) : μ n ≪ dominatingMeasure μ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [dominatingMeasure_apply _ hs, ENNReal.tsum_eq_zero] at h0
  exact (mul_eq_zero.mp (h0 n)).resolve_left (domWeight_ne_zero μ n)

/-- **Every member of a countable family of finite measures is, up to measure class, a
restriction of one finite measure.** -/
theorem exists_supports_measureEquiv_restrict (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] :
    ∃ S : ℕ → Set X, (∀ n, MeasurableSet (S n)) ∧
      ∀ n, MeasureEquiv (μ n) ((dominatingMeasure μ).restrict (S n)) := by
  refine ⟨fun n => {x | (μ n).rnDeriv (dominatingMeasure μ) x ≠ 0}, fun n => ?_, fun n => ?_⟩
  · exact (Measure.measurable_rnDeriv _ _ (measurableSet_singleton 0)).compl
  · have hwd := measureEquiv_withDensity_restrict (dominatingMeasure μ)
      (Measure.measurable_rnDeriv (μ n) (dominatingMeasure μ))
    rwa [Measure.withDensity_rnDeriv_eq _ _ (absolutelyContinuous_dominatingMeasure μ n)] at hwd

end Dominating

section Rank

variable {X : Type*}

open scoped Classical in
/-- The number of indices below `n` at which `x` lies in the family. -/
-- Exposed: `rank_zero` and `rank_succ` are `rfl`, and every induction below runs on them.
@[expose]
noncomputable def rank (S : ℕ → Set X) (x : X) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rank S x n + (if x ∈ S n then 1 else 0)

/-- No index precedes `0`, so the rank there is zero. -/
theorem rank_zero (S : ℕ → Set X) (x : X) : rank S x 0 = 0 := rfl

open scoped Classical in
/-- The rank increases by one exactly at the indices where the point lies in the family. -/
theorem rank_succ (S : ℕ → Set X) (x : X) (n : ℕ) :
    rank S x (n + 1) = rank S x n + (if x ∈ S n then 1 else 0) := rfl

/-- The rank is monotone in the index. -/
theorem rank_le_rank (S : ℕ → Set X) (x : X) {m n : ℕ} (h : m ≤ n) :
    rank S x m ≤ rank S x n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact le_trans (ih (Nat.lt_succ_iff.mp hlt))
        (by rw [rank_succ]; exact Nat.le_add_right _ _)
    · rw [le_antisymm h hge]

/-- **Membership strictly increases the rank.**  This is what makes the level pieces pairwise
disjoint in the index. -/
theorem rank_lt_rank_of_mem (S : ℕ → Set X) {x : X} {m n : ℕ} (hmn : m < n) (h : x ∈ S m) :
    rank S x m < rank S x n := by
  have hstep : rank S x m < rank S x (m + 1) := by
    rw [rank_succ, ite_eq_left h]
    omega
  exact lt_of_lt_of_le hstep (rank_le_rank S x hmn)

/-- **Every rank is attained on the way up.**  If some index has rank `k + 1` then some index
has rank `k` and lies in the family there.  Three lines of induction, and it is the whole reason
the level sets are antitone. -/
theorem exists_mem_rank_eq_of_rank_eq_succ (S : ℕ → Set X) {x : X} {n k : ℕ}
    (h : rank S x n = k + 1) : ∃ m, x ∈ S m ∧ rank S x m = k := by
  induction n with
  | zero =>
    rw [rank_zero] at h
    simp at h
  | succ n ih =>
    rw [rank_succ] at h
    by_cases hx : x ∈ S n
    · rw [ite_eq_left hx] at h
      exact ⟨n, hx, by omega⟩
    · rw [ite_eq_right hx] at h
      exact ih (by omega)

/-- The rank is measurable, by induction on the index: each step adds the indicator of a
measurable set. -/
theorem measurable_rank [MeasurableSpace X] (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    (n : ℕ) :
    Measurable fun x => rank S x n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [rank_succ]
    exact ih.add (Measurable.ite (hS n) measurable_const measurable_const)

end Rank

section Levels

variable {X : Type*}

/-- The part of `S n` at which exactly `k` earlier members of the family contain the point. -/
noncomputable def levelPiece (S : ℕ → Set X) (n k : ℕ) : Set X :=
  S n ∩ {x | rank S x n = k}

/-- The `k`-th **level set**: the points contained in at least `k + 1` members of the family.

Defined as the union of the level pieces, which is the form both partition statements need. -/
noncomputable def levelSet (S : ℕ → Set X) (k : ℕ) : Set X :=
  ⋃ n, levelPiece S n k

/-- Level pieces are measurable. -/
theorem measurableSet_levelPiece [MeasurableSpace X] {S : ℕ → Set X}
    (hS : ∀ n, MeasurableSet (S n)) (n k : ℕ) : MeasurableSet (levelPiece S n k) :=
  (hS n).inter (measurable_rank S hS n (measurableSet_singleton k))

/-- Level sets are measurable, being countable unions of level pieces. -/
theorem measurableSet_levelSet [MeasurableSpace X] {S : ℕ → Set X}
    (hS : ∀ n, MeasurableSet (S n)) (k : ℕ) : MeasurableSet (levelSet S k) :=
  MeasurableSet.iUnion fun n => measurableSet_levelPiece hS n k

/-- For a fixed index the level pieces partition that member of the family. -/
theorem iUnion_levelPiece_eq (S : ℕ → Set X) (n : ℕ) : (⋃ k, levelPiece S n k) = S n := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun k => Set.inter_subset_left) fun x hx => ?_
  exact Set.mem_iUnion.mpr ⟨rank S x n, hx, rfl⟩

/-- For a fixed index the level pieces are pairwise disjoint in the level: the level *is* the
rank there. -/
theorem pairwise_disjoint_levelPiece_level (S : ℕ → Set X) (n : ℕ) :
    Pairwise fun k k' => Disjoint (levelPiece S n k) (levelPiece S n k') := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun x hx hx' => hkk' ?_
  rw [← hx.2, ← hx'.2]

/-- For a fixed level the level pieces partition the level set: on a level set the level
determines the index. -/
theorem pairwise_disjoint_levelPiece_index (S : ℕ → Set X) (k : ℕ) :
    Pairwise fun n n' => Disjoint (levelPiece S n k) (levelPiece S n' k) := by
  have key : ∀ n n' : ℕ, n < n' → Disjoint (levelPiece S n k) (levelPiece S n' k) := by
    intro n n' hlt
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have hlt' : rank S x n < rank S x n' := rank_lt_rank_of_mem S hlt hx.1
    rw [hx.2, hx'.2] at hlt'
    exact lt_irrefl k hlt'
  intro n n' hnn'
  rcases Nat.lt_or_ge n n' with h | h
  · exact key n n' h
  · exact (key n' n (lt_of_le_of_ne h (Ne.symm hnn'))).symm

/-- **The level sets decrease.** -/
theorem antitone_levelSet (S : ℕ → Set X) : Antitone (levelSet S) := by
  refine antitone_nat_of_succ_le fun k => ?_
  rintro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨m, hm, hrank⟩ := exists_mem_rank_eq_of_rank_eq_succ S hxn.2
  exact Set.mem_iUnion.mpr ⟨m, hm, hrank⟩

/-- **Every member of the family sits inside the zeroth level set.**  A point of `S n` has some
rank there, so it lies in the level piece of that rank, hence in that level set, hence -- by
antitonicity -- in `levelSet S 0`.

This is what makes `levelSet S 0` the support of the whole construction: outside it no member of
the family lives, so a base measure carried by the family is carried by it. -/
theorem subset_levelSet_zero (S : ℕ → Set X) (n : ℕ) : S n ⊆ levelSet S 0 := by
  intro x hx
  have hmem : x ∈ levelSet S (rank S x n) := Set.mem_iUnion.mpr ⟨n, hx, rfl⟩
  exact antitone_levelSet S (Nat.zero_le _) hmem


end Levels

section Rearrangement

variable {X : Type*}

/-- The index at which a point of the `k`-th level set sits: the unique `n` with
`x ∈ levelPiece S n k`, and `0` when there is none. -/
noncomputable def invIdx (S : ℕ → Set X) (x : X) (k : ℕ) : ℕ :=
  sInf {n | x ∈ levelPiece S n k}

/-- On a level piece the index is recovered from the level, because the pieces are disjoint in
the index. -/
theorem invIdx_eq_of_mem {S : ℕ → Set X} {x : X} {n k : ℕ} (h : x ∈ levelPiece S n k) :
    invIdx S x k = n := by
  have hmem : invIdx S x k ∈ {n | x ∈ levelPiece S n k} := Nat.sInf_mem ⟨n, h⟩
  by_contra hne
  exact (Set.disjoint_left.mp (pairwise_disjoint_levelPiece_index S k hne) hmem) h

/-- Off the level set the inverse index is the junk value `0`. -/
theorem invIdx_eq_zero_of_notMem {S : ℕ → Set X} {x : X} {k : ℕ}
    (h : ∀ n, x ∉ levelPiece S n k) : invIdx S x k = 0 := by
  refine Nat.sInf_eq_zero.mpr (Or.inr ?_)
  exact Set.eq_empty_iff_forall_notMem.mpr h

/-- The inverse index is measurable: its fibre over a nonzero index is a level piece, and its
fibre over `0` is a level piece together with the complement of the level set. -/
theorem measurable_invIdx [MeasurableSpace X] {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (k : ℕ) : Measurable fun x => invIdx S x k := by
  refine measurable_to_countable' fun n => ?_
  have hset : (fun x => invIdx S x k) ⁻¹' {n}
      = levelPiece S n k ∪ (if n = 0 then (levelSet S k)ᶜ else ∅) := by
    refine Set.ext fun x => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · intro hx
      by_cases hmem : x ∈ levelSet S k
      · obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hmem
        have hmn : m = n := by rw [← invIdx_eq_of_mem hxm]; exact hx
        exact Or.inl (hmn ▸ hxm)
      · have h0 : invIdx S x k = 0 :=
          invIdx_eq_zero_of_notMem fun m hm => hmem (Set.mem_iUnion.mpr ⟨m, hm⟩)
        have hn0 : n = 0 := by omega
        subst hn0
        exact Or.inr (by simp [hmem])
    · rintro (hx | hx)
      · exact invIdx_eq_of_mem hx
      · by_cases hn0 : n = 0
        · subst hn0
          exact invIdx_eq_zero_of_notMem fun m hm => hx (Set.mem_iUnion.mpr ⟨m, hm⟩)
        · rw [ite_eq_right hn0] at hx
          exact absurd hx (Set.notMem_empty x)
  rw [hset]
  refine (measurableSet_levelPiece hS n k).union ?_
  by_cases hn0 : n = 0
  · rw [ite_eq_left hn0]
    exact (measurableSet_levelSet hS k).compl
  · rw [ite_eq_right hn0]
    exact MeasurableSet.empty

/-- The fibrewise relabelling `(x, n) ↦ (x, rank S x n)`. -/
-- Exposed: `fst_rankMap` is `rfl`, and it is the fact that makes the relabelling commute with
-- multiplication by any symbol pulled back along `Prod.fst`.
@[expose]
noncomputable def rankMap (S : ℕ → Set X) : X × ℕ → X × ℕ :=
  fun p => (p.1, rank S p.1 p.2)

/-- The inverse relabelling `(x, k) ↦ (x, invIdx S x k)`. -/
noncomputable def rankInv (S : ℕ → Set X) : X × ℕ → X × ℕ :=
  fun p => (p.1, invIdx S p.1 p.2)

/-- The relabelling is measurable. -/
theorem measurable_rankMap [MeasurableSpace X] {S : ℕ → Set X}
    (hS : ∀ n, MeasurableSet (S n)) :
    Measurable (rankMap S) :=
  measurable_fst.prodMk (measurable_from_prod_countable_left fun n => measurable_rank S hS n)

/-- The inverse relabelling is measurable. -/
theorem measurable_rankInv [MeasurableSpace X] {S : ℕ → Set X}
    (hS : ∀ n, MeasurableSet (S n)) :
    Measurable (rankInv S) :=
  measurable_fst.prodMk (measurable_from_prod_countable_left fun k => measurable_invIdx hS k)

/-- **The relabelling fixes the spectral coordinate.**  This is why it commutes with
multiplication by any symbol pulled back along `Prod.fst`. -/
theorem fst_rankMap (S : ℕ → Set X) (p : X × ℕ) : (rankMap S p).1 = p.1 := rfl

/-- The relabelling is inverted on the support of the source measure. -/
theorem rankInv_rankMap_of_mem {S : ℕ → Set X} {x : X} {n : ℕ} (h : x ∈ S n) :
    rankInv S (rankMap S (x, n)) = (x, n) := by
  have hpiece : x ∈ levelPiece S n (rank S x n) := ⟨h, rfl⟩
  simp only [rankMap, rankInv]
  rw [invIdx_eq_of_mem hpiece]

/-- The relabelling is inverted on the support of the target measure. -/
theorem rankMap_rankInv_of_mem {S : ℕ → Set X} {x : X} {k : ℕ} (h : x ∈ levelSet S k) :
    rankMap S (rankInv S (x, k)) = (x, k) := by
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp h
  simp only [rankMap, rankInv]
  rw [invIdx_eq_of_mem hxn, hxn.2]

end Rearrangement

section NormalForm

variable {X : Type*} [MeasurableSpace X]

/-- A slice sum of restrictions lives on the sets it restricts to. -/
theorem ae_mem_sliceSum_restrict (ρ : Measure X) {A : ℕ → Set X}
    (hA : ∀ n, MeasurableSet (A n)) :
    ∀ᵐ p ∂(sliceSum fun n => ρ.restrict (A n)), p.1 ∈ A p.2 := by
  rw [ae_iff]
  have hN : {p : X × ℕ | ¬ p.1 ∈ A p.2} = ⋃ n, ((A n)ᶜ ×ˢ ({n} : Set ℕ)) := by
    refine Set.ext fun p => ?_
    constructor
    · intro hp
      exact Set.mem_iUnion.mpr ⟨p.2, hp, rfl⟩
    · intro hp
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
      have hp2 : p.2 = n := hn.2
      rw [Set.mem_ofPred_eq, hp2]
      exact hn.1
  have hNmeas : MeasurableSet {p : X × ℕ | ¬ p.1 ∈ A p.2} := by
    rw [hN]
    exact MeasurableSet.iUnion fun n => (hA n).compl.prod (measurableSet_singleton n)
  rw [sliceSum_apply _ hNmeas, ENNReal.tsum_eq_zero]
  intro n
  have hfib : {x : X | (x, n) ∈ {p : X × ℕ | ¬ p.1 ∈ A p.2}} = (A n)ᶜ := rfl
  rw [hfib, Measure.restrict_apply (hA n).compl, Set.compl_inter_self, measure_empty]

/-- **The relabelling carries the slice sum over the supports onto the slice sum over the level
sets.**

Both sides are computed by splitting into level pieces: for a fixed index they partition that
support as the level varies, and for a fixed level they partition that level set as the index
varies.  The two iterated sums differ only in the order of summation. -/
theorem map_rankMap_sliceSum (ρ : Measure X) {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n)) :
    Measure.map (rankMap S) (sliceSum fun n => ρ.restrict (S n))
      = sliceSum fun k => ρ.restrict (levelSet S k) := by
  refine Measure.ext fun t ht => ?_
  have hfib : ∀ k : ℕ, MeasurableSet {x : X | (x, k) ∈ t} := fun k =>
    (measurable_id.prodMk (measurable_const : Measurable fun _ : X => k)) ht
  have hPmeas : ∀ n k : ℕ, MeasurableSet (levelPiece S n k ∩ {x : X | (x, k) ∈ t}) :=
    fun n k => (measurableSet_levelPiece hS n k).inter (hfib k)
  have hL : Measure.map (rankMap S) (sliceSum fun n => ρ.restrict (S n)) t
      = ∑' n, ∑' k, ρ (levelPiece S n k ∩ {x : X | (x, k) ∈ t}) := by
    rw [Measure.map_apply (measurable_rankMap hS) ht,
      sliceSum_apply _ (measurable_rankMap hS ht)]
    refine tsum_congr fun n => ?_
    have hmeas : MeasurableSet {x : X | (x, rank S x n) ∈ t} :=
      (measurable_id.prodMk (measurable_rank S hS n)) ht
    have hsetn : {x : X | (x, n) ∈ (rankMap S) ⁻¹' t} = {x : X | (x, rank S x n) ∈ t} := rfl
    have hunion : {x : X | (x, rank S x n) ∈ t} ∩ S n
        = ⋃ k, (levelPiece S n k ∩ {x : X | (x, k) ∈ t}) := by
      refine Set.ext fun x => ?_
      constructor
      · rintro ⟨hxt, hxS⟩
        exact Set.mem_iUnion.mpr ⟨rank S x n, ⟨hxS, rfl⟩, hxt⟩
      · intro hx
        obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
        refine ⟨?_, hxk.1.1⟩
        have hrk : rank S x n = k := hxk.1.2
        rw [Set.mem_ofPred_eq, hrk]
        exact hxk.2
    have hdisj : Pairwise (Function.onFun Disjoint
        fun k => levelPiece S n k ∩ {x : X | (x, k) ∈ t}) := fun k k' hkk' =>
      (pairwise_disjoint_levelPiece_level S n hkk').mono Set.inter_subset_left
        Set.inter_subset_left
    rw [hsetn, Measure.restrict_apply hmeas, hunion,
      measure_iUnion hdisj fun k => hPmeas n k]
  have hR : (sliceSum fun k => ρ.restrict (levelSet S k)) t
      = ∑' k, ∑' n, ρ (levelPiece S n k ∩ {x : X | (x, k) ∈ t}) := by
    rw [sliceSum_apply _ ht]
    refine tsum_congr fun k => ?_
    have hunion : {x : X | (x, k) ∈ t} ∩ levelSet S k
        = ⋃ n, (levelPiece S n k ∩ {x : X | (x, k) ∈ t}) := by
      refine Set.ext fun x => ?_
      constructor
      · rintro ⟨hxt, hxL⟩
        obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxL
        exact Set.mem_iUnion.mpr ⟨n, hxn, hxt⟩
      · intro hx
        obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
        exact ⟨hxn.2, Set.mem_iUnion.mpr ⟨n, hxn.1⟩⟩
    have hdisj : Pairwise (Function.onFun Disjoint
        fun n => levelPiece S n k ∩ {x : X | (x, k) ∈ t}) := fun n n' hnn' =>
      (pairwise_disjoint_levelPiece_index S k hnn').mono Set.inter_subset_left
        Set.inter_subset_left
    rw [Measure.restrict_apply (hfib k), hunion, measure_iUnion hdisj fun n => hPmeas n k]
  rw [hL, hR, ENNReal.tsum_comm]

/-- **Multiplicity normal form.**  A countable family of finite measures presents the same
multiplication operator as the level-set family of one finite measure, with the level sets
antitone.

The two moves are domination -- every member becomes a restriction of one finite measure, up to
measure class, so the Radon--Nikodym unitary applies -- and the fibrewise relabelling
`(x, n) ↦ (x, rank S x n)`, which fixes the first coordinate and so commutes with multiplication
by any symbol pulled back along `Prod.fst`.

**The unitary is `star`-equivariant**, and that is recorded in the conclusion rather than left to
a second existential.  Both moves are, and the equivariance is
`TauCeti.star_rnDerivL2Equiv` and `TauCeti.star_compLp` respectively -- the Radon--Nikodym
density is a nonnegative *real* function, so conjugation passes through it, and composition with
a point map commutes with pointwise conjugation outright.  A separate existential would be
useless here: `OperatorUnitaryEquiv` forgets its witness, so a second statement about "the"
unitary could not be paired with this one. -/
theorem exists_multiplicityLevels (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)]
    {g : X → ℂ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    ∃ (ρ : Measure X) (D : ℕ → Set X), IsFiniteMeasure ρ ∧ (∀ k, MeasurableSet (D k)) ∧
      Antitone D ∧
      (∀ N : Set X, MeasurableSet N → (∀ n, μ n N = 0) → ρ N = 0) ∧
      ρ (D 0)ᶜ = 0 ∧
      StarOperatorUnitaryEquiv star star
        (mulLp (sliceSum μ) (hg.comp measurable_fst) (fun p => hgC p.1))
        (mulLp (sliceSum fun k => ρ.restrict (D k)) (hg.comp measurable_fst)
          (fun p => hgC p.1)) := by
  classical
  obtain ⟨S, hSmeas, hSequiv⟩ := exists_supports_measureEquiv_restrict μ
  refine ⟨dominatingMeasure μ, levelSet S, inferInstance,
    fun k => measurableSet_levelSet hSmeas k, antitone_levelSet S, ?_, ?_, ?_⟩
  · intro N hN hzero
    rw [dominatingMeasure_apply _ hN, ENNReal.tsum_eq_zero]
    exact fun n => by rw [hzero n, mul_zero]
  · rw [dominatingMeasure_apply _ (measurableSet_levelSet hSmeas 0).compl,
      ENNReal.tsum_eq_zero]
    intro n
    have hzero : μ n (levelSet S 0)ᶜ = 0 := by
      refine (hSequiv n).1 ?_
      rw [Measure.restrict_apply (measurableSet_levelSet hSmeas 0).compl]
      refine measure_mono_null (fun x hx => ?_) measure_empty
      exact absurd (subset_levelSet_zero S n hx.2) hx.1
    rw [hzero, mul_zero]
  have heq : MeasureEquiv (sliceSum μ)
      (sliceSum fun n => (dominatingMeasure μ).restrict (S n)) :=
    measureEquiv_sliceSum hSequiv
  have step1 : StarOperatorUnitaryEquiv star star
      (mulLp (sliceSum μ) (hg.comp measurable_fst) (fun p => hgC p.1))
      (mulLp (sliceSum fun n => (dominatingMeasure μ).restrict (S n))
        (hg.comp measurable_fst) (fun p => hgC p.1)) :=
    starOperatorUnitaryEquiv_of_intertwines (rnDerivL2Equiv heq.1 heq.2)
      (fun F => rnDerivL2Equiv_mulLp heq.1 heq.2 (hg.comp measurable_fst) (fun p => hgC p.1) F)
      fun F => (star_rnDerivL2Equiv heq.1 heq.2 F).symm
  have hmap : Measure.map (rankMap S)
      (sliceSum fun n => (dominatingMeasure μ).restrict (S n))
      = sliceSum fun k => (dominatingMeasure μ).restrict (levelSet S k) :=
    map_rankMap_sliceSum (dominatingMeasure μ) hSmeas
  have hgf : ∀ᵐ p ∂(sliceSum fun n => (dominatingMeasure μ).restrict (S n)),
      rankInv S (rankMap S p) = p := by
    filter_upwards [ae_mem_sliceSum_restrict (dominatingMeasure μ) hSmeas] with p hp
    simpa using rankInv_rankMap_of_mem (S := S) (x := p.1) (n := p.2) hp
  have hfg : ∀ᵐ p ∂(sliceSum fun k => (dominatingMeasure μ).restrict (levelSet S k)),
      rankMap S (rankInv S p) = p := by
    filter_upwards [ae_mem_sliceSum_restrict (dominatingMeasure μ)
      fun k => measurableSet_levelSet hSmeas k] with p hp
    simpa using rankMap_rankInv_of_mem (S := S) (x := p.1) (k := p.2) hp
  have hpres : MeasurePreserving (rankMap S)
      (sliceSum fun n => (dominatingMeasure μ).restrict (S n))
      (sliceSum fun k => (dominatingMeasure μ).restrict (levelSet S k)) :=
    ⟨measurable_rankMap hSmeas, hmap⟩
  have hpres' : MeasurePreserving (rankInv S)
      (sliceSum fun k => (dominatingMeasure μ).restrict (levelSet S k))
      (sliceSum fun n => (dominatingMeasure μ).restrict (S n)) := by
    refine ⟨measurable_rankInv hSmeas, ?_⟩
    rw [← hmap, Measure.map_map (measurable_rankInv hSmeas) (measurable_rankMap hSmeas)]
    exact (Measure.map_congr hgf).trans Measure.map_id
  have step2 : StarOperatorUnitaryEquiv star star
      (mulLp (sliceSum fun n => (dominatingMeasure μ).restrict (S n))
        (hg.comp measurable_fst) (fun p => hgC p.1))
      (mulLp (sliceSum fun k => (dominatingMeasure μ).restrict (levelSet S k))
        (hg.comp measurable_fst) (fun p => hgC p.1)) :=
    starOperatorUnitaryEquiv_of_intertwines
      (compLpEquiv (rankInv S) (rankMap S) hpres' hpres hfg hgf)
      (fun F => compLp_mulLp hpres' (hg.comp measurable_fst) (fun p => hgC p.1) F)
      fun F => (star_compLp hpres' F).symm
  exact step1.trans step2

end NormalForm

end TauCeti
