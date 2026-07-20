/-
Copyright (c) 2026 Math_XMUM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math_XMUM
-/
import LeanPool.Brouwer.Brouwer

/-!
# Brouwer's fixed-point theorem on a product of simplices

This file extends Brouwer's fixed-point theorem from a single standard simplex to
a finite product of standard simplices. A continuous retraction collapses the big
simplex onto the product, so a fixed point of a continuous self-map of the product
is obtained from the single-simplex theorem.
-/

open Filter

section Brouwer.ProductRetraction
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+)

/-- Total number of coordinates: the sum of `card i` over all `i`. -/
noncomputable def totalCard (card : I → ℕ+)
    : ℕ+ := ⟨(Finset.univ : Finset I).sum (fun i => (card i : ℕ)), by
  apply Finset.sum_pos
  · simp
  · exact Finset.univ_nonempty⟩

omit [DecidableEq I] [LinearOrder I] in
private lemma totalCard_pos_real : 0 < (totalCard card : ℝ) := by
  norm_cast; exact PNat.pos (totalCard card)

omit [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] in
private lemma card_pos_real (i : I) : 0 < (card i : ℝ) := by
  norm_cast; exact PNat.pos (card i)

/-- The big simplex on `totalCard card` coordinates. -/
abbrev BigSimplex := stdSimplex ℝ (Fin (totalCard card))

/-- The product of simplices indexed by `I`. -/
abbrev ProductSimplices := (i : I) → stdSimplex ℝ (Fin (card i))



/-- Cumulative sum of `card` over indices strictly less than `i`. -/
noncomputable def prefixSum (card : I → ℕ+) (i : I) : ℕ :=
  ∑ j ∈ Finset.univ.filter (· < i), (card j : ℕ)


omit [DecidableEq I] in
/-- A flat index `k` belongs to a unique block `i` with an in-block index `j`. -/
lemma index_split_existence (k : Fin (totalCard card)) : ∃ (p : Σ i, Fin (card i)),
    prefixSum card p.1 ≤ k.val ∧ k.val < prefixSum card p.1 + (card p.1 : ℕ) ∧
    p.2.val = k.val - prefixSum card p.1 := by
  let prefix_sum_inclusive (i : I) : ℕ := ∑ j ∈ Finset.univ.filter (· ≤ i), (card j : ℕ)
  let S : Set I := {i | k.val < prefix_sum_inclusive i}
  have s_nonempty : S.Nonempty := by
    let i_max := (Finset.univ : Finset I).max' Finset.univ_nonempty
    use i_max
    have h_sum_eq_total : prefix_sum_inclusive i_max = (totalCard card : ℕ) := by
      simp only [prefix_sum_inclusive, totalCard]
      rw [Finset.filter_true_of_mem (fun j _ => Finset.le_max' _ _ (Finset.mem_univ j))]
      rfl
    change k.val < prefix_sum_inclusive i_max
    rw [h_sum_eq_total]
    exact k.is_lt
  let i₀ := @WellFounded.min I (· < ·) wellFounded_lt S s_nonempty
  have i₀_in_S : i₀ ∈ S := WellFounded.min_mem wellFounded_lt S s_nonempty
  have i₀_is_min : ∀ j < i₀, j ∉ S := fun j hlt => by
    intro hj
    have := WellFounded.min_le wellFounded_lt hj
    exact not_le_of_gt hlt this
  have h_lt : k.val < prefixSum card i₀ + (card i₀ : ℕ) := by
    change k.val < (∑ j ∈ Finset.univ.filter (· ≤ i₀), (card j : ℕ)) at i₀_in_S
    have : (∑ j ∈ Finset.univ.filter (· ≤ i₀), (card j : ℕ)) =
            (∑ j ∈ Finset.univ.filter (· < i₀), (card j : ℕ)) + (card i₀ : ℕ) := by
      have h_split : Finset.univ.filter (· ≤ i₀) = Finset.univ.filter (· < i₀) ∪ {i₀} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          Finset.mem_singleton]
        exact le_iff_lt_or_eq
      have h_disj : Disjoint (Finset.univ.filter (· < i₀)) {i₀} := by simp
      rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]
    rwa [this] at i₀_in_S
  have h_le : prefixSum card i₀ ≤ k.val := by
    by_cases h_i₀_is_min : i₀ = (Finset.univ.min' Finset.univ_nonempty)
    · rw [h_i₀_is_min, prefixSum]
      rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro j hj
        simp only [Finset.mem_filter] at hj
        exact False.elim (not_lt_of_ge (Finset.min'_le _ _ (Finset.mem_univ j)) hj.2)
    · let pred_set := Finset.univ.filter (· < i₀)
      have pred_set_nonempty : pred_set.Nonempty := by
        have : i₀ ≠ Finset.univ.min' Finset.univ_nonempty := h_i₀_is_min
        have : ¬ (∀ j ∈ Finset.univ, i₀ ≤ j) := by
          intro h_all_ge
          have h_min : i₀ = Finset.univ.min' Finset.univ_nonempty := by
            apply le_antisymm
            · exact h_all_ge (Finset.univ.min' Finset.univ_nonempty) (Finset.mem_univ _)
            · exact Finset.min'_le _ _ (Finset.mem_univ i₀)
          exact this h_min
        push Not at this
        obtain ⟨j, _, hj⟩ := this
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
      let j₀ := pred_set.max' pred_set_nonempty
      have j₀_lt_i₀ : j₀ < i₀ := by
        have h_mem : j₀ ∈ pred_set := Finset.max'_mem pred_set pred_set_nonempty
        exact (Finset.mem_filter.mp h_mem).2
      have j₀_notin_S : j₀ ∉ S := i₀_is_min j₀ j₀_lt_i₀
      have j₀_ineq : prefix_sum_inclusive j₀ ≤ k.val := by
        simp only [S, Set.mem_setOf_eq] at j₀_notin_S
        exact le_of_not_gt j₀_notin_S
      have : prefixSum card i₀ = prefix_sum_inclusive j₀ := by
        simp only [prefixSum, prefix_sum_inclusive]
        congr 1
        ext x
        simp only [Finset.mem_filter]
        apply Iff.intro
        · intro h_x_lt_i₀
          exact ⟨Finset.mem_univ x, Finset.le_max' pred_set x (Finset.mem_filter.mpr h_x_lt_i₀)⟩
        · intro h_x_le_j₀
          exact ⟨Finset.mem_univ x, lt_of_le_of_lt h_x_le_j₀.2 j₀_lt_i₀⟩
      exact this ▸ j₀_ineq
  use { fst := i₀, snd := ⟨k.val - prefixSum card i₀, by
    rw [Nat.sub_lt_iff_lt_add h_le]; rwa [add_comm]⟩ }

/-- Split a flat index `k` into its block/index pair `(i, j)`. -/
noncomputable def indexSplit (k : Fin (totalCard card)) : Σ i, Fin (card i) :=
  Classical.choose (index_split_existence card k)

omit [DecidableEq I] in
/-- Specification of `indexSplit`: bounds and value relation for `(i, j)`. -/
lemma index_split_spec (k : Fin (totalCard card)) :
  let p := indexSplit card k
  prefixSum card p.1 ≤ k.val ∧ k.val < prefixSum card p.1 + (card p.1 : ℕ) ∧
  p.2.val = k.val - prefixSum card p.1 :=
  Classical.choose_spec (index_split_existence card k)

/-- Combine a block/index pair `(i, j)` back into a flat index. -/
noncomputable def indexCombine (p : Σ i, Fin (card i)) : Fin (totalCard card) :=
  ⟨prefixSum card p.1 + (p.2 : ℕ), by
    have h1 : prefixSum card p.1 + (p.2 : ℕ) < prefixSum card p.1 + (card p.1 : ℕ) := by
      simpa only [add_lt_add_iff_left] using p.2.is_lt
    have h2 : prefixSum card p.1 + (card p.1 : ℕ) ≤ (totalCard card : ℕ) := by
      simp only [prefixSum, totalCard]
      have h_subset : Finset.univ.filter (· ≤ p.1) ⊆ Finset.univ := Finset.filter_subset _ _
      have h_eq : (Finset.univ.filter (· ≤ p.1)).sum (fun j => (card j : ℕ)) =
                   (Finset.univ.filter (· < p.1)).sum (fun j => (card j : ℕ)) + (card p.1 : ℕ) := by
        have h_split : Finset.univ.filter (· ≤ p.1) = Finset.univ.filter (· < p.1) ∪ {p.1} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_singleton]
          exact le_iff_lt_or_eq
        have h_disj : Disjoint (Finset.univ.filter (· < p.1)) {p.1} := by simp
        rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]
      rw [← h_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => by positivity)
    exact lt_of_lt_of_le h1 h2⟩


/-- `indexSplit` is a left inverse to `indexCombine`. -/
lemma index_split_combine_inverse (p : Σ i, Fin (card i)) : indexSplit card (indexCombine card p)
    = p := by
  classical
  cases p with
  | mk i j =>
    let k : Fin (totalCard card) := indexCombine card ⟨i, j⟩
    have hspec := index_split_spec card k
    have prefix_sum_mono_lt : ∀ {a b : I}, a < b →
        prefixSum card a + (card a : ℕ) ≤ prefixSum card b := by
      intro a b hlt
      have h_subset : (Finset.univ.filter (· ≤ a)) ⊆ (Finset.univ.filter (· < b)) := by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxU, hxle⟩
        exact Finset.mem_filter.mpr ⟨hxU, lt_of_le_of_lt hxle hlt⟩
      have h_eq_a : (Finset.univ.filter (· ≤ a)).sum (fun j => (card j : ℕ)) =
          (Finset.univ.filter (· < a)).sum (fun j => (card j : ℕ)) + (card a : ℕ) := by
        have h_split : Finset.univ.filter (· ≤ a) =
            Finset.univ.filter (· < a) ∪ {a} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_singleton]
          exact le_iff_lt_or_eq
        have h_disj : Disjoint (Finset.univ.filter (· < a)) {a} := by simp
        rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]
      have h_le : (Finset.univ.filter (· ≤ a)).sum (fun j => (card j : ℕ)) ≤
          (Finset.univ.filter (· < b)).sum (fun j => (card j : ℕ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg h_subset (by
          intro j _ _; exact Nat.zero_le _)
      simpa [prefixSum, h_eq_a] using h_le
    have hk_le : prefixSum card i ≤ k.val := by
      simp [k, indexCombine]
    have hk_lt : k.val < prefixSum card i + (card i : ℕ) := by
      simp [k, indexCombine, add_lt_add_iff_left]
    have hnot_lt1 : ¬ (indexSplit card k).1 < i := by
      intro hlt
      have hmono := prefix_sum_mono_lt hlt
      have : k.val < prefixSum card i := Nat.lt_of_lt_of_le hspec.2.1 hmono
      exact (not_lt_of_ge hk_le) this
    have hnot_lt2 : ¬ i < (indexSplit card k).1 := by
      intro hlt
      have hmono := prefix_sum_mono_lt hlt
      have : k.val < prefixSum card (indexSplit card k).1 := Nat.lt_of_lt_of_le hk_lt hmono
      exact (not_lt_of_ge hspec.1) this
    have hi : (indexSplit card k).1 = i :=
      le_antisymm (le_of_not_gt hnot_lt2) (le_of_not_gt hnot_lt1)
    have hj_spec : (indexSplit card k).2.val = k.val - prefixSum card (indexSplit card k).1 :=
        hspec.2.2
    have hj_spec_i : (indexSplit card k).2.val = k.val - prefixSum card i := by
      simpa [hi] using hj_spec
    have hj_val : (indexSplit card k).2.val = j.val := by
      simpa [k, indexCombine, Nat.add_sub_cancel_left] using hj_spec_i
    cases hsplit : indexSplit card k with
    | mk i' j' =>
      have hi' : i' = i := by simpa [hsplit] using hi
      subst hi'
      have hj' : j' = j := by
        apply Fin.ext
        rw [hsplit] at hj_val
        exact hj_val
      simpa [hsplit] using hj'

/-- `indexCombine` is a left inverse to `indexSplit`. -/
lemma index_combine_split_inverse (k : Fin (totalCard card))
    : indexCombine card (indexSplit card k) = k := by
  classical
  have hspec := index_split_spec card k
  apply Fin.ext
  simp [indexCombine, hspec.2.2, Nat.add_sub_of_le hspec.1]


/-- Weight (size fraction) of block `i`: `(card i) / (totalCard card)`. -/
noncomputable def blockWeight (i : I) : ℝ := (card i : ℝ) / (totalCard card : ℝ)

/-- Sum of coordinates of `x` over the block `i`. -/
noncomputable def blockSum (i : I) (x : BigSimplex card) : ℝ :=
  ∑ j : Fin (card i), x.1 (indexCombine card ⟨i, j⟩)

/-- The uniform point in each block simplex. -/
noncomputable def uniformProduct : ProductSimplices card :=
  fun i =>
    (⟨fun _ => (1 : ℝ) / (card i : ℝ), by
      simp only [stdSimplex, Set.mem_setOf_eq]
      constructor
      · intro _; apply div_nonneg <;> positivity
      · simp [Finset.sum_const]
    ⟩ : stdSimplex ℝ (Fin (card i)))

/-- The uniform point in the big simplex. -/
noncomputable def zUniform : BigSimplex card :=
  ⟨fun _ => (1 : ℝ) / (totalCard card : ℝ), by
    simp only [stdSimplex, Set.mem_setOf_eq]
    constructor
    · intro _
      apply div_nonneg
      · norm_num
      · have : 0 < (totalCard card : ℝ) := by
          norm_cast; exact PNat.pos (totalCard card)
        exact le_of_lt this
    · have hpos : 0 < (totalCard card : ℝ) := by
        norm_cast; exact PNat.pos (totalCard card)
      have hcard : (Fintype.card (Fin (totalCard card)) : ℝ) = (totalCard card : ℝ) := by
        simp
      simp [Finset.sum_const, (ne_of_gt hpos)]
  ⟩

/-- Total positive shortfall of block sums relative to block weights. -/
noncomputable def deficit (x : BigSimplex card) : ℝ :=
  ∑ i, max (0 : ℝ) ((blockWeight card i) - blockSum card i x)

/-- Amount to push `x` toward `zUniform` (always in `[0, 1]`). -/
noncomputable def tPush (x : BigSimplex card) : ℝ :=
  (deficit card x) / (1 + deficit card x)

/-- Convex push of `x` toward `zUniform` by amount `tPush`. -/
noncomputable def pushTowardsZ (x : BigSimplex card) : BigSimplex card :=
  ⟨fun k => (1 - tPush card x) * x.1 k + (tPush card x) * (zUniform card).1 k, by
    simp only [stdSimplex, Set.mem_setOf_eq]
    constructor
    · intro k;
      have hx_nonneg : 0 ≤ x.1 k := x.2.1 k
      have hz_nonneg : 0 ≤ (zUniform card).1 k := (zUniform card).2.1 k
      have h_def_nonneg : 0 ≤ deficit card x := by
        unfold deficit
        apply Finset.sum_nonneg
        intro i _
        exact le_max_left _ _
      have hden_pos : 0 < (1 : ℝ) + deficit card x :=
        add_pos_of_pos_of_nonneg (by norm_num) h_def_nonneg
      have ht_nonneg : 0 ≤ tPush card x := by
        simpa [tPush] using div_nonneg h_def_nonneg (le_of_lt hden_pos)
      have h_t_le_one : tPush card x ≤ 1 := by
        have hle : deficit card x ≤ 1 + deficit card x := by linarith
        have hinv_nonneg : 0 ≤ (1 + deficit card x)⁻¹ :=
          inv_nonneg.mpr (le_of_lt hden_pos)
        have hmul := mul_le_mul_of_nonneg_right hle hinv_nonneg
        have hdiv :
            (deficit card x) / (1 + deficit card x) ≤
              (1 + deficit card x) / (1 + deficit card x) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
        simpa [tPush, div_self (ne_of_gt hden_pos)] using hdiv
      have hone_minus_nonneg : 0 ≤ 1 - tPush card x := by linarith
      have hterm1 : 0 ≤ (1 - tPush card x) * x.1 k := mul_nonneg hone_minus_nonneg hx_nonneg
      have hterm2 : 0 ≤ (tPush card x) * (zUniform card).1 k := mul_nonneg ht_nonneg hz_nonneg
      exact add_nonneg hterm1 hterm2
    · classical
      have hpos_tc : 0 < (totalCard card : ℝ) := by
        norm_cast; exact PNat.pos (totalCard card)
      have hx_sum_all : (∑ k, x.1 k) = 1 := x.2.2
      have hz_sum_all : (∑ k, (zUniform card).1 k) = 1 := by
        simp [zUniform, Finset.sum_const, (ne_of_gt hpos_tc)]
      have hx_sum : (∑ k ∈ Finset.univ, x.1 k) = 1 := by simpa using hx_sum_all
      have hz_sum : (∑ k ∈ Finset.univ, (zUniform card).1 k) = 1 := by simpa using hz_sum_all
      calc
        (∑ k ∈ Finset.univ, ((1 - tPush card x) * x.1 k + (tPush card x) * (zUniform card).1 k))
            = (1 - tPush card x) * (∑ k ∈ Finset.univ, x.1 k) + (tPush card x)
                * (∑ k ∈ Finset.univ, (zUniform card).1 k) := by
              simp [Finset.sum_add_distrib, Finset.mul_sum]
        _ = 1 := by
              simp [hx_sum, hz_sum]
  ⟩

omit [DecidableEq I] [LinearOrder I] in
lemma blockWeight_pos (i : I) : 0 < blockWeight card i :=
  div_pos (card_pos_real card i) (totalCard_pos_real card)

/-- `blockSum card i x` is always nonnegative. -/
lemma blockSum_nonneg (i : I) (x : BigSimplex card) : 0 ≤ blockSum card i x := by
  unfold blockSum
  apply Finset.sum_nonneg
  intro j _
  exact x.2.1 _

/-- `deficit card x` is always nonnegative. -/
lemma deficit_nonneg (x : BigSimplex card) : 0 ≤ deficit card x := by
  unfold deficit
  apply Finset.sum_nonneg
  intro i _
  exact le_max_left _ _

/-- `tPush card x` is always in `[0, 1]`. -/
lemma tPush_mem_Icc (x : BigSimplex card) : tPush card x ∈ Set.Icc (0 : ℝ) 1 := by
  have hdef := deficit_nonneg card x
  have hdenpos : 0 < (1 : ℝ) + deficit card x := by linarith
  refine ⟨?_, ?_⟩
  · simpa [tPush] using div_nonneg hdef (le_of_lt hdenpos)
  · rw [tPush, div_le_one hdenpos]; linarith

/-- The block sum after pushing towards `zUniform` follows a linear formula. -/
lemma blockSum_pushTowardsZ_formula (i : I) (x : BigSimplex card) :
    blockSum card i (pushTowardsZ card x) =
      (1 - tPush card x) * blockSum card i x + (tPush card x) * blockWeight card i := by
  simp [blockSum, pushTowardsZ, sub_eq_add_neg, Finset.sum_add_distrib, Finset.mul_sum,
        zUniform, blockWeight, div_eq_mul_inv, mul_left_comm]

/-- The block sum after pushing towards `zUniform` is always positive. -/
lemma blockSum_pushTowardsZ_pos (i : I) (x : BigSimplex card) :
    0 < blockSum card i (pushTowardsZ card x) := by
  rw [blockSum_pushTowardsZ_formula]
  have h_bw_pos := blockWeight_pos card i
  have h_block_nonneg := blockSum_nonneg card i x
  have ⟨h_t_nonneg, h_t_le_one⟩ := tPush_mem_Icc card x
  have h_one_minus_nonneg : 0 ≤ 1 - tPush card x := by linarith
  by_cases ht0 : tPush card x = 0
  · have h_def0 : deficit card x = 0 := by
      have hden_pos : 0 < 1 + deficit card x :=
        add_pos_of_pos_of_nonneg (by norm_num) (deficit_nonneg card x)
      exact (div_eq_zero_iff.mp ht0).resolve_right (ne_of_gt hden_pos)
    have h_term_le_sum : max 0 (blockWeight card i - blockSum card i x) ≤ deficit card x := by
      classical
      have hnonneg : ∀ i' ∈ (Finset.univ : Finset I),
          0 ≤ max 0 (blockWeight card i' - blockSum card i' x) := fun i' _ => le_max_left _ _
      simpa [deficit] using Finset.single_le_sum hnonneg (by simp)
    have h_bw_le_sum : blockWeight card i ≤ blockSum card i x := by
      have h_term_zero : max 0 (blockWeight card i - blockSum card i x) = 0 :=
        le_antisymm (h_term_le_sum.trans (le_of_eq h_def0)) (le_max_left _ _)
      simpa [sub_nonpos] using (max_eq_left_iff.1 h_term_zero)
    have : 0 < blockSum card i x := lt_of_lt_of_le h_bw_pos h_bw_le_sum
    simpa [ht0] using this
  · have htpos : 0 < tPush card x := lt_of_le_of_ne h_t_nonneg (Ne.symm ht0)
    have : 0 < (tPush card x) * blockWeight card i := mul_pos htpos h_bw_pos
    linarith [mul_nonneg h_one_minus_nonneg h_block_nonneg]

/-- Retraction from the big simplex to the product of simplices. -/
noncomputable def projectToProduct (x : BigSimplex card) : ProductSimplices card :=
  fun i =>
    let y := pushTowardsZ card x
    let s := blockSum card i y
    have hspos : 0 < s := blockSum_pushTowardsZ_pos card i x
    (⟨fun j => y.1 (indexCombine card ⟨i, j⟩) / s, by
      simp only [stdSimplex, Set.mem_setOf_eq]
      constructor
      · intro j
        have hy := y.2.1 (indexCombine card ⟨i, j⟩)
        exact div_nonneg hy (le_of_lt hspos)
      · classical
        have h :
           (∑ j : Fin (card i), y.1 (indexCombine card ⟨i, j⟩) / s)
             = (∑ j : Fin (card i), y.1 (indexCombine card ⟨i, j⟩)) * s⁻¹ := by
         simp [div_eq_mul_inv, Finset.sum_mul]
        have hsum : (∑ j : Fin (card i), y.1 (indexCombine card ⟨i, j⟩)) = s := rfl
        rw [h, hsum]
        field_simp
    ⟩ : stdSimplex ℝ (Fin (card i)))

/-- Embedding of the product of simplices into the big simplex. -/
noncomputable def embedFromProduct (y : ProductSimplices card) : BigSimplex card :=
  ⟨fun k =>
    let p := indexSplit card k
    (y p.1).1 p.2 * (card p.1 : ℝ) / (totalCard card : ℝ), by
    simp only [stdSimplex, Set.mem_setOf_eq]
    constructor
    · intro k
      let p := indexSplit card k
      have h_denom_pos : 0 < (totalCard card : ℝ) := by
        norm_cast
        exact PNat.pos (totalCard card)
      have h_num_nonneg : 0 ≤ (y p.1).1 p.2 * (card p.1 : ℝ) :=
        mul_nonneg ((y p.1).2.1 p.2) (by positivity)
      exact div_nonneg h_num_nonneg (le_of_lt h_denom_pos)
    · rw [← Finset.sum_div]
      have h_numerator : (∑ k,
          (y (indexSplit card k).1).1 (indexSplit card k).2 * (card (indexSplit card k).1 : ℝ))
          = ↑(totalCard card) := by
        have : (∑ k,
            (y (indexSplit card k).1).1 (indexSplit card k).2 * (card (indexSplit card k).1 :
            ℝ)) =
               (∑ i, ∑ j : Fin (card i), (y i).1 j * (card i : ℝ)) := by
          let f (p : Σ i, Fin (card i)) := (y p.1).1 p.2 * (card p.1 : ℝ)
          change
            (∑ k ∈ (Finset.univ : Finset (Fin (totalCard card))), f (indexSplit card k)) =
            (∑ i ∈ (Finset.univ : Finset I), ∑ j ∈ (Finset.univ : Finset (Fin (card i))), f ⟨i, j⟩)
          rw [← Finset.sum_sigma (s := (Finset.univ : Finset I))
              (t := fun i => (Finset.univ : Finset (Fin (card i))))]
          apply Finset.sum_bij (fun k _ => indexSplit card k)
          · intro; simp
          · intro a₁ _ a₂ _ h
            rw [← index_combine_split_inverse card a₁, ← index_combine_split_inverse card a₂, h]
          · intro k _
            use indexCombine card k
            exact ⟨Finset.mem_univ _, index_split_combine_inverse card k⟩
          · intro i j; rfl
        rw [this]
        simp_rw [← Finset.sum_mul, (y _).2.2, one_mul]
        rw [← Nat.cast_sum]
        simp [totalCard]
      rw [h_numerator]
      field_simp⟩

/-- `projectToProduct ∘ embedFromProduct = id`. -/
lemma project_embed_id (y : ProductSimplices card) :
  projectToProduct card (embedFromProduct card y) = y := by
  classical
  have h_blockSum : ∀ i, blockSum card i (embedFromProduct card y) = blockWeight card i := by
    intro i
    have :
        blockSum card i (embedFromProduct card y) =
          (((∑ j : Fin (card i), (y i).1 j) * (card i : ℝ)) / (totalCard card : ℝ)) := by
      classical
      have hsum :
          (∑ j : Fin (card i), (embedFromProduct card y).1 (indexCombine card ⟨i, j⟩)) =
            (∑ j : Fin (card i), (y i).1 j * (card i : ℝ) / (totalCard card : ℝ)) := by
        refine Finset.sum_congr rfl ?_;
        intro j _
        simpa [embedFromProduct] using
          congrArg
            (fun p : Σ i, Fin (card i) =>
              (y p.1).1 p.2 * (card p.1 : ℝ) / (totalCard card : ℝ))
            (index_split_combine_inverse card ⟨i, j⟩)
      simpa [blockSum, Finset.sum_div, Finset.sum_mul] using hsum
    simpa [blockWeight, (y i).2.2, one_mul] using this
  have h_deficit_zero : deficit card (embedFromProduct card y) = 0 := by
    simp [deficit, h_blockSum]
  have h_tPush_zero : tPush card (embedFromProduct card y) = 0 := by
    simp [tPush, h_deficit_zero]
  have h_push_id : pushTowardsZ card (embedFromProduct card y) = embedFromProduct card y := by
    apply Subtype.ext
    funext k
    simp [pushTowardsZ, h_tPush_zero]
  funext i
  apply Subtype.ext
  funext j
  have h_denom :
      blockSum card i (pushTowardsZ card (embedFromProduct card y)) = blockWeight card i := by
    simpa [h_push_id] using h_blockSum i
  have h_bw_pos : 0 < blockWeight card i := blockWeight_pos card i
  have h_norm_eq_div :
      ((projectToProduct card (embedFromProduct card y)) i).1 j =
        ((embedFromProduct card y).1 (indexCombine card ⟨i, j⟩)) / (blockWeight card i) := by
    simp only [projectToProduct, h_push_id]
    rw [h_blockSum i]
  have h_div_cancel :
      ((embedFromProduct card y).1 (indexCombine card ⟨i, j⟩)) / (blockWeight card i) =
        (y i).1 j := by
    have hnum : (embedFromProduct card y).1 (indexCombine card ⟨i, j⟩) =
        (y i).1 j * (card i : ℝ) / (totalCard card : ℝ) := by
      simpa [embedFromProduct] using
        congrArg
          (fun p : Σ i, Fin (card i) =>
            (y p.1).1 p.2 * (card p.1 : ℝ) / (totalCard card : ℝ))
          (index_split_combine_inverse card ⟨i, j⟩)
    have hbw_ne : blockWeight card i ≠ 0 := ne_of_gt h_bw_pos
    have htc : (totalCard card : ℝ) ≠ 0 := ne_of_gt (totalCard_pos_real card)
    have hci : (card i : ℝ) ≠ 0 := ne_of_gt (card_pos_real card i)
    have :
        ((y i).1 j * (card i : ℝ) / (totalCard card : ℝ)) /
            ((card i : ℝ) / (totalCard card : ℝ)) =
          (y i).1 j := by
      field_simp [hci, htc]
    simpa [hnum, blockWeight] using this
  simpa [h_norm_eq_div] using h_div_cancel

/-- Continuity of `blockSum card i`. -/
lemma blockSum_continuous (i : I) : Continuous (blockSum card i) := by
  change Continuous (fun x : BigSimplex card =>
    ∑ j : Fin (card i), x.1 (indexCombine card ⟨i, j⟩))
  apply continuous_finsetSum
  intro j _
  exact (continuous_apply _).comp continuous_subtype_val

/-- Continuity of `deficit card`. -/
lemma deficit_continuous : Continuous (deficit card) := by
  change Continuous (fun x : BigSimplex card =>
    ∑ i, max (0 : ℝ) ((blockWeight card i) - blockSum card i x))
  apply continuous_finsetSum
  intro i _
  exact continuous_const.max (continuous_const.sub (blockSum_continuous card i))

/-- Continuity of `tPush card`. -/
lemma tPush_continuous : Continuous (tPush card) := by
  have h_denom_cont : Continuous (fun x => (1 : ℝ) + deficit card x) :=
    continuous_const.add (deficit_continuous card)
  have h_denom_ne : ∀ x, (1 : ℝ) + deficit card x ≠ 0 := fun x =>
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num) (deficit_nonneg card x))
  exact Continuous.div (deficit_continuous card) h_denom_cont h_denom_ne

/-- Continuity of `pushTowardsZ card`. -/
lemma pushTowardsZ_continuous : Continuous (pushTowardsZ card) := by
  apply Continuous.subtype_mk
  classical
  apply continuous_pi
  intro k
  have hxk : Continuous (fun x : BigSimplex card => x.1 k) :=
    (continuous_apply k).comp continuous_subtype_val
  have hone_minus_t : Continuous (fun x => (1 : ℝ) - tPush card x) :=
    continuous_const.sub (tPush_continuous card)
  have hterm1 : Continuous (fun x => ((1 : ℝ) - tPush card x) * x.1 k) :=
    hone_minus_t.mul hxk
  have hterm2 : Continuous (fun x => (tPush card x) * (zUniform card).1 k) :=
    (tPush_continuous card).mul continuous_const
  have hsum : Continuous
      (fun x : BigSimplex card =>
        ((1 : ℝ) - tPush card x) * x.1 k + (tPush card x) * (zUniform card).1 k) :=
    hterm1.add hterm2
  simpa [pushTowardsZ] using hsum

/-- Continuity of `projectToProduct`. -/
lemma project_continuous : Continuous (projectToProduct card) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  let k : Fin (totalCard card) := indexCombine card ⟨i, j⟩
  have h_num_cont : Continuous (fun x : BigSimplex card => (pushTowardsZ card x).1 k) :=
    (continuous_apply k).comp (continuous_subtype_val.comp (pushTowardsZ_continuous card))
  have h_denom_cont : Continuous (fun x : BigSimplex card =>
      blockSum card i (pushTowardsZ card x)) := by
    change Continuous (fun x : BigSimplex card =>
      ∑ j : Fin (card i), (pushTowardsZ card x).1 (indexCombine card ⟨i, j⟩))
    apply continuous_finsetSum
    intro j _
    exact (continuous_apply (indexCombine card ⟨i, j⟩)).comp
      (continuous_subtype_val.comp (pushTowardsZ_continuous card))
  have h_denom_ne : ∀ x : BigSimplex card, blockSum card i (pushTowardsZ card x) ≠ 0 :=
    fun x => ne_of_gt (blockSum_pushTowardsZ_pos card i x)
  have h_div : Continuous (fun x : BigSimplex card =>
      (pushTowardsZ card x).1 k / blockSum card i (pushTowardsZ card x)) :=
    Continuous.div h_num_cont h_denom_cont h_denom_ne
  simpa [projectToProduct, blockSum] using h_div


/-- Continuity of `embedFromProduct`. -/
lemma embed_continuous : Continuous (embedFromProduct card) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  let p := indexSplit card k
  apply Continuous.div
  · refine Continuous.mul ?_ continuous_const
    exact ((continuous_apply p.2).comp continuous_subtype_val).comp (continuous_apply p.1)
  · exact continuous_const
  · intro y
    simp only [totalCard]
    norm_cast
    exact ne_of_gt (Finset.sum_pos (fun i _ => PNat.pos (card i)) Finset.univ_nonempty)

omit [Fintype I] [DecidableEq I] in
/-- Brouwer fixed point theorem for a product of simplices, via a retraction. -/
theorem Brouwer_Product [Finite I]
  (f : ProductSimplices card → ProductSimplices card) (hf : Continuous f) :
  ∃ x : ProductSimplices card, f x = x := by
  classical
  have : Fintype I := Fintype.ofFinite I
  let f_lifted : BigSimplex card → BigSimplex card :=
    embedFromProduct card ∘ f ∘ projectToProduct card
  have hf_lifted : Continuous f_lifted :=
    Continuous.comp (embed_continuous card) (Continuous.comp hf (project_continuous card))
  obtain ⟨x_big, hx_big⟩ := Brouwer f_lifted hf_lifted
  refine ⟨projectToProduct card x_big, ?_⟩
  have : f (projectToProduct card x_big) = projectToProduct card (f_lifted x_big) := by
    simp [f_lifted, project_embed_id]
  rw [this, hx_big]

end Brouwer.ProductRetraction
