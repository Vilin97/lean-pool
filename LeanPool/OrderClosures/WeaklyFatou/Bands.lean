/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.WeaklyFatou.TreeNorm


/-!
# Bands, upshift, trimming, and the weak Fatou estimate
-/

@[expose] public section

namespace OrderClosures

open Set Filter Topology
open scoped NNReal Topology

universe u

/-! ## Bands, upshift, and the weak Fatou estimate -/

/-- Indexing the root band and the sibling bands. -/
abbrev TreeBandIndex (n : ℕ) := Option (TreeNonterminal n)

/-- Support of a sibling band, with `none` denoting the root band. -/
def treeBandSupport (n : ℕ) : TreeBandIndex n → Set (TreeNode n)
  | none => {TreeNode.root n}
  | some u => {t | TreeNode.parent t = u.1 ∧ t ≠ TreeNode.root n}

/-- Coordinate projection onto a sibling band. -/
noncomputable def treeBandProjection (n : ℕ) (B : TreeBandIndex n)
    (w : TreeCoefficients n) : TreeCoefficients n :=
  by
    classical
    exact w.filter fun t ↦ t ∈ treeBandSupport n B

/-- Projection onto a finite family of sibling bands. -/
noncomputable def finiteBandProjection (n : ℕ) (Λ : Finset (TreeBandIndex n))
    (w : TreeCoefficients n) : TreeCoefficients n :=
  by
    classical
    exact w.filter fun t ↦ ∃ B ∈ Λ, t ∈ treeBandSupport n B

/-- Assigns a node to the root band or the sibling band indexed by its parent;
used to define the finite band partition pointwise. -/
noncomputable def treeBandOfNode (n : ℕ) (t : TreeNode n) : TreeBandIndex n :=
  by
    classical
    exact if h : t = TreeNode.root n then none else
      some ⟨TreeNode.parent t, by
        have htpos : 0 < TreeNode.level t := Nat.pos_of_ne_zero fun hzero ↦ h (by
          apply Subtype.ext
          have hnil : t.1 = [] := List.length_eq_zero_iff.mp (by
            simpa [TreeNode.level] using hzero)
          simpa [TreeNode.root] using hnil)
        have hp : TreeNode.level (TreeNode.parent t) = TreeNode.level t - 1 := by
          simp [TreeNode.parent, TreeNode.level]
        have htn : TreeNode.level t ≤ n := t.2
        omega⟩

/-- Assigns every node to its canonical root or sibling band; used to partition
coefficient supports. -/
theorem node_mem_its_treeBand (n : ℕ) (t : TreeNode n) :
    t ∈ treeBandSupport n (treeBandOfNode n t) := by
  classical
  by_cases h : t = TreeNode.root n
  · simp [treeBandOfNode, h, treeBandSupport]
  · simp [treeBandOfNode, h, treeBandSupport]

/-- Recovers the canonical band from membership in a band support; used to
prove uniqueness in the band partition. -/
theorem treeBandOfNode_eq_of_mem (n : ℕ) (t : TreeNode n)
    (B : TreeBandIndex n) (ht : t ∈ treeBandSupport n B) :
    treeBandOfNode n t = B := by
  classical
  cases B with
  | none =>
      have htroot : t = TreeNode.root n := by simpa [treeBandSupport] using ht
      simp [treeBandOfNode, htroot]
  | some u =>
      have ht' : TreeNode.parent t = u.1 ∧ t ≠ TreeNode.root n := by
        simpa [treeBandSupport] using ht
      simp [treeBandOfNode, ht'.2, ht'.1]

/-- Characterizes when a band projection has nonempty support; used to define
and track recurrent bands. -/
theorem treeBandProjection_support_nonempty_iff (n : ℕ)
    (B : TreeBandIndex n) (w : TreeCoefficients n) :
    (treeBandProjection n B w).support.Nonempty ↔
      ∃ t ∈ w.support, treeBandOfNode n t = B := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    have ht' : t ∈ w.support ∧ t ∈ treeBandSupport n B := by
      simpa [treeBandProjection] using ht
    exact ⟨t, ht'.1, treeBandOfNode_eq_of_mem n t B ht'.2⟩
  · rintro ⟨t, htw, htB⟩
    refine ⟨t, ?_⟩
    have htmem := node_mem_its_treeBand n t
    rw [htB] at htmem
    simp [treeBandProjection, htw, htmem]

/-- The finite set of canonical bands meeting the support of `w`; used by the
subsequence recursion in `tree_thinning`. -/
noncomputable def bandsAt (n : ℕ) (w : TreeCoefficients n) :
    Finset (TreeBandIndex n) := by
  classical
  exact w.support.image (treeBandOfNode n)

/-- Characterizes the finite set of bands occurring in a coefficient vector;
used in the thinning recursion. -/
theorem mem_bandsAt_iff (n : ℕ) (w : TreeCoefficients n)
    (B : TreeBandIndex n) :
    B ∈ bandsAt n w ↔ (treeBandProjection n B w).support.Nonempty := by
  classical
  rw [treeBandProjection_support_nonempty_iff]
  simp [bandsAt, eq_comm]

/-- Gives the pointwise formula for projection onto finitely many bands; used
to decompose coefficients in trimming and moderatedness. -/
theorem finiteBandProjection_apply (n : ℕ) (Λ : Finset (TreeBandIndex n))
    (w : TreeCoefficients n) (t : TreeNode n) :
    (treeBandOfNode n t ∈ Λ → finiteBandProjection n Λ w t = w t) ∧
      (treeBandOfNode n t ∉ Λ → finiteBandProjection n Λ w t = 0) := by
  classical
  constructor
  · intro hB
    apply Finsupp.filter_apply_pos
    exact ⟨treeBandOfNode n t, hB, node_mem_its_treeBand n t⟩
  · intro hB
    apply Finsupp.filter_apply_neg
    rintro ⟨B, hBΛ, htB⟩
    exact hB (treeBandOfNode_eq_of_mem n t B htB ▸ hBΛ)

/-- A finite band projection preserves nonnegativity. -/
theorem finiteBandProjection_nonneg (n : ℕ) (Λ : Finset (TreeBandIndex n))
    {w : TreeCoefficients n} (hw : 0 ≤ w) : 0 ≤ finiteBandProjection n Λ w := by
  intro t
  by_cases ht : treeBandOfNode n t ∈ Λ
  · rw [(finiteBandProjection_apply n Λ w t).1 ht]
    exact hw t
  · rw [(finiteBandProjection_apply n Λ w t).2 ht]
    exact le_rfl

/-- A finite band projection decreases nonnegative coefficient vectors. -/
theorem finiteBandProjection_le (n : ℕ) (Λ : Finset (TreeBandIndex n))
    {w : TreeCoefficients n} (hw : 0 ≤ w) : finiteBandProjection n Λ w ≤ w := by
  intro t
  by_cases ht : treeBandOfNode n t ∈ Λ
  · rw [(finiteBandProjection_apply n Λ w t).1 ht]
  · rw [(finiteBandProjection_apply n Λ w t).2 ht]
    exact hw t

/-- Expresses the mass of a finite band projection as a finite sum; used for
tail-mass estimates in the trimming lemma. -/
theorem treeRho_finiteBandProjection (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    treeRho n (finiteBandProjection n Λ w) =
      ∑ B ∈ Λ, treeRho n (treeBandProjection n B w) := by
  classical
  have hfinite : treeRho n (finiteBandProjection n Λ w) =
      ∑ t ∈ w.support, (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) *
        |finiteBandProjection n Λ w t| := by
    rw [treeRho]
    apply Finsupp.sum_of_support_subset
    · rw [finiteBandProjection, Finsupp.support_filter]
      exact Finset.filter_subset _ _
    · simp
  have hband (B : TreeBandIndex n) : treeRho n (treeBandProjection n B w) =
      ∑ t ∈ w.support, (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) *
        |treeBandProjection n B w t| := by
    rw [treeRho]
    apply Finsupp.sum_of_support_subset
    · rw [treeBandProjection, Finsupp.support_filter]
      exact Finset.filter_subset _ _
    · simp
  rw [hfinite]
  simp_rw [hband]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hΛ : treeBandOfNode n t ∈ Λ
  · rw [(finiteBandProjection_apply n Λ w t).1 hΛ]
    rw [Finset.sum_eq_single (treeBandOfNode n t)]
    · rw [treeBandProjection, Finsupp.filter_apply_pos]
      exact node_mem_its_treeBand n t
    · intro B hBΛ hBne
      have hnot : t ∉ treeBandSupport n B := by
        intro htB
        exact hBne (treeBandOfNode_eq_of_mem n t B htB).symm
      rw [treeBandProjection, Finsupp.filter_apply_neg _ _ hnot]
      simp
    · intro hnot
      exact (hnot hΛ).elim
  · rw [(finiteBandProjection_apply n Λ w t).2 hΛ]
    simp only [abs_zero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro B hBΛ
    have hnot : t ∉ treeBandSupport n B := by
      intro htB
      exact hΛ (treeBandOfNode_eq_of_mem n t B htB ▸ hBΛ)
    rw [treeBandProjection, Finsupp.filter_apply_neg _ _ hnot]
    simp

/-- Chooses the root or parent node representing a band; used to define the
upshift of all coefficients in that band. -/
noncomputable def treeBandParent (n : ℕ) : TreeBandIndex n → TreeNode n
  | none => TreeNode.root n
  | some u => u.1

/-- Identifies a nonroot node's parent with the representative of its band;
used to analyze the support of the upshift. -/
theorem parent_eq_treeBandParent (n : ℕ) (t : TreeNode n) :
    TreeNode.parent t = treeBandParent n (treeBandOfNode n t) := by
  classical
  by_cases ht : t = TreeNode.root n
  · subst t
    simp [treeBandOfNode, treeBandParent, TreeNode.parent, TreeNode.root]
  · simp [treeBandOfNode, treeBandParent, ht]

/-- The upshift `S_n`, merging coefficients at their parents. -/
noncomputable def treeUpshift (n : ℕ) (w : TreeCoefficients n) : TreeCoefficients n :=
  w.mapDomain TreeNode.parent

/-- The finite set of representative parents of a finite band family; used to
bound the support of upshifted coefficients. -/
noncomputable def treeBandParents (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) : Finset (TreeNode n) := by
  classical
  exact Λ.image (treeBandParent n)

/-- Bounds the support of an upshift by the finite set of band parents; used
to obtain a finite-dimensional convergent subsequence. -/
theorem treeUpshift_support_subset_bandParents (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    (treeUpshift n (finiteBandProjection n Λ w)).support ⊆
      treeBandParents n Λ := by
  classical
  intro q hq
  rw [treeUpshift] at hq
  have hq' := Finsupp.mapDomain_support hq
  rcases Finset.mem_image.mp hq' with ⟨t, ht, rfl⟩
  rw [treeBandParents]
  apply Finset.mem_image.mpr
  refine ⟨treeBandOfNode n t, ?_, (parent_eq_treeBandParent n t).symm⟩
  have htfinite : t ∈ (finiteBandProjection n Λ w).support := ht
  by_contra hnot
  have hzero := (finiteBandProjection_apply n Λ w t).2 hnot
  exact Finsupp.mem_support_iff.mp htfinite hzero

/-- Compares the weight of a parent node with that of its child; used to bound
the `treeRho` cost of upshifting. -/
theorem treeParent_weight_le (n : ℕ) (t : TreeNode n) :
    (2 : ℝ) ^ (-(TreeNode.level (TreeNode.parent t) : ℤ)) ≤
      2 * (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by
  have hp : TreeNode.level (TreeNode.parent t) = TreeNode.level t - 1 := by
    simp [TreeNode.parent, TreeNode.level]
  by_cases ht : TreeNode.level t = 0
  · simp [hp, ht]
  · have hz : -(TreeNode.level (TreeNode.parent t) : ℤ) =
        -(TreeNode.level t : ℤ) + 1 := by omega
    rw [hz, zpow_add₀ (by norm_num)]
    simp [mul_comm]

/-- Shows that a node cylinder lies inside its parent cylinder; used to prove
that upshifting increases the associated tree operator. -/
theorem treeCylinder_subset_parent (n : ℕ) (t : TreeNode n) :
    treeCylinder n t ⊆ treeCylinder n (TreeNode.parent t) := by
  intro α hα j
  let j' : Fin (TreeNode.level t) := ⟨j, by
    exact j.isLt.trans_le (by simp [TreeNode.parent, TreeNode.level])⟩
  have hj := hα j'
  have hpref : strictPrefix (TreeNode.parent t) j = strictPrefix t j' := by
    apply Subtype.ext
    apply Subtype.ext
    change t.1.dropLast.take j = t.1.take j'
    have htne : t.1 ≠ [] := by
      intro ht
      have hjlt := j.isLt
      simp [TreeNode.parent, TreeNode.level, ht] at hjlt
    nth_rewrite 2 [← List.dropLast_append_getLast htne]
    exact (List.take_append_of_le_length j.isLt.le).symm
  have hget : (TreeNode.parent t).1.get j = t.1.get j' := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp [TreeNode.parent]
    rfl
  rw [hpref, hget]
  exact hj

/-- Converts cylinder inclusion into domination by the parent tree function;
used in `treeUpshift_basic`. -/
theorem treeFunction_le_parent (n : ℕ) (t : TreeNode n) :
    treeFunction n t ≤ treeFunction n (TreeNode.parent t) := by
  intro α
  change treeFunction n t α ≤ treeFunction n (TreeNode.parent t) α
  by_cases hα : α ∈ treeCylinder n t
  · rw [treeFunction_apply_of_mem n t hα,
      treeFunction_apply_of_mem n _ (treeCylinder_subset_parent n t hα)]
  · rw [treeFunction_apply_of_notMem n t hα]
    exact treeFunction_nonneg n _ α

/-- Paper Lemma `lem:upshift-basic`. -/
theorem treeUpshift_basic (n : ℕ) (w : TreeCoefficients n) (hw : 0 ≤ w) :
    treeRho n (treeUpshift n w) ≤ 2 * treeRho n w ∧
      treeOperator n w ≤ treeOperator n (treeUpshift n w) := by
  have hupnonneg : 0 ≤ treeUpshift n w :=
    Finsupp.mapDomain_nonneg hw
  constructor
  · classical
    have hrho_up : treeRho n (treeUpshift n w) =
        (treeUpshift n w).sum fun t a ↦
          (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * a := by
      rw [treeRho]
      apply Finsupp.sum_congr
      intro t _
      rw [abs_of_nonneg (hupnonneg t)]
    rw [hrho_up]
    rw [treeUpshift, Finsupp.sum_mapDomain_index (by simp) (by simp [mul_add])]
    rw [treeRho, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    rw [abs_of_nonneg (hw t)]
    calc
      (2 : ℝ) ^ (-(TreeNode.level (TreeNode.parent t) : ℤ)) * w t ≤
          (2 * (2 : ℝ) ^ (-(TreeNode.level t : ℤ))) * w t :=
        mul_le_mul_of_nonneg_right (treeParent_weight_le n t) (hw t)
      _ = 2 * ((2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * w t) := by ring
  · classical
    change (w.sum fun t a ↦ a • treeFunction n t) ≤
      (Finsupp.mapDomain TreeNode.parent w).sum fun t a ↦ a • treeFunction n t
    rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
    apply Finsupp.sum_le_sum
    intro t _ α
    change w t * treeFunction n t α ≤ w t * treeFunction n (TreeNode.parent t) α
    exact mul_le_mul_of_nonneg_left (treeFunction_le_parent n t α) (hw t)

/-- A single band projection cannot increase `treeRho`; used to uniformly
bound each coordinate in the sharp-subsequence extraction. -/
theorem treeRho_bandProjection_le (n : ℕ) (B : TreeBandIndex n)
    (w : TreeCoefficients n) :
    treeRho n (treeBandProjection n B w) ≤ treeRho n w := by
  classical
  have heq : treeRho n (treeBandProjection n B w) =
      ∑ t ∈ w.support.filter (fun t ↦ t ∈ treeBandSupport n B),
        (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |w t| := by
    rw [treeRho, treeBandProjection, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp ht).2]
  rw [heq, treeRho, Finsupp.sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro t _ _
  exact mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)

/-- A projection onto finitely many bands cannot increase `treeRho`; used in
the coefficient decomposition for `component_moderated`. -/
theorem treeRho_finiteBandProjection_le (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    treeRho n (finiteBandProjection n Λ w) ≤ treeRho n w := by
  classical
  have heq : treeRho n (finiteBandProjection n Λ w) =
      ∑ t ∈ w.support.filter (fun t ↦ treeBandOfNode n t ∈ Λ),
        (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |w t| := by
    have hp (t : TreeNode n) :
        (∃ B ∈ Λ, t ∈ treeBandSupport n B) ↔ treeBandOfNode n t ∈ Λ := by
      constructor
      · rintro ⟨B, hB, ht⟩
        exact treeBandOfNode_eq_of_mem n t B ht ▸ hB
      · intro ht
        exact ⟨treeBandOfNode n t, ht, node_mem_its_treeBand n t⟩
    rw [treeRho, finiteBandProjection, Finsupp.sum, Finsupp.support_filter]
    simp_rw [hp]
    apply Finset.sum_congr rfl
    intro t ht
    have happly : (w.filter fun x ↦ treeBandOfNode n x ∈ Λ) t = w t :=
      Finsupp.filter_apply_pos (fun x ↦ treeBandOfNode n x ∈ Λ) w
        (Finset.mem_filter.mp ht).2
    rw [happly]
  rw [heq, treeRho, Finsupp.sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro t _ _
  exact mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)

/-- Bounds the total mass of any finite band family by the original mass;
used to prove summability of limiting band masses in `tree_trim`. -/
theorem sum_treeRho_bandProjection_le (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    ∑ B ∈ Λ, treeRho n (treeBandProjection n B w) ≤ treeRho n w := by
  rw [← treeRho_finiteBandProjection]
  exact treeRho_finiteBandProjection_le n Λ w

/-- Paper Lemma `lem:sharp-subsequence`. -/
theorem tree_sharp_subsequence
    (n : ℕ) (w : ℕ → TreeCoefficients n) (C : ℝ)
    (hw : ∀ m, treeRho n (w m) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B : TreeBandIndex n,
      ∃ l : ℝ, Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w (φ m))))
        atTop (nhds l) := by
  classical
  let : Countable (TreeNode n) := by
    unfold TreeNode
    infer_instance
  let : Countable (TreeNonterminal n) := by
    unfold TreeNonterminal
    infer_instance
  let D := max C 0
  let y : ℕ → TreeBandIndex n → Set.Icc (0 : ℝ) D := fun m B ↦
    ⟨treeRho n (treeBandProjection n B (w m)),
      treeRho_nonneg n _,
      (treeRho_bandProjection_le n B (w m)).trans
        ((hw m).trans (le_max_left C 0))⟩
  let : SeqCompactSpace (TreeBandIndex n → Set.Icc (0 : ℝ) D) := inferInstance
  obtain ⟨l, _, φ, hφ, hlim⟩ :=
    (SeqCompactSpace.isSeqCompact_univ
      (X := TreeBandIndex n → Set.Icc (0 : ℝ) D)) (x := y) (fun _ ↦ Set.mem_univ _)
  refine ⟨φ, hφ, fun B ↦ ⟨(l B).1, ?_⟩⟩
  have hcoord := tendsto_pi_nhds.mp hlim B
  simpa [y, Function.comp_def] using tendsto_subtype_rng.mp hcoord

/-- The bands occurring in infinitely many supports of a sequence. -/
def recurrentBands (n : ℕ) (w : ℕ → TreeCoefficients n) : Set (TreeBandIndex n) :=
  {B | Set.Infinite {m | (treeBandProjection n B (w m)).support.Nonempty}}

/-- Records a final support occurrence for each nonrecurrent band; used to
construct a subsequence in which transient bands occur at most once. -/
noncomputable def lastBandOccurrence (n : ℕ)
    (w : ℕ → TreeCoefficients n) (B : TreeBandIndex n) : ℕ := by
  classical
  let S : Set ℕ := {m | (treeBandProjection n B (w m)).support.Nonempty}
  exact if h : S.Finite then h.toFinset.sup id else 0

/-- Bounds every occurrence of a nonrecurrent band by its recorded last index;
used to choose a subsequence with transient bands occurring at most once. -/
theorem le_lastBandOccurrence (n : ℕ) (w : ℕ → TreeCoefficients n)
    (B : TreeBandIndex n)
    (hfinite : {m | (treeBandProjection n B (w m)).support.Nonempty}.Finite)
    {m : ℕ} (hm : (treeBandProjection n B (w m)).support.Nonempty) :
    m ≤ lastBandOccurrence n w B := by
  classical
  rw [lastBandOccurrence, dite_eq_left hfinite]
  exact Finset.le_sup (s := hfinite.toFinset) (f := id) (by simpa using hm)

/-- A countable family admits positive weights with every finite sum below a given budget. -/
private theorem exists_positive_finite_sum_budget {ι : Type*} [Countable ι]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ι → ℝ, (∀ i, 0 < δ i) ∧ ∀ F : Finset ι, ∑ i ∈ F, δ i ≤ ε := by
  classical
  let : Encodable ι := Encodable.ofCountable _
  let a := ε / 2
  have ha : 0 < a := div_pos hε (by norm_num)
  let δ : ι → ℝ := fun i ↦ a * (1 / 2 : ℝ) ^ Encodable.encode i
  have hδpos (i : ι) : 0 < δ i := mul_pos ha (pow_pos (by norm_num) _)
  have hgeom : Summable (fun i : ι ↦ (1 / 2 : ℝ) ^ Encodable.encode i) := by
    simpa [Function.comp_def] using
      summable_geometric_two.comp_injective Encodable.encode_injective
  have hgeom_tsum_le : ∑' i : ι, (1 / 2 : ℝ) ^ Encodable.encode i ≤ 2 := by
    calc
      ∑' i : ι, (1 / 2 : ℝ) ^ Encodable.encode i ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k :=
        hgeom.tsum_le_tsum_of_inj Encodable.encode Encodable.encode_injective
          (fun k _ ↦ by positivity) (fun _ ↦ le_rfl) summable_geometric_two
      _ = 2 := tsum_geometric_two
  have hδsummable : Summable δ := hgeom.mul_left a
  refine ⟨δ, hδpos, fun F ↦ ?_⟩
  calc
    ∑ i ∈ F, δ i ≤ ∑' i, δ i :=
      Summable.sum_le_tsum F (fun i _ ↦ (hδpos i).le) hδsummable
    _ = a * ∑' i : ι, (1 / 2 : ℝ) ^ Encodable.encode i := tsum_mul_left
    _ ≤ a * 2 := mul_le_mul_of_nonneg_left hgeom_tsum_le ha.le
    _ = ε := by dsimp [a]; ring

/-- Paper Lemma `lem:trim`. -/
theorem tree_trim
    (n : ℕ) (x : ℕ → TreeComponent n) (w : ℕ → TreeCoefficients n)
    {ε : ℝ} (hε : 0 < ε)
    (hw : ∀ m, 0 ≤ w m)
    (hdom : ∀ m, (x m).1 ≤ treeOperator n (w m))
    (hrho : ∀ m, treeRho n (w m) < 1 + ε / 4)
    (hsharp : ∀ B : TreeBandIndex n, ∃ l : ℝ,
      Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w m)))
        atTop (nhds l)) :
    ∃ w' : ℕ → TreeCoefficients n,
      (∀ m, 0 ≤ w' m ∧ (x m).1 ≤ treeOperator n (w' m) ∧
        treeRho n (w' m) < 1 + ε / 2) ∧
      (recurrentBands n w').Finite := by
  classical
  let M : ℝ := (2 : ℝ) ^ n
  have hM : 0 < M := pow_pos (by norm_num) n
  let lam : TreeBandIndex n → ℝ := fun B ↦ Classical.choose (hsharp B)
  have hlamlim (B : TreeBandIndex n) :
      Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w m)))
        atTop (nhds (lam B)) := Classical.choose_spec (hsharp B)
  have hlamnonneg (B : TreeBandIndex n) : 0 ≤ lam B := by
    apply ge_of_tendsto (hlamlim B)
    exact Filter.Eventually.of_forall fun m ↦ treeRho_nonneg n _
  have hlamfinite (S : Finset (TreeBandIndex n)) :
      ∑ B ∈ S, lam B ≤ 1 + ε / 4 := by
    have hlim : Tendsto
        (fun m ↦ ∑ B ∈ S, treeRho n (treeBandProjection n B (w m)))
        atTop (nhds (∑ B ∈ S, lam B)) :=
      tendsto_finsetSum S fun B _ ↦ hlamlim B
    apply le_of_tendsto hlim
    exact Filter.Eventually.of_forall fun m ↦
      (sum_treeRho_bandProjection_le n S (w m)).trans (hrho m).le
  have hlamsummable : Summable lam :=
    summable_of_sum_le (fun B ↦ hlamnonneg B) hlamfinite
  let tailBudget : ℝ := ε / (8 * M)
  have htailBudget : 0 < tailBudget := div_pos hε (mul_pos (by norm_num) hM)
  obtain ⟨Λ₀, hΛ₀⟩ :=
    (Metric.tendsto_atTop.mp hlamsummable.hasSum) tailBudget htailBudget
  let Λ : Finset (TreeBandIndex n) := insert none Λ₀
  have hnoneΛ : none ∈ Λ := by simp [Λ]
  have hΛapprox : dist (∑ B ∈ Λ, lam B) (∑' B, lam B) < tailBudget :=
    hΛ₀ Λ (Finset.subset_insert none Λ₀)
  have hΛsum_le : ∑ B ∈ Λ, lam B ≤ ∑' B, lam B :=
    Summable.sum_le_tsum Λ (fun B _ ↦ hlamnonneg B) hlamsummable
  have htail (F : Finset (TreeBandIndex n))
      (hF : ∀ B ∈ F, B ∉ Λ) : ∑ B ∈ F, lam B < tailBudget := by
    have hdis : Disjoint Λ F := Finset.disjoint_left.mpr fun B hBΛ hBF ↦
      (hF B hBF) hBΛ
    have hunion : (∑ B ∈ Λ, lam B) + ∑ B ∈ F, lam B =
        ∑ B ∈ Λ ∪ F, lam B := by
      exact (Finset.sum_union hdis).symm
    have hle : ∑ B ∈ Λ ∪ F, lam B ≤ ∑' B, lam B :=
      Summable.sum_le_tsum (Λ ∪ F) (fun B _ ↦ hlamnonneg B) hlamsummable
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hΛsum_le)] at hΛapprox
    linarith
  obtain ⟨δ, hδpos, hδfinite⟩ :=
    exists_positive_finite_sum_budget (ι := TreeBandIndex n) htailBudget
  have hcutoff (B : TreeBandIndex n) : ∃ N : ℕ, ∀ m ≥ N,
      treeRho n (treeBandProjection n B (w m)) < lam B + δ B := by
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp (hlamlim B)) (δ B) (hδpos B)
    refine ⟨N, fun m hm ↦ ?_⟩
    have habs := hN m hm
    rw [Real.dist_eq] at habs
    have hsub : treeRho n (treeBandProjection n B (w m)) - lam B < δ B :=
      (le_abs_self _).trans_lt habs
    linarith
  let N : TreeBandIndex n → ℕ := fun B ↦ Classical.choose (hcutoff B)
  have hN (B : TreeBandIndex n) (m : ℕ) (hm : N B ≤ m) :
      treeRho n (treeBandProjection n B (w m)) < lam B + δ B :=
    Classical.choose_spec (hcutoff B) m hm
  let removedBands : ℕ → Finset (TreeBandIndex n) := fun m ↦
    (bandsAt n (w m)).filter fun B ↦ B ∉ Λ ∧ N B ≤ m
  let r : ℕ → TreeCoefficients n := fun m ↦
    finiteBandProjection n (removedBands m) (w m)
  let w' : ℕ → TreeCoefficients n := fun m ↦
    w m - r m + (M * treeRho n (r m)) • treeBasis (TreeNode.root n)
  have hr_nonneg (m : ℕ) : 0 ≤ r m :=
    finiteBandProjection_nonneg n (removedBands m) (hw m)
  have hkeep_nonneg (m : ℕ) : 0 ≤ w m - r m :=
    sub_nonneg.mpr (finiteBandProjection_le n (removedBands m) (hw m))
  have hrho_r (m : ℕ) : treeRho n (r m) < ε / (4 * M) := by
    have hRB (B : TreeBandIndex n) (hB : B ∈ removedBands m) :
        treeRho n (treeBandProjection n B (w m)) < lam B + δ B := by
      exact hN B m (Finset.mem_filter.mp hB).2.2
    have houtside (B : TreeBandIndex n) (hB : B ∈ removedBands m) : B ∉ Λ :=
      (Finset.mem_filter.mp hB).2.1
    change treeRho n (finiteBandProjection n (removedBands m) (w m)) < _
    rw [treeRho_finiteBandProjection]
    calc
      ∑ B ∈ removedBands m, treeRho n (treeBandProjection n B (w m)) ≤
          ∑ B ∈ removedBands m, (lam B + δ B) := by
        apply Finset.sum_le_sum
        intro B hB
        exact (hRB B hB).le
      _ = (∑ B ∈ removedBands m, lam B) + ∑ B ∈ removedBands m, δ B := by
        rw [← Finset.sum_add_distrib]
      _ < tailBudget + tailBudget :=
        add_lt_add_of_lt_of_le (htail (removedBands m) houtside)
          (hδfinite (removedBands m))
      _ = ε / (4 * M) := by
        dsimp [tailBudget]
        field_simp
        ring
  refine ⟨w', ?_, ?_⟩
  · intro m
    have hroot_nonneg : 0 ≤
        (M * treeRho n (r m)) • treeBasis (TreeNode.root n) := by
      intro t
      change 0 ≤ (M * treeRho n (r m)) * treeBasis (TreeNode.root n) t
      apply mul_nonneg (mul_nonneg hM.le (treeRho_nonneg n (r m)))
      by_cases ht : t = TreeNode.root n <;> simp [treeBasis, ht]
    refine ⟨add_nonneg (hkeep_nonneg m) hroot_nonneg, ?_, ?_⟩
    · calc
        (x m).1 ≤ treeOperator n (w m) := hdom m
        _ = treeOperator n (w m - r m) + treeOperator n (r m) := by
          rw [← treeOperator_add]
          congr 1
          abel
        _ ≤ treeOperator n (w m - r m) +
            (M * treeRho n (r m)) • treeFunction n (TreeNode.root n) := by
          exact add_le_add le_rfl
            (treeOperator_le_root_of_nonneg n (r m) (hr_nonneg m))
        _ = treeOperator n (w' m) := by
          change _ = treeOperator n
            (w m - r m + (M * treeRho n (r m)) • treeBasis (TreeNode.root n))
          rw [treeOperator_add, treeOperator_smul, treeBasis,
            treeOperator_single, one_smul]
    · have hkeep_le : w m - r m ≤ w m := by
        exact sub_le_self _ (hr_nonneg m)
      calc
        treeRho n (w' m) ≤ treeRho n (w m - r m) +
            treeRho n ((M * treeRho n (r m)) • treeBasis (TreeNode.root n)) :=
          treeRho_add_le n _ _
        _ ≤ treeRho n (w m) + M * treeRho n (r m) := by
          apply add_le_add
          · exact treeRho_mono_of_nonneg n (hkeep_nonneg m) hkeep_le
          · rw [treeRho_smul, abs_of_nonneg
              (mul_nonneg hM.le (treeRho_nonneg n (r m)))]
            simp [treeBasis, treeRho, TreeNode.root, TreeNode.level]
        _ < 1 + ε / 2 := by
          have hMr : M * treeRho n (r m) < ε / 4 := by
            calc
              M * treeRho n (r m) < M * (ε / (4 * M)) :=
                mul_lt_mul_of_pos_left (hrho_r m) hM
              _ = ε / 4 := by field_simp
          linarith [hrho m]
  · apply Set.Finite.subset Λ.finite_toSet
    intro B hBrec
    by_contra hBΛ
    have hoccFinite :
        {m | (treeBandProjection n B (w' m)).support.Nonempty}.Finite := by
      apply (Finset.finite_toSet (Finset.range (N B))).subset
      intro m hm
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hmN
      have hNm : N B ≤ m := Nat.le_of_not_gt hmN
      rcases hm with ⟨t, ht⟩
      have htw' : t ∈ (w' m).support ∧ t ∈ treeBandSupport n B := by
        simpa [treeBandProjection] using ht
      have htBand : treeBandOfNode n t = B :=
        treeBandOfNode_eq_of_mem n t B htw'.2
      have htroot : t ≠ TreeNode.root n := by
        intro htr
        have : B = none := by
          rw [← htBand, htr]
          simp [treeBandOfNode]
        exact hBΛ (this ▸ hnoneΛ)
      have hwt_ne : w m t ≠ 0 := by
        intro hzero
        have hrzero : r m t = 0 := by
          by_cases htR : treeBandOfNode n t ∈ removedBands m
          · change finiteBandProjection n (removedBands m) (w m) t = 0
            rw [(finiteBandProjection_apply n (removedBands m) (w m) t).1 htR,
              hzero]
          · change finiteBandProjection n (removedBands m) (w m) t = 0
            rw [(finiteBandProjection_apply n (removedBands m) (w m) t).2 htR]
        have hrootzero : treeBasis (TreeNode.root n) t = 0 := by
          simp [treeBasis, htroot]
        have htne := Finsupp.mem_support_iff.mp htw'.1
        change (w m - r m +
          (M * treeRho n (r m)) • treeBasis (TreeNode.root n)) t ≠ 0 at htne
        simp [Finsupp.add_apply, Finsupp.sub_apply, hzero, hrzero,
          Finsupp.smul_apply, hrootzero, smul_eq_mul] at htne
      have hBbands : B ∈ bandsAt n (w m) := by
        rw [mem_bandsAt_iff, treeBandProjection_support_nonempty_iff]
        exact ⟨t, Finsupp.mem_support_iff.mpr hwt_ne, htBand⟩
      have hBR : B ∈ removedBands m := by
        apply Finset.mem_filter.mpr
        exact ⟨hBbands, hBΛ, hNm⟩
      have hrval : r m t = w m t := by
        change finiteBandProjection n (removedBands m) (w m) t = w m t
        rw [(finiteBandProjection_apply n (removedBands m) (w m) t).1]
        exact htBand ▸ hBR
      have hrootzero : treeBasis (TreeNode.root n) t = 0 := by
        simp [treeBasis, htroot]
      have htne := Finsupp.mem_support_iff.mp htw'.1
      change (w m - r m +
        (M * treeRho n (r m)) • treeBasis (TreeNode.root n)) t ≠ 0 at htne
      simp [Finsupp.add_apply, Finsupp.sub_apply, hrval,
        Finsupp.smul_apply, hrootzero, smul_eq_mul] at htne
    exact hBrec hoccFinite

end OrderClosures
