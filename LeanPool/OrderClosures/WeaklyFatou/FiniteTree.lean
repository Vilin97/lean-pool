/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.WeaklyFatou.Reductions


/-!
# The finite tree

The finite-height tree, its cylinder sets, and the parent-disjointness lemma.
-/

@[expose] public section

namespace OrderClosures

open Set Filter Topology
open scoped NNReal Topology

universe u

/-- Nodes of the finite-height tree `G_n = ⋃_{k ≤ n} ℕ^k`. -/
abbrev TreeNode (n : ℕ) := {t : List ℕ // t.length ≤ n}

namespace TreeNode

/-- Level of a node. -/
abbrev level {n : ℕ} (t : TreeNode n) : ℕ := t.1.length

/-- The root `∅`. -/
def root (n : ℕ) : TreeNode n := ⟨[], by simp⟩

/-- The child `t⌢m`. -/
def child {n : ℕ} (t : TreeNode n) (h : level t < n) (m : ℕ) : TreeNode n :=
  ⟨t.1 ++ [m], by
    simpa [level] using h⟩

/-- The parent map, fixing the root. -/
def parent {n : ℕ} (t : TreeNode n) : TreeNode n :=
  ⟨t.1.dropLast, by
    rw [List.length_dropLast]
    exact (Nat.sub_le _ _).trans t.2⟩

/-- Restriction `t|j`. -/
def restrict {n : ℕ} (t : TreeNode n) (j : ℕ) : TreeNode n :=
  ⟨t.1.take j, by
    rw [List.length_take]
    exact (min_le_right _ _).trans t.2⟩

end TreeNode

/-- Non-terminal nodes `H_n`. -/
abbrev TreeNonterminal (n : ℕ) := {t : TreeNode n // TreeNode.level t < n}

/-- The product space `I_n = ℕ^{H_n}`. -/
abbrev TreeProduct (n : ℕ) := TreeNonterminal n → ℕ

/-- The strict prefix `t|j`, regarded as a non-terminal node. -/
def strictPrefix {n : ℕ} (t : TreeNode n) (j : Fin (TreeNode.level t)) :
    TreeNonterminal n :=
  ⟨TreeNode.restrict t j, by
    calc
      (TreeNode.restrict t j).level ≤ j := List.length_take_le _ _
      _ < TreeNode.level t := j.isLt
      _ ≤ n := t.2⟩

/-- The cylinder `E_t`. -/
def treeCylinder (n : ℕ) (t : TreeNode n) : Set (TreeProduct n) :=
  {α | ∀ j : Fin (TreeNode.level t), α (strictPrefix t j) ≤ t.1.get j}

/-- Characterizes membership in a child cylinder by the parent coordinates
and one new label; used in the cylinder partition proofs. -/
theorem mem_treeCylinder_child_iff
    (n : ℕ) (t : TreeNode n) (ht : TreeNode.level t < n) (m : ℕ)
    (α : TreeProduct n) :
    α ∈ treeCylinder n (TreeNode.child t ht m) ↔
      α ∈ treeCylinder n t ∧ α ⟨t, ht⟩ ≤ m := by
  constructor
  · intro h
    constructor
    · intro j
      let j' : Fin (TreeNode.level (TreeNode.child t ht m)) :=
        ⟨j, by
          simp [TreeNode.level, TreeNode.child]⟩
      have hj := h j'
      have hpref : strictPrefix (TreeNode.child t ht m) j' = strictPrefix t j := by
        apply Subtype.ext
        apply Subtype.ext
        exact List.take_append_of_le_length j.isLt.le
      have hget : (TreeNode.child t ht m).1.get j' = t.1.get j := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact List.getElem_append_left j.isLt
      rw [hpref, hget] at hj
      exact hj
    · let j : Fin (TreeNode.level (TreeNode.child t ht m)) :=
        ⟨TreeNode.level t, by simp [TreeNode.level, TreeNode.child]⟩
      have hj := h j
      have hpref : strictPrefix (TreeNode.child t ht m) j = ⟨t, ht⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        simp [j, strictPrefix, TreeNode.restrict, TreeNode.level, TreeNode.child]
      have hget : (TreeNode.child t ht m).1.get j = m := by
        simp [j, TreeNode.level, TreeNode.child]
      rw [hpref, hget] at hj
      exact hj
  · rintro ⟨h, hlast⟩ j
    by_cases hj : (j : ℕ) < TreeNode.level t
    · let j' : Fin (TreeNode.level t) := ⟨j, hj⟩
      have hprefix := h j'
      have hpref : strictPrefix (TreeNode.child t ht m) j = strictPrefix t j' := by
        apply Subtype.ext
        apply Subtype.ext
        exact List.take_append_of_le_length hj.le
      have hget : (TreeNode.child t ht m).1.get j = t.1.get j' := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact List.getElem_append_left hj
      rw [hpref, hget]
      exact hprefix
    · have hjeq : (j : ℕ) = TreeNode.level t := by
        have hjlt : (j : ℕ) < TreeNode.level t + 1 := by
          simpa [TreeNode.level, TreeNode.child] using j.isLt
        omega
      let jlast : Fin (TreeNode.level (TreeNode.child t ht m)) :=
        ⟨TreeNode.level t, by simp [TreeNode.level, TreeNode.child]⟩
      have hjlast : j = jlast := Fin.ext hjeq
      rw [hjlast]
      have hpref : strictPrefix (TreeNode.child t ht m) jlast = ⟨t, ht⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        simp [jlast, strictPrefix, TreeNode.restrict, TreeNode.level, TreeNode.child]
      have hget : (TreeNode.child t ht m).1.get jlast = m := by
        simp [jlast, TreeNode.level, TreeNode.child]
      rw [hpref, hget]
      exact hlast

/-- Paper Lemma `lem:basic-tree`, part (a). -/
theorem treeCylinder_isClopen (n : ℕ) (t : TreeNode n) :
    IsClopen (treeCylinder n t) := by
  rw [show treeCylinder n t =
      ⋂ j : Fin (TreeNode.level t),
        {α | α (strictPrefix t j) ≤ t.1.get j} by
    ext α
    simp [treeCylinder]]
  apply isClopen_iInter_of_finite
  intro j
  exact (isClopen_discrete {m : ℕ | m ≤ t.1.get j}).preimage
    (continuous_apply (strictPrefix t j))

/-- The characteristic function `s_t = χ_{E_t}`. -/
noncomputable def treeFunction (n : ℕ) (t : TreeNode n) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  BoundedContinuousFunction.indicator (treeCylinder n t) (treeCylinder_isClopen n t)

/-- Evaluates a tree function on its supporting cylinder; used in the exact
basis and tree-operator computations. -/
theorem treeFunction_apply_of_mem (n : ℕ) (t : TreeNode n)
    {α : TreeProduct n} (hα : α ∈ treeCylinder n t) : treeFunction n t α = 1 := by
  classical
  simp [treeFunction, BoundedContinuousFunction.indicator, Set.indicator, hα]

/-- Evaluates a tree function off its supporting cylinder; used to show finite
tree sums vanish outside their cylinder union. -/
theorem treeFunction_apply_of_notMem (n : ℕ) (t : TreeNode n)
    {α : TreeProduct n} (hα : α ∉ treeCylinder n t) : treeFunction n t α = 0 := by
  classical
  simp [treeFunction, BoundedContinuousFunction.indicator, Set.indicator, hα]

/-- BanLat's vector-lattice structure is supplied here for real-valued bounded
continuous functions; all non-proof data comes from Mathlib's pointwise instances. -/
noncomputable instance boundedContinuousFunctionNormedVectorLattice
    (A : Type u) [TopologicalSpace A] :
    NormedVectorLattice (BoundedContinuousFunction A ℝ) where
  smul_le_smul_of_nonneg_left := by
    intro a ha f g h p
    exact mul_le_mul_of_nonneg_left (h p) ha

/-- Paper Lemma `lem:basic-tree`, parts (b) and (c). -/
theorem treeFunction_child_properties
    (n : ℕ) (t : TreeNode n) (ht : TreeNode.level t < n) :
    (∀ m, treeCylinder n (TreeNode.child t ht m) ⊆ treeCylinder n t ∧
      treeFunction n (TreeNode.child t ht m) ≤ treeFunction n t) ∧
    Monotone (fun m ↦ treeFunction n (TreeNode.child t ht m)) ∧
      IsLUB (Set.range fun m ↦ treeFunction n (TreeNode.child t ht m))
        (treeFunction n t) := by
  have hnonneg : ∀ u : TreeNode n, 0 ≤ treeFunction n u := by
    intro u α
    change 0 ≤ treeFunction n u α
    by_cases hα : α ∈ treeCylinder n u
    · rw [treeFunction_apply_of_mem n u hα]
      norm_num
    · rw [treeFunction_apply_of_notMem n u hα]
  have hindicator_mono : ∀ {u v : TreeNode n},
      treeCylinder n u ⊆ treeCylinder n v → treeFunction n u ≤ treeFunction n v := by
    intro u v huv α
    change treeFunction n u α ≤ treeFunction n v α
    by_cases hα : α ∈ treeCylinder n u
    · rw [treeFunction_apply_of_mem n u hα,
        treeFunction_apply_of_mem n v (huv hα)]
    · rw [treeFunction_apply_of_notMem n u hα]
      exact hnonneg v α
  have hsubset : ∀ m,
      treeCylinder n (TreeNode.child t ht m) ⊆ treeCylinder n t := by
    intro m α hα
    exact (mem_treeCylinder_child_iff n t ht m α).mp hα |>.1
  have hle : ∀ m, treeFunction n (TreeNode.child t ht m) ≤ treeFunction n t :=
    fun m ↦ hindicator_mono (hsubset m)
  refine ⟨fun m ↦ ⟨hsubset m, hle m⟩, ?_, ?_⟩
  · intro a b hab
    apply hindicator_mono
    intro α hα
    rcases (mem_treeCylinder_child_iff n t ht a α).mp hα with ⟨hαt, hlast⟩
    exact (mem_treeCylinder_child_iff n t ht b α).mpr ⟨hαt, hlast.trans hab⟩
  · constructor
    · rintro _ ⟨m, rfl⟩
      exact hle m
    · intro g hg α
      change treeFunction n t α ≤ g α
      by_cases hα : α ∈ treeCylinder n t
      · let m := α ⟨t, ht⟩
        have hchild : α ∈ treeCylinder n (TreeNode.child t ht m) :=
          (mem_treeCylinder_child_iff n t ht m α).mpr ⟨hα, le_rfl⟩
        calc
          treeFunction n t α = 1 := treeFunction_apply_of_mem n t hα
          _ = treeFunction n (TreeNode.child t ht m) α :=
            (treeFunction_apply_of_mem n _ hchild).symm
          _ ≤ g α := hg ⟨m, rfl⟩ α
      · rw [treeFunction_apply_of_notMem n t hα]
        exact (hnonneg (TreeNode.child t ht 0) α).trans (hg ⟨0, rfl⟩ α)

/-- Paper Lemma `lem:finite-cover`. -/
theorem treeCylinder_finite_cover
    (n : ℕ) (t : TreeNode n) (F : Finset (TreeNode n))
    (hcover : ∀ α ∈ treeCylinder n t, ∃ u ∈ F, α ∈ treeCylinder n u) :
    ∃ u ∈ F, treeCylinder n t ⊆ treeCylinder n u := by
  classical
  by_contra hconcl
  push Not at hconcl
  let witness : ↥F → TreeProduct n := fun u ↦
    Classical.choose (Set.not_subset.mp (hconcl u.1 u.2))
  have hwitness_mem (u : ↥F) : witness u ∈ treeCylinder n t :=
    (Classical.choose_spec (Set.not_subset.mp (hconcl u.1 u.2))).1
  have hwitness_notMem (u : ↥F) : witness u ∉ treeCylinder n u.1 :=
    (Classical.choose_spec (Set.not_subset.mp (hconcl u.1 u.2))).2
  let α : TreeProduct n := fun q ↦ Finset.univ.sup fun u : ↥F ↦ witness u q
  have hαt : α ∈ treeCylinder n t := by
    intro j
    apply Finset.sup_le
    intro u _
    exact hwitness_mem u j
  obtain ⟨u, huF, hαu⟩ := hcover α hαt
  let uF : ↥F := ⟨u, huF⟩
  have hnot := hwitness_notMem uF
  simp only [treeCylinder, Set.mem_ofPred_eq] at hnot
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  have hle : witness uF (strictPrefix u j) ≤ α (strictPrefix u j) := by
    exact Finset.le_sup (s := Finset.univ)
      (f := fun v : ↥F ↦ witness v (strictPrefix u j)) (Finset.mem_univ uF)
  exact (not_lt_of_ge (hαu j)) (hj.trans_le hle)

/-- Parent-disjointness (`π`-disjointness in the source). -/
def ParentDisjoint {n : ℕ} (A B : Set (TreeNode n)) : Prop :=
  TreeNode.parent '' A ∩ TreeNode.parent '' B = ∅

/-- The finite union of the cylinders indexed by `F`. -/
def finiteCylinderUnion (n : ℕ) (F : Finset (TreeNode n)) : Set (TreeProduct n) :=
  ⋃ t : F, treeCylinder n t.1

/-- The finite supremum of the tree functions, represented by the indicator
of the corresponding finite union. -/
noncomputable def finiteTreeSup (n : ℕ) (F : Finset (TreeNode n)) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  BoundedContinuousFunction.indicator (finiteCylinderUnion n F) (by
    apply isClopen_iUnion_of_finite
    exact fun t ↦ treeCylinder_isClopen n t.1)

/-- The last label of a nonroot node, with a harmless root default; used to
construct coordinates escaping finite cylinder unions. -/
def treeLastLabel {n : ℕ} (t : TreeNode n) : ℕ :=
  if h : 0 < TreeNode.level t then
    t.1.get ⟨TreeNode.level t - 1, Nat.sub_lt h (by omega)⟩ else 0

/-- Identifies the last strict prefix with the parent of a nonroot node; used
when constructing points outside parent-disjoint cylinder families. -/
theorem strictPrefix_last_eq_parent {n : ℕ} (t : TreeNode n)
    (ht : 0 < TreeNode.level t) :
    let j : Fin (TreeNode.level t) :=
      ⟨TreeNode.level t - 1, Nat.sub_lt ht (by omega)⟩
    (strictPrefix t j).1 = TreeNode.parent t ∧ t.1.get j = treeLastLabel t := by
  dsimp
  constructor
  · apply Subtype.ext
    simp [strictPrefix, TreeNode.restrict, TreeNode.parent, TreeNode.level,
      List.dropLast_eq_take]
  · simp only [treeLastLabel, dite_eq_left ht]
    rfl

/-- Records positivity of a finite supremum of tree functions; used in the
least-upper-bound statement for parent-disjoint families. -/
theorem finiteTreeSup_nonneg (n : ℕ) (F : Finset (TreeNode n)) :
    0 ≤ finiteTreeSup n F := by
  intro α
  classical
  by_cases hα : α ∈ finiteCylinderUnion n F <;>
    simp [finiteTreeSup, BoundedContinuousFunction.indicator, Set.indicator, hα]

/-- Shows that a finite tree supremum vanishes outside its cylinder union;
used in the common-lower-bound argument. -/
theorem finiteTreeSup_apply_of_notMem (n : ℕ) (F : Finset (TreeNode n))
    {α : TreeProduct n} (hα : α ∉ finiteCylinderUnion n F) :
    finiteTreeSup n F α = 0 := by
  classical
  simp [finiteTreeSup, BoundedContinuousFunction.indicator, Set.indicator, hα]

/-- Forces a common lower bound to be nonpositive when supports have
parent-disjoint subsequences; reused in both tree and transient-band lemmas. -/
theorem commonLower_le_zero_of_parentDisjoint_subseq
    (n : ℕ) (F : ℕ → Finset (TreeNode n))
    (hF : Pairwise fun i j ↦ ParentDisjoint (F i : Set (TreeNode n))
      (F j : Set (TreeNode n)))
    (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (hroot : ∀ m, TreeNode.root n ∉ F (φ m))
    (g : ℕ → BoundedContinuousFunction (TreeProduct n) ℝ)
    (hgzero : ∀ m α, α ∉ finiteCylinderUnion n (F (φ m)) → g (φ m) α = 0)
    {z : BoundedContinuousFunction (TreeProduct n) ℝ}
    (hz : ∀ m, z ≤ g m) : z ≤ 0 := by
  classical
  intro α
  change z α ≤ 0
  let β : ℕ → TreeProduct n := fun m q ↦
    max (α q) ((F (φ m)).sup fun t ↦
      if TreeNode.parent t = q.1 then treeLastLabel t + 1 else 0)
  have hβoutside : ∀ m, β m ∉ finiteCylinderUnion n (F (φ m)) := by
    intro m hmem
    simp only [finiteCylinderUnion, Set.mem_iUnion] at hmem
    obtain ⟨t, ht⟩ := hmem
    have htF : t.1 ∈ F (φ m) := t.2
    have htroot : t.1 ≠ TreeNode.root n := fun h ↦ hroot m (h ▸ htF)
    have htpos : 0 < TreeNode.level t.1 := Nat.pos_of_ne_zero fun hzero ↦ by
      apply htroot
      apply Subtype.ext
      have hnil : t.1.1 = [] := List.length_eq_zero_iff.mp (by
        simpa [TreeNode.level] using hzero)
      simpa [TreeNode.root] using hnil
    let j : Fin (TreeNode.level t.1) :=
      ⟨TreeNode.level t.1 - 1, Nat.sub_lt htpos (by omega)⟩
    have hj := strictPrefix_last_eq_parent t.1 htpos
    have hsup : treeLastLabel t.1 + 1 ≤
        (F (φ m)).sup fun u ↦
          if TreeNode.parent u = (strictPrefix t.1 j).1 then treeLastLabel u + 1 else 0 := by
      have hle := Finset.le_sup (s := F (φ m))
        (f := fun u ↦ if TreeNode.parent u = (strictPrefix t.1 j).1 then
          treeLastLabel u + 1 else 0) htF
      have hjparent : TreeNode.parent t.1 = (strictPrefix t.1 j).1 := hj.1.symm
      change (if TreeNode.parent t.1 = (strictPrefix t.1 j).1 then
        treeLastLabel t.1 + 1 else 0) ≤ _ at hle
      rw [ite_eq_left hjparent] at hle
      exact hle
    have hlarge : treeLastLabel t.1 + 1 ≤ β m (strictPrefix t.1 j) :=
      hsup.trans (le_max_right _ _)
    have hcyl := ht j
    rw [hj.2] at hcyl
    exact (not_lt_of_ge hcyl) (lt_of_lt_of_le (Nat.lt_succ_self _) hlarge)
  have hβtendsto : Tendsto β atTop (nhds α) := by
    rw [tendsto_pi_nhds]
    intro q
    let bad : Set ℕ := {m | ∃ t ∈ F (φ m), TreeNode.parent t = q.1}
    have hbadsub : bad.Subsingleton := by
      intro i hi j hj
      rcases hi with ⟨ti, hti, hpi⟩
      rcases hj with ⟨tj, htj, hpj⟩
      by_contra hij
      have hindices : φ i ≠ φ j := fun h ↦ hij (hφ h)
      have hdis := hF hindices
      have hqmem : q.1 ∈
          TreeNode.parent '' (F (φ i) : Set (TreeNode n)) ∩
            TreeNode.parent '' (F (φ j) : Set (TreeNode n)) := by
        constructor
        · exact ⟨ti, hti, hpi⟩
        · exact ⟨tj, htj, hpj⟩
      rw [hdis] at hqmem
      exact hqmem
    have hevent : ∀ᶠ m in atTop, m ∉ bad := by
      rw [← Nat.cofinite_eq_atTop]
      exact hbadsub.finite.eventually_cofinite_notMem
    have heq : (fun m ↦ β m q) =ᶠ[atTop] fun _ ↦ α q := by
      filter_upwards [hevent] with m hm
      have hsupzero : (F (φ m)).sup (fun t ↦
          if TreeNode.parent t = q.1 then treeLastLabel t + 1 else 0) = 0 := by
        apply le_antisymm
        · apply Finset.sup_le
          intro t ht
          rw [ite_eq_right]
          intro hparent
          exact hm ⟨t, ht, hparent⟩
        · exact bot_le
      simp [β, hsupzero]
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  have hzβ : ∀ m, z (β m) ≤ 0 := by
    intro m
    have hle := hz (φ m) (β m)
    change z (β m) ≤ g (φ m) (β m) at hle
    rw [hgzero m (β m) (hβoutside m)] at hle
    exact hle
  have hzlim : Tendsto (fun m ↦ z (β m)) atTop (nhds (z α)) :=
    Filter.Tendsto.comp z.continuous.continuousAt hβtendsto
  exact isClosed_Iic.mem_of_tendsto hzlim (Eventually.of_forall hzβ)

/-- Paper Lemma `lem:pi-disjoint`. -/
theorem parentDisjoint_treeFunctions_iInf
    (n : ℕ) (F : ℕ → Finset (TreeNode n))
    (hF : Pairwise fun i j ↦ ParentDisjoint (F i : Set (TreeNode n)) (F j : Set (TreeNode n))) :
    IsGLB (Set.range fun m ↦ finiteTreeSup n (F m)) 0 := by
  constructor
  · rintro _ ⟨m, rfl⟩
    exact finiteTreeSup_nonneg n (F m)
  · intro z hz
    have hzall : ∀ m, z ≤ finiteTreeSup n (F m) := fun m ↦ hz ⟨m, rfl⟩
    by_cases hrootExists : ∃ i, TreeNode.root n ∈ F i
    · obtain ⟨i, hi⟩ := hrootExists
      let φ : ℕ → ℕ := fun m ↦ i + m + 1
      have hφ : Function.Injective φ := by
        intro a b h
        dsimp [φ] at h
        omega
      have hroot : ∀ m, TreeNode.root n ∉ F (φ m) := by
        intro m hm
        have hne : i ≠ φ m := by
          dsimp [φ]
          omega
        have hdis := hF hne
        have hmem : TreeNode.root n ∈
            TreeNode.parent '' (F i : Set (TreeNode n)) ∩
              TreeNode.parent '' (F (φ m) : Set (TreeNode n)) := by
          constructor
          · exact ⟨TreeNode.root n, hi, by rfl⟩
          · exact ⟨TreeNode.root n, hm, by rfl⟩
        rw [hdis] at hmem
        exact hmem
      exact commonLower_le_zero_of_parentDisjoint_subseq n F hF φ hφ hroot
        (fun m ↦ finiteTreeSup n (F m))
        (fun m α hα ↦ finiteTreeSup_apply_of_notMem n _ hα) hzall
    · push Not at hrootExists
      exact commonLower_le_zero_of_parentDisjoint_subseq n F hF id
        Function.injective_id hrootExists (fun m ↦ finiteTreeSup n (F m))
        (fun m α hα ↦ finiteTreeSup_apply_of_notMem n _ hα) hzall

end OrderClosures
