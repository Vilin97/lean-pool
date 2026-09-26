/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.WeaklyFatou.FiniteTree


/-!
# The induced tree seminorm and component lattice
-/

@[expose] public section

namespace OrderClosures

open Set Filter Topology
open scoped NNReal Topology

universe u

/-! ## The induced seminorm -/

/-- `W_n = c₀₀(G_n)`. -/
abbrev TreeCoefficients (n : ℕ) := TreeNode n →₀ ℝ

/-- The basis vector `e_t`. -/
noncomputable def treeBasis {n : ℕ} (t : TreeNode n) : TreeCoefficients n :=
  Finsupp.single t 1

/-- The weighted `ℓ¹` functional `ρ_n`. -/
noncomputable def treeRho (n : ℕ) (w : TreeCoefficients n) : ℝ :=
  w.sum fun t a ↦ (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |a|

/-- The positive operator `T_n`. -/
noncomputable def treeOperator (n : ℕ) (w : TreeCoefficients n) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  w.sum fun t a ↦ a • treeFunction n t

/-- The infimum formula defining `p_n`. -/
noncomputable def treeSeminorm (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ w : TreeCoefficients n,
    0 ≤ w ∧ |x| ≤ treeOperator n w ∧ treeRho n w = r}

/-- Records nonnegativity of the weighted coefficient functional; used in all
seminorm and band-mass estimates. -/
theorem treeRho_nonneg (n : ℕ) (w : TreeCoefficients n) :
    0 ≤ treeRho n w := by
  classical
  exact Finsupp.sum_nonneg' fun t ↦
    mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)

/-- Shows that `treeRho` is invariant under negation; used for symmetry of the
bundled lattice seminorm. -/
theorem treeRho_neg (n : ℕ) (w : TreeCoefficients n) :
    treeRho n (-w) = treeRho n w := by
  classical
  rw [treeRho, treeRho, Finsupp.sum, Finsupp.sum, Finsupp.support_neg]
  simp

/-- Computes `treeRho` under scalar multiplication; used for homogeneity of
the tree seminorm. -/
theorem treeRho_smul (n : ℕ) (a : ℝ) (w : TreeCoefficients n) :
    treeRho n (a • w) = |a| * treeRho n w := by
  classical
  unfold treeRho
  rw [Finsupp.sum_of_support_subset (a • w) Finsupp.support_smul _ (by simp)]
  simp only [Finsupp.sum, Finsupp.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Gives the triangle inequality for `treeRho`; used to prove subadditivity
of the induced seminorm. -/
theorem treeRho_add_le (n : ℕ) (u v : TreeCoefficients n) :
    treeRho n (u + v) ≤ treeRho n u + treeRho n v := by
  classical
  rw [treeRho, treeRho, treeRho]
  rw [Finsupp.sum_of_support_subset (u + v) Finsupp.support_add _ (by simp)]
  rw [Finsupp.sum_of_support_subset u
    (show u.support ⊆ u.support ∪ v.support from Finset.subset_union_left) _ (by simp)]
  rw [Finsupp.sum_of_support_subset v
    (show v.support ⊆ u.support ∪ v.support from Finset.subset_union_right) _ (by simp)]
  simp only [Finsupp.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  simpa [mul_add] using
    (mul_le_mul_of_nonneg_left (abs_add_le (u t) (v t))
      (zpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
        (-(TreeNode.level t : ℤ))))

/-- Shows coefficientwise monotonicity of `treeRho` on the positive cone;
used to compare band projections and trimmed coefficients. -/
theorem treeRho_mono_of_nonneg (n : ℕ) {u v : TreeCoefficients n}
    (hu : 0 ≤ u) (huv : u ≤ v) : treeRho n u ≤ treeRho n v := by
  classical
  have hv : 0 ≤ v := hu.trans huv
  rw [treeRho, treeRho]
  rw [Finsupp.sum_of_support_subset u
    (show u.support ⊆ u.support ∪ v.support from Finset.subset_union_left) _ (by simp)]
  rw [Finsupp.sum_of_support_subset v
    (show v.support ⊆ u.support ∪ v.support from Finset.subset_union_right) _ (by simp)]
  apply Finset.sum_le_sum
  intro t _
  rw [abs_of_nonneg (hu t), abs_of_nonneg (hv t)]
  exact mul_le_mul_of_nonneg_left (huv t) (zpow_nonneg (by norm_num) _)

/-- Computes the tree operator at zero; used in the zero law for the induced
seminorm and generated sublattice. -/
theorem treeOperator_zero (n : ℕ) :
    treeOperator n (0 : TreeCoefficients n) = 0 := by
  simp [treeOperator]

/-- Records additivity of the tree operator; used in seminorm subadditivity
and the moderatedness decomposition. -/
theorem treeOperator_add (n : ℕ) (u v : TreeCoefficients n) :
    treeOperator n (u + v) = treeOperator n u + treeOperator n v := by
  classical
  simp only [treeOperator]
  exact Finsupp.sum_add_index (by simp) (by simp [add_smul])

/-- Records homogeneity of the tree operator; used to scale majorants in the
seminorm and component constructions. -/
theorem treeOperator_smul (n : ℕ) (a : ℝ) (w : TreeCoefficients n) :
    treeOperator n (a • w) = a • treeOperator n w := by
  classical
  simp only [treeOperator]
  rw [Finsupp.sum_smul_index (by simp)]
  change (∑ t ∈ w.support, (a * w t) • treeFunction n t) =
    a • ∑ t ∈ w.support, w t • treeFunction n t
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp [smul_smul]

/-- A coefficientwise positive vector has a positive tree image; used whenever
an operator majorant is treated as a positive component. -/
theorem treeOperator_nonneg (n : ℕ) (w : TreeCoefficients n) (hw : 0 ≤ w) :
    0 ≤ treeOperator n w := by
  classical
  change 0 ≤ w.sum fun t a ↦ a • treeFunction n t
  apply Finsupp.sum_nonneg'
  intro t α
  change 0 ≤ w t * treeFunction n t α
  exact mul_nonneg (hw t) (by
    by_cases h : α ∈ treeCylinder n t <;> simp [treeFunction,
      BoundedContinuousFunction.indicator, Set.indicator, h])

/-- Evaluates the tree operator on a single basis coefficient; used to place
tree functions in the generated component. -/
theorem treeOperator_single (n : ℕ) (t : TreeNode n) (a : ℝ) :
    treeOperator n (Finsupp.single t a) = a • treeFunction n t := by
  simp [treeOperator]

/-- Expands pointwise evaluation of the tree operator as a finite sum; used in
support-vanishing and root estimates. -/
theorem treeOperator_apply (n : ℕ) (w : TreeCoefficients n)
    (α : TreeProduct n) :
    treeOperator n w α = w.sum (fun t a ↦ a * treeFunction n t α) := by
  classical
  rw [treeOperator, Finsupp.sum, Finsupp.sum]
  change (BoundedContinuousFunction.evalCLM ℝ α)
      (∑ t ∈ w.support, w t • treeFunction n t) =
    ∑ t ∈ w.support, w t * treeFunction n t α
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp

/-- Identifies the root tree function with the constant one function; used as
the universal positive order majorant. -/
theorem treeFunction_root (n : ℕ) :
    treeFunction n (TreeNode.root n) = 1 := by
  ext α
  simp [treeFunction, BoundedContinuousFunction.indicator, treeCylinder,
    TreeNode.root, TreeNode.level]

/-- Dominates any continuous function by its uniform norm times the root;
used to prove that the admissible-majorant set is nonempty. -/
theorem abs_le_norm_smul_root (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    |x| ≤ ‖x‖ • treeFunction n (TreeNode.root n) := by
  rw [treeFunction_root]
  intro α
  change |x α| ≤ ‖x‖ * 1
  simpa using x.norm_coe_le_norm α

/-- Supplies a coefficient majorant for every function; needed to define the
infimum in `treeSeminorm`. -/
theorem treeAdmissible_nonempty (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    {r : ℝ | ∃ w : TreeCoefficients n,
      0 ≤ w ∧ |x| ≤ treeOperator n w ∧ treeRho n w = r}.Nonempty := by
  let w : TreeCoefficients n := Finsupp.single (TreeNode.root n) ‖x‖
  refine ⟨treeRho n w, w, ?_, ?_, rfl⟩
  · exact Finsupp.single_nonneg.mpr (norm_nonneg x)
  · rw [treeOperator_single]
    exact abs_le_norm_smul_root n x

/-- Bounds all admissible `treeRho` values below by zero; used to justify
order properties of the defining infimum. -/
theorem treeAdmissible_bddBelow (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    BddBelow {r : ℝ | ∃ w : TreeCoefficients n,
      0 ≤ w ∧ |x| ≤ treeOperator n w ∧ treeRho n w = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨w, _, _, rfl⟩
  exact treeRho_nonneg n w

/-- Proves nonnegativity of `treeSeminorm`; used as a field of the bundled
lattice seminorm. -/
theorem treeSeminorm_nonneg (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    0 ≤ treeSeminorm n x := by
  apply le_csInf (treeAdmissible_nonempty n x)
  rintro r ⟨w, _, _, rfl⟩
  exact treeRho_nonneg n w

/-- Bounds the seminorm by any admissible coefficient majorant; used throughout
the exact-basis and moderatedness estimates. -/
theorem treeSeminorm_le_of_majorant (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) (w : TreeCoefficients n)
    (hw : 0 ≤ w) (hxw : |x| ≤ treeOperator n w) :
    treeSeminorm n x ≤ treeRho n w := by
  exact csInf_le (treeAdmissible_bddBelow n x) ⟨w, hw, hxw, rfl⟩

/-- Evaluates the tree seminorm at zero; used for the zero field of
`treeLatticeSeminorm`. -/
theorem treeSeminorm_zero (n : ℕ) :
    treeSeminorm n (0 : BoundedContinuousFunction (TreeProduct n) ℝ) = 0 := by
  apply le_antisymm
  · simpa [treeRho] using
      (treeSeminorm_le_of_majorant n 0 0 (by simp)
        (by simp [treeOperator_zero]))
  · exact treeSeminorm_nonneg n 0

/-- Approximates the infimum defining `treeSeminorm` by a strict majorant;
used to prove seminorm laws and to select coefficients in `component_moderated`. -/
theorem exists_treeMajorant_lt (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TreeCoefficients n, 0 ≤ w ∧ |x| ≤ treeOperator n w ∧
      treeRho n w < treeSeminorm n x + ε := by
  obtain ⟨r, ⟨w, hw, hxw, hwr⟩, hr⟩ :=
    exists_lt_of_csInf_lt (treeAdmissible_nonempty n x)
      (lt_add_of_pos_right (treeSeminorm n x) hε)
  exact ⟨w, hw, hxw, by simpa [hwr] using hr⟩

/-- Gives the difficult direction of seminorm homogeneity; used together with
rescaling to prove equality in the bundled seminorm. -/
theorem treeSeminorm_smul_le (n : ℕ) (a : ℝ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    treeSeminorm n (a • x) ≤ |a| * treeSeminorm n x := by
  by_cases ha : a = 0
  · subst a
    simpa using (treeSeminorm_zero n).le
  apply le_of_forall_pos_le_add
  intro ε hε
  have habs : 0 < |a| := abs_pos.mpr ha
  obtain ⟨w, hw, hxw, hrho⟩ := exists_treeMajorant_lt n x (div_pos hε habs)
  have hmajor : |a • x| ≤ treeOperator n (|a| • w) := by
    rw [treeOperator_smul]
    intro α
    change |a * x α| ≤ |a| * treeOperator n w α
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hxw α) (abs_nonneg a)
  have hwscale : 0 ≤ |a| • w := by
    intro t
    change 0 ≤ |a| * w t
    exact mul_nonneg (abs_nonneg a) (hw t)
  calc
    treeSeminorm n (a • x) ≤ treeRho n (|a| • w) :=
      treeSeminorm_le_of_majorant n _ _ hwscale hmajor
    _ = |a| * treeRho n w := by rw [treeRho_smul, abs_of_nonneg (abs_nonneg a)]
    _ ≤ |a| * treeSeminorm n x + ε := by
      have := mul_lt_mul_of_pos_left hrho habs
      rw [mul_add, mul_div_cancel₀ _ habs.ne'] at this
      exact this.le

/-- Bounds every tree function in uniform norm; used to control finite tree
operators by their coefficient sums. -/
theorem treeFunction_norm_le_one (n : ℕ) (t : TreeNode n) :
    ‖treeFunction n t‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le zero_le_one]
  intro α
  by_cases h : α ∈ treeCylinder n t
  · rw [treeFunction_apply_of_mem n t h]
    norm_num
  · rw [treeFunction_apply_of_notMem n t h]
    norm_num

/-- Bounds the uniform norm of a tree operator by the absolute coefficient
sum; used in the comparison between uniform and tree norms. -/
theorem treeOperator_norm_le_sum (n : ℕ) (w : TreeCoefficients n) :
    ‖treeOperator n w‖ ≤ ∑ t ∈ w.support, |w t| := by
  classical
  rw [treeOperator, Finsupp.sum]
  calc
    ‖∑ t ∈ w.support, w t • treeFunction n t‖ ≤
        ∑ t ∈ w.support, ‖w t • treeFunction n t‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ w.support, |w t| := by
      apply Finset.sum_le_sum
      intro t _
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (w t), treeFunction_norm_le_one n t]

/-- Controls the unweighted coefficient sum by `treeRho`; combined with the
operator estimate to obtain the norm comparison. -/
theorem treeRho_controls_sum (n : ℕ) (w : TreeCoefficients n) :
    (∑ t ∈ w.support, |w t|) ≤ (2 : ℝ) ^ n * treeRho n w := by
  classical
  rw [treeRho, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hc : (1 : ℝ) ≤
      (2 : ℝ) ^ n * (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    apply one_le_zpow₀ (by norm_num)
    exact sub_nonneg.mpr (by exact_mod_cast t.2)
  nlinarith [abs_nonneg (w t)]

/-- Combines the preceding estimates into the main operator norm bound; used
to prove definiteness and equivalence of the component norm. -/
theorem norm_le_pow_mul_treeRho (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) (w : TreeCoefficients n)
    (hw : 0 ≤ w) (hxw : |x| ≤ treeOperator n w) :
    ‖x‖ ≤ (2 : ℝ) ^ n * treeRho n w := by
  calc
    ‖x‖ ≤ ‖treeOperator n w‖ := by
      apply norm_le_norm_of_abs_le_abs
      simpa [abs_of_nonneg (treeOperator_nonneg n w hw)] using hxw
    _ ≤ ∑ t ∈ w.support, |w t| := treeOperator_norm_le_sum n w
    _ ≤ (2 : ℝ) ^ n * treeRho n w := treeRho_controls_sum n w

/-- Dominates a positive tree operator by its total coefficient mass times the
root; used in the upper norm comparison. -/
theorem treeOperator_le_root_of_nonneg (n : ℕ) (w : TreeCoefficients n)
    (hw : 0 ≤ w) :
    treeOperator n w ≤
      ((2 : ℝ) ^ n * treeRho n w) • treeFunction n (TreeNode.root n) := by
  calc
    treeOperator n w = |treeOperator n w| :=
      (abs_of_nonneg (treeOperator_nonneg n w hw)).symm
    _ ≤ ‖treeOperator n w‖ • treeFunction n (TreeNode.root n) :=
      abs_le_norm_smul_root n (treeOperator n w)
    _ ≤ ((2 : ℝ) ^ n * treeRho n w) • treeFunction n (TreeNode.root n) := by
      intro α
      simpa [treeFunction_root] using
        (treeOperator_norm_le_sum n w).trans (treeRho_controls_sum n w)

/-- Paper Lemma `lem:pn-seminorm`, bundled using BanLat's `LatticeSeminorm`. -/
noncomputable def treeLatticeSeminorm (n : ℕ) :
    LatticeSeminorm (BoundedContinuousFunction (TreeProduct n) ℝ) where
  toFun := treeSeminorm n
  map_zero' := by
    exact treeSeminorm_zero n
  add_le' := by
    intro x y
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u, hu, hxu, hρu⟩ := exists_treeMajorant_lt n x (half_pos hε)
    obtain ⟨v, hv, hyv, hρv⟩ := exists_treeMajorant_lt n y (half_pos hε)
    have hmajor : |x + y| ≤ treeOperator n (u + v) := by
      rw [treeOperator_add]
      exact (abs_add_le x y).trans (add_le_add hxu hyv)
    calc
      treeSeminorm n (x + y) ≤ treeRho n (u + v) :=
        treeSeminorm_le_of_majorant n _ _ (add_nonneg hu hv) hmajor
      _ ≤ treeRho n u + treeRho n v := treeRho_add_le n u v
      _ ≤ treeSeminorm n x + treeSeminorm n y + ε := by linarith
  neg' := by
    intro x
    simp [treeSeminorm]
  smul' := by
    intro a x
    apply le_antisymm
    · exact treeSeminorm_smul_le n a x
    · by_cases ha : a = 0
      · subst a
        simp [treeSeminorm_zero]
      have hinv := treeSeminorm_smul_le n a⁻¹ (a • x)
      have habs : 0 < |a| := abs_pos.mpr ha
      calc
        |a| * treeSeminorm n x =
            |a| * treeSeminorm n (a⁻¹ • (a • x)) := by
              simp [smul_smul, ha]
        _ ≤ |a| * (|a⁻¹| * treeSeminorm n (a • x)) :=
          mul_le_mul_of_nonneg_left hinv habs.le
        _ = treeSeminorm n (a • x) := by
          rw [abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr ha), one_mul]
  monotone_abs' := by
    intro x y hxy
    apply le_csInf (treeAdmissible_nonempty n y)
    rintro r ⟨w, hw, hyw, rfl⟩
    exact treeSeminorm_le_of_majorant n x w hw (hxy.trans hyw)

/-- Paper Lemma `lem:norm-comparison`. -/
theorem treeSeminorm_norm_comparison
    (n : ℕ) (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    treeSeminorm n x ≤ ‖x‖ ∧ ‖x‖ ≤ (2 : ℝ) ^ n * treeSeminorm n x := by
  constructor
  · let w : TreeCoefficients n := Finsupp.single (TreeNode.root n) ‖x‖
    have hw : 0 ≤ w := Finsupp.single_nonneg.mpr (norm_nonneg x)
    have hxw : |x| ≤ treeOperator n w := by
      rw [treeOperator_single]
      exact abs_le_norm_smul_root n x
    calc
      treeSeminorm n x ≤ treeRho n w := treeSeminorm_le_of_majorant n x w hw hxw
      _ = ‖x‖ := by simp [w, treeRho, TreeNode.root, TreeNode.level]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    obtain ⟨w, hw, hxw, hrho⟩ :=
      exists_treeMajorant_lt n x (div_pos hε hpow)
    have hnorm := norm_le_pow_mul_treeRho n x w hw hxw
    have hscaled := mul_lt_mul_of_pos_left hrho hpow
    rw [mul_add, mul_div_cancel₀ _ hpow.ne'] at hscaled
    exact hnorm.trans hscaled.le

/-- Computes the level of a strict prefix; used to compare nodes from nested
tree cylinders in the exact-basis proof. -/
theorem level_strictPrefix {n : ℕ} (t : TreeNode n)
    (j : Fin (TreeNode.level t)) :
    TreeNode.level (strictPrefix t j).1 = j := by
  simp [strictPrefix, TreeNode.restrict, TreeNode.level]

/-- Shows that inclusion of nonempty tree cylinders forces the corresponding
level inequality; used to isolate the maximal-weight basis term. -/
theorem level_le_of_treeCylinder_subset {n : ℕ} {t u : TreeNode n}
    (hsub : treeCylinder n t ⊆ treeCylinder n u) :
    TreeNode.level u ≤ TreeNode.level t := by
  classical
  by_contra h
  have hlt : TreeNode.level t < TreeNode.level u := Nat.lt_of_not_ge h
  let j : Fin (TreeNode.level u) := ⟨TreeNode.level t, hlt⟩
  let q : TreeNonterminal n := strictPrefix u j
  let α : TreeProduct n := fun r ↦ if r = q then u.1.get j + 1 else 0
  have hαt : α ∈ treeCylinder n t := by
    intro k
    have hne : strictPrefix t k ≠ q := by
      intro heq
      have hlevel := congrArg (fun r : TreeNonterminal n ↦ TreeNode.level r.1) heq
      change TreeNode.level (strictPrefix t k).1 = TreeNode.level q.1 at hlevel
      rw [level_strictPrefix t k, show TreeNode.level q.1 = j by
        exact level_strictPrefix u j] at hlevel
      exact (Nat.ne_of_lt k.isLt) hlevel
    simp [α, hne]
  have hαu := hsub hαt j
  simp [α, q] at hαu

/-- Records positivity of every tree function; used for lattice estimates and
for the positive terminal family in the component construction. -/
theorem treeFunction_nonneg (n : ℕ) (t : TreeNode n) :
    0 ≤ treeFunction n t := by
  intro α
  change (0 : ℝ) ≤ treeFunction n t α
  by_cases hα : α ∈ treeCylinder n t
  · rw [treeFunction_apply_of_mem n t hα]
    norm_num
  · rw [treeFunction_apply_of_notMem n t hα]

/-- Paper Lemma `lem:exact-basis`. -/
theorem treeSeminorm_exact_basis (n : ℕ) (t : TreeNode n) :
    (∀ w : TreeCoefficients n, 0 ≤ w → treeFunction n t ≤ treeOperator n w →
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) ≤ treeRho n w) ∧
    treeSeminorm n (treeFunction n t) =
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by
  classical
  let a : ℝ := (2 : ℝ) ^ (-(TreeNode.level t : ℤ))
  have ha : 0 < a := zpow_pos (by norm_num) _
  have hlower : ∀ w : TreeCoefficients n, 0 ≤ w →
      treeFunction n t ≤ treeOperator n w → a ≤ treeRho n w := by
    intro w hw hdom
    let C := w.support.filter fun u ↦ treeCylinder n t ⊆ treeCylinder n u
    let N := w.support.filter fun u ↦ ¬treeCylinder n t ⊆ treeCylinder n u
    have hnotcover : ¬(∀ α ∈ treeCylinder n t,
        ∃ u ∈ N, α ∈ treeCylinder n u) := by
      intro hcover
      obtain ⟨u, huN, hsub⟩ := treeCylinder_finite_cover n t N hcover
      exact (Finset.mem_filter.mp huN).2 hsub
    push Not at hnotcover
    obtain ⟨α, hαt, hαN⟩ := hnotcover
    have hoperator : treeOperator n w α = ∑ u ∈ C, w u := by
      rw [treeOperator_apply, Finsupp.sum]
      change (∑ u ∈ w.support, w u * treeFunction n u α) = ∑ u ∈ C, w u
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hsub : treeCylinder n t ⊆ treeCylinder n u
      · rw [ite_eq_left hsub, treeFunction_apply_of_mem n u (hsub hαt), mul_one]
      · have huN : u ∈ N := Finset.mem_filter.mpr ⟨hu, hsub⟩
        rw [ite_eq_right hsub, treeFunction_apply_of_notMem n u (hαN u huN), mul_zero]
    have hsum : 1 ≤ ∑ u ∈ C, w u := by
      have hdomα := hdom α
      change treeFunction n t α ≤ treeOperator n w α at hdomα
      rw [treeFunction_apply_of_mem n t hαt, hoperator] at hdomα
      exact hdomα
    calc
      a ≤ a * ∑ u ∈ C, w u := by nlinarith
      _ = ∑ u ∈ C, a * w u := by rw [Finset.mul_sum]
      _ ≤ ∑ u ∈ C,
          (2 : ℝ) ^ (-(TreeNode.level u : ℤ)) * |w u| := by
        apply Finset.sum_le_sum
        intro u huC
        have hsub := (Finset.mem_filter.mp huC).2
        have hlevel := level_le_of_treeCylinder_subset hsub
        have hweight : a ≤ (2 : ℝ) ^ (-(TreeNode.level u : ℤ)) := by
          apply zpow_le_zpow_right₀ (by norm_num)
          exact neg_le_neg (by exact_mod_cast hlevel)
        rw [abs_of_nonneg (hw u)]
        exact mul_le_mul_of_nonneg_right hweight (hw u)
      _ ≤ ∑ u ∈ w.support,
          (2 : ℝ) ^ (-(TreeNode.level u : ℤ)) * |w u| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro u _ _
        exact mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)
      _ = treeRho n w := by rw [treeRho, Finsupp.sum]
  refine ⟨hlower, ?_⟩
  apply le_antisymm
  · let w : TreeCoefficients n := treeBasis t
    have hw : 0 ≤ w := by simp [w, treeBasis]
    have hmajor : |treeFunction n t| ≤ treeOperator n w := by
      rw [abs_of_nonneg (treeFunction_nonneg n t)]
      change treeFunction n t ≤ treeOperator n (treeBasis t)
      rw [treeBasis, treeOperator_single, one_smul]
    calc
      treeSeminorm n (treeFunction n t) ≤ treeRho n w :=
        treeSeminorm_le_of_majorant n _ w hw hmajor
      _ = a := by simp [w, treeBasis, treeRho, a]
  · apply le_csInf (treeAdmissible_nonempty n (treeFunction n t))
    rintro r ⟨w, hw, hmajor, rfl⟩
    apply hlower w hw
    simpa [abs_of_nonneg (treeFunction_nonneg n t)] using hmajor

/-- The closed vector sublattice generated by the tree functions. -/
noncomputable def treeSublattice (n : ℕ) :
    VectorSublattice (BoundedContinuousFunction (TreeProduct n) ℝ) :=
  (VectorSublattice.generated (Set.range (treeFunction n))).topologicalClosure

/-- Places every finitely supported tree operator in the generated closed
sublattice; used to turn coefficient majorants into component elements. -/
theorem treeOperator_mem_treeSublattice (n : ℕ) (w : TreeCoefficients n) :
    treeOperator n w ∈ treeSublattice n := by
  classical
  apply subset_closure
  change treeOperator n w ∈
    VectorSublattice.generated (Set.range (treeFunction n))
  rw [treeOperator, Finsupp.sum]
  apply Submodule.sum_mem
  intro t ht
  exact (VectorSublattice.generated (Set.range (treeFunction n))).toSubmodule.smul_mem
    _ (VectorSublattice.subset_generated _ ⟨t, rfl⟩)

/-- The component space `X_n`, using the underlying submodule carrier. -/
abbrev TreeComponent (n : ℕ) := ↥(treeSublattice n).toSubmodule

/-- Pointwise lattice operations on the component subspace. -/
noncomputable instance treeComponentLattice (n : ℕ) : Lattice (TreeComponent n) where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ hxy hyz ↦ hxy.trans hyz
  le_antisymm := fun x y hxy hyx ↦ Subtype.ext (le_antisymm hxy hyx)
  sup := fun x y ↦ ⟨x.1 ⊔ y.1, (treeSublattice n).sup_mem x.2 y.2⟩
  le_sup_left := fun _ _ ↦ le_sup_left
  le_sup_right := fun _ _ ↦ le_sup_right
  sup_le := fun _ _ _ hx hz ↦ sup_le hx hz
  inf := fun x y ↦ ⟨x.1 ⊓ y.1, (treeSublattice n).inf_mem x.2 y.2⟩
  inf_le_left := fun _ _ ↦ inf_le_left
  inf_le_right := fun _ _ ↦ inf_le_right
  le_inf := fun _ _ _ hx hz ↦ le_inf hx hz

/-- Compatibility of the inherited addition with the pointwise order. -/
instance treeComponentIsOrderedAddMonoid (n : ℕ) :
    IsOrderedAddMonoid (TreeComponent n) where
  add_le_add_left a b hab c := by
    intro p
    simpa [add_comm] using add_le_add_right (hab p) (c.1 p)

/-- The component subspace is a real vector lattice. -/
noncomputable instance treeComponentVectorLattice (n : ℕ) :
    VectorLattice (TreeComponent n) where
  smul_le_smul_of_nonneg_left := by
    intro a ha x y hxy
    exact smul_le_smul_of_nonneg_left hxy ha

/-- The norm `p_n` restricted to `X_n`. -/
noncomputable def componentLatticeNorm (n : ℕ) : PaperLatticeNorm (TreeComponent n) where
  toFun := fun x ↦ treeSeminorm n x.1
  nonneg := by
    intro x
    exact apply_nonneg (treeLatticeSeminorm n).toSeminorm x.1
  eq_zero_iff := by
    intro x
    constructor
    · intro hx
      apply Subtype.ext
      apply norm_eq_zero.mp
      have hle := (treeSeminorm_norm_comparison n x.1).2
      rw [hx, mul_zero] at hle
      exact le_antisymm hle (norm_nonneg _)
    · rintro rfl
      exact map_zero (treeLatticeSeminorm n).toSeminorm
  add_le := by
    intro x y
    exact map_add_le_add (treeLatticeSeminorm n).toSeminorm x.1 y.1
  smul := by
    intro a x
    rw [← Real.norm_eq_abs]
    exact map_smul_eq_mul (treeLatticeSeminorm n).toSeminorm a x.1
  solid := by
    intro x y hxy
    exact (treeLatticeSeminorm n).monotone_abs' hxy

/-- The constant function `1`, as an element of `X_n`. -/
noncomputable def componentRoot (n : ℕ) : TreeComponent n :=
  ⟨treeFunction n (TreeNode.root n), by
    change treeFunction n (TreeNode.root n) ∈
      closure (VectorSublattice.generated (Set.range (treeFunction n)) :
        Set (BoundedContinuousFunction (TreeProduct n) ℝ))
    apply subset_closure
    exact VectorSublattice.subset_generated _ ⟨TreeNode.root n, rfl⟩⟩

/-- Any tree function, viewed in the generated component. -/
noncomputable def componentTreeFunction (n : ℕ) (t : TreeNode n) : TreeComponent n :=
  ⟨treeFunction n t, by
    change treeFunction n t ∈
      closure (VectorSublattice.generated (Set.range (treeFunction n)) :
        Set (BoundedContinuousFunction (TreeProduct n) ℝ))
    apply subset_closure
    exact VectorSublattice.subset_generated _ ⟨t, rfl⟩⟩

/-- Paper Corollary `cor:Yn-basic`. -/
theorem component_basic (n : ℕ) :
    TopologicalSpace.IsSeparable (Set.univ : Set (TreeComponent n)) ∧
      IsCompleteFor (componentLatticeNorm n) ∧
      componentLatticeNorm n (componentRoot n) = 1 ∧
      (∀ t : TreeNode n, TreeNode.level t = n →
        componentLatticeNorm n (componentTreeFunction n t) =
          (2 : ℝ) ^ (-(n : ℤ))) := by
  have hseparable : TopologicalSpace.IsSeparable
      (Set.univ : Set (TreeComponent n)) := by
    let : Countable (TreeNode n) := by
      unfold TreeNode
      infer_instance
    let : TopologicalSpace.SeparableSpace (TreeComponent n) :=
      VectorSublattice.separableSpace_topologicalClosure_generated_of_countable
        (Set.countable_range (treeFunction n))
    exact TopologicalSpace.isSeparable_univ_iff.mpr inferInstance
  have hcomplete : IsCompleteFor (componentLatticeNorm n) := by
    intro f hf
    have hnormCauchy : CauchySeq (fun m ↦ (f m).1) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
      obtain ⟨N, hN⟩ := hf (ε / (2 : ℝ) ^ n) (div_pos hε hpow)
      refine ⟨N, fun m hm k hk ↦ ?_⟩
      have hp := hN m hm k hk
      have hnorm := (treeSeminorm_norm_comparison n ((f m).1 - (f k).1)).2
      rw [dist_eq_norm_sub]
      change treeSeminorm n ((f m).1 - (f k).1) < ε / (2 : ℝ) ^ n at hp
      have hscaled := mul_lt_mul_of_pos_left hp hpow
      rw [mul_div_cancel₀ _ hpow.ne'] at hscaled
      exact hnorm.trans_lt hscaled
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hnormCauchy
    have hymem : y ∈ treeSublattice n := by
      apply isClosed_closure.mem_of_tendsto hy
      exact Eventually.of_forall fun m ↦ (f m).2
    let z : TreeComponent n := ⟨y, hymem⟩
    refine ⟨z, ?_⟩
    rw [Metric.tendsto_atTop] at hy
    intro ε hε
    obtain ⟨N, hN⟩ := hy ε hε
    refine ⟨N, fun m hm ↦ ?_⟩
    have hp := (treeSeminorm_norm_comparison n ((f m).1 - y)).1
    have hdist := hN m hm
    rw [dist_eq_norm_sub] at hdist
    change treeSeminorm n ((f m).1 - y) < ε
    exact hp.trans_lt hdist
  refine ⟨hseparable, hcomplete, ?_, ?_⟩
  · change treeSeminorm n (treeFunction n (TreeNode.root n)) = 1
    simpa [TreeNode.root, TreeNode.level] using
      (treeSeminorm_exact_basis n (TreeNode.root n)).2
  · intro t ht
    change treeSeminorm n (treeFunction n t) = (2 : ℝ) ^ (-(n : ℤ))
    simpa [ht] using (treeSeminorm_exact_basis n t).2

end OrderClosures
