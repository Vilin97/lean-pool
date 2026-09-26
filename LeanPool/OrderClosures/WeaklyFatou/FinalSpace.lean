/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.WeaklyFatou.Moderated


/-!
# Component adherence and the final `c₀`-sum
-/

@[expose] public section

namespace OrderClosures

open Set Filter Topology
open scoped NNReal Topology

universe u

/-! ## Component spaces and the final `c₀`-sum -/

/-- Terminal tree functions `L_n`. -/
def terminalTreeFunctions (n : ℕ) : Set (BoundedContinuousFunction (TreeProduct n) ℝ) :=
  treeFunction n '' {t : TreeNode n | TreeNode.level t = n}

/-- Paper Proposition `prop:component`. -/
theorem component_large_iterated_adherence (n : ℕ) :
    TopologicalSpace.IsSeparable (Set.univ : Set (TreeComponent n)) ∧
      IsCompleteFor (componentLatticeNorm n) ∧
      HasWeakFatouProperty (componentLatticeNorm n) 2 ∧
      ((2 : ℝ) ^ n • componentRoot n) ∈
        iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) n ∧
      componentLatticeNorm n ((2 : ℝ) ^ n • componentRoot n) = (2 : ℝ) ^ n := by
  have hiter : ∀ k : ℕ, ∀ t : TreeNode n, TreeNode.level t + k = n →
      ((2 : ℝ) ^ n • componentTreeFunction n t) ∈
        iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k := by
    intro k
    induction k with
    | zero =>
        intro t ht
        have hlevel : TreeNode.level t = n := by omega
        change componentLatticeNorm n ((2 : ℝ) ^ n • componentTreeFunction n t) ≤ 1
        rw [(componentLatticeNorm n).smul, abs_of_pos (pow_pos (by norm_num) n),
          (component_basic n).2.2.2 t hlevel]
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
        norm_num
    | succ k ih =>
        intro t ht
        have ht_nonterminal : TreeNode.level t < n := by omega
        let f : ℕ → TreeComponent n := fun m ↦
          (2 : ℝ) ^ n • componentTreeFunction n (TreeNode.child t ht_nonterminal m)
        have hf : ∀ m, f m ∈
            iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k := by
          intro m
          apply ih
          have hlevelchild : TreeNode.level (TreeNode.child t ht_nonterminal m) =
              TreeNode.level t + 1 := by simp [TreeNode.child, TreeNode.level]
          rw [hlevelchild]
          omega
        have hchild := treeFunction_child_properties n t ht_nonterminal
        have hmono : Monotone
            (fun m ↦ componentTreeFunction n (TreeNode.child t ht_nonterminal m)) := by
          intro a b hab
          exact hchild.2.1 hab
        have hlub : IsLUB
            (Set.range fun m ↦ componentTreeFunction n
              (TreeNode.child t ht_nonterminal m)) (componentTreeFunction n t) := by
          constructor
          · rintro _ ⟨m, rfl⟩
            exact hchild.1 m |>.2
          · intro z hz
            change treeFunction n t ≤ z.1
            apply hchild.2.2.2
            rintro _ ⟨m, rfl⟩
            exact hz ⟨m, rfl⟩
        change ((2 : ℝ) ^ n • componentTreeFunction n t) ∈ orderAdherence
          (iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k)
        refine ⟨ℕ, inferInstance, inferInstance, inferInstance, f, hf, ?_⟩
        simpa [f] using
          (orderConvergesTo_of_monotone_isLUB hmono hlub).smul ((2 : ℝ) ^ n)
  have hroot : componentTreeFunction n (TreeNode.root n) = componentRoot n := rfl
  have hmembership : ((2 : ℝ) ^ n • componentRoot n) ∈
      iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) n := by
    rw [← hroot]
    apply hiter n (TreeNode.root n)
    simp [TreeNode.root, TreeNode.level]
  have hnorm : componentLatticeNorm n ((2 : ℝ) ^ n • componentRoot n) =
      (2 : ℝ) ^ n := by
    rw [(componentLatticeNorm n).smul, abs_of_pos (pow_pos (by norm_num) n),
      (component_basic n).2.2.1, mul_one]
  exact ⟨(component_basic n).1, (component_basic n).2.1,
    (component_weakFatou n).2, hmembership, hnorm⟩

/-- The ambient product of all component spaces. -/
abbrev ComponentProduct := ∀ n : ℕ, TreeComponent n

/-- The usual `c₀` condition for the component norms. -/
def componentVanishes (x : ComponentProduct) : Prop :=
  Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0)

/-- The concrete `c₀`-sum as a vector sublattice of the component product. -/
noncomputable def componentC0Sublattice : VectorSublattice ComponentProduct where
  carrier := {x | componentVanishes x}
  zero_mem' := by
    change Tendsto (fun n ↦ componentLatticeNorm n (0 : TreeComponent n)) atTop (nhds 0)
    have hzero : (fun n ↦ componentLatticeNorm n (0 : TreeComponent n)) =
        fun _ ↦ 0 := by
      funext n
      exact (componentLatticeNorm n).eq_zero_iff 0 |>.2 rfl
    rw [hzero]
    exact tendsto_const_nhds
  add_mem' := by
    intro x y hx hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0) at hx
    change Tendsto (fun n ↦ componentLatticeNorm n (y n)) atTop (nhds 0) at hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n + y n)) atTop (nhds 0)
    apply squeeze_zero
    · exact fun n ↦ (componentLatticeNorm n).nonneg _
    · exact fun n ↦ (componentLatticeNorm n).add_le _ _
    · simpa using hx.add hy
  smul_mem' := by
    intro a x hx
    change Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0) at hx
    change Tendsto (fun n ↦ componentLatticeNorm n (a • x n)) atTop (nhds 0)
    have heq : (fun n ↦ componentLatticeNorm n (a • x n)) =
        fun n ↦ |a| * componentLatticeNorm n (x n) := by
      funext n
      exact (componentLatticeNorm n).smul a (x n)
    rw [heq]
    simpa using hx.const_mul |a|
  sup_mem' := by
    intro x y hx hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0) at hx
    change Tendsto (fun n ↦ componentLatticeNorm n (y n)) atTop (nhds 0) at hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n ⊔ y n)) atTop (nhds 0)
    apply squeeze_zero
    · exact fun n ↦ (componentLatticeNorm n).nonneg _
    · intro n
      have habsx : componentLatticeNorm n |x n| = componentLatticeNorm n (x n) := by
        apply le_antisymm
        · exact (componentLatticeNorm n).solid (by simp)
        · exact (componentLatticeNorm n).solid (by simp)
      have habsy : componentLatticeNorm n |y n| = componentLatticeNorm n (y n) := by
        apply le_antisymm
        · exact (componentLatticeNorm n).solid (by simp)
        · exact (componentLatticeNorm n).solid (by simp)
      calc
        componentLatticeNorm n (x n ⊔ y n) ≤
            componentLatticeNorm n (|x n| + |y n|) :=
          (componentLatticeNorm n).solid (by
            have hsum0 : (0 : TreeComponent n) ≤ |x n| + |y n| :=
              add_nonneg (abs_nonneg _) (abs_nonneg _)
            rw [abs_of_nonneg hsum0]
            apply abs_le'.mpr
            constructor
            · exact sup_le ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
                ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
            · exact (neg_le_neg (le_sup_left : x n ≤ x n ⊔ y n)).trans
                ((neg_le_abs _).trans (le_add_of_nonneg_right (abs_nonneg _))))
        _ ≤ componentLatticeNorm n |x n| + componentLatticeNorm n |y n| :=
          (componentLatticeNorm n).add_le _ _
        _ = componentLatticeNorm n (x n) + componentLatticeNorm n (y n) := by
          rw [habsx, habsy]
    · simpa using hx.add hy

/-- The final space `X = c₀(X_n)`, using the underlying submodule carrier. -/
abbrev FinalSpace := ↥componentC0Sublattice.toSubmodule

/-- Inclusion of one component as a coordinate band of the final `c₀`-sum. -/
noncomputable def finalCoordinateEmbedding (n : ℕ) (z : TreeComponent n) : FinalSpace :=
  ⟨fun m ↦ if h : m = n then h.symm ▸ z else 0, by
    change Tendsto
      (fun m ↦ componentLatticeNorm m (if h : m = n then h.symm ▸ z else 0))
      atTop (nhds 0)
    have heq : (fun m ↦ componentLatticeNorm m
        (if h : m = n then h.symm ▸ z else 0)) =ᶠ[atTop] fun _ ↦ 0 := by
      filter_upwards [eventually_gt_atTop n] with m hm
      rw [dite_eq_right hm.ne']
      exact (componentLatticeNorm m).eq_zero_iff _ |>.2 rfl
    exact (tendsto_congr' heq).2 tendsto_const_nhds⟩

@[simp] private theorem finalCoordinateEmbedding_same (n : ℕ) (z : TreeComponent n) :
    (finalCoordinateEmbedding n z).1 n = z := by
  simp [finalCoordinateEmbedding]

/-- Evaluates a single-coordinate embedding away from its chosen coordinate;
used in the final lattice and convergence calculations. -/
theorem finalCoordinateEmbedding_ne (n m : ℕ) (h : m ≠ n)
    (z : TreeComponent n) : (finalCoordinateEmbedding n z).1 m = 0 := by
  simp [finalCoordinateEmbedding, h]

/-- Pointwise lattice operations on the final `c₀`-sum. -/
noncomputable instance finalSpaceLattice : Lattice FinalSpace where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ hxy hyz ↦ hxy.trans hyz
  le_antisymm := fun x y hxy hyx ↦ Subtype.ext (le_antisymm hxy hyx)
  sup := fun x y ↦ ⟨x.1 ⊔ y.1, componentC0Sublattice.sup_mem x.2 y.2⟩
  le_sup_left := fun _ _ ↦ le_sup_left
  le_sup_right := fun _ _ ↦ le_sup_right
  sup_le := fun _ _ _ hx hz ↦ sup_le hx hz
  inf := fun x y ↦ ⟨x.1 ⊓ y.1, componentC0Sublattice.inf_mem x.2 y.2⟩
  inf_le_left := fun _ _ ↦ inf_le_left
  inf_le_right := fun _ _ ↦ inf_le_right
  le_inf := fun _ _ _ hx hz ↦ le_inf hx hz

/-- Compatibility of addition and order on the final space. -/
instance finalSpaceIsOrderedAddMonoid : IsOrderedAddMonoid FinalSpace where
  add_le_add_left a b hab c := by
    intro n
    simpa [add_comm] using add_le_add_right (hab n) (c.1 n)

/-- The final `c₀`-sum is a real vector lattice. -/
noncomputable instance finalSpaceVectorLattice : VectorLattice FinalSpace where
  smul_le_smul_of_nonneg_left := by
    intro a ha x y hxy n
    exact smul_le_smul_of_nonneg_left (hxy n) ha

/-- The supremum norm on the final `c₀`-sum. -/
noncomputable def finalNormValue (x : FinalSpace) : ℝ :=
  sSup (Set.range fun n ↦ componentLatticeNorm n (x.1 n))

/-- Records boundedness of the component norms of a `c₀` vector; needed to
justify the supremum defining `finalNormValue`. -/
theorem finalNormValue_bddAbove (x : FinalSpace) :
    BddAbove (Set.range fun n ↦ componentLatticeNorm n (x.1 n)) :=
  x.2.bddAbove_range

/-- Bounds each component norm by the final supremum norm; used in all norm
laws and coordinatewise estimates for the final space. -/
theorem componentNorm_le_finalNormValue (x : FinalSpace) (n : ℕ) :
    componentLatticeNorm n (x.1 n) ≤ finalNormValue x := by
  exact le_csSup (finalNormValue_bddAbove x) ⟨n, rfl⟩

/-- The final lattice norm, with all its laws exposed as proof obligations. -/
noncomputable def finalLatticeNorm : PaperLatticeNorm FinalSpace where
  toFun := finalNormValue
  nonneg := by
    intro x
    exact ((componentLatticeNorm 0).nonneg _).trans
      (componentNorm_le_finalNormValue x 0)
  eq_zero_iff := by
    intro x
    constructor
    · intro hx
      apply Subtype.ext
      funext n
      apply (componentLatticeNorm n).eq_zero_iff (x.1 n) |>.1
      apply le_antisymm
      · simpa [hx] using componentNorm_le_finalNormValue x n
      · exact (componentLatticeNorm n).nonneg _
    · rintro rfl
      unfold finalNormValue
      have hzero : (fun n ↦ componentLatticeNorm n ((0 : FinalSpace).1 n)) =
          fun _ ↦ 0 := by
        funext n
        apply (componentLatticeNorm n).eq_zero_iff _ |>.2
        rfl
      rw [hzero]
      simp
  add_le := by
    intro x y
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    calc
      componentLatticeNorm n ((x + y).1 n) ≤
          componentLatticeNorm n (x.1 n) + componentLatticeNorm n (y.1 n) := by
        simpa using (componentLatticeNorm n).add_le (x.1 n) (y.1 n)
      _ ≤ finalNormValue x + finalNormValue y :=
        add_le_add (componentNorm_le_finalNormValue x n)
          (componentNorm_le_finalNormValue y n)
  smul := by
    intro a x
    unfold finalNormValue
    simp_rw [show ∀ n, componentLatticeNorm n ((a • x).1 n) =
        |a| * componentLatticeNorm n (x.1 n) by
      intro n
      simpa using (componentLatticeNorm n).smul a (x.1 n)]
    exact
      (Real.smul_iSup_of_nonneg (abs_nonneg a)
        (fun n ↦ componentLatticeNorm n (x.1 n))).symm
  solid := by
    intro x y hxy
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    exact ((componentLatticeNorm n).solid (hxy n)).trans
      (componentNorm_le_finalNormValue y n)

/-- Paper Lemma `lem:c0-weak-fatou`. -/
theorem finalSpace_weakFatou :
    IsCompleteFor finalLatticeNorm ∧ HasWeakFatouProperty finalLatticeNorm 2 := by
  have hcomplete : IsCompleteFor finalLatticeNorm := by
    intro f hf
    have hcoordCauchy (k : ℕ) :
        ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ q ≥ N,
          componentLatticeNorm k ((f m).1 k - (f q).1 k) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hf ε hε
      refine ⟨N, fun m hm q hq ↦ ?_⟩
      exact (componentNorm_le_finalNormValue (f m - f q) k).trans_lt
        (hN m hm q hq)
    choose x hx using fun k ↦ (component_basic k).2.1 (fun m ↦ (f m).1 k) (hcoordCauchy k)
    have hxVanishes : componentVanishes x := by
      change Tendsto (fun k ↦ componentLatticeNorm k (x k)) atTop (nhds 0)
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
      obtain ⟨N, hN⟩ := hf (ε / 3) hthird
      have hfN : Tendsto (fun k ↦ componentLatticeNorm k ((f N).1 k))
          atTop (nhds 0) := (f N).2
      rw [Metric.tendsto_atTop] at hfN
      obtain ⟨K, hK⟩ := hfN (ε / 3) hthird
      refine ⟨K, fun k hk ↦ ?_⟩
      obtain ⟨L, hL⟩ := hx k (ε / 3) hthird
      let m := max N L
      have hmN : N ≤ m := le_max_left _ _
      have hmL : L ≤ m := le_max_right _ _
      have hmx : componentLatticeNorm k ((f m).1 k - x k) < ε / 3 := hL m hmL
      have hfmN : componentLatticeNorm k ((f m).1 k - (f N).1 k) < ε / 3 := by
        exact (componentNorm_le_finalNormValue (f m - f N) k).trans_lt (hN m hmN N le_rfl)
      have hfNk : componentLatticeNorm k ((f N).1 k) < ε / 3 := by
        have := hK k hk
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ((componentLatticeNorm k).nonneg _)] at this
        exact this
      have hneg : componentLatticeNorm k (x k - (f m).1 k) =
          componentLatticeNorm k ((f m).1 k - x k) := by
        rw [show x k - (f m).1 k = -((f m).1 k - x k) by abel,
          show -((f m).1 k - x k) = (-1 : ℝ) • ((f m).1 k - x k) by simp,
          (componentLatticeNorm k).smul]
        norm_num
      have hxbound : componentLatticeNorm k (x k) < ε := by
        calc
          componentLatticeNorm k (x k) =
              componentLatticeNorm k ((x k - (f m).1 k) +
                (((f m).1 k - (f N).1 k) + (f N).1 k)) := by
            congr 1
            abel
          _ ≤ componentLatticeNorm k (x k - (f m).1 k) +
              componentLatticeNorm k (((f m).1 k - (f N).1 k) + (f N).1 k) :=
            (componentLatticeNorm k).add_le _ _
          _ ≤ componentLatticeNorm k (x k - (f m).1 k) +
              (componentLatticeNorm k ((f m).1 k - (f N).1 k) +
                componentLatticeNorm k ((f N).1 k)) :=
            add_le_add le_rfl ((componentLatticeNorm k).add_le _ _)
          _ < ε := by rw [hneg]; linarith
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ((componentLatticeNorm k).nonneg _)]
      exact hxbound
    let x₀ : FinalSpace := ⟨x, hxVanishes⟩
    refine ⟨x₀, ?_⟩
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨N, hN⟩ := hf (ε / 2) hhalf
    refine ⟨N, fun q hq ↦ ?_⟩
    have hcoord (k : ℕ) :
        componentLatticeNorm k ((f q).1 k - x k) ≤ ε / 2 := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      obtain ⟨L, hL⟩ := hx k δ hδ
      let m := max N L
      have hmN : N ≤ m := le_max_left _ _
      have hmL : L ≤ m := le_max_right _ _
      calc
        componentLatticeNorm k ((f q).1 k - x k) =
            componentLatticeNorm k (((f q).1 k - (f m).1 k) +
              ((f m).1 k - x k)) := by
          congr 1
          abel
        _ ≤ componentLatticeNorm k ((f q).1 k - (f m).1 k) +
            componentLatticeNorm k ((f m).1 k - x k) :=
          (componentLatticeNorm k).add_le _ _
        _ ≤ ε / 2 + δ :=
          (add_lt_add (componentNorm_le_finalNormValue (f q - f m) k |>.trans_lt
            (hN q hq m hmN)) (hL m hmL)).le
    have hfinal : finalLatticeNorm (f q - x₀) ≤ ε / 2 := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨k, rfl⟩
      exact hcoord k
    exact hfinal.trans_lt (by linarith)
  have hweak : HasWeakFatouProperty finalLatticeNorm 2 := by
    refine ⟨by norm_num, ?_⟩
    intro ι _ _ _ f x hfmono hfpos hflub c hfc
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    have hcoordLUB : IsLUB (Set.range fun i ↦ (f i).1 k) (x.1 k) := by
      constructor
      · rintro _ ⟨i, rfl⟩
        exact hflub.1 ⟨i, rfl⟩ k
      · intro z hz
        let y : FinalSpace := x + finalCoordinateEmbedding k (z - x.1 k)
        have hyupper : y ∈ upperBounds (Set.range f) := by
          rintro _ ⟨i, rfl⟩ m
          by_cases hmk : m = k
          · subst m
            simpa [y] using hz ⟨i, rfl⟩
          · have hix := hflub.1 ⟨i, rfl⟩ m
            simpa [y, finalCoordinateEmbedding_ne k m hmk] using hix
        have hxy := hflub.2 hyupper k
        simpa [y] using hxy
    exact (component_weakFatou k).2.2 (fun i ↦ (f i).1 k) (x.1 k)
      (fun _ _ hij ↦ hfmono hij k) (fun i ↦ hfpos i k) hcoordLUB c
      (fun i ↦ (componentNorm_le_finalNormValue (f i) k).trans (hfc i))
  exact ⟨hcomplete, hweak⟩

/-- Shows that single-coordinate inclusion is isometric; used to transfer the
component large-vector norm to the final space. -/
theorem finalLatticeNorm_coordinateEmbedding (n : ℕ) (z : TreeComponent n) :
    finalLatticeNorm (finalCoordinateEmbedding n z) = componentLatticeNorm n z := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨m, rfl⟩
    by_cases hmn : m = n
    · subst m
      simp
    · change componentLatticeNorm m ((finalCoordinateEmbedding n z).1 m) ≤ _
      rw [finalCoordinateEmbedding_ne n m hmn]
      rw [(componentLatticeNorm m).eq_zero_iff 0 |>.2 rfl]
      exact (componentLatticeNorm n).nonneg z
  · have h := componentNorm_le_finalNormValue (finalCoordinateEmbedding n z) n
    rw [finalCoordinateEmbedding_same] at h
    exact h

/-- Shows that single-coordinate inclusion preserves order convergence; used
to transfer iterated component adherence into the final space. -/
theorem finalCoordinateEmbedding_orderConverges
    {n : ℕ} {ι : Type} [Preorder ι] {f : ι → TreeComponent n} {z : TreeComponent n}
    (hf : OrderConvergesTo f z) :
    OrderConvergesTo (fun i ↦ finalCoordinateEmbedding n (f i))
      (finalCoordinateEmbedding n z) := by
  classical
  rcases hf with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrpos, hrglb, hcontrol⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκne
  refine ⟨κ, inferInstance, inferInstance, inferInstance,
    fun k ↦ finalCoordinateEmbedding n (r k), ?_, ?_, ?_, ?_⟩
  · intro a b hab m
    by_cases hmn : m = n
    · subst m
      simpa using hranti hab
    · simp [finalCoordinateEmbedding_ne n m hmn]
  · intro k m
    by_cases hmn : m = n
    · subst m
      simpa using hrpos k
    · simp [finalCoordinateEmbedding_ne n m hmn]
  · constructor
    · rintro _ ⟨k, rfl⟩
      intro m
      by_cases hmn : m = n
      · subst m
        simpa using hrpos k
      · simp [finalCoordinateEmbedding_ne n m hmn]
    · intro y hy m
      by_cases hmn : m = n
      · subst m
        apply hrglb.2
        rintro _ ⟨k, rfl⟩
        simpa using hy ⟨k, rfl⟩ n
      · let k₀ : κ := Classical.choice inferInstance
        have := hy ⟨k₀, rfl⟩ m
        simpa [finalCoordinateEmbedding_ne n m hmn] using this
  · intro k
    filter_upwards [hcontrol k] with i hi
    intro m
    by_cases hmn : m = n
    · subst m
      change |(finalCoordinateEmbedding n (f i)).1 n -
          (finalCoordinateEmbedding n z).1 n| ≤
        (finalCoordinateEmbedding n (r k)).1 n
      simpa using hi
    · change |(finalCoordinateEmbedding n (f i)).1 m -
          (finalCoordinateEmbedding n z).1 m| ≤
        (finalCoordinateEmbedding n (r k)).1 m
      rw [finalCoordinateEmbedding_ne n m hmn,
        finalCoordinateEmbedding_ne n m hmn,
        finalCoordinateEmbedding_ne n m hmn]
      simp

/-- Transfers membership through every finite adherence stage along a
coordinate embedding; used for `finalLargeVector_properties`. -/
theorem finalCoordinateEmbedding_iteratedOrderAdherence (n k : ℕ)
    {z : TreeComponent n}
    (hz : z ∈ iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k) :
    finalCoordinateEmbedding n z ∈
      iteratedOrderAdherence (unitBallFor finalLatticeNorm) k := by
  induction k generalizing z with
  | zero =>
      change componentLatticeNorm n z ≤ 1 at hz
      change finalLatticeNorm (finalCoordinateEmbedding n z) ≤ 1
      simpa [finalLatticeNorm_coordinateEmbedding] using hz
  | succ k ih =>
      change z ∈ orderAdherence
        (iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k) at hz
      rcases hz with ⟨ι, hpre, hdir, hne, f, hfmem, hfz⟩
      let : Preorder ι := hpre
      let : IsDirected ι (· ≤ ·) := hdir
      let : Nonempty ι := hne
      change finalCoordinateEmbedding n z ∈ orderAdherence
        (iteratedOrderAdherence (unitBallFor finalLatticeNorm) k)
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun i ↦ finalCoordinateEmbedding n (f i), fun i ↦ ih (hfmem i), ?_⟩
      exact finalCoordinateEmbedding_orderConverges hfz

/-- The vector `z_n`, supported in coordinate `n`. -/
noncomputable def finalLargeVector (n : ℕ) : FinalSpace :=
  ⟨fun m ↦ if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0, by
    change Tendsto
      (fun m ↦ componentLatticeNorm m
        (if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0))
      atTop (nhds 0)
    have heq : (fun m ↦ componentLatticeNorm m
        (if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0)) =ᶠ[atTop]
        fun _ ↦ 0 := by
      filter_upwards [eventually_gt_atTop n] with m hm
      rw [dite_eq_right hm.ne']
      exact (componentLatticeNorm m).eq_zero_iff _ |>.2 rfl
    exact (tendsto_congr' heq).2 tendsto_const_nhds⟩

/-- Paper Proposition `prop:zn`. -/
theorem finalLargeVector_properties (n : ℕ) :
    finalLargeVector n ∈ iteratedOrderAdherence (unitBallFor finalLatticeNorm) n ∧
      finalLatticeNorm (finalLargeVector n) = (2 : ℝ) ^ n := by
  have heq : finalLargeVector n =
      finalCoordinateEmbedding n ((2 : ℝ) ^ n • componentRoot n) := by
    apply Subtype.ext
    funext m
    simp [finalLargeVector, finalCoordinateEmbedding]
  rw [heq]
  exact ⟨finalCoordinateEmbedding_iteratedOrderAdherence n n
      (component_large_iterated_adherence n).2.2.2.1,
    (finalLatticeNorm_coordinateEmbedding n _).trans
      (component_large_iterated_adherence n).2.2.2.2⟩

/-- The constructed `c₀`-sum admits no equivalent Fatou lattice norm. -/
theorem finalSpace_not_equivalent_fatou :
    ∀ q : PaperLatticeNorm FinalSpace,
      HasFatouProperty q → ¬ EquivalentNorms finalLatticeNorm q := by
  intro q hq hequiv
  rcases hequiv with ⟨c, C, hc, hC, hcompare⟩
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (C / c : ℝ) (by norm_num : (1 : ℝ) < 2)
  let n := n₀ + 1
  have hn : 1 ≤ n := by simp [n]
  have hlarge : C < c * (2 : ℝ) ^ n := by
    have hpow : (2 : ℝ) ^ n₀ < (2 : ℝ) ^ n := by
      change (2 : ℝ) ^ n₀ < (2 : ℝ) ^ (n₀ + 1)
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n₀]
    have hcdiv : C < c * (2 : ℝ) ^ n₀ := by
      rw [div_lt_iff₀ hc] at hn₀
      simpa [mul_comm] using hn₀
    exact hcdiv.trans (mul_lt_mul_of_pos_left hpow hc)
  have hball : unitBallFor finalLatticeNorm ⊆ scaleSet C (unitBallFor q) := by
    intro z hz
    refine ⟨C⁻¹ • z, ?_, ?_⟩
    · change q (C⁻¹ • z) ≤ 1
      rw [q.smul, abs_of_pos (inv_pos.mpr hC), inv_mul_le_one₀ hC]
      exact (hcompare z).2.trans (by
        simpa using mul_le_mul_of_nonneg_left hz hC.le)
    · simp [smul_smul, hC.ne']
  have hitermono : ∀ k,
      iteratedOrderAdherence (unitBallFor finalLatticeNorm) k ⊆
        iteratedOrderAdherence (scaleSet C (unitBallFor q)) k := by
    intro k
    induction k with
    | zero => exact hball
    | succ k ih => exact orderAdherence_mono ih
  have hsolidq : LatticeOrderedAddCommGroup.IsSolid (unitBallFor q) := by
    intro y hy z hzy
    exact (q.solid hzy).trans hy
  have hscale :=
    (iteratedOrderAdherence_mono_and_scale hsolidq hsolidq hC).2.2 n
  have hz := hitermono n (finalLargeVector_properties n).1
  rw [hscale, fatou_iterated_unitBall q hq n hn] at hz
  rcases hz with ⟨y, hy, hyz⟩
  have hqz : q (finalLargeVector n) ≤ C := by
    rw [← hyz, q.smul, abs_of_pos hC]
    simpa using mul_le_mul_of_nonneg_left hy hC.le
  have hpz : finalLatticeNorm (finalLargeVector n) = (2 : ℝ) ^ n :=
    (finalLargeVector_properties n).2
  have hlower := (hcompare (finalLargeVector n)).1
  rw [hpz] at hlower
  exact (not_lt_of_ge (hlower.trans hqz)) hlarge

/-- Paper Theorem `thm:fremlin-main`. -/
theorem exists_weaklyFatou_not_equivalent_fatou :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ p : PaperLatticeNorm X, IsCompleteFor p ∧ HasWeakFatouProperty p 2 ∧
        ∀ q : PaperLatticeNorm X, HasFatouProperty q → ¬ EquivalentNorms p q := by
  refine ⟨FinalSpace, inferInstance, inferInstance, inferInstance, inferInstance,
    finalLatticeNorm, (finalSpace_weakFatou).1, (finalSpace_weakFatou).2,
    finalSpace_not_equivalent_fatou⟩

end OrderClosures
