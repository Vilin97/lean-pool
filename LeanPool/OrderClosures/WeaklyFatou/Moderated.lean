/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.WeaklyFatou.Bands


/-!
# Thinning, transient bands, and component moderatedness
-/

@[expose] public section

namespace OrderClosures

open Set Filter Topology
open scoped NNReal Topology

universe u

/-- Paper Lemma `lem:thinning`. -/
theorem tree_thinning
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hΛ : recurrentBands n w ⊆ (Λ : Set (TreeBandIndex n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w (φ m))).support.Nonempty}.Subsingleton := by
  classical
  let φ : ℕ → ℕ := fun m ↦ Nat.rec 0 (fun _ r ↦
    max (r + 1) (((bandsAt n (w r)).filter fun B ↦ B ∉ Λ).sup fun B ↦
      lastBandOccurrence n w B + 1)) m
  have hφ_succ (m : ℕ) : φ (m + 1) =
      max (φ m + 1) (((bandsAt n (w (φ m))).filter fun B ↦ B ∉ Λ).sup fun B ↦
        lastBandOccurrence n w B + 1) := by simp [φ]
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro m
    rw [hφ_succ]
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  refine ⟨φ, hφ, ?_⟩
  intro B hBΛ
  have hBfinite : {m | (treeBandProjection n B (w m)).support.Nonempty}.Finite := by
    apply Set.not_infinite.mp
    intro hInf
    exact hBΛ (hΛ hInf)
  intro i hi j hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hBbands : B ∈ bandsAt n (w (φ i)) :=
      (mem_bandsAt_iff n _ B).mpr hi
    have hBfilter : B ∈ (bandsAt n (w (φ i))).filter fun B ↦ B ∉ Λ :=
      Finset.mem_filter.mpr ⟨hBbands, hBΛ⟩
    have hlast_lt_succ : lastBandOccurrence n w B < φ (i + 1) := by
      have hle := Finset.le_sup
        (s := (bandsAt n (w (φ i))).filter fun B ↦ B ∉ Λ)
        (f := fun B ↦ lastBandOccurrence n w B + 1) hBfilter
      change lastBandOccurrence n w B + 1 ≤ _ at hle
      have hle' := hle.trans (le_max_right (φ i + 1)
        (((bandsAt n (w (φ i))).filter fun B ↦ B ∉ Λ).sup fun B ↦
          lastBandOccurrence n w B + 1))
      rw [← hφ_succ] at hle'
      omega
    have hsucc_le : φ (i + 1) ≤ φ j := hφ.monotone (Nat.succ_le_iff.mpr hijlt)
    have hjlast := le_lastBandOccurrence n w B hBfinite hj
    omega
  · have hBbands : B ∈ bandsAt n (w (φ j)) :=
      (mem_bandsAt_iff n _ B).mpr hj
    have hBfilter : B ∈ (bandsAt n (w (φ j))).filter fun B ↦ B ∉ Λ :=
      Finset.mem_filter.mpr ⟨hBbands, hBΛ⟩
    have hlast_lt_succ : lastBandOccurrence n w B < φ (j + 1) := by
      have hle := Finset.le_sup
        (s := (bandsAt n (w (φ j))).filter fun B ↦ B ∉ Λ)
        (f := fun B ↦ lastBandOccurrence n w B + 1) hBfilter
      change lastBandOccurrence n w B + 1 ≤ _ at hle
      have hle' := hle.trans (le_max_right (φ j + 1)
        (((bandsAt n (w (φ j))).filter fun B ↦ B ∉ Λ).sup fun B ↦
          lastBandOccurrence n w B + 1))
      rw [← hφ_succ] at hle'
      omega
    have hsucc_le : φ (j + 1) ≤ φ i := hφ.monotone (Nat.succ_le_iff.mpr hjilt)
    have hilast := le_lastBandOccurrence n w B hBfinite hi
    omega

/-- Shows that a tree operator vanishes outside the union of cylinders in its
support; used by `tree_transient` to eliminate common positive lower bounds. -/
theorem treeOperator_apply_eq_zero_of_outside_support
    (n : ℕ) (w : TreeCoefficients n) {α : TreeProduct n}
    (hα : α ∉ finiteCylinderUnion n w.support) :
    treeOperator n w α = 0 := by
  classical
  rw [treeOperator_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hnot : α ∉ treeCylinder n t := by
    intro hmem
    apply hα
    simp only [finiteCylinderUnion, Set.mem_iUnion]
    exact ⟨⟨t, ht⟩, hmem⟩
  rw [treeFunction_apply_of_notMem n t hnot, mul_zero]

/-- Paper Lemma `lem:transient`. -/
theorem tree_transient
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hnone : none ∈ Λ)
    (hdis : ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w m)).support.Nonempty}.Subsingleton) :
    let v := fun m ↦ w m - finiteBandProjection n Λ (w m)
    (Pairwise fun i j ↦ ParentDisjoint ((v i).support : Set (TreeNode n))
      ((v j).support : Set (TreeNode n))) ∧
    ∀ z : BoundedContinuousFunction (TreeProduct n) ℝ,
      0 ≤ z → (∀ m, z ≤ treeOperator n (v m)) → z = 0 := by
  classical
  dsimp
  let v : ℕ → TreeCoefficients n := fun m ↦
    w m - finiteBandProjection n Λ (w m)
  have hv_apply (m : ℕ) (t : TreeNode n) :
      v m t = if treeBandOfNode n t ∈ Λ then 0 else w m t := by
    change (w m - finiteBandProjection n Λ (w m)) t = _
    rw [Finsupp.sub_apply]
    by_cases hB : treeBandOfNode n t ∈ Λ
    · rw [(finiteBandProjection_apply n Λ (w m) t).1 hB]
      simp [hB]
    · rw [(finiteBandProjection_apply n Λ (w m) t).2 hB]
      simp [hB]
  have hv_band_notMem {m : ℕ} {t : TreeNode n} (ht : t ∈ (v m).support) :
      treeBandOfNode n t ∉ Λ := by
    intro hB
    have htne := Finsupp.mem_support_iff.mp ht
    rw [hv_apply, ite_eq_left hB] at htne
    exact htne rfl
  have hv_root_notMem (m : ℕ) : TreeNode.root n ∉ (v m).support := by
    intro ht
    have hB := hv_band_notMem ht
    apply hB
    simpa [treeBandOfNode] using hnone
  have hpair : Pairwise fun i j ↦
      ParentDisjoint ((v i).support : Set (TreeNode n))
        ((v j).support : Set (TreeNode n)) := by
    intro i j hij
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    rcases hq.1 with ⟨ti, hti, hpti⟩
    rcases hq.2 with ⟨tj, htj, hptj⟩
    have htiroot : ti ≠ TreeNode.root n := fun h ↦ hv_root_notMem i (h ▸ hti)
    have htjroot : tj ≠ TreeNode.root n := fun h ↦ hv_root_notMem j (h ▸ htj)
    let B := treeBandOfNode n ti
    have hBnot : B ∉ Λ := hv_band_notMem hti
    have hBsame : treeBandOfNode n tj = B := by
      change treeBandOfNode n tj = treeBandOfNode n ti
      rw [treeBandOfNode, dite_eq_right htjroot, treeBandOfNode, dite_eq_right htiroot]
      congr 2
      exact hptj.trans hpti.symm
    have hwti : ti ∈ (w i).support := by
      rw [Finsupp.mem_support_iff]
      have hvne := Finsupp.mem_support_iff.mp hti
      rw [hv_apply, ite_eq_right hBnot] at hvne
      exact hvne
    have hBt_i : (treeBandProjection n B (w i)).support.Nonempty :=
      (treeBandProjection_support_nonempty_iff n B (w i)).mpr
        ⟨ti, hwti, rfl⟩
    have hwjt : tj ∈ (w j).support := by
      rw [Finsupp.mem_support_iff]
      have hvne := Finsupp.mem_support_iff.mp htj
      rw [hv_apply, ite_eq_right (hBsame ▸ hBnot)] at hvne
      exact hvne
    have hBt_j : (treeBandProjection n B (w j)).support.Nonempty :=
      (treeBandProjection_support_nonempty_iff n B (w j)).mpr
        ⟨tj, hwjt, hBsame⟩
    exact hij ((hdis B hBnot) hBt_i hBt_j)
  refine ⟨hpair, ?_⟩
  intro z hzpos hzlower
  apply le_antisymm
  · exact commonLower_le_zero_of_parentDisjoint_subseq n
      (fun m ↦ (v m).support) hpair id Function.injective_id hv_root_notMem
      (fun m ↦ treeOperator n (v m))
      (fun m α hα ↦ treeOperator_apply_eq_zero_of_outside_support n (v m) hα)
      hzlower
  · exact hzpos

/-- Selects positive majorants whose transient bands occur in at most one sequence term. -/
private theorem exists_thinned_treeMajorants
    (n : ℕ) (x : ℕ → TreeComponent n) (hxmono : Monotone x)
    (hxpos : ∀ m, 0 ≤ x m) (hxnorm : ∀ m, componentLatticeNorm n (x m) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Λ : Finset (TreeBandIndex n)) (W : ℕ → TreeCoefficients n),
      none ∈ Λ ∧ (∀ m, 0 ≤ W m) ∧ (∀ m, (x m).1 ≤ treeOperator n (W m)) ∧
      (∀ m, treeRho n (W m) < 1 + ε / 2) ∧
      ∀ B ∉ Λ, {m | (treeBandProjection n B (W m)).support.Nonempty}.Subsingleton := by
  classical
  have hquarter : 0 < ε / 4 := div_pos hε (by norm_num)
  choose w hw hmajor hrho using fun m ↦
    exists_treeMajorant_lt n (x m).1 hquarter
  have hdom (m : ℕ) : (x m).1 ≤ treeOperator n (w m) := by
    have hxpos' : 0 ≤ (x m).1 := hxpos m
    simpa [abs_of_nonneg hxpos'] using hmajor m
  have hrho' (m : ℕ) : treeRho n (w m) < 1 + ε / 4 := by
    have hn := hxnorm m
    change treeSeminorm n (x m).1 ≤ 1 at hn
    linarith [hrho m]
  obtain ⟨φ, hφ, hsharp⟩ :=
    tree_sharp_subsequence n w (1 + ε / 4) (fun m ↦ (hrho' m).le)
  have hφid (m : ℕ) : m ≤ φ m := hφ.id_le m
  have hdomφ (m : ℕ) : (x m).1 ≤ treeOperator n (w (φ m)) := by
    have hxm := hxmono (hφid m)
    change (x m).1 ≤ (x (φ m)).1 at hxm
    exact hxm.trans (hdom (φ m))
  obtain ⟨wt, hwt, hrec⟩ := tree_trim n x (fun m ↦ w (φ m)) hε
    (fun m ↦ hw (φ m)) hdomφ (fun m ↦ hrho' (φ m)) hsharp
  let Λ : Finset (TreeBandIndex n) := insert none hrec.toFinset
  have hnoneΛ : none ∈ Λ := by simp [Λ]
  have hrecΛ : recurrentBands n wt ⊆ (Λ : Set (TreeBandIndex n)) := by
    intro B hB
    simp only [Λ, Finset.mem_coe, Finset.mem_insert]
    exact Or.inr (hrec.mem_toFinset.mpr hB)
  obtain ⟨ψ, hψ, hthin⟩ := tree_thinning n wt Λ hrecΛ
  have hψid (m : ℕ) : m ≤ ψ m := hψ.id_le m
  let W : ℕ → TreeCoefficients n := fun m ↦ wt (ψ m)
  have hWpos (m : ℕ) : 0 ≤ W m := (hwt (ψ m)).1
  have hWdom (m : ℕ) : (x m).1 ≤ treeOperator n (W m) := by
    have hxm := hxmono (hψid m)
    change (x m).1 ≤ (x (ψ m)).1 at hxm
    exact hxm.trans (hwt (ψ m)).2.1
  have hWrho (m : ℕ) : treeRho n (W m) < 1 + ε / 2 :=
    (hwt (ψ m)).2.2
  have hthinW : ∀ B ∉ Λ,
      {m | (treeBandProjection n B (W m)).support.Nonempty}.Subsingleton :=
    hthin
  exact ⟨Λ, W, hnoneΛ, hWpos, hWdom, hWrho, hthinW⟩

/-- Paper Proposition `prop:moderated`. -/
theorem component_moderated
    (n : ℕ) (x : ℕ → TreeComponent n) (hxmono : Monotone x)
    (hxpos : ∀ m, 0 ≤ x m) (hxnorm : ∀ m, componentLatticeNorm n (x m) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TreeCoefficients n, 0 ≤ w ∧
      (∀ m, (x m).1 ≤ treeOperator n w) ∧ treeRho n w ≤ 2 + ε := by
  classical
  obtain ⟨Λ, W, hnoneΛ, hWpos, hWdom, hWrho, hthinW⟩ :=
    exists_thinned_treeMajorants n x hxmono hxpos hxnorm hε
  let U₀ : ℕ → TreeCoefficients n := fun m ↦ finiteBandProjection n Λ (W m)
  let V : ℕ → TreeCoefficients n := fun m ↦ W m - U₀ m
  let U : ℕ → TreeCoefficients n := fun m ↦ treeUpshift n (U₀ m)
  have hU₀pos (m : ℕ) : 0 ≤ U₀ m := finiteBandProjection_nonneg n Λ (hWpos m)
  have hVpos (m : ℕ) : 0 ≤ V m := sub_nonneg.mpr (finiteBandProjection_le n Λ (hWpos m))
  have hUpos (m : ℕ) : 0 ≤ U m :=
    Finsupp.mapDomain_nonneg (hU₀pos m)
  let P : Finset (TreeNode n) := treeBandParents n Λ
  have hUsupport (m : ℕ) : (U m).support ⊆ P :=
    treeUpshift_support_subset_bandParents n Λ (W m)
  have hUrho (m : ℕ) : treeRho n (U m) < 2 + ε := by
    calc
      treeRho n (U m) ≤ 2 * treeRho n (U₀ m) :=
        (treeUpshift_basic n (U₀ m) (hU₀pos m)).1
      _ ≤ 2 * treeRho n (W m) :=
        mul_le_mul_of_nonneg_left (treeRho_finiteBandProjection_le n Λ (W m))
          (by norm_num)
      _ < 2 * (1 + ε / 2) := mul_lt_mul_of_pos_left (hWrho m) (by norm_num)
      _ = 2 + ε := by ring
  let M : ℝ := (2 : ℝ) ^ n
  have hM : 0 < M := pow_pos (by norm_num) n
  let D : ℝ := M * (2 + ε)
  have htwoeps : 0 < 2 + ε := by linarith
  have hD : 0 < D := mul_pos hM htwoeps
  have hUcoord (m : ℕ) (t : TreeNode n) : |U m t| ≤ D := by
    have hone : |U m t| ≤ ∑ q ∈ (U m).support, |U m q| := by
      by_cases ht : U m t = 0
      · rw [ht, abs_zero]
        exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
      · exact Finset.single_le_sum (fun q _ ↦ abs_nonneg (U m q))
          (Finsupp.mem_support_iff.mpr ht)
    calc
      |U m t| ≤ ∑ q ∈ (U m).support, |U m q| := hone
      _ ≤ M * treeRho n (U m) := treeRho_controls_sum n (U m)
      _ ≤ M * (2 + ε) := mul_le_mul_of_nonneg_left (hUrho m).le hM.le
      _ = D := rfl
  let y : ℕ → ↥P → Set.Icc (-D) D := fun m t ↦
    ⟨U m t.1, by
      have habs := hUcoord m t.1
      exact ⟨(neg_le_neg habs).trans (neg_abs_le _), (le_abs_self _).trans habs⟩⟩
  let : SeqCompactSpace (↥P → Set.Icc (-D) D) := inferInstance
  obtain ⟨l, _, θ, hθ, hlim⟩ :=
    (SeqCompactSpace.isSeqCompact_univ (X := ↥P → Set.Icc (-D) D))
      (x := y) (fun _ ↦ Set.mem_univ _)
  let coeff : TreeNode n → ℝ := fun t ↦
    if ht : t ∈ P then (l ⟨t, ht⟩).1 else 0
  let u : TreeCoefficients n := Finsupp.onFinset P coeff (by
    intro t ht
    by_contra htP
    simp [coeff, htP] at ht)
  have hcoordlim (t : TreeNode n) :
      Tendsto (fun m ↦ U (θ m) t) atTop (nhds (u t)) := by
    by_cases ht : t ∈ P
    · have htend := tendsto_pi_nhds.mp hlim ⟨t, ht⟩
      have htend' := tendsto_subtype_rng.mp htend
      simpa [y, u, coeff, ht, Function.comp_def] using htend'
    · have hzero (m : ℕ) : U (θ m) t = 0 := by
        by_contra hne
        exact ht (hUsupport (θ m) (Finsupp.mem_support_iff.mpr hne))
      have huzero : u t = 0 := by simp [u, coeff, ht]
      simp only [hzero, huzero]
      exact tendsto_const_nhds
  have hupos : 0 ≤ u := by
    intro t
    apply ge_of_tendsto (hcoordlim t)
    exact Filter.Eventually.of_forall fun m ↦ hUpos (θ m) t
  have huSupport : u.support ⊆ P := Finsupp.support_onFinset_subset
  have hTop_repr (q : TreeCoefficients n) (hq : q.support ⊆ P) :
      treeOperator n q = ∑ t ∈ P, q t • treeFunction n t := by
    rw [treeOperator]
    apply Finsupp.sum_of_support_subset q hq
    intro t _
    simp
  have hRho_repr (q : TreeCoefficients n) (hq : q.support ⊆ P) :
      treeRho n q = ∑ t ∈ P,
        (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |q t| := by
    rw [treeRho]
    apply Finsupp.sum_of_support_subset q hq
    intro t _
    simp
  have hToplim : Tendsto (fun m ↦ treeOperator n (U (θ m))) atTop
      (nhds (treeOperator n u)) := by
    have hsum : Tendsto
        (fun m ↦ ∑ t ∈ P, U (θ m) t • treeFunction n t) atTop
        (nhds (∑ t ∈ P, u t • treeFunction n t)) :=
      tendsto_finsetSum P fun t _ ↦ (hcoordlim t).smul_const (treeFunction n t)
    rw [hTop_repr u huSupport]
    apply tendsto_congr' _ |>.mpr hsum
    exact Filter.Eventually.of_forall fun m ↦ hTop_repr (U (θ m)) (hUsupport (θ m))
  have hRholim : Tendsto (fun m ↦ treeRho n (U (θ m))) atTop
      (nhds (treeRho n u)) := by
    have hsum : Tendsto
        (fun m ↦ ∑ t ∈ P,
          (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |U (θ m) t|) atTop
        (nhds (∑ t ∈ P,
          (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |u t|)) :=
      tendsto_finsetSum P fun t _ ↦ tendsto_const_nhds.mul (hcoordlim t).abs
    rw [hRho_repr u huSupport]
    apply tendsto_congr' _ |>.mpr hsum
    exact Filter.Eventually.of_forall fun m ↦ hRho_repr (U (θ m)) (hUsupport (θ m))
  have hurho : treeRho n u ≤ 2 + ε := by
    apply le_of_tendsto hRholim
    exact Filter.Eventually.of_forall fun m ↦ (hUrho (θ m)).le
  have htransient_subseq (χ : ℕ → ℕ) (hχ : Function.Injective χ)
      (z : BoundedContinuousFunction (TreeProduct n) ℝ) (hz : 0 ≤ z)
      (hzlower : ∀ k, z ≤ treeOperator n (V (χ k))) : z = 0 := by
    have hsub : ∀ B ∉ Λ,
        {k | (treeBandProjection n B (W (χ k))).support.Nonempty}.Subsingleton := by
      intro B hB i hi j hj
      exact hχ (hthinW B hB hi hj)
    have htr := (tree_transient n (fun k ↦ W (χ k)) Λ hnoneΛ hsub).2
    apply htr z hz
    intro k
    change z ≤ treeOperator n
      (W (χ k) - finiteBandProjection n Λ (W (χ k)))
    exact hzlower k
  refine ⟨u, hupos, ?_, hurho⟩
  intro j α
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨m₀, hm₀⟩ := (Metric.tendsto_atTop.mp hToplim) η hη
  let K : ℕ := max j m₀
  let χ : ℕ → ℕ := fun k ↦ θ (k + K)
  have hχ : Function.Injective χ := hθ.injective.comp fun a b hab ↦ by
    omega
  have hclose (k : ℕ) :
      ‖treeOperator n (U (χ k)) - treeOperator n u‖ < η := by
    have hk : m₀ ≤ k + K := le_trans (le_max_right j m₀) (Nat.le_add_left K k)
    have := hm₀ (k + K) hk
    rw [dist_eq_norm_sub] at this
    exact this
  have happrox (k : ℕ) :
      treeOperator n (U (χ k)) ≤ treeOperator n u +
        η • treeFunction n (TreeNode.root n) := by
    let d := treeOperator n (U (χ k)) - treeOperator n u
    have habs : |d| ≤ η • treeFunction n (TreeNode.root n) := by
      calc
        |d| ≤ ‖d‖ • treeFunction n (TreeNode.root n) :=
          abs_le_norm_smul_root n d
        _ ≤ η • treeFunction n (TreeNode.root n) := by
          intro β
          simpa [treeFunction_root] using (hclose k).le
    calc
      treeOperator n (U (χ k)) = d + treeOperator n u := by
        dsimp [d]
        abel
      _ ≤ |d| + treeOperator n u := add_le_add (le_abs_self d) le_rfl
      _ ≤ η • treeFunction n (TreeNode.root n) + treeOperator n u :=
        add_le_add habs le_rfl
      _ = treeOperator n u + η • treeFunction n (TreeNode.root n) := add_comm _ _
  let b : BoundedContinuousFunction (TreeProduct n) ℝ :=
    treeOperator n u + η • treeFunction n (TreeNode.root n)
  let z : BoundedContinuousFunction (TreeProduct n) ℝ := ((x j).1 - b)⁺
  have hzpos : 0 ≤ z := posPart_nonneg _
  have hzlower (k : ℕ) : z ≤ treeOperator n (V (χ k)) := by
    have hjχ : j ≤ χ k := by
      have hK : j ≤ k + K := le_trans (le_max_left j m₀) (Nat.le_add_left K k)
      exact hK.trans (hθ.id_le (k + K))
    have hxjχ := hxmono hjχ
    change (x j).1 ≤ (x (χ k)).1 at hxjχ
    have hxW : (x j).1 ≤ treeOperator n (W (χ k)) :=
      hxjχ.trans (hWdom (χ k))
    have hdecomp : treeOperator n (W (χ k)) =
        treeOperator n (U₀ (χ k)) + treeOperator n (V (χ k)) := by
      rw [← treeOperator_add]
      congr 1
      dsimp [V]
      abel
    have hup := (treeUpshift_basic n (U₀ (χ k)) (hU₀pos (χ k))).2
    have hmain : (x j).1 ≤ b + treeOperator n (V (χ k)) := by
      calc
        (x j).1 ≤ treeOperator n (W (χ k)) := hxW
        _ = treeOperator n (U₀ (χ k)) + treeOperator n (V (χ k)) := hdecomp
        _ ≤ treeOperator n (U (χ k)) + treeOperator n (V (χ k)) :=
          add_le_add hup le_rfl
        _ ≤ b + treeOperator n (V (χ k)) :=
          add_le_add (happrox k) le_rfl
    have hdiff : (x j).1 - b ≤ treeOperator n (V (χ k)) := by
      rw [sub_le_iff_le_add]
      simpa [add_comm] using hmain
    change ((x j).1 - b) ⊔ 0 ≤ treeOperator n (V (χ k))
    exact sup_le hdiff (treeOperator_nonneg n (V (χ k)) (hVpos (χ k)))
  have hz0 := htransient_subseq χ hχ z hzpos hzlower
  have hxb : (x j).1 ≤ b := by
    rw [← sub_nonpos]
    exact (le_posPart ((x j).1 - b)).trans_eq hz0
  have hpoint := hxb α
  simpa [b, treeFunction_root] using hpoint

/-- Paper Corollary `cor:weak-fatou`. -/
theorem component_weakFatou (n : ℕ) :
    IsWeakNakanoConstant (componentLatticeNorm n) 2 ∧
      HasWeakFatouProperty (componentLatticeNorm n) 2 := by
  have hseq : IsWeakSequentialNakanoConstant (componentLatticeNorm n) 2 := by
    refine ⟨by norm_num, ?_⟩
    intro x hxmono hxpos _ hxnorm ε hε
    obtain ⟨w, hw, hwupper, hwrho⟩ :=
      component_moderated n x hxmono hxpos hxnorm hε
    let y : TreeComponent n := ⟨treeOperator n w, treeOperator_mem_treeSublattice n w⟩
    refine ⟨y, ?_, ?_, ?_⟩
    · exact treeOperator_nonneg n w hw
    · exact hwupper
    · change treeSeminorm n (treeOperator n w) ≤ 2 + ε
      apply (treeSeminorm_le_of_majorant n (treeOperator n w) w hw ?_).trans hwrho
      rw [abs_of_nonneg (treeOperator_nonneg n w hw)]
  let : Countable (TreeNode n) := by
    unfold TreeNode
    infer_instance
  let : TopologicalSpace.SeparableSpace (TreeComponent n) :=
    VectorSublattice.separableSpace_topologicalClosure_generated_of_countable
      (Set.countable_range (treeFunction n))
  have hNak : IsWeakNakanoConstant (componentLatticeNorm n) 2 :=
    weakNakano_of_weakSequentialNakano_p (Y := TreeComponent n) (K := 2)
      (componentLatticeNorm n) hseq
  exact ⟨hNak, weakFatou_of_weakNakano_p (componentLatticeNorm n) hNak⟩

end OrderClosures
