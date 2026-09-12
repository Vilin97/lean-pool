/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8

/-!
# Hopf problem: foundations · euclidean sphere

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem
    _root_.PartialEquiv.image_source_minus_singleton_eq {α β : Type*} (e : PartialEquiv α β)
    {a : α} (h : a ∈ e.source) : e '' (e.source \ { a }) = e.target \ {e a} := by
  rw [Set.image_sdiff_of_injOn, PartialEquiv.image_source_eq_target, Set.image_singleton]
  · exact e.injOn
  · exact Set.singleton_subset_iff.mpr h

private theorem _root_.PartialEquiv.symm_image_target_minus_singleton_eq {α β : Type*}
    (e : PartialEquiv α β) {b : β} (h : b ∈ e.target) :
    e.symm '' (e.target \ { b }) = e.source \ {e.symm b} :=
  e.symm.image_source_minus_singleton_eq h

private theorem
    _root_.Path.exists_partition_unitInterval_of_open_cover {X : Type u} [TopologicalSpace X]
    {ι : Type v} {c : ι → Set X} {a : X} (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : Set.univ ⊆ ⋃ i, c i)
    (γ : Path a a) :
    ∃ (n : ℕ) (t : Fin (n + 2) → (unitInterval)),
      t 0 = 0 ∧
        t (Fin.last (n + 1)) = 1 ∧
          ∀ k : Fin (n + 1), ∃ i, γ '' (Set.uIcc (t k.castSucc) (t k.succ)) ⊆ c i := by
  have ⟨t, ht₀, ht_mono, ⟨n, ht₁⟩, ht_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i ↦ IsOpen.preimage (Path.continuous γ) (hc₁ i))
      (fun s _ ↦ (Set.preimage_iUnion ▸ hc₂ (Set.mem_univ _)))
  use n, t ∘ Fin.toNat
  suffices ∀ (k : Fin (n + 1)), ∃ i, Set.uIcc (t ↑k) (t (↑k + 1)) ⊆ ⇑γ ⁻¹' c i by simpa [ht₀, ht₁]
  intro k
  have ⟨i, hi⟩ := ht_sub k
  use i
  rwa [Set.uIcc_of_le (ht_mono (Nat.le_add_right _ _))]

private theorem
    _root_.Path.exists_path_range_of_isPathConnected_inter {X : Type u} [TopologicalSpace X]
    {ι : Type v} {c : ι → Set X} {a : X} (hc₃ : ∀ i j, IsPathConnected (c i ∩ c j))
    (ha : ∀ i, a ∈ c i) {n : ℕ} (τ : Fin (n + 1) → ι) (p : Fin (n + 2) → X)
    (hτ₁ : ∀ k, p k.castSucc ∈ c (τ k)) (hτ₂ : ∀ k, p k.succ ∈ c (τ k)) :
    ∀ k : Fin n,
      ∃ g : Path a (p k.succ.castSucc), Set.range g ⊆ c (τ k.castSucc) ∩ c (τ k.succ) := by
  intro k
  have ⟨γ, hγ⟩ :=
    (hc₃ (τ k.castSucc) (τ k.succ)).joinedIn a ⟨ha (τ k.castSucc), ha (τ k.succ)⟩
      (p k.castSucc.succ) ⟨hτ₂ k.castSucc, hτ₁ k.succ⟩
  use γ
  exact Set.range_subset_iff.mpr hγ

private lemma _root_.Path.Homotopic.cancel_junction_mo1973_3458 {X : Type u} [TopologicalSpace X]
    {a b c d e f : X} (p : Path a b) (q : Path b c) (r : Path d c) (s : Path c e) (t : Path e f) :
    ((p ≫ₚ q ≫ₚ r.symm) ≫ₚ (r ≫ₚ s ≫ₚ t)).Homotopic (p ≫ₚ (q ≫ₚ s) ≫ₚ t) := by
  apply Path.Homotopic.Quotient.exact
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [←
    Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk r).symm
      (Path.Homotopic.Quotient.mk r),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

private lemma
    _root_.Path.Homotopic.concat_trans_trans_symm {X : Type u} [TopologicalSpace X] {n : ℕ}
    (p q : Fin (n + 1) → X) (F : ∀ k : Fin n, Path (p k.castSucc) (p k.succ))
    (G : ∀ k : Fin (n + 1), Path (q k) (p k)) :
    (Path.concat q (fun k ↦ (G k.castSucc) ≫ₚ (F k) ≫ₚ (G k.succ).symm)).Homotopic
      ((G 0) ≫ₚ (Path.concat p F) ≫ₚ (G (Fin.last n)).symm) := by
  induction n with
  | zero =>
    simp only [Path.concat_zero, ← FundamentalGroupoid.fromPath_eq_iff_homotopic]
    aesop_cat
  | succ n
    hn =>
    have ih :=
      hn (p ∘ Fin.castSucc) (q ∘ Fin.castSucc) (fun k ↦ F k.castSucc) (fun k ↦ G k.castSucc)
    rw [Path.concat_succ q, Path.concat_succ p]
    exact
      (ih.hcomp (Path.Homotopic.refl _)).trans
        (Path.Homotopic.cancel_junction_mo1973_3458 (G 0)
          (Path.concat (p ∘ Fin.castSucc) (fun k ↦ F k.castSucc)) (G (Fin.last n).castSucc)
          (F (Fin.last n)) (G (Fin.last (n + 1))).symm)

private lemma _root_.Path.Homotopic.cast_trans_trans_homotopic_of_homotopic_cast_mo1973_3460
    {X : Type u} [TopologicalSpace X] {x x₀ x₁ : X} {h₀ : x₀ = x} {h₁ : x₁ = x} {p : Path x₀ x₁}
    {q : Path x x} (h : p.Homotopic (q.cast h₀ h₁)) :
    (((Path.refl x).cast rfl h₀) ≫ₚ p ≫ₚ ((Path.refl x).cast h₁ rfl)).Homotopic q := by
  subst_vars
  exact
    Path.Homotopic.trans
      (Path.Homotopic.trans ⟨Path.Homotopy.reflTrans _⟩ ⟨Path.Homotopy.transRefl _⟩) h

private theorem _root_.Path.Homotopic.exists_loops_homotopic_concat_of_open_cover {X : Type u}
    [TopologicalSpace X] {ι : Type v} {c : ι → Set X} {a : X} (hc₁ : ∀ i, IsOpen (c i))
    (hc₂ : Set.univ ⊆ ⋃ i, c i) (hc₃ : ∀ i j, IsPathConnected (c i ∩ c j)) (ha : ∀ i, a ∈ c i)
    (γ : Path a a) :
    ∃ (n : ℕ) (D : Fin (n + 1) → Path a a),
      Path.Homotopic (Path.concat (fun _ ↦ a) D) γ ∧ (∀ k, ∃ i : ι, Set.range (D k) ⊆ c i) := by
  have ⟨n, t, ht₀, ht₁, ht_range⟩ := Path.exists_partition_unitInterval_of_open_cover hc₁ hc₂ γ
  choose τ hτ using ht_range
  have :=
    Path.exists_path_range_of_isPathConnected_inter hc₃ ha τ (γ ∘ t)
      (fun k ↦ hτ k (Set.mem_image_of_mem γ Set.left_mem_uIcc))
      (fun k ↦ hτ k (Set.mem_image_of_mem γ Set.right_mem_uIcc))
  choose G hG using this
  let G' :=
    Fin.snoc (α := fun k ↦ Path a (γ (t k)))
      (Fin.cons (α := fun k ↦ Path a (γ (t k.castSucc))) ((Path.refl a).cast rfl (ht₀ ▸ γ.source))
        G)
      ((Path.refl a).cast rfl (ht₁ ▸ γ.target))
  have hG'₀ : G' 0 = (Path.refl a).cast rfl (ht₀ ▸ γ.source) :=
    (Fin.snoc_apply_zero _ _).trans (Fin.cons_zero _ _)
  have hG'₁ : G' (Fin.last (n + 1)) = (Path.refl a).cast rfl (ht₁ ▸ γ.target) := Fin.snoc_last _ _
  have hG'_range₀ k : Set.range (G' k.castSucc) ⊆ c (τ k) := by
    unfold G'
    rw [Fin.snoc_castSucc]
    cases k using Fin.cases with
    | zero =>
      change Set.range (fun _ : (unitInterval) ↦ a) ⊆ c (τ 0)
      simpa only [Set.range_const, Set.singleton_subset_iff] using ha (τ 0)
    | succ j => exact (Set.subset_inter_iff.mp (hG j)).right
  have hG'_range₁ k : Set.range (G' k.succ) ⊆ c (τ k) := by
    unfold G'
    cases k using Fin.lastCases with
    | cast =>
      rw [Fin.succ_castSucc, Fin.snoc_castSucc]
      exact (Set.subset_inter_iff.mp (hG _)).left
    | last =>
      rw [Fin.succ_last, Fin.snoc_last]
      change Set.range (fun _ : (unitInterval) ↦ a) ⊆ c (τ (Fin.last n))
      simpa only [Set.range_const, Set.singleton_subset_iff] using ha (τ (Fin.last n))
  use n, fun k ↦ (G' k.castSucc) ≫ₚ (γ.subpath (t k.castSucc) (t k.succ)) ≫ₚ (G' k.succ).symm
  constructor
  · apply Path.Homotopic.trans (Path.Homotopic.concat_trans_trans_symm _ _ _ _)
    rw [hG'₀, hG'₁, ← Path.cast_symm, Path.refl_symm]
    refine
      Path.Homotopic.cast_trans_trans_homotopic_of_homotopic_cast_mo1973_3460
        (Path.Homotopic.trans (Path.Homotopic.concat_subpath _ _) ?_)
    rw! (castMode := .all) [ht₀, ht₁, Path.subpath_zero_one]
    rfl
  · intro k
    use τ k
    grind [Path.trans_range, Path.symm_range, Set.union_subset, Path.range_subpath]

private instance EuclideanSphere.instLocal1 {n : ℕ} :
    Nonempty ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :=
  Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr (by norm_num))

private instance EuclideanSphere.instLocal2 {n : ℕ} :
    Infinite ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1)) := by
  rw [← Set.infinite_univ_iff]
  have v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1) :=
    Nonempty.some inferInstance
  apply Set.Infinite.of_image (stereographic' (n + 1) v)
  rw [Set.image_univ]
  apply
    Set.Infinite.mono (PartialEquiv.target_subset_range (stereographic' (n + 1) v).toPartialEquiv)
  rw [stereographic'_target]
  exact Set.infinite_univ

private instance EuclideanSphere.instLocal3 (n : ℕ) :
    PathConnectedSpace
      ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  apply isPathConnected_sphere
  · rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact Nat.one_lt_ofNat
  · exact zero_le_one' ℝ

private instance EuclideanSphere.instContractibleSpace1 {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    ContractibleSpace
      ({ v }ᶜ : Set ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n)) := by
  let proj := stereographic' n v
  have : ContractibleSpace proj.target := by
    rw [stereographic'_target]
    exact Homeomorph.contractibleSpace (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin n)))
  convert Homeomorph.contractibleSpace proj.toHomeomorphSourceTarget <;>
    exact (stereographic'_source v).symm

private theorem EuclideanSphere.isPathConnected_compl_singleton {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1)) :
    IsPathConnected ({ v }ᶜ) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  infer_instance

private lemma EuclideanSphere.stereographic'_symm_zero {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    (stereographic' n v).toPartialEquiv.symm 0 = -v := by
  ext
  simp [stereographic', stereographic, stereoInvFun]

private theorem EuclideanSphere.isPathConnected_compl_singleton_inter_neg {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 2)) :
    IsPathConnected ({ v }ᶜ ∩ {-v}ᶜ) := by
  let proj := stereographic' (n + 2) v
  have : proj.toPartialEquiv.symm '' (proj.target \ {0}) = { v }ᶜ ∩ {-v}ᶜ := by
    rw [PartialEquiv.symm_image_target_minus_singleton_eq, stereographic'_source,
      stereographic'_symm_zero, Set.sdiff_eq]
    rw [stereographic'_target]
    exact Set.mem_univ 0
  rw [← this]
  apply IsPathConnected.image'
  · rw [stereographic'_target, ← Set.compl_eq_univ_sdiff]
    exact
      isPathConnected_compl_singleton_of_one_lt_rank
        (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; exact Nat.one_lt_ofNat) 0
  · exact ContinuousOn.mono proj.continuousOn_invFun Set.sdiff_subset

private abbrev EuclideanSphere.c_mo1973_3470 {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    Fin 2 → Set ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :=
  Fin.cases { v }ᶜ (fun _ ↦ {-v}ᶜ)

private lemma EuclideanSphere.hc₁_mo1973_3471 {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    ∀ i, IsOpen (c_mo1973_3470 v i) := by apply Fin.cases <;> simp

private lemma EuclideanSphere.hc₂_mo1973_3472 {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    Set.univ ⊆ ⋃ i, c_mo1973_3470 v i := by
  intro s _
  rcases eq_or_ne s v with rfl | h
  · rw [Set.mem_iUnion]
    use 1
    change
      s ∈ ({-s}ᶜ : Set ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n))
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, ← Ne, ← Subtype.coe_ne_coe, coe_neg_sphere]
    intro hv
    apply (ne_zero_of_mem_unit_sphere s)
    ext k
    rw [PiLp.zero_apply, ← CharZero.eq_neg_self_iff, ← PiLp.neg_apply, ← hv]
  · rw [Set.mem_iUnion]
    use 0
    exact h

private lemma EuclideanSphere.hc₃_mo1973_3473 {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 2)) :
    ∀ i j, IsPathConnected (c_mo1973_3470 v i ∩ c_mo1973_3470 v j) := by
  apply Fin.cases
  · apply Fin.cases
    · simp only [Fin.cases_zero, Set.inter_self]
      exact isPathConnected_compl_singleton v
    · intro _
      simp only [Fin.cases_zero, Fin.cases_succ]
      exact isPathConnected_compl_singleton_inter_neg v
  · intro _
    apply Fin.cases
    · simp only [Fin.cases_succ, Fin.cases_zero, Set.inter_comm]
      exact isPathConnected_compl_singleton_inter_neg v
    · intro _
      simp only [Fin.cases_succ, Set.inter_self]
      exact isPathConnected_compl_singleton (-v)

private lemma EuclideanSphere.hx_mo1973_3474 {n : ℕ}
    (x : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1)) :
    ∃ v, ∀ i : Fin 2, x ∈ c_mo1973_3470 v i := by
  have ⟨v, hv⟩ := Infinite.exists_notMem_finset {x, -x}
  use v
  apply Fin.cases
  · simp only [Fin.cases_zero, Set.mem_compl_singleton_iff]
    intro h
    apply hv
    rw [Finset.mem_insert]
    exact Or.inl h.symm
  · simp only [Fin.cases_succ, Set.mem_compl_singleton_iff]
    intro _ h
    apply hv
    rw [Finset.mem_insert, Finset.mem_singleton, h]
    exact Or.inr (neg_neg v).symm

public
theorem EuclideanSphere.homotopic_refl_of_not_surjective {n : ℕ}
    {v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n} (γ : Path v v)
    (h : ¬(Function.Surjective γ)) : γ.Homotopic (Path.refl v) := by
  unfold Function.Surjective at h
  push Not at h
  obtain ⟨w, hw⟩ := h
  let w_compl : Set ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :=
    { w }ᶜ
  let v' : w_compl :=
    ⟨v, by
      rw [Set.mem_compl_singleton_iff]
      convert hw 0
      exact γ.source.symm⟩
  let f : (unitInterval) → γ ⁻¹' { w }ᶜ := fun x ↦ ⟨x, hw x⟩
  let γ' : Path v' v' :=
    { toFun := γ.restrictPreimage { w }ᶜ ∘ f
      source' := by
        rw [Function.comp_apply, ContinuousMap.restrictPreimage_apply]; ext
        simp [f, v']
      target' := by
        rw [Function.comp_apply, ContinuousMap.restrictPreimage_apply]; ext
        simp [f, v'] }
  have h : SimplyConnectedSpace w_compl := inferInstance
  let incl :
    C(w_compl, (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  exact Path.Homotopic.map ((simply_connected_iff_loops_nullhomotopic.mp h).right v' γ') incl

private protected theorem EuclideanSphere.simplyConnectedSpace (n : ℕ) :
    SimplyConnectedSpace
      ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 2)) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  constructor
  · infer_instance
  · intro x p
    let ⟨v, hv⟩ := hx_mo1973_3474 x
    have ⟨m, D, hDh, hDr⟩ :=
      Path.Homotopic.exists_loops_homotopic_concat_of_open_cover (hc₁_mo1973_3471 v)
        (hc₂_mo1973_3472 v) (hc₃_mo1973_3473 v) hv p
    apply Path.Homotopic.trans hDh.symm
    rw [← Path.concat_refl]
    apply Path.Homotopic.concat_hcomp
    intro k
    have ⟨i, hi⟩ := hDr k
    fin_cases i
    · simp only [Fin.zero_eta, Fin.cases_zero] at hi
      apply homotopic_refl_of_not_surjective
      exact fun h ↦ hi (h v) rfl
    · have : (1 : Fin 2) = Fin.succ 0 := rfl
      simp only [Fin.mk_one, this, Fin.cases_succ] at hi
      apply homotopic_refl_of_not_surjective
      exact fun a ↦ hi (a (-v)) rfl

end Mathoverflow1973

end
