/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Directed

/-!
# Finite covers and their refinement preorder (CC8, D2/D3/D4)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.1, D2–D4, proof plans §6.2–§6.3).

* `FinCover Ω` (`Ω : Opens X`): a `Fin n`-indexed family of opens contained in `Ω` and covering
  it. Small (`Type u`, no universe bump).
* Refinement preorder: `𝒰 ≤ 𝒱` iff `𝒱` refines `𝒰` (`IsRefIdx`, `chosenRefIdx`); `FinCover.meet`
  gives pairwise meets, hence `IsDirectedOrder`.
* `IsChartDisk`/`FinCover.IsGood`: chart-disk covers, a cofinal class (`exists_good_refinement`,
  `exists_good_refinement_closure`).
* `FinCover.IsAdapted`: adapted covers (Miranda IX Ex. 3.6), `exists_adapted_refinement`.
-/

open Set Filter Topology TopologicalSpace

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X]

/-! ### `FinCover` and the refinement preorder (D2/D3) -/

/-- A finite cover of the open set `Ω` by opens of `X`, indexed by `Fin n` (D2). -/
structure FinCover (Ω : Opens X) : Type _ where
  /-- The number of members of the cover. -/
  n : ℕ
  /-- The members of the cover. -/
  U : Fin n → Opens X
  le_base : ∀ i, U i ≤ Ω
  covers : ∀ x ∈ Ω, ∃ i, x ∈ U i

variable {Ω : Opens X}

/-- The trivial one-member cover `{Ω}`. -/
def FinCover.single (Ω : Opens X) : FinCover Ω where
  n := 1
  U _ := Ω
  le_base _ := le_rfl
  covers _ hx := ⟨0, hx⟩

instance : Nonempty (FinCover Ω) := ⟨FinCover.single Ω⟩

/-- `τ` is a valid refinement index from `𝒰` to `𝒱`: each member of `𝒱` sits inside the
`τ`-indexed member of `𝒰` (D3). -/
def IsRefIdx (𝒰 𝒱 : FinCover Ω) (τ : Fin 𝒱.n → Fin 𝒰.n) : Prop := ∀ k, 𝒱.U k ≤ 𝒰.U (τ k)

instance : Preorder (FinCover Ω) where
  le 𝒰 𝒱 := ∃ τ, IsRefIdx 𝒰 𝒱 τ
  le_refl 𝒰 := ⟨id, fun _ => le_rfl⟩
  le_trans 𝒰 𝒱 𝒲 h h' :=
    ⟨h.choose ∘ h'.choose, fun k => (h'.choose_spec k).trans (h.choose_spec _)⟩

theorem le_def {𝒰 𝒱 : FinCover Ω} : 𝒰 ≤ 𝒱 ↔ ∃ τ, IsRefIdx 𝒰 𝒱 τ := Iff.rfl

/-- A chosen (classical) refinement index witnessing `𝒰 ≤ 𝒱`. -/
noncomputable def chosenRefIdx {𝒰 𝒱 : FinCover Ω} (h : 𝒰 ≤ 𝒱) : Fin 𝒱.n → Fin 𝒰.n := h.choose

theorem chosenRefIdx_spec {𝒰 𝒱 : FinCover Ω} (h : 𝒰 ≤ 𝒱) : IsRefIdx 𝒰 𝒱 (chosenRefIdx h) :=
  h.choose_spec

/-! ### Pairwise meets and directedness -/

/-- The pairwise meet of two covers (member-wise `⊓`, reindexed by `Fin (m*n) ≃ Fin m × Fin n`). -/
def FinCover.meet (𝒰 𝒱 : FinCover Ω) : FinCover Ω where
  n := 𝒰.n * 𝒱.n
  U p := 𝒰.U (finProdFinEquiv.symm p).1 ⊓ 𝒱.U (finProdFinEquiv.symm p).2
  le_base p := le_trans inf_le_left (𝒰.le_base _)
  covers x hx := by
    obtain ⟨i, hi⟩ := 𝒰.covers x hx
    obtain ⟨j, hj⟩ := 𝒱.covers x hx
    exact ⟨finProdFinEquiv (i, j), by simp [Opens.mem_inf, hi, hj]⟩

theorem le_meet_left (𝒰 𝒱 : FinCover Ω) : 𝒰 ≤ 𝒰.meet 𝒱 :=
  ⟨fun p => (finProdFinEquiv.symm p).1, fun _ => inf_le_left⟩

theorem le_meet_right (𝒰 𝒱 : FinCover Ω) : 𝒱 ≤ 𝒰.meet 𝒱 :=
  ⟨fun p => (finProdFinEquiv.symm p).2, fun _ => inf_le_right⟩

instance : IsDirectedOrder (FinCover Ω) where
  directed 𝒰 𝒱 := ⟨𝒰.meet 𝒱, le_meet_left 𝒰 𝒱, le_meet_right 𝒰 𝒱⟩

noncomputable instance : DecidableEq (FinCover Ω) := Classical.decEq _

/-! ### Chart-disk covers (D4) -/

variable [ChartedSpace ℂ X]

/-- `V` is a chart disk: some chart maps it bijectively onto a round ball (D4). -/
def IsChartDisk (V : Opens X) : Prop :=
  ∃ (x : X) (r : ℝ), 0 < r ∧ x ∈ V ∧ (V : Set X) ⊆ (chartAt ℂ x).source ∧
    chartAt ℂ x '' V = Metric.ball (chartAt ℂ x x) r

/-- A cover all of whose members are chart disks. -/
def FinCover.IsGood (𝒰 : FinCover Ω) : Prop := ∀ i, IsChartDisk (𝒰.U i)

/-- Every neighbourhood of a point contains a chart-disk neighbourhood of it (§6.3). -/
theorem exists_chartDisk_basis {x : X} {W : Set X} (hW : W ∈ 𝓝 x) :
    ∃ V : Opens X, IsChartDisk V ∧ x ∈ V ∧ (V : Set X) ⊆ W := by
  set e := chartAt ℂ x with he_def
  have hxs : x ∈ e.source := mem_chart_source ℂ x
  set O : Set X := e.source ∩ interior W with hO_def
  have hOopen : IsOpen O := e.open_source.inter isOpen_interior
  have hxO : x ∈ O := ⟨hxs, mem_interior_iff_mem_nhds.2 hW⟩
  have hOsub : O ⊆ e.source := inter_subset_left
  have himgOpen : IsOpen (e '' O) := e.isOpen_image_of_subset_source hOopen hOsub
  have hex_mem : e x ∈ e '' O := ⟨x, hxO, rfl⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 himgOpen (e x) hex_mem
  have htarget : Metric.ball (e x) r ⊆ e.target :=
    hsub.trans (fun _ ⟨w, hw, hwe⟩ => hwe ▸ e.map_source (hOsub hw))
  set V0 : Set X := e.symm '' Metric.ball (e x) r with hV0_def
  have hV0open : IsOpen V0 := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball htarget
  have hV0mem : x ∈ V0 := ⟨e x, Metric.mem_ball_self hr, e.left_inv hxs⟩
  refine ⟨⟨V0, hV0open⟩, ⟨x, r, hr, ?_, ?_, ?_⟩, hV0mem, ?_⟩
  · exact hV0mem
  · change V0 ⊆ e.source
    rw [hV0_def, e.symm_image_eq_source_inter_preimage htarget]
    exact inter_subset_left
  · change e '' V0 = Metric.ball (e x) r
    rw [hV0_def]
    exact e.image_symm_image_of_subset_target htarget
  · change V0 ⊆ W
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨w, hw, rfl⟩ := hsub hz
    rw [e.left_inv (hOsub hw)]
    exact interior_subset hw.2

/-- Compact-closure version: the chart-disk neighbourhood can be chosen with compact closure
inside the given neighbourhood (§6.3, needs `[T2Space X]`). -/
theorem exists_chartDisk_closure_basis [T2Space X] {x : X} {W : Set X} (hW : W ∈ 𝓝 x) :
    ∃ V : Opens X, IsChartDisk V ∧ x ∈ V ∧ closure (V : Set X) ⊆ W ∧
      IsCompact (closure (V : Set X)) := by
  set e := chartAt ℂ x with he_def
  have hxs : x ∈ e.source := mem_chart_source ℂ x
  set O : Set X := e.source ∩ interior W with hO_def
  have hOopen : IsOpen O := e.open_source.inter isOpen_interior
  have hxO : x ∈ O := ⟨hxs, mem_interior_iff_mem_nhds.2 hW⟩
  have hOsub : O ⊆ e.source := inter_subset_left
  have himgOpen : IsOpen (e '' O) := e.isOpen_image_of_subset_source hOopen hOsub
  have hex_mem : e x ∈ e '' O := ⟨x, hxO, rfl⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 himgOpen (e x) hex_mem
  have hr2 : (0:ℝ) < r / 2 := by linarith
  have hballsub : Metric.closedBall (e x) (r / 2) ⊆ e '' O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hsub
  have htarget : Metric.closedBall (e x) (r / 2) ⊆ e.target :=
    hballsub.trans (fun _ ⟨w, hw, hwe⟩ => hwe ▸ e.map_source (hOsub hw))
  have htarget' : Metric.ball (e x) (r / 2) ⊆ e.target :=
    (Metric.ball_subset_closedBall).trans htarget
  set V0 : Set X := e.symm '' Metric.ball (e x) (r / 2) with hV0_def
  set K : Set X := e.symm '' Metric.closedBall (e x) (r / 2) with hK_def
  have hV0open : IsOpen V0 := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball htarget'
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (e x) (r / 2)).image_of_continuousOn
      (e.continuousOn_symm.mono htarget)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hV0subK : V0 ⊆ K := Set.image_mono Metric.ball_subset_closedBall
  have hclosureV0 : closure V0 ⊆ K := hKclosed.closure_subset_iff.2 hV0subK
  have hKsubW : K ⊆ W := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨w, hw, rfl⟩ := hballsub hz
    rw [e.left_inv (hOsub hw)]
    exact interior_subset hw.2
  have hV0mem : x ∈ V0 := ⟨e x, Metric.mem_ball_self hr2, e.left_inv hxs⟩
  refine ⟨⟨V0, hV0open⟩, ⟨x, r / 2, hr2, ?_, ?_, ?_⟩, hV0mem, ?_,
    hKcompact.of_isClosed_subset isClosed_closure hclosureV0⟩
  · exact hV0mem
  · change V0 ⊆ e.source
    rw [hV0_def, e.symm_image_eq_source_inter_preimage htarget']
    exact inter_subset_left
  · change e '' V0 = Metric.ball (e x) (r / 2)
    rw [hV0_def]
    exact e.image_symm_image_of_subset_target htarget'
  · change closure V0 ⊆ W
    exact hclosureV0.trans hKsubW

/-- Chart-disk covers are cofinal (§6.3): every cover of `X` admits a good refinement. -/
theorem exists_good_refinement [CompactSpace X] (𝒰 : FinCover (⊤ : Opens X)) :
    ∃ 𝒱, 𝒰 ≤ 𝒱 ∧ 𝒱.IsGood := by
  choose i hi using fun x : X => 𝒰.covers x trivial
  choose V hVgood hVmem hVsub using
    fun x : X => exists_chartDisk_basis (x := x) (W := (𝒰.U (i x) : Set X))
      ((𝒰.U (i x)).2.mem_nhds (hi x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).2) (by
      intro x _
      exact mem_iUnion.2 ⟨x, hVmem x⟩)
  classical
  set e := t.equivFin with he_def
  refine ⟨⟨t.card, fun k => V (e.symm k : X), fun k => le_top, fun x _ => ?_⟩,
    ⟨fun k => i (e.symm k : X), fun k => hVsub (e.symm k : X)⟩, fun k => hVgood (e.symm k : X)⟩
  have hxmem : x ∈ ⋃ y ∈ t, (V y : Set X) := ht (mem_univ x)
  simp only [Set.mem_iUnion] at hxmem
  obtain ⟨y, hyt, hxy⟩ := hxmem
  exact ⟨e ⟨y, hyt⟩, by simpa using hxy⟩

/-- Compact-closure good refinement (§6.3) — the nested-cover input for finiteness-and-chi. -/
theorem exists_good_refinement_closure [CompactSpace X] [T2Space X]
    (𝒰 : FinCover (⊤ : Opens X)) :
    ∃ 𝒱 : FinCover (⊤ : Opens X), ∃ τ : Fin 𝒱.n → Fin 𝒰.n, IsRefIdx 𝒰 𝒱 τ ∧ 𝒱.IsGood ∧
      ∀ k, closure (𝒱.U k : Set X) ⊆ 𝒰.U (τ k) ∧ IsCompact (closure (𝒱.U k : Set X)) := by
  choose i hi using fun x : X => 𝒰.covers x trivial
  choose V hVgood hVmem hVclosure hVcompact using
    fun x : X => exists_chartDisk_closure_basis (x := x) (W := (𝒰.U (i x) : Set X))
      ((𝒰.U (i x)).2.mem_nhds (hi x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).2) (by
      intro x _
      exact mem_iUnion.2 ⟨x, hVmem x⟩)
  classical
  set e := t.equivFin with he_def
  refine ⟨⟨t.card, fun k => V (e.symm k : X), fun k => le_top, fun x _ => ?_⟩,
    fun k => i (e.symm k : X),
    fun k => subset_closure.trans (hVclosure (e.symm k : X)),
    fun k => hVgood (e.symm k : X), fun k => ⟨hVclosure (e.symm k : X), hVcompact (e.symm k : X)⟩⟩
  have hxmem : x ∈ ⋃ y ∈ t, (V y : Set X) := ht (mem_univ x)
  simp only [Set.mem_iUnion] at hxmem
  obtain ⟨y, hyt, hxy⟩ := hxmem
  exact ⟨e ⟨y, hyt⟩, by simpa using hxy⟩

/-! ### Adapted covers (Miranda IX Ex. 3.6) -/

/-- `𝒰` is adapted to the finite set `S`: each point of `S` lies in exactly one member. -/
def FinCover.IsAdapted (𝒰 : FinCover Ω) (S : Finset X) : Prop := ∀ p ∈ S, ∃! i, p ∈ 𝒰.U i

/-- The open complement of a finite set (`[T1Space X]`). -/
def compOpens [T1Space X] (T : Finset X) : Opens X := ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩

omit [ChartedSpace ℂ X] in
theorem mem_compOpens [T1Space X] {T : Finset X} {x : X} :
    x ∈ compOpens T ↔ x ∉ T := by
  change x ∈ ((T : Set X)ᶜ) ↔ x ∉ T
  rw [Set.mem_compl_iff, Finset.mem_coe]

omit [ChartedSpace ℂ X] in
/-- Refine a cover so that it is adapted to a finite set `S ⊆ Ω`, respecting prescribed
neighbourhoods `O p` of each `p ∈ S` (§6.2; pure finite-lattice bookkeeping, `[T1Space X]`).
Deviation from the design doc: an explicit `hS : ∀ p ∈ S, p ∈ Ω` hypothesis is added — without
it `𝒱.IsAdapted S` is unprovable for points of `S` outside `Ω` (every member of a `FinCover Ω`
lies inside `Ω`); every use site has `Ω = ⊤`, where the hypothesis is trivial. -/
theorem exists_adapted_refinement [T1Space X] (𝒰 : FinCover Ω) (S : Finset X)
    (hS : ∀ p ∈ S, p ∈ Ω) (O : X → Opens X) (hO : ∀ p ∈ S, p ∈ O p) :
    ∃ 𝒱, 𝒰 ≤ 𝒱 ∧ 𝒱.IsAdapted S ∧ ∀ p ∈ S, ∀ k, p ∈ 𝒱.U k → 𝒱.U k ≤ O p := by
  classical
  choose i hi using fun (p : X) (hp : p ∈ S) => 𝒰.covers p (hS p hp)
  set A : (↥(S : Finset X)) → Opens X :=
    fun q => O (q : X) ⊓ 𝒰.U (i (q : X) q.2) ⊓ compOpens (S.erase (q : X)) with hA_def
  set B : Fin 𝒰.n → Opens X := fun j => 𝒰.U j ⊓ compOpens S with hB_def
  set idxEquiv : Fin 𝒰.n ⊕ (↥(S : Finset X)) ≃ Fin (𝒰.n + S.card) :=
    (Equiv.sumCongr (Equiv.refl _) S.equivFin).trans finSumFinEquiv with hidx_def
  set Ucov : Fin (𝒰.n + S.card) → Opens X := fun k => Sum.elim B A (idxEquiv.symm k) with hU_def
  set τfun : Fin (𝒰.n + S.card) → Fin 𝒰.n :=
    fun k => Sum.elim id (fun (q : ↥(S : Finset X)) => i (q : X) q.2) (idxEquiv.symm k)
    with hτ_def
  have hAle : ∀ q : ↥(S : Finset X), A q ≤ 𝒰.U (i (q : X) q.2) :=
    fun q => le_trans inf_le_left inf_le_right
  have hBle : ∀ j : Fin 𝒰.n, B j ≤ 𝒰.U j := fun j => inf_le_left
  have hAleO : ∀ q : ↥(S : Finset X), A q ≤ O (q : X) := fun q => le_trans inf_le_left inf_le_left
  -- membership characterizations
  have hmemA : ∀ (q : ↥(S : Finset X)) (x : X), x ∈ A q ↔
      x ∈ O (q : X) ∧ x ∈ 𝒰.U (i (q : X) q.2) ∧ x ∉ S.erase (q : X) := by
    intro q x
    change (x ∈ O (q:X) ∧ x ∈ 𝒰.U (i (q:X) q.2)) ∧ x ∈ compOpens (S.erase (q:X)) ↔ _
    rw [mem_compOpens]
    tauto
  have hmemB : ∀ (j : Fin 𝒰.n) (x : X), x ∈ B j ↔ x ∈ 𝒰.U j ∧ x ∉ S := by
    intro j x
    change x ∈ 𝒰.U j ∧ x ∈ compOpens S ↔ _
    rw [mem_compOpens]
  refine ⟨⟨𝒰.n + S.card, Ucov, ?_, ?_⟩, ⟨τfun, ?_⟩, ?_, ?_⟩
  · -- le_base
    intro k
    rcases hcase : idxEquiv.symm k with j | q
    · simp only [hU_def, hcase]
      exact le_trans (hBle j) (𝒰.le_base j)
    · simp only [hU_def, hcase]
      exact le_trans (hAle q) (𝒰.le_base _)
  · -- covers
    intro x hx
    by_cases hxS : x ∈ S
    · refine ⟨idxEquiv (Sum.inr ⟨x, hxS⟩), ?_⟩
      change x ∈ Sum.elim B A (idxEquiv.symm (idxEquiv (Sum.inr ⟨x, hxS⟩)))
      rw [Equiv.symm_apply_apply]
      change x ∈ A ⟨x, hxS⟩
      rw [hmemA]
      exact ⟨hO x hxS, hi x hxS, Finset.notMem_erase x S⟩
    · obtain ⟨j, hj⟩ := 𝒰.covers x hx
      refine ⟨idxEquiv (Sum.inl j), ?_⟩
      change x ∈ Sum.elim B A (idxEquiv.symm (idxEquiv (Sum.inl j)))
      rw [Equiv.symm_apply_apply]
      change x ∈ B j
      rw [hmemB]
      exact ⟨hj, hxS⟩
  · -- IsRefIdx 𝒰 𝒱
    intro k
    rcases hcase : idxEquiv.symm k with j | q
    · simp only [hU_def, hτ_def, hcase]
      exact hBle j
    · simp only [hU_def, hτ_def, hcase]
      exact hAle q
  · -- IsAdapted
    intro p hp
    refine ⟨idxEquiv (Sum.inr ⟨p, hp⟩), ?_, ?_⟩
    · change p ∈ Sum.elim B A (idxEquiv.symm (idxEquiv (Sum.inr ⟨p, hp⟩)))
      rw [Equiv.symm_apply_apply]
      change p ∈ A ⟨p, hp⟩
      rw [hmemA]
      exact ⟨hO p hp, hi p hp, Finset.notMem_erase p S⟩
    · intro k hk
      simp only [hU_def] at hk
      rcases hcase : idxEquiv.symm k with j | q
      · exfalso
        simp only [hcase] at hk
        have hkB : p ∈ B j := hk
        exact ((hmemB j p).1 hkB).2 hp
      · simp only [hcase] at hk
        have hpq : p ∈ A q := hk
        have hqp : (q : X) = p := by
          by_contra hne
          exact ((hmemA q p).1 hpq).2.2 (Finset.mem_erase_of_ne_of_mem (Ne.symm hne) hp)
        have hqeq : q = ⟨p, hp⟩ := Subtype.ext hqp
        rw [← hqeq, ← hcase, Equiv.apply_symm_apply]
  · -- the O-clause
    intro p hp k hk
    simp only [hU_def] at hk
    rcases hcase : idxEquiv.symm k with j | q
    · exfalso
      simp only [hcase] at hk
      have hkB : p ∈ B j := hk
      exact ((hmemB j p).1 hkB).2 hp
    · simp only [hcase] at hk
      have hpq : p ∈ A q := hk
      have hqp : (q : X) = p := by
        by_contra hne
        exact ((hmemA q p).1 hpq).2.2 (Finset.mem_erase_of_ne_of_mem (Ne.symm hne) hp)
      simp only [hU_def, hcase, ← hqp]
      exact hAleO q

omit [ChartedSpace ℂ X] in
/-- If `𝒰` is adapted to `S`, distinct members meet `S` in at most disjoint points: no member
other than the unique one containing `p` also contains it (immediate from `IsAdapted`, kept as
a named export for the skyscraper unit). -/
theorem FinCover.IsAdapted.not_mem_inf {𝒰 : FinCover Ω} {S : Finset X} (h𝒰 : 𝒰.IsAdapted S) {p : X}
    (hp : p ∈ S) {i j : Fin 𝒰.n} (hij : i ≠ j) : p ∉ 𝒰.U i ⊓ 𝒰.U j := by
  rintro ⟨hi, hj⟩
  obtain ⟨k, -, hk⟩ := h𝒰 p hp
  exact hij ((hk i hi).trans (hk j hj).symm)

end RS.Cech
