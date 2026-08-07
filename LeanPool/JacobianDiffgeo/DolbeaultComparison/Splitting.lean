/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.DolbeaultComparison.GlueForm01
import LeanPool.JacobianDiffgeo.Cech.Refinement

/-!
# PoU splitting of a Čech `0`-cocycle (`Jacobian/DolbeaultComparison/Splitting.lean`)

Unit: dolbeault-comparison (`docs/design/dolbeault-comparison.md` §4.3/§6.2/§6.3). Builds the
Forster 12.6 "smooth splitting" of a `D = 0` Čech cocycle by a partition of unity, and packages
each splitting's PDE data as a `DbarGlueData` (via `GlueForm01.lean`), whose glued form
`dolbForm h𝒰 f` is independent of the chosen splitting modulo `range dbar` — the input to
`Comparison.lean`'s Čech → Dolbeault map.

* `Z1.repr`: pointwise holomorphic representatives of a `D = 0` cocycle's components.
* `Z1.repr_cocycle`/`Z1.repr_add`/`Z1.repr_smul`: pointwise algebraic identities on pair-meets.
* `SmoothSplitting`, `exists_smoothSplitting` (D5 formula, via `RS.exists_smoothPartitionOfUnity`).
* `SmoothSplitting.glueData`, `dolbForm`.
* Independence lemmas, all reducing to `DbarGlueData.form_unique`
  (`sub_mem_range_dbar_of_splittings`, `dolbForm_add_sub_mem`, `dolbForm_smul_sub_mem`,
  `dolbForm_mem_range_of_mem_B1`, `dolbForm_res_sub_mem`).
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Dolb

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `Z1.repr`: pointwise holomorphic representatives -/

/-- Pointwise holomorphic representative of a component of a `D = 0` cocycle. -/
noncomputable def Z1.repr {𝒰 : FinCover (⊤ : Opens X)} (f : Z1 (0 : RS.Divisor X) 𝒰)
    (p : Fin 𝒰.n × Fin 𝒰.n) : X → ℂ :=
  RS.MeroGermOn.holoRepr
    ((f : C1 (0 : RS.Divisor X) 𝒰) p : RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X))

theorem Z1.repr_contMDiffOn {𝒰 : FinCover (⊤ : Opens X)} (f : Z1 (0 : RS.Divisor X) 𝒰)
    (p : Fin 𝒰.n × Fin 𝒰.n) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (Z1.repr f p) (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X) := by
  change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (RS.MeroGermOn.holoRepr ((f : C1 (0 : RS.Divisor X) 𝒰) p :
        RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X))) (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)
  apply RS.MeroGermOn.holoRepr_contMDiffOn (𝒰.U p.1 ⊓ 𝒰.U p.2).isOpen
  intro x hx
  exact (RS.mem_linSysOn_iff_of_isOpen (𝒰.U p.1 ⊓ 𝒰.U p.2).isOpen).1
    ((f : C1 (0 : RS.Divisor X) 𝒰) p).2 x hx

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Pointwise cocycle identity (via `evalAt` rigidity; same pattern as dbar DiskAcyclic's
member-splitting computation). -/
theorem Z1.repr_cocycle {𝒰 : FinCover (⊤ : Opens X)} (f : Z1 (0 : RS.Divisor X) 𝒰)
    {a b c : Fin 𝒰.n} {x : X} (hx : x ∈ (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X)) :
    Z1.repr f (b, c) x - Z1.repr f (a, c) x + Z1.repr f (a, b) x = 0 := by
  have hmem : (f : C1 (0 : RS.Divisor X) 𝒰) ∈ Z1 (0 : RS.Divisor X) 𝒰 := f.2
  have hbc : 𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c ≤ 𝒰.U b ⊓ 𝒰.U c :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hac : 𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c ≤ 𝒰.U a ⊓ 𝒰.U c :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hab : 𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c ≤ 𝒰.U a ⊓ 𝒰.U b := inf_le_left
  have hrel := RS.Cech.Z1.rel_res (0 : RS.Divisor X) hmem a b c (le_refl _) hbc hac hab
  have hrelv : (RS.MeroGermOn.restrict hbc
        ((f : C1 (0 : RS.Divisor X) 𝒰) (b, c) : RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))) -
      (RS.MeroGermOn.restrict hac
        ((f : C1 (0 : RS.Divisor X) 𝒰) (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))) +
      (RS.MeroGermOn.restrict hab
        ((f : C1 (0 : RS.Divisor X) 𝒰) (a, b) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X))) = 0 := by
    have hcast := congrArg Subtype.val hrel
    exact hcast
  have hordbc : 0 ≤ ((f : C1 (0 : RS.Divisor X) 𝒰) (b, c) :
      RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X)).ord x := by
    have h := (RS.mem_linSysOn_iff_of_isOpen (𝒰.U b ⊓ 𝒰.U c).isOpen).1
      ((f : C1 (0 : RS.Divisor X) 𝒰) (b, c)).2 x (hbc hx)
    simpa using h
  have hordab : 0 ≤ ((f : C1 (0 : RS.Divisor X) 𝒰) (a, b) :
      RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X)).ord x := by
    have h := (RS.mem_linSysOn_iff_of_isOpen (𝒰.U a ⊓ 𝒰.U b).isOpen).1
      ((f : C1 (0 : RS.Divisor X) 𝒰) (a, b)).2 x (hab hx)
    simpa using h
  have hordbc_r : 0 ≤ (RS.MeroGermOn.restrict hbc
      ((f : C1 (0 : RS.Divisor X) 𝒰) (b, c) :
        RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))).ord x := by
    rw [RS.MeroGermOn.ord_restrict hbc (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c).isOpen (𝒰.U b ⊓ 𝒰.U c).isOpen hx]
    exact hordbc
  have hordab_r : 0 ≤ (RS.MeroGermOn.restrict hab
      ((f : C1 (0 : RS.Divisor X) 𝒰) (a, b) :
        RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X))).ord x := by
    rw [RS.MeroGermOn.ord_restrict hab (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c).isOpen (𝒰.U a ⊓ 𝒰.U b).isOpen hx]
    exact hordab
  have hsum : (RS.MeroGermOn.restrict hbc
        ((f : C1 (0 : RS.Divisor X) 𝒰) (b, c) : RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))) +
      (RS.MeroGermOn.restrict hab
        ((f : C1 (0 : RS.Divisor X) 𝒰) (a, b) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X))) =
      (RS.MeroGermOn.restrict hac
        ((f : C1 (0 : RS.Divisor X) 𝒰) (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))) := by
    linear_combination hrelv
  have heval := congrArg (fun ψ => RS.MeroGermOn.evalAt ψ x) hsum
  dsimp only at heval
  rw [RS.MeroGermOn.evalAt_add (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c).isOpen hx hordbc_r hordab_r] at heval
  rw [RS.MeroGermOn.evalAt_restrict hbc (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c).isOpen (𝒰.U b ⊓ 𝒰.U c).isOpen hx,
    RS.MeroGermOn.evalAt_restrict hab (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c).isOpen (𝒰.U a ⊓ 𝒰.U b).isOpen hx,
    RS.MeroGermOn.evalAt_restrict hac (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c).isOpen (𝒰.U a ⊓ 𝒰.U c).isOpen hx]
    at heval
  change ((f : C1 (0 : RS.Divisor X) 𝒰) (b, c) :
      RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X)).evalAt x -
    ((f : C1 (0 : RS.Divisor X) 𝒰) (a, c) :
      RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X)).evalAt x +
    ((f : C1 (0 : RS.Divisor X) 𝒰) (a, b) :
      RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X)).evalAt x = 0
  linear_combination heval

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem Z1.repr_add {𝒰 : FinCover (⊤ : Opens X)} (f f' : Z1 (0 : RS.Divisor X) 𝒰)
    (p : Fin 𝒰.n × Fin 𝒰.n) {x : X} (hx : x ∈ (𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X)) :
    Z1.repr (f + f') p x = Z1.repr f p x + Z1.repr f' p x := by
  have hordf : 0 ≤ ((f : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)).ord x :=
    (RS.mem_linSysOn_iff_of_isOpen (𝒰.U p.1 ⊓ 𝒰.U p.2).isOpen).1
      ((f : C1 (0 : RS.Divisor X) 𝒰) p).2 x hx
  have hordf' : 0 ≤ ((f' : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)).ord x :=
    (RS.mem_linSysOn_iff_of_isOpen (𝒰.U p.1 ⊓ 𝒰.U p.2).isOpen).1
      ((f' : C1 (0 : RS.Divisor X) 𝒰) p).2 x hx
  have hpeq : (((f + f' : Z1 (0 : RS.Divisor X) 𝒰) : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)) =
      (f : C1 (0 : RS.Divisor X) 𝒰) p + (f' : C1 (0 : RS.Divisor X) 𝒰) p := by
    simp only [Submodule.coe_add]; rfl
  change (((f + f' : Z1 (0 : RS.Divisor X) 𝒰) : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)).evalAt x =
    ((f : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)).evalAt x +
    ((f' : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)).evalAt x
  rw [hpeq]
  exact RS.MeroGermOn.evalAt_add (𝒰.U p.1 ⊓ 𝒰.U p.2).isOpen hx hordf hordf'

theorem Z1.repr_smul {𝒰 : FinCover (⊤ : Opens X)} (c : ℂ) (f : Z1 (0 : RS.Divisor X) 𝒰)
    (p : Fin 𝒰.n × Fin 𝒰.n) {x : X} (hx : x ∈ (𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X)) :
    Z1.repr (c • f) p x = c * Z1.repr f p x := by
  have hordf : 0 ≤ ((f : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)).ord x :=
    (RS.mem_linSysOn_iff_of_isOpen (𝒰.U p.1 ⊓ 𝒰.U p.2).isOpen).1
      ((f : C1 (0 : RS.Divisor X) 𝒰) p).2 x hx
  have hpeq : (((c • f : Z1 (0 : RS.Divisor X) 𝒰) : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)) =
      c • (f : C1 (0 : RS.Divisor X) 𝒰) p := by
    simp only [Submodule.coe_smul]; rfl
  change (((c • f : Z1 (0 : RS.Divisor X) 𝒰) : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)).evalAt x =
    c * ((f : C1 (0 : RS.Divisor X) 𝒰) p :
      RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X)).evalAt x
  rw [hpeq]
  exact RS.MeroGermOn.evalAt_smul (𝒰.U p.1 ⊓ 𝒰.U p.2).isOpen hx hordf

/-! ### Extension-by-zero smul lemma -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Extension-by-zero workhorse: `ψ` globally smooth with `tsupport ψ ⊆ W`, `F` smooth on
`W ⊓ U` ⇒ `fun x => ψ x • F x` is smooth on `U` (values off `W` are junk-irrelevant: `ψ`
vanishes there). -/
theorem contMDiffOn_smul_of_tsupport_subset {ψ : X → ℝ} {F : X → ℂ} {W U : Opens X}
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ ψ) (hsupp : tsupport ψ ⊆ (W : Set X))
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F (W ⊓ U : Set X)) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => ψ x • F x) (U : Set X) := by
  intro x hx
  by_cases hxW : x ∈ (W : Set X)
  · have hxWU : x ∈ (W ⊓ U : Opens X) := ⟨hxW, hx⟩
    exact ((hψ x).smul (hF.contMDiffAt ((W ⊓ U).isOpen.mem_nhds hxWU))).contMDiffWithinAt
  · have hzero : ψ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      have hnhds : (tsupport ψ)ᶜ ∈ nhds x :=
        (isClosed_tsupport ψ).isOpen_compl.mem_nhds (fun hmem => hxW (hsupp hmem))
      filter_upwards [hnhds] with y hy
      by_contra hne
      exact hy (subset_tsupport ψ hne)
    have heq : (fun x => ψ x • F x) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hzero] with y hy
      show ψ y • F y = 0
      rw [hy]; simp
    exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Finite sums of `ContMDiffOn` functions are `ContMDiffOn` (no generic lemma found at the
pin for `ContMDiffOn`; proved by `Finset.induction`). -/
private theorem contMDiffOn_finset_sum {ι : Type*} (s : Finset ι) {F : ι → X → ℂ}
    {U : Set X} (h : ∀ i ∈ s, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (F i) U) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => ∑ i ∈ s, F i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contMDiffOn_const
  | @insert a s ha ih =>
    have hsub : ∀ i ∈ s, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (F i) U :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hstep : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => F a x + ∑ i ∈ s, F i x) U :=
      (h a (Finset.mem_insert_self a s)).add (ih hsub)
    have heq : (fun x => ∑ i ∈ insert a s, F i x) = (fun x => F a x + ∑ i ∈ s, F i x) := by
      funext x; rw [Finset.sum_insert ha]
    rw [heq]; exact hstep

/-! ### `SmoothSplitting` and its existence -/

/-- A smooth splitting of a `D = 0` cocycle (Forster 12.6 output, D5's frozen sign
convention). -/
structure SmoothSplitting (𝒰 : FinCover (⊤ : Opens X)) (f : Z1 (0 : RS.Divisor X) 𝒰) where
  /-- The member-wise functions realizing the splitting. -/
  g : Fin 𝒰.n → X → ℂ
  smoothOn : ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (g i) (𝒰.U i : Set X)
  split : ∀ i j, ∀ x ∈ (𝒰.U i ⊓ 𝒰.U j : Opens X), Z1.repr f (i, j) x = g j x - g i x

theorem exists_smoothSplitting [T2Space X] [CompactSpace X] (𝒰 : FinCover (⊤ : Opens X))
    (f : Z1 (0 : RS.Divisor X) 𝒰) : Nonempty (SmoothSplitting 𝒰 f) := by
  have hcov : (univ : Set X) ⊆ ⋃ i, (𝒰.U i : Set X) := by
    intro x _
    obtain ⟨i, hi⟩ := 𝒰.covers x trivial
    exact mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨p, hsub⟩ := RS.exists_smoothPartitionOfUnity (fun i => (𝒰.U i : Set X))
    (fun i => (𝒰.U i).isOpen) hcov
  refine ⟨⟨fun i x => ∑ k, p k x • Z1.repr f (k, i) x, ?_, ?_⟩⟩
  · intro i
    apply contMDiffOn_finset_sum
    intro k _
    apply contMDiffOn_smul_of_tsupport_subset (p k).contMDiff (hsub k)
    exact RS.contMDiffOn_real_of_holomorphicOn (𝒰.U k ⊓ 𝒰.U i).isOpen
      (Z1.repr_contMDiffOn f (k, i))
  · intro i j x hx
    have hxi : x ∈ (𝒰.U i : Set X) := hx.1
    have hxj : x ∈ (𝒰.U j : Set X) := hx.2
    change Z1.repr f (i, j) x =
      (∑ k, p k x • Z1.repr f (k, j) x) - (∑ k, p k x • Z1.repr f (k, i) x)
    have hterm : ∀ k : Fin 𝒰.n, p k x • Z1.repr f (k, j) x - p k x • Z1.repr f (k, i) x =
        p k x • Z1.repr f (i, j) x := by
      intro k
      rw [← smul_sub]
      by_cases hpk : (p k) x = 0
      · rw [hpk, zero_smul, zero_smul]
      · have hxk : x ∈ (𝒰.U k : Set X) := hsub k (subset_tsupport (⇑(p k)) hpk)
        have hxkij : x ∈ (𝒰.U k ⊓ 𝒰.U i ⊓ 𝒰.U j : Opens X) := ⟨⟨hxk, hxi⟩, hxj⟩
        have hcoc := Z1.repr_cocycle f hxkij
        have heq : Z1.repr f (k, j) x - Z1.repr f (k, i) x = Z1.repr f (i, j) x := by
          linear_combination -hcoc
        rw [heq]
    have hsum1 : ∑ k : Fin 𝒰.n, (p k) x = 1 := by
      rw [← finsum_eq_sum_of_fintype]
      exact p.sum_eq_one (mem_univ x)
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_smul,
      hsum1, one_smul]

/-! ### `SmoothSplitting.glueData`, `dolbForm` -/

/-- The glue data of a splitting on a GOOD cover, and its glued form (design §6.2). -/
noncomputable def SmoothSplitting.glueData {𝒰 : FinCover (⊤ : Opens X)} (h𝒰 : 𝒰.IsGood)
    {f : Z1 (0 : RS.Divisor X) 𝒰} (s : SmoothSplitting 𝒰 f) : DbarGlueData X where
  n := 𝒰.n
  V := 𝒰.U
  covers := fun x => 𝒰.covers x trivial
  center := fun i => (h𝒰 i).choose
  subChart := fun i => (h𝒰 i).choose_spec.choose_spec.2.2.1
  u := s.g
  smoothOn := s.smoothOn
  holoSub := fun i j => by
    have hcong : ∀ x ∈ (𝒰.U i ⊓ 𝒰.U j : Set X), (s.g i - s.g j) x = -(Z1.repr f (i, j) x) := by
      intro x hx
      change s.g i x - s.g j x = -(Z1.repr f (i, j) x)
      have h := s.split i j x hx
      linear_combination h
    exact ((Z1.repr_contMDiffOn f (i, j)).neg).congr hcong

/-- The glued form of a chosen splitting of `f` on a good cover: the comparison map's core
per-cover output (design §6.2). -/
noncomputable def dolbForm [T2Space X] [CompactSpace X] {𝒰 : FinCover (⊤ : Opens X)}
    (h𝒰 : 𝒰.IsGood) (f : Z1 (0 : RS.Divisor X) 𝒰) : Form01 X :=
  ((exists_smoothSplitting 𝒰 f).some.glueData h𝒰).form

/-! ### Compat: `IsDbarOn.add`/`IsDbarOn.congr` -/

theorem IsDbarOn.add {u v : X → ℂ} {θ η : Form01 X} {s : Set X} (hs : IsOpen s)
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u s) (hv : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ v s)
    (h1 : IsDbarOn u θ s) (h2 : IsDbarOn v η s) : IsDbarOn (u + v) (θ + η) s := by
  intro x hx
  change wirtingerDbar ((u + v) ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
    (θ + η).coeffAt x (chartAt ℂ x x)
  have hequ : (u + v) ∘ ⇑(chartAt ℂ x).symm =
      (u ∘ ⇑(chartAt ℂ x).symm) + (v ∘ ⇑(chartAt ℂ x).symm) := by funext y; simp
  have hud : DifferentiableAt ℝ (u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (RS.contMDiffAt_real_iff_contDiffAt.1
      ((hu x hx).contMDiffAt (hs.mem_nhds hx))).differentiableAt (by norm_num)
  have hvd : DifferentiableAt ℝ (v ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (RS.contMDiffAt_real_iff_contDiffAt.1
      ((hv x hx).contMDiffAt (hs.mem_nhds hx))).differentiableAt (by norm_num)
  rw [hequ, wirtingerDbar_add _ _ (chartAt ℂ x x) hud hvd, h1 x hx, h2 x hx]
  exact (Form01.coeffAt_add θ η x (chartAt ℂ x x)).symm

theorem IsDbarOn.congr {u₁ u₂ : X → ℂ} {θ : Form01 X} {s : Set X} (hs : IsOpen s)
    (h : Set.EqOn u₁ u₂ s) (hu : IsDbarOn u₁ θ s) : IsDbarOn u₂ θ s := by
  intro x hx
  have heq : (u₁ ∘ ⇑(chartAt ℂ x).symm) =ᶠ[nhds (chartAt ℂ x x)]
      (u₂ ∘ ⇑(chartAt ℂ x).symm) := by
    have hWopen : IsOpen (⇑(chartAt ℂ x) '' (s ∩ (chartAt ℂ x).source)) :=
      (chartAt ℂ x).isOpen_image_of_subset_source (hs.inter (chartAt ℂ x).open_source)
        inter_subset_right
    have hzW : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' (s ∩ (chartAt ℂ x).source) :=
      ⟨x, ⟨hx, mem_chart_source ℂ x⟩, rfl⟩
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    obtain ⟨q, ⟨hqs, hqx⟩, rfl⟩ := hw
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hqx]
    exact h hqs
  change wirtingerDbar (u₂ ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = θ.coeffAt x (chartAt ℂ x x)
  rw [← wirtingerDbar_congr_nhds _ _ (chartAt ℂ x x) heq]
  exact hu x hx

/-! ### Independence lemmas: everything reduces to `DbarGlueData.form_unique` -/

/-- Two splittings of the same cocycle glue to forms differing by `range dbar`. -/
theorem sub_mem_range_dbar_of_splittings {𝒰 : FinCover (⊤ : Opens X)} (h𝒰 : 𝒰.IsGood)
    {f : Z1 (0 : RS.Divisor X) 𝒰} (s s' : SmoothSplitting 𝒰 f) :
    (s.glueData h𝒰).form - (s'.glueData h𝒰).form ∈ LinearMap.range (RS.dbar (X := X)) := by
  classical
  set idx : X → Fin 𝒰.n := fun x => (𝒰.covers x trivial).choose with hidx_def
  have hidx : ∀ x, x ∈ (𝒰.U (idx x) : Set X) := fun x => (𝒰.covers x trivial).choose_spec
  set w : X → ℂ := fun x => s.g (idx x) x - s'.g (idx x) x with hw_def
  have hagree : ∀ (i : Fin 𝒰.n) {x : X}, x ∈ (𝒰.U i : Set X) → w x = s.g i x - s'.g i x := by
    intro i x hxi
    change s.g (idx x) x - s'.g (idx x) x = s.g i x - s'.g i x
    have hxmem : x ∈ (𝒰.U i ⊓ 𝒰.U (idx x) : Opens X) := ⟨hxi, hidx x⟩
    have h1 := s.split i (idx x) x hxmem
    have h2 := s'.split i (idx x) x hxmem
    linear_combination h2 - h1
  have hCM : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ w := by
    intro x₀
    have hCM0 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => s.g (idx x₀) x - s'.g (idx x₀) x)
        (𝒰.U (idx x₀) : Set X) := (s.smoothOn (idx x₀)).sub (s'.smoothOn (idx x₀))
    have hCMAt : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (fun x => s.g (idx x₀) x - s'.g (idx x₀) x) x₀ :=
      hCM0.contMDiffAt ((𝒰.U (idx x₀)).isOpen.mem_nhds (hidx x₀))
    apply hCMAt.congr_of_eventuallyEq
    filter_upwards [(𝒰.U (idx x₀)).isOpen.mem_nhds (hidx x₀)] with y hy
    exact hagree (idx x₀) hy
  have hkey : (s'.glueData h𝒰).form + RS.dbar ⟨w, hCM⟩ = (s.glueData h𝒰).form := by
    apply DbarGlueData.form_unique
    intro i x hxi
    have hIsDbarOnSum : IsDbarOn (s'.g i + w) ((s'.glueData h𝒰).form + RS.dbar ⟨w, hCM⟩)
        (𝒰.U i : Set X) :=
      IsDbarOn.add (𝒰.U i).isOpen (s'.smoothOn i) hCM.contMDiffOn
        ((s'.glueData h𝒰).isDbarOn_form i) (fun y _ => RS.isDbarOn_dbar ⟨w, hCM⟩ y trivial)
    have hcongr : Set.EqOn (s'.g i + w) (s.g i) (𝒰.U i : Set X) := fun y hy => by
      change s'.g i y + w y = s.g i y
      rw [hagree i hy]; ring
    exact IsDbarOn.congr (𝒰.U i).isOpen hcongr hIsDbarOnSum x hxi
  refine ⟨⟨w, hCM⟩, ?_⟩
  rw [← hkey]; abel

/-- `dolbForm` kills coboundaries. -/
theorem dolbForm_mem_range_of_mem_B1 [T2Space X] [CompactSpace X] {𝒰 : FinCover (⊤ : Opens X)}
    (h𝒰 : 𝒰.IsGood) {f : Z1 (0 : RS.Divisor X) 𝒰}
    (hf : (f : C1 (0 : RS.Divisor X) 𝒰) ∈ B1 (0 : RS.Divisor X) 𝒰) :
    dolbForm h𝒰 f ∈ LinearMap.range (RS.dbar (X := X)) := by
  obtain ⟨c, hc⟩ := hf
  have hordc : ∀ i, ∀ x ∈ (𝒰.U i : Set X), 0 ≤ (c i : RS.MeroGermOn X (𝒰.U i : Set X)).ord x :=
    fun i x hx => by
      have h := (RS.mem_linSysOn_iff_of_isOpen (𝒰.U i).isOpen).1 (c i).2 x hx
      simpa using h
  set g : Fin 𝒰.n → X → ℂ :=
    fun i => RS.MeroGermOn.holoRepr (c i : RS.MeroGermOn X (𝒰.U i : Set X)) with hg_def
  have hsmoothOn : ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (g i) (𝒰.U i : Set X) := fun i =>
    RS.contMDiffOn_real_of_holomorphicOn (𝒰.U i).isOpen
      (RS.MeroGermOn.holoRepr_contMDiffOn (𝒰.U i).isOpen (hordc i))
  have hsplit : ∀ i j, ∀ x ∈ (𝒰.U i ⊓ 𝒰.U j : Opens X), Z1.repr f (i, j) x = g j x - g i x := by
    intro i j x hx
    have hd0 : (RS.Cech.d0 (0 : RS.Divisor X) 𝒰 c) (i, j) =
        (f : C1 (0 : RS.Divisor X) 𝒰) (i, j) := by rw [hc]
    rw [RS.Cech.d0_apply] at hd0
    have hval : (LinSysOn.restrictL (0 : RS.Divisor X)
          (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U j) (c j) :
          RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)) -
        (LinSysOn.restrictL (0 : RS.Divisor X) (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i) (c i) :
          RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)) =
        ((f : C1 (0 : RS.Divisor X) 𝒰) (i, j) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)) := by
      have hcast := congrArg Subtype.val hd0
      simpa using hcast
    rw [restrictL_apply_coe, restrictL_apply_coe] at hval
    have hordi_r : 0 ≤ (RS.MeroGermOn.restrict (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i)
        (c i : RS.MeroGermOn X (𝒰.U i : Set X))).ord x := by
      rw [RS.MeroGermOn.ord_restrict inf_le_left (𝒰.U i ⊓ 𝒰.U j).isOpen (𝒰.U i).isOpen hx]
      exact hordc i x hx.1
    have hordf : 0 ≤ ((f : C1 (0 : RS.Divisor X) 𝒰) (i, j) :
        RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)).ord x :=
      (RS.mem_linSysOn_iff_of_isOpen (𝒰.U i ⊓ 𝒰.U j).isOpen).1
        ((f : C1 (0 : RS.Divisor X) 𝒰) (i, j)).2 x hx
    have hsum : RS.MeroGermOn.restrict (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i)
          (c i : RS.MeroGermOn X (𝒰.U i : Set X)) +
        ((f : C1 (0 : RS.Divisor X) 𝒰) (i, j) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)) =
        RS.MeroGermOn.restrict (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U j)
          (c j : RS.MeroGermOn X (𝒰.U j : Set X)) := by
      linear_combination -hval
    have heval := congrArg (fun ψ => RS.MeroGermOn.evalAt ψ x) hsum
    dsimp only at heval
    rw [RS.MeroGermOn.evalAt_add (𝒰.U i ⊓ 𝒰.U j).isOpen hx hordi_r hordf,
      RS.MeroGermOn.evalAt_restrict (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i)
        (𝒰.U i ⊓ 𝒰.U j).isOpen (𝒰.U i).isOpen hx,
      RS.MeroGermOn.evalAt_restrict (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U j)
        (𝒰.U i ⊓ 𝒰.U j).isOpen (𝒰.U j).isOpen hx] at heval
    change ((f : C1 (0 : RS.Divisor X) 𝒰) (i, j) :
        RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)).evalAt x =
      (c j : RS.MeroGermOn X (𝒰.U j : Set X)).evalAt x -
        (c i : RS.MeroGermOn X (𝒰.U i : Set X)).evalAt x
    linear_combination heval
  set s0 : SmoothSplitting 𝒰 f := ⟨g, hsmoothOn, hsplit⟩ with hs0_def
  have hIsDbarZero : ∀ i, IsDbarOn (g i) 0 (𝒰.U i : Set X) := by
    intro i x hx
    change wirtingerDbar (g i ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
      (0 : Form01 X).coeffAt x (chartAt ℂ x x)
    rw [Form01.coeffAt_zero]
    have hCMAt : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (g i) x :=
      (RS.MeroGermOn.holoRepr_contMDiffOn (𝒰.U i).isOpen (hordc i)).contMDiffAt
        ((𝒰.U i).isOpen.mem_nhds hx)
    have hAt : AnalyticAt ℂ (g i ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      RS.contMDiffAt_iff_analyticAt_comp_chartAt.1 hCMAt
    exact wirtingerDbar_eq_zero_of_differentiableAt _ _ hAt.differentiableAt
  have hzero : (s0.glueData h𝒰).form = 0 :=
    (DbarGlueData.form_unique (s0.glueData h𝒰) hIsDbarZero).symm
  have hmem0 : (s0.glueData h𝒰).form ∈ LinearMap.range (RS.dbar (X := X)) := by
    rw [hzero]; exact ⟨0, map_zero _⟩
  have hdiff : ((exists_smoothSplitting 𝒰 f).some.glueData h𝒰).form - (s0.glueData h𝒰).form ∈
      LinearMap.range (RS.dbar (X := X)) :=
    sub_mem_range_dbar_of_splittings h𝒰 (exists_smoothSplitting 𝒰 f).some s0
  have hsum : dolbForm h𝒰 f =
      (((exists_smoothSplitting 𝒰 f).some.glueData h𝒰).form - (s0.glueData h𝒰).form) +
        (s0.glueData h𝒰).form := by
    change ((exists_smoothSplitting 𝒰 f).some.glueData h𝒰).form = _
    abel
  rw [hsum]
  exact Submodule.add_mem _ hdiff hmem0

/-- Additivity mod range. -/
theorem dolbForm_add_sub_mem [T2Space X] [CompactSpace X] {𝒰 : FinCover (⊤ : Opens X)}
    (h𝒰 : 𝒰.IsGood) (f f' : Z1 (0 : RS.Divisor X) 𝒰) :
    dolbForm h𝒰 (f + f') - dolbForm h𝒰 f - dolbForm h𝒰 f' ∈
      LinearMap.range (RS.dbar (X := X)) := by
  set sf := (exists_smoothSplitting 𝒰 f).some with hsf_def
  set sf' := (exists_smoothSplitting 𝒰 f').some with hsf'_def
  set ssum := (exists_smoothSplitting 𝒰 (f + f')).some with hssum_def
  set s2 : SmoothSplitting 𝒰 (f + f') :=
    { g := fun i => sf.g i + sf'.g i
      smoothOn := fun i => (sf.smoothOn i).add (sf'.smoothOn i)
      split := fun i j x hx => by
        change Z1.repr (f + f') (i, j) x = (sf.g j x + sf'.g j x) - (sf.g i x + sf'.g i x)
        rw [Z1.repr_add f f' (i, j) hx]
        have h1 := sf.split i j x hx
        have h2 := sf'.split i j x hx
        linear_combination h1 + h2 } with hs2_def
  have hkey : (sf.glueData h𝒰).form + (sf'.glueData h𝒰).form = (s2.glueData h𝒰).form := by
    apply DbarGlueData.form_unique
    intro i x hxi
    exact IsDbarOn.add (𝒰.U i).isOpen (sf.smoothOn i) (sf'.smoothOn i)
      ((sf.glueData h𝒰).isDbarOn_form i) ((sf'.glueData h𝒰).isDbarOn_form i) x hxi
  have hdiff : (ssum.glueData h𝒰).form - (s2.glueData h𝒰).form ∈
      LinearMap.range (RS.dbar (X := X)) := sub_mem_range_dbar_of_splittings h𝒰 ssum s2
  have hsum : dolbForm h𝒰 (f + f') - dolbForm h𝒰 f - dolbForm h𝒰 f' =
      (ssum.glueData h𝒰).form - (s2.glueData h𝒰).form := by
    change (ssum.glueData h𝒰).form - (sf.glueData h𝒰).form - (sf'.glueData h𝒰).form = _
    rw [← hkey]; abel
  rw [hsum]; exact hdiff

/-- Homogeneity mod range. -/
theorem dolbForm_smul_sub_mem [T2Space X] [CompactSpace X] {𝒰 : FinCover (⊤ : Opens X)}
    (h𝒰 : 𝒰.IsGood) (c : ℂ) (f : Z1 (0 : RS.Divisor X) 𝒰) :
    dolbForm h𝒰 (c • f) - c • dolbForm h𝒰 f ∈ LinearMap.range (RS.dbar (X := X)) := by
  set sf := (exists_smoothSplitting 𝒰 f).some with hsf_def
  set scsmul := (exists_smoothSplitting 𝒰 (c • f)).some with hscsmul_def
  set s2 : SmoothSplitting 𝒰 (c • f) :=
    { g := fun i => c • sf.g i
      smoothOn := fun i => by
        have hL : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
            (⇑(ContinuousLinearMap.mul ℝ ℂ c) ∘ sf.g i) (𝒰.U i : Set X) :=
          ((ContinuousLinearMap.mul ℝ ℂ c).contMDiffOn (s := Set.univ)).comp (sf.smoothOn i)
            (fun x _ => Set.mem_univ _)
        have heq : (⇑(ContinuousLinearMap.mul ℝ ℂ c) ∘ sf.g i) = fun x => c • sf.g i x := by
          funext x; simp [ContinuousLinearMap.mul_apply', smul_eq_mul]
        rwa [heq] at hL
      split := fun i j x hx => by
        change Z1.repr (c • f) (i, j) x = c • sf.g j x - c • sf.g i x
        rw [Z1.repr_smul c f (i, j) hx]
        have h1 := sf.split i j x hx
        simp only [smul_eq_mul]
        linear_combination c * h1 } with hs2_def
  have hkey : c • ((sf.glueData h𝒰).form) = (s2.glueData h𝒰).form := by
    apply DbarGlueData.form_unique
    intro i x hxi
    change wirtingerDbar ((c • sf.g i) ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
      (c • (sf.glueData h𝒰).form).coeffAt x (chartAt ℂ x x)
    have heq : (c • sf.g i) ∘ ⇑(chartAt ℂ x).symm =
        fun w => c * (sf.g i ∘ ⇑(chartAt ℂ x).symm) w := by
      funext w; simp
    have hud : DifferentiableAt ℝ (sf.g i ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      (RS.contMDiffAt_real_iff_contDiffAt.1
        ((sf.smoothOn i x hxi).contMDiffAt
          ((𝒰.U i).isOpen.mem_nhds hxi))).differentiableAt (by norm_num)
    rw [heq, wirtingerDbar_const_mul _ (chartAt ℂ x x) c hud]
    have h1 : wirtingerDbar (sf.g i ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
        (sf.glueData h𝒰).form.coeffAt x (chartAt ℂ x x) :=
      (sf.glueData h𝒰).isDbarOn_form i x hxi
    rw [h1]
    change c * (sf.glueData h𝒰).form.coeffAt x (chartAt ℂ x x) =
      (c • (sf.glueData h𝒰).form).coeffAt x (chartAt ℂ x x)
    rw [Form01.coeffAt_smul]
  have hdiff : (scsmul.glueData h𝒰).form - (s2.glueData h𝒰).form ∈
      LinearMap.range (RS.dbar (X := X)) := sub_mem_range_dbar_of_splittings h𝒰 scsmul s2
  have hsum : dolbForm h𝒰 (c • f) - c • dolbForm h𝒰 f =
      (scsmul.glueData h𝒰).form - (s2.glueData h𝒰).form := by
    change (scsmul.glueData h𝒰).form - c • (sf.glueData h𝒰).form = _
    rw [hkey]
  rw [hsum]; exact hdiff

/-- Refinement compatibility mod range (good-to-good). -/
theorem dolbForm_res_sub_mem [T2Space X] [CompactSpace X] {𝒰 𝒱 : FinCover (⊤ : Opens X)}
    (h𝒰 : 𝒰.IsGood) (h𝒱 : 𝒱.IsGood) (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ)
    (f : Z1 (0 : RS.Divisor X) 𝒰) :
    dolbForm h𝒱 (resZ1 (0 : RS.Divisor X) τ hτ f) - dolbForm h𝒰 f ∈
      LinearMap.range (RS.dbar (X := X)) := by
  set s𝒰 := (exists_smoothSplitting 𝒰 f).some with hs𝒰_def
  set s𝒱arb := (exists_smoothSplitting 𝒱 (resZ1 (0 : RS.Divisor X) τ hτ f)).some with hs𝒱arb_def
  set s𝒱 : SmoothSplitting 𝒱 (resZ1 (0 : RS.Divisor X) τ hτ f) :=
    { g := fun k => s𝒰.g (τ k)
      smoothOn := fun k => (s𝒰.smoothOn (τ k)).mono (hτ k)
      split := fun k l x hx => by
        show Z1.repr (resZ1 (0 : RS.Divisor X) τ hτ f) (k, l) x = s𝒰.g (τ l) x - s𝒰.g (τ k) x
        have hxkl : x ∈ (𝒰.U (τ k) ⊓ 𝒰.U (τ l) : Opens X) := ⟨hτ k hx.1, hτ l hx.2⟩
        have heq : Z1.repr (resZ1 (0 : RS.Divisor X) τ hτ f) (k, l) x =
            Z1.repr f (τ k, τ l) x := by
          change ((resZ1 (0 : RS.Divisor X) τ hτ f : C1 (0 : RS.Divisor X) 𝒱) (k, l) :
              RS.MeroGermOn X (𝒱.U k ⊓ 𝒱.U l : Set X)).evalAt x =
            ((f : C1 (0 : RS.Divisor X) 𝒰) (τ k, τ l) :
              RS.MeroGermOn X (𝒰.U (τ k) ⊓ 𝒰.U (τ l) : Set X)).evalAt x
          rw [resZ1_apply_coe, resC1_apply, restrictL_apply_coe]
          exact RS.MeroGermOn.evalAt_restrict (inf_le_inf (hτ k) (hτ l))
            (𝒱.U k ⊓ 𝒱.U l).isOpen (𝒰.U (τ k) ⊓ 𝒰.U (τ l)).isOpen hx
            ((f : C1 (0 : RS.Divisor X) 𝒰) (τ k, τ l))
        rw [heq]
        exact s𝒰.split (τ k) (τ l) x hxkl } with hs𝒱_def
  have hkey : (s𝒰.glueData h𝒰).form = (s𝒱.glueData h𝒱).form := by
    apply DbarGlueData.form_unique
    intro k x hxk
    exact (s𝒰.glueData h𝒰).isDbarOn_form (τ k) x (hτ k hxk)
  have hdiff : (s𝒱arb.glueData h𝒱).form - (s𝒱.glueData h𝒱).form ∈
      LinearMap.range (RS.dbar (X := X)) := sub_mem_range_dbar_of_splittings h𝒱 s𝒱arb s𝒱
  have hsum : dolbForm h𝒱 (resZ1 (0 : RS.Divisor X) τ hτ f) - dolbForm h𝒰 f =
      (s𝒱arb.glueData h𝒱).form - (s𝒱.glueData h𝒱).form := by
    change (s𝒱arb.glueData h𝒱).form - (s𝒰.glueData h𝒰).form = _
    rw [hkey]
  rw [hsum]; exact hdiff

end RS.Dolb
