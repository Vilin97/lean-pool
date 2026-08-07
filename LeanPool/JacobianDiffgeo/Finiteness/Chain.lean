/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Finiteness.CompactRestrict
import LeanPool.JacobianDiffgeo.Cech.Cochains

/-!
# `ShrinkChain`: Forster's four-level shrinking chain (`finiteness-and-chi`)

Unit: finiteness-and-chi (`docs/design/finiteness-and-chi.md` D3, §4.2, proof plan §6.4).

`ShrinkChain X` packages Forster's `𝔚 ⋐ 𝔙 ⋐ 𝔘 ⋐ 𝔘*` same-index-set shrinking chain (D3): `U*`
chart disks (Leray-good), `U` the level whose closure sits inside `U*`, `V` the Montel-compact
middle level, `W` the coboundary level whose closure sits inside `V`. All four induced
`FinCover ⊤`s share the same index set, so every refinement map between them is `τ = id`
(`ref_star_U`/`ref_star_V`/`ref_star_W`/`ref_U_V`/`ref_V_W`/`ref_U_W`) — no `τ`-plumbing ever
enters the norm layer.

Existence (`ShrinkChain.nonempty`) iterates the cech `exists_chartDisk_closure_basis` pattern
four times per point (chart disk ⋐ level 1 ⋐ level 2 ⋐ level 3), then extracts a finite subcover
of the innermost level `W`, reindexed by `Finset.equivFin` exactly as `Cech.Covers`'s
`exists_good_refinement_closure` does.

Also provides the Banach cochain layer at one level `P ∈ {U, V, W}`: `NC0`/`NC1` (finite `Pi`s
of `BddHoloOn`), `deltaCLM` (the `0`-to-`1` coboundary, Cech's `d0` transposed to the norm
layer), `NZ1` (bounded cocycles, packaged as `ContinuousLinearMap.ker` of an internal `d1NC` —
closed and complete "for free", no hand-rolled pointwise-condition closedness proof needed),
`resNC0`/`resNC1` (restriction CLMs between same-index levels), the cocycle-relation workhorse
`NZ1.rel_res` (mirrors `Cech.Refinement`'s `Z1.rel_res`), `resNC1_mapsTo_NZ1` (mirrors
`resC1_mem_Z1`), and `resZ` (restriction of bounded cocycles, via
`ContinuousLinearMap.codRestrict`).

Finally, Forster's 14.6(b) Banach geometry (§4.2, §5 step 1): `tradeDefect` (the defect CLM
`(ζ, ξ, η) ↦ ζ|𝔚 − ξ|𝔚 − δ𝔚 η` on `Z¹(𝔘) × Z¹(𝔙) × C⁰(𝔚)`), `tradeSpace` (Forster's subspace
`L ⊆ Z¹(𝔘) × Z¹(𝔙) × C⁰(𝔚)`, its `ContinuousLinearMap.ker` — complete for free), the
membership unfolders `mem_tradeSpace_iff`/`mem_tradeSpace_iff_eq`, and the two Schwartz-cospan
projections `tradePi` (`π = pr₂`, the leg `TradeBounded.lean` proves surjective) and
`tradeCompact` (`v = res_UV ∘ pr₁`, the Montel-compact leg), plus registered instance
shortcuts on `↥(NZ1 T P)`/`↥(tradeSpace T)` that make the surrounding instance searches
reliable (see the note above `NZ1`'s instances and the resolution note at the end of this
file — the former `TODO(blocker)` is RESOLVED). Still deferred (NOT instance-blocked, just
not built here): the two `IsCompactOperator` assembly lemmas of design §4.4
(`isCompactOperator_resZ_UV`, `isCompactOperator_tradeCompact`) — see the end-of-file note.
Nothing here uses the forbidden tactic.
-/

open scoped ContDiff Manifold BoundedContinuousFunction
open Set Filter Topology TopologicalSpace Metric RS.Cech

namespace RS.Finiteness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Forster's `𝔚 ⋐ 𝔙 ⋐ 𝔘 ⋐ 𝔘*` with `𝔘*` chart disks; same index set (D3). -/
structure ShrinkChain (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The number of chart centres in the chain. -/
  n : ℕ
  /-- The chart centres. -/
  c : Fin n → X
  /-- The outermost opens, each inside its centre's chart source. -/
  Ustar : Fin n → Opens X
  /-- The first shrinking: `closure (U i) ⊆ Ustar i`. -/
  U : Fin n → Opens X
  /-- The second shrinking: `closure (V i) ⊆ U i`. -/
  V : Fin n → Opens X
  /-- The innermost opens, which still cover `X`. -/
  W : Fin n → Opens X
  isChartDisk_Ustar : ∀ i, IsChartDisk (Ustar i)
  Ustar_subset_source : ∀ i, (Ustar i : Set X) ⊆ (chartAt ℂ (c i)).source
  closure_U_subset : ∀ i, closure (U i : Set X) ⊆ (Ustar i : Set X)
  closure_V_subset : ∀ i, closure (V i : Set X) ⊆ (U i : Set X)
  closure_W_subset : ∀ i, closure (W i : Set X) ⊆ (V i : Set X)
  covers_W : ∀ x : X, ∃ i, x ∈ W i

namespace ShrinkChain

variable (T : ShrinkChain X)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem W_subset_V (i : Fin T.n) : (T.W i : Set X) ⊆ (T.V i : Set X) :=
  subset_closure.trans (T.closure_W_subset i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem V_subset_U (i : Fin T.n) : (T.V i : Set X) ⊆ (T.U i : Set X) :=
  subset_closure.trans (T.closure_V_subset i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem U_subset_Ustar (i : Fin T.n) : (T.U i : Set X) ⊆ (T.Ustar i : Set X) :=
  subset_closure.trans (T.closure_U_subset i)

/-! `Opens`-level `≤` forms of the chain inclusions — the shapes `restrictCLM`/`resNC1`/`resZ`
consume (definitionally the same statements as the `Set`-level `_subset_` lemmas above). -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem W_le_V (i : Fin T.n) : T.W i ≤ T.V i := T.W_subset_V i

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem V_le_U (i : Fin T.n) : T.V i ≤ T.U i := T.V_subset_U i

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem U_le_Ustar (i : Fin T.n) : T.U i ≤ T.Ustar i := T.U_subset_Ustar i

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem W_le_U (i : Fin T.n) : T.W i ≤ T.U i := (T.W_le_V i).trans (T.V_le_U i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem covers_V (x : X) : ∃ i, x ∈ T.V i := (T.covers_W x).imp (fun i hi => T.W_subset_V i hi)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem covers_U (x : X) : ∃ i, x ∈ T.U i :=
  (T.covers_W x).imp (fun i hi => T.V_subset_U i (T.W_subset_V i hi))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem covers_Ustar (x : X) : ∃ i, x ∈ T.Ustar i :=
  (T.covers_W x).imp (fun i hi => T.U_subset_Ustar i (T.V_subset_U i (T.W_subset_V i hi)))

/-- The four `FinCover ⊤`s induced by a `ShrinkChain`. Reducible: their fields must unfold at
`implicit` transparency, or applications like `C1 D T.coverW` are not type-correct there and
every rewrite in such a goal fails. -/
@[reducible] noncomputable def coverW : FinCover (⊤ : Opens X) where
  n := T.n
  U := T.W
  le_base _ := le_top
  covers x _ := T.covers_W x

/-- The cover of `X` by the `V`-level opens. -/
@[reducible] noncomputable def coverV : FinCover (⊤ : Opens X) where
  n := T.n
  U := T.V
  le_base _ := le_top
  covers x _ := T.covers_V x

/-- The cover of `X` by the `U`-level opens. -/
@[reducible] noncomputable def coverU : FinCover (⊤ : Opens X) where
  n := T.n
  U := T.U
  le_base _ := le_top
  covers x _ := T.covers_U x

/-- The cover of `X` by the outermost `Ustar`-level opens. -/
@[reducible] noncomputable def coverStar : FinCover (⊤ : Opens X) where
  n := T.n
  U := T.Ustar
  le_base _ := le_top
  covers x _ := T.covers_Ustar x

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem good_star : T.coverStar.IsGood := T.isChartDisk_Ustar

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ref_star_U : IsRefIdx T.coverStar T.coverU id := fun i => T.U_subset_Ustar i
omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ref_star_V : IsRefIdx T.coverStar T.coverV id :=
  fun i => (T.V_subset_U i).trans (T.U_subset_Ustar i)
omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ref_star_W : IsRefIdx T.coverStar T.coverW id :=
  fun i => ((T.W_subset_V i).trans (T.V_subset_U i)).trans (T.U_subset_Ustar i)
omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ref_U_V : IsRefIdx T.coverU T.coverV id := fun i => T.V_subset_U i
omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ref_V_W : IsRefIdx T.coverV T.coverW id := fun i => T.W_subset_V i
omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ref_U_W : IsRefIdx T.coverU T.coverW id := fun i => (T.W_subset_V i).trans (T.V_subset_U i)

end ShrinkChain

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **Existence** of a `ShrinkChain` (§6.4): iterate the cech chart-disk-with-compact-closure
basis four times per point, then extract a finite subcover of the innermost level. -/
theorem ShrinkChain.nonempty [T2Space X] [CompactSpace X] : Nonempty (ShrinkChain X) := by
  choose Ustar hUstarGood hxUstar hUstarCompact using
    fun x : X => exists_chartDisk_closure_basis (x := x) (W := (Set.univ : Set X))
      Filter.univ_mem
  choose U hUgood hxU hUsubUstar hUcompact using
    fun x : X => exists_chartDisk_closure_basis (x := x) (W := (Ustar x : Set X))
      ((Ustar x).2.mem_nhds (hxUstar x))
  choose V hVgood hxV hVsubU hVcompact using
    fun x : X => exists_chartDisk_closure_basis (x := x) (W := (U x : Set X))
      ((U x).2.mem_nhds (hxU x))
  choose W hWgood hxW hWsubV hWcompact using
    fun x : X => exists_chartDisk_closure_basis (x := x) (W := (V x : Set X))
      ((V x).2.mem_nhds (hxV x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (W x : Set X)) (fun x => (W x).2) (by
      intro x _
      exact mem_iUnion.2 ⟨x, hxW x⟩)
  classical
  set eF := t.equivFin with heF_def
  set c' : Fin t.card → X := fun k => (eF.symm k : X) with hc'_def
  -- Extract the chart-disk witness point/radius for `Ustar` at each reindexed center.
  choose x' r' hr' hx' hsub' himg' using fun k : Fin t.card => hUstarGood (c' k)
  refine ⟨⟨t.card, x', fun k => Ustar (c' k), fun k => U (c' k), fun k => V (c' k),
    fun k => W (c' k), fun k => ⟨x' k, r' k, hr' k, hx' k, hsub' k, himg' k⟩, hsub', ?_, ?_, ?_,
        ?_⟩⟩
  · exact fun k => hUsubUstar (c' k)
  · exact fun k => hVsubU (c' k)
  · exact fun k => hWsubV (c' k)
  · intro x
    have hxmem : x ∈ ⋃ y ∈ t, (W y : Set X) := ht (mem_univ x)
    simp only [Set.mem_iUnion] at hxmem
    obtain ⟨y, hyt, hxy⟩ := hxmem
    exact ⟨eF ⟨y, hyt⟩, by simpa [hc'_def] using hxy⟩

/-! ### Banach cochain layer at a level `P ∈ {U, V, W}` -/

variable (T : ShrinkChain X) (P P' : Fin T.n → Opens X)

/-- `0`-cochains at level `P` (a finite `Pi` of `BddHoloOn`s). -/
abbrev NC0 : Type _ := ∀ i : Fin T.n, BddHoloOn (P i)

/-- `1`-cochains at level `P` (full product over ordered pairs, no `i < j` convention — matches
cech's D5 convention). -/
abbrev NC1 : Type _ := ∀ p : Fin T.n × Fin T.n, BddHoloOn (P p.1 ⊓ P p.2)

/-- `(δ⁰f)_{ij} = f_j − f_i` (after restriction to `P i ⊓ P j`); the Banach-layer analogue of
`Cech.d0`. -/
noncomputable def deltaCLM : NC0 T P →L[ℂ] NC1 T P :=
  ContinuousLinearMap.pi fun p : Fin T.n × Fin T.n =>
    (restrictCLM (inf_le_right : P p.1 ⊓ P p.2 ≤ P p.2)).comp (ContinuousLinearMap.proj p.2)
    - (restrictCLM (inf_le_left : P p.1 ⊓ P p.2 ≤ P p.1)).comp (ContinuousLinearMap.proj p.1)

@[simp] theorem deltaCLM_apply (f : NC0 T P) (p : Fin T.n × Fin T.n) :
    deltaCLM T P f p = restrictCLM inf_le_right (f p.2) - restrictCLM inf_le_left (f p.1) := rfl

/-- The `1`-to-`2`-cochain coboundary at level `P`, purely internal (used only to package `NZ1`
as a continuous-kernel submodule — no `NC2` is ever exported). -/
noncomputable def d1NC :
    NC1 T P →L[ℂ] ∀ t : Fin T.n × Fin T.n × Fin T.n, BddHoloOn (P t.1 ⊓ P t.2.1 ⊓ P t.2.2) :=
  ContinuousLinearMap.pi fun t : Fin T.n × Fin T.n × Fin T.n =>
    (restrictCLM (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        P t.1 ⊓ P t.2.1 ⊓ P t.2.2 ≤ P t.2.1 ⊓ P t.2.2)).comp
        (ContinuousLinearMap.proj (t.2.1, t.2.2))
    - (restrictCLM (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        P t.1 ⊓ P t.2.1 ⊓ P t.2.2 ≤ P t.1 ⊓ P t.2.2)).comp
        (ContinuousLinearMap.proj (t.1, t.2.2))
    + (restrictCLM (inf_le_left : P t.1 ⊓ P t.2.1 ⊓ P t.2.2 ≤ P t.1 ⊓ P t.2.1)).comp
        (ContinuousLinearMap.proj (t.1, t.2.1))

/-- **Bounded cocycles**: the kernel of `d1NC`, a *closed* submodule (`ContinuousLinearMap.ker`)
— Banach for free (`ContinuousLinearMap.completeSpace_ker`), no hand-rolled pointwise-condition
closedness proof needed. -/
@[simp] theorem d1NC_apply (f : NC1 T P) (t : Fin T.n × Fin T.n × Fin T.n) :
    d1NC T P f t =
      restrictCLM (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (f (t.2.1, t.2.2))
      - restrictCLM (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (f (t.1, t.2.2))
      + restrictCLM inf_le_left (f (t.1, t.2.1)) := rfl

/-- The norm-bounded cocycles at level `P`: the kernel of the bounded coboundary `d1NC`. -/
noncomputable def NZ1 : Submodule ℂ (NC1 T P) := (d1NC T P).ker

instance : CompleteSpace (NZ1 T P) := ContinuousLinearMap.completeSpace_ker (d1NC T P)

/- Instance shortcuts for `↥(NZ1 T P)` (this is the resolution of the file's former
`TODO(blocker)`; see the note at the end of the file). Without these, blind instance search on
the coerced type of this `ContinuousLinearMap.ker`-valued `Submodule` is unreliable: the
`Sub`-of-CLMs instance needed by `tradeDefect` below synthesizes `AddCommGroup ↥(NZ1 T P)` as
a nested subgoal, and that search either times out (default budget) or finds an instance along
a non-canonical path whose `toAddCommMonoid` is not cheaply defeq to the
`Submodule.addCommMonoid` already baked into the goal's CLM type — so the candidate is
rejected outright *no matter the heartbeat budget* (the previously recorded
`IsTopologicalAddGroup` wall was this same failure surfacing one class higher). Registering
the canonical `Submodule.*` instances by hand makes every downstream search find them first
and keeps all cross-instance defeq checks trivial. -/

noncomputable instance : AddCommGroup (NZ1 T P) := (NZ1 T P).addCommGroup

instance : IsTopologicalAddGroup (NZ1 T P) := (NZ1 T P).topologicalAddGroup

noncomputable instance : NormedAddCommGroup (NZ1 T P) := (NZ1 T P).normedAddCommGroup

noncomputable instance : NormedSpace ℂ (NZ1 T P) := (NZ1 T P).normedSpace

theorem mem_NZ1_iff (f : NC1 T P) : f ∈ NZ1 T P ↔ ∀ t, d1NC T P f t = 0 := by
  rw [NZ1, LinearMap.mem_ker]
  exact ⟨fun h t => congrFun h t, fun h => funext h⟩

/-- **The cocycle-relation workhorse** (mirrors `Cech.Refinement`'s `Z1.rel_res`): any
cocycle-relation triple, restricted to any smaller open `W` (via arbitrary — by proof
irrelevance, any — witnessing inequalities). -/
theorem NZ1.rel_res {f : NC1 T P} (hf : f ∈ NZ1 T P) (a b c : Fin T.n) {W : Opens X}
    (h : W ≤ P a ⊓ P b ⊓ P c) (hbc : W ≤ P b ⊓ P c) (hac : W ≤ P a ⊓ P c) (hab : W ≤ P a ⊓ P b) :
    restrictCLM hbc (f (b, c)) - restrictCLM hac (f (a, c)) + restrictCLM hab (f (a, b)) = 0 := by
  have hzero : d1NC T P f (a, b, c) = 0 := (mem_NZ1_iff T P f).1 hf (a, b, c)
  rw [d1NC_apply] at hzero
  have hcongr := congrArg (restrictCLM h) hzero
  simp only [map_add, map_sub, map_zero] at hcongr
  rw [restrictCLM_restrictCLM (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h hbc,
    restrictCLM_restrictCLM (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h hac,
    restrictCLM_restrictCLM inf_le_left h hab] at hcongr
  exact hcongr

/-- Restriction of `0`-cochains along a same-index shrinking `P' ≤ P`. -/
noncomputable def resNC0 (h : ∀ i, P' i ≤ P i) : NC0 T P →L[ℂ] NC0 T P' :=
  ContinuousLinearMap.pi fun i => (restrictCLM (h i)).comp (ContinuousLinearMap.proj i)

/-- Restriction of `1`-cochains along a same-index shrinking `P' ≤ P`. -/
noncomputable def resNC1 (h : ∀ i, P' i ≤ P i) : NC1 T P →L[ℂ] NC1 T P' :=
  ContinuousLinearMap.pi fun p : Fin T.n × Fin T.n =>
    (restrictCLM (inf_le_inf (h p.1) (h p.2))).comp (ContinuousLinearMap.proj p)

@[simp] theorem resNC1_apply (h : ∀ i, P' i ≤ P i) (f : NC1 T P) (p : Fin T.n × Fin T.n) :
    resNC1 T P P' h f p = restrictCLM (inf_le_inf (h p.1) (h p.2)) (f p) := rfl

/-- Restriction takes bounded cocycles to bounded cocycles (naturality of `d1NC`, via the
`NZ1.rel_res` workhorse — mirrors `Cech.Refinement`'s `resC1_mem_Z1`). -/
theorem resNC1_mapsTo_NZ1 (h : ∀ i, P' i ≤ P i) {f : NC1 T P} (hf : f ∈ NZ1 T P) :
    resNC1 T P P' h f ∈ NZ1 T P' := by
  rw [mem_NZ1_iff]
  rintro ⟨k, l, m⟩
  rw [d1NC_apply, resNC1_apply, resNC1_apply, resNC1_apply]
  have hkh : P' k ⊓ P' l ⊓ P' m ≤ P (k) := (inf_le_left.trans inf_le_left).trans (h k)
  have hlh : P' k ⊓ P' l ⊓ P' m ≤ P l := (inf_le_left.trans inf_le_right).trans (h l)
  have hmh : P' k ⊓ P' l ⊓ P' m ≤ P m := inf_le_right.trans (h m)
  have key := NZ1.rel_res T P hf k l m
    (le_inf (le_inf hkh hlh) hmh) (le_inf hlh hmh) (le_inf hkh hmh) (le_inf hkh hlh)
  rw [restrictCLM_restrictCLM (inf_le_inf (h l) (h m))
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf hlh hmh),
    restrictCLM_restrictCLM (inf_le_inf (h k) (h m))
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf hkh hmh),
    restrictCLM_restrictCLM (inf_le_inf (h k) (h l)) inf_le_left (le_inf hkh hlh)]
  exact key

/-- Restriction of bounded cocycles between same-index levels. -/
noncomputable def resZ (h : ∀ i, P' i ≤ P i) : NZ1 T P →L[ℂ] NZ1 T P' :=
  ((resNC1 T P P' h).comp (NZ1 T P).subtypeL).codRestrict (NZ1 T P')
    (fun f => resNC1_mapsTo_NZ1 T P P' h f.2)

/-! ### Forster 14.6(b): the trade subspace `L` and its two Schwartz-cospan projections -/

/-- **Forster 14.6(b)'s defect map** `(ζ, ξ, η) ↦ ζ|𝔚 − ξ|𝔚 − δ𝔚 η` on the triple product
`Z¹(𝔘) × Z¹(𝔙) × C⁰(𝔚)` (§4.2/§5 step 1); its kernel is Forster's subspace `L`
(`tradeSpace`). -/
noncomputable def tradeDefect :
    (NZ1 T T.U × NZ1 T T.V × NC0 T T.W) →L[ℂ] NC1 T T.W :=
  (resNC1 T T.U T.W T.W_le_U).comp
      ((NZ1 T T.U).subtypeL.comp
        (ContinuousLinearMap.fst ℂ (NZ1 T T.U) (NZ1 T T.V × NC0 T T.W)))
    - (resNC1 T T.V T.W T.W_le_V).comp
      ((NZ1 T T.V).subtypeL.comp
        ((ContinuousLinearMap.fst ℂ (NZ1 T T.V) (NC0 T T.W)).comp
          (ContinuousLinearMap.snd ℂ (NZ1 T T.U) (NZ1 T T.V × NC0 T T.W))))
    - (deltaCLM T T.W).comp
      ((ContinuousLinearMap.snd ℂ (NZ1 T T.V) (NC0 T T.W)).comp
        (ContinuousLinearMap.snd ℂ (NZ1 T T.U) (NZ1 T T.V × NC0 T T.W)))

@[simp] theorem tradeDefect_apply
    (x : NZ1 T T.U × NZ1 T T.V × NC0 T T.W) (p : Fin T.n × Fin T.n) :
    tradeDefect T x p =
      restrictCLM (inf_le_inf (T.W_le_U p.1) (T.W_le_U p.2)) ((x.1 : NC1 T T.U) p)
      - restrictCLM (inf_le_inf (T.W_le_V p.1) (T.W_le_V p.2)) ((x.2.1 : NC1 T T.V) p)
      - (restrictCLM inf_le_right (x.2.2 p.2) - restrictCLM inf_le_left (x.2.2 p.1)) := rfl

/-- **Forster's subspace `L`** (14.6(b)): triples `(ζ, ξ, η)` with `ζ = ξ + δη` on `𝔚`,
packaged as `ContinuousLinearMap.ker` (closed, hence complete for free). -/
noncomputable def tradeSpace :
    Submodule ℂ (NZ1 T T.U × NZ1 T T.V × NC0 T T.W) :=
  (tradeDefect T).ker

theorem mem_tradeSpace_iff (x : NZ1 T T.U × NZ1 T T.V × NC0 T T.W) :
    x ∈ tradeSpace T ↔ ∀ p : Fin T.n × Fin T.n, tradeDefect T x p = 0 := by
  rw [tradeSpace, LinearMap.mem_ker]
  exact ⟨fun h p => congrFun h p, fun h => funext h⟩

/-- Membership in `L`, rearranged to Forster's `ζ = ξ + δη` shape on each `𝔚`-pair (the form
`TradeBounded.lean`'s §5 steps 2/6/8 consume). -/
theorem mem_tradeSpace_iff_eq (x : NZ1 T T.U × NZ1 T T.V × NC0 T T.W) :
    x ∈ tradeSpace T ↔ ∀ p : Fin T.n × Fin T.n,
      restrictCLM (inf_le_inf (T.W_le_U p.1) (T.W_le_U p.2)) ((x.1 : NC1 T T.U) p)
        = restrictCLM (inf_le_inf (T.W_le_V p.1) (T.W_le_V p.2)) ((x.2.1 : NC1 T T.V) p)
          + (restrictCLM inf_le_right (x.2.2 p.2) - restrictCLM inf_le_left (x.2.2 p.1)) := by
  rw [mem_tradeSpace_iff]
  refine forall_congr' fun p => ?_
  rw [tradeDefect_apply T x p, sub_sub, sub_eq_zero]

instance : CompleteSpace (tradeSpace T) :=
  ContinuousLinearMap.completeSpace_ker (tradeDefect T)

/- Same instance-shortcut rationale as at `NZ1`: `tradeSpace T` is the Schwartz source `E` of
`schwartz_finite_cospan (u := tradePi T) (v := tradeCompact T)` in `H1Finite.lean`'s §6.5
assembly, which needs `[NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]`. -/

noncomputable instance : NormedAddCommGroup (tradeSpace T) :=
  (tradeSpace T).normedAddCommGroup

noncomputable instance : NormedSpace ℂ (tradeSpace T) :=
  (tradeSpace T).normedSpace

/-- **The surjective leg** `π : L →L Z¹(𝔙)`, `(ζ, ξ, η) ↦ ξ` (14.6(b)'s projection;
surjectivity = the qualitative trade, proved in `TradeBounded.lean` as `tradePi_surjective`;
the norm constant of 14.6(b) is recovered inside `schwartz_finite_cospan` by
`exists_preimage_norm_le` — design §5 step 7). -/
noncomputable def tradePi : tradeSpace T →L[ℂ] NZ1 T T.V :=
  (ContinuousLinearMap.fst ℂ (NZ1 T T.V) (NC0 T T.W)).comp
    ((ContinuousLinearMap.snd ℂ (NZ1 T T.U) (NZ1 T T.V × NC0 T T.W)).comp
      (tradeSpace T).subtypeL)

/-- **The compact leg** `v : L →L Z¹(𝔙)`, `(ζ, ξ, η) ↦ ζ|𝔙` (compactness = Montel, assembled
from `isCompactOperator_restrictCLM` — deferred, see the end-of-file note). -/
noncomputable def tradeCompact : tradeSpace T →L[ℂ] NZ1 T T.V :=
  (resZ T T.U T.V T.V_le_U).comp
    ((ContinuousLinearMap.fst ℂ (NZ1 T T.U) (NZ1 T T.V × NC0 T T.W)).comp
      (tradeSpace T).subtypeL)

@[simp] theorem tradePi_apply (x : tradeSpace T) :
    tradePi T x = x.1.2.1 := rfl

@[simp] theorem tradeCompact_apply (x : tradeSpace T) :
    tradeCompact T x = resZ T T.U T.V T.V_le_U x.1.1 := rfl

/- NOTE (resolution of the former `TODO(blocker)`; recorded for future units). The four trade
declarations above were blocked by what looked like an `IsTopologicalAddGroup`-on-`NZ1`
synthesis timeout. The real failure mode (found by elaborating the `Sub`-of-CLMs instance
piece by piece): any instance whose *conclusion type re-mentions structure instances of the
domain* — e.g. `ContinuousLinearMap.sub`, which must unify its `AddCommGroup.toAddCommMonoid`
against the `Submodule.addCommMonoid` already baked into the goal's CLM type — forces a blind
`AddCommGroup ↥(NZ1 …)` search whose result, found along a non-canonical path, is *rejected*
by that defeq check no matter the heartbeat budget (bumping to 4M never helped because the
failure is a rejection, not a timeout). Fix: the `noncomputable instance` shortcuts registered
after `NZ1`'s `CompleteSpace` instance above pin the canonical `Submodule.*` instances, making
the searches deterministic and the defeq checks trivial; the `Sub` then resolves with an
ordinary `synthInstance.maxHeartbeats 1000000` bump. Verified downstream (scratch, this
session): `schwartz_finite_cospan (u := tradePi T) (v := tradeCompact T)` and
`finiteDimensional_of_cospan` both type-check against these declarations with an 800000 bump —
`TradeBounded.lean`/`H1Finite.lean`'s §5/§6.5 consumption shapes are viable as designed.
Still deferred (NOT instance-blocked; simply not built, as they are `TradeBounded.lean`-gate
work): the two `IsCompactOperator` assembly lemmas of design §4.4/§6.3-step-5
(`isCompactOperator_resZ_UV` — finite-`Pi`/product assembly of `CompactRestrict.lean`'s
single-chart Montel lemma — and `isCompactOperator_tradeCompact` — that plus
`IsCompactOperator.comp_clm` through `pr₁ ∘ subtypeL`). -/

end RS.Finiteness
