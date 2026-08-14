/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Meromorphic
import LeanPool.JacobianDiffgeo.Surface.Bridges
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# `BddHoloOn`: bounded-holomorphic Banach spaces, and the germ bridges (`finiteness-and-chi`)

Unit: finiteness-and-chi (`docs/design/finiteness-and-chi.md` D1, D5, §4.1).

The norm-layer carrier: `BddHoloOn S`, bounded-continuous functions on the open subtype `↥S`
that agree on `S` with some `ContMDiffOn ω` (holomorphic) function. Sup-norm, chart-free
(deviation (D-a) from Forster's `L²` norms — see the design doc §0). This file provides:

* `BddHoloOn S : Submodule ℂ (↥S →ᵇ ℂ)`, `isClosed_bddHoloOn` (uniform limits of holomorphic
  functions are holomorphic, proved chart-locally via `Surface.Bridges` +
  `TendstoLocallyUniformlyOn.differentiableOn`), hence `CompleteSpace (BddHoloOn S)`.
* `restrictCLM`: restriction between nested `BddHoloOn`s, norm `≤ 1`.
* `toGerm`/`evalAt_toGerm`/`toGerm_restrict_comm`: germification into `LinSysOn 0` (D5).
* `restrictGerm`/`toGerm_restrictGerm`/`restrictGerm_toGerm`: de-germification onto a
  compactly-contained smaller open via `holoRepr` (`[T2Space X] [CompactSpace X]`).

D5 (Čech/Banach interface localized here): all germ-vs-function traffic goes through these
three named maps; the Banach files (`Chain.lean`, `CompactRestrict.lean`) never touch
`MeroGermOn` internals directly, and the germ files never touch `→ᵇ` internals.
-/

open scoped ContDiff Manifold BoundedContinuousFunction
open Set Filter Topology TopologicalSpace Metric

namespace RS.Finiteness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `BddHoloOn` -/

/-- Compat: sum of `ContMDiffOn ω` functions `X → ℂ` on an open set (chart-local via the
Surface bridge + `AnalyticAt.add`). -/
theorem contMDiffOn_add {U : Set X} (hU : IsOpen U) {g₁ g₂ : X → ℂ}
    (h1 : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g₁ U) (h2 : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g₂ U) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (g₁ + g₂) U := by
  intro x hx
  have hc1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g₁ x := h1.contMDiffAt (hU.mem_nhds hx)
  have hc2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g₂ x := h2.contMDiffAt (hU.mem_nhds hx)
  have ha1 : AnalyticAt ℂ (g₁ ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) :=
    RS.contMDiffAt_iff_analyticAt.1 hc1
  have ha2 : AnalyticAt ℂ (g₂ ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) :=
    RS.contMDiffAt_iff_analyticAt.1 hc2
  have heq : (g₁ + g₂) ∘ (extChartAt 𝓘(ℂ) x).symm
      = (g₁ ∘ (extChartAt 𝓘(ℂ) x).symm) + (g₂ ∘ (extChartAt 𝓘(ℂ) x).symm) := rfl
  have ha : AnalyticAt ℂ ((g₁ + g₂) ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) := by
    rw [heq]; exact ha1.add ha2
  exact (RS.contMDiffAt_iff_analyticAt.2 ha).contMDiffWithinAt

/-- Compat: scalar multiple of a `ContMDiffOn ω` function `X → ℂ` on an open set. -/
theorem contMDiffOn_const_smul {U : Set X} (hU : IsOpen U) (c : ℂ) {g : X → ℂ}
    (hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g U) : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (c • g) U := by
  intro x hx
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g x := hg.contMDiffAt (hU.mem_nhds hx)
  have ha : AnalyticAt ℂ (g ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) :=
    RS.contMDiffAt_iff_analyticAt.1 hc
  have ha' : AnalyticAt ℂ (c • (g ∘ (extChartAt 𝓘(ℂ) x).symm)) (extChartAt 𝓘(ℂ) x x) :=
      ha.const_smul
  have heq : (c • g) ∘ (extChartAt 𝓘(ℂ) x).symm = c • (g ∘ (extChartAt 𝓘(ℂ) x).symm) := rfl
  have ha2 : AnalyticAt ℂ ((c • g) ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) := by
    rw [heq]; exact ha'
  exact (RS.contMDiffAt_iff_analyticAt.2 ha2).contMDiffWithinAt

/-- Bounded-holomorphic elements: BCF on the open subtype agreeing with a holomorphic function
on `S`. -/
noncomputable def BddHoloOn (S : Opens X) : Submodule ℂ (↥(S : Set X) →ᵇ ℂ) where
  carrier :=
      {f | ∃ g : X → ℂ, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g (S : Set X) ∧ ∀ z : ↥(S : Set X), f z = g z}
  zero_mem' := ⟨fun _ => 0, contMDiffOn_const, fun _ => rfl⟩
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, hfg₁⟩ ⟨g₂, hg₂, hfg₂⟩
    exact ⟨g₁ + g₂, contMDiffOn_add S.2 hg₁ hg₂, fun z => by simp [hfg₁, hfg₂]⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hfg⟩
    exact ⟨c • g, contMDiffOn_const_smul S.2 c hg, fun z => by simp [hfg]⟩

theorem mem_bddHoloOn_iff {S : Opens X} {f : ↥(S : Set X) →ᵇ ℂ} :
    f ∈ BddHoloOn S ↔ ∃ g : X → ℂ, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g (S : Set X) ∧
      ∀ z : ↥(S : Set X), f z = g z := Iff.rfl

/-- Uniform limits of holomorphic functions are holomorphic (chart-local, via `Surface.Bridges`
+ `TendstoLocallyUniformlyOn.differentiableOn`): `BddHoloOn S` is closed. -/
theorem isClosed_bddHoloOn (S : Opens X) :
    IsClosed ((BddHoloOn S : Submodule ℂ (↥(S : Set X) →ᵇ ℂ)) : Set (↥(S : Set X) →ᵇ ℂ)) := by
  classical
  apply isClosed_of_closure_subset
  intro f hf
  obtain ⟨Fb, hFbmem, hFbtend⟩ := mem_closure_iff_seq_limit.1 hf
  choose g hgc hgeq using hFbmem
  set gLim : X → ℂ := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0 with hgLim_def
  have hunif : ∀ ε > 0, ∀ᶠ n in (atTop : Filter ℕ), ∀ z : ↥(S : Set X), dist (f z) (Fb n z) < ε :=
      by
    have := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hFbtend
    rwa [tendstoUniformly_iff] at this
  refine ⟨gLim, ?_, fun z => by simp [hgLim_def]⟩
  intro x hx
  set e := chartAt ℂ x with he_def
  set V : Opens X := S ⊓ ⟨e.source, e.open_source⟩ with hV_def
  have hxV : x ∈ V := ⟨hx, mem_chart_source ℂ x⟩
  have hVsub : (V : Set X) ⊆ e.source := fun _ hy => hy.2
  have hVS : (V : Set X) ⊆ (S : Set X) := fun _ hy => hy.1
  have huc : TendstoUniformlyOn (fun n => (g n) ∘ e.symm) (gLim ∘ e.symm) atTop (e '' (V : Set X))
      := by
    rw [tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hunif ε hε] with n hn
    rintro w ⟨y, hyV, rfl⟩
    have hys : y ∈ (S : Set X) := hyV.1
    have hey : e.symm (e y) = y := e.left_inv hyV.2
    change dist (gLim (e.symm (e y))) ((g n) (e.symm (e y))) < ε
    rw [hey]
    have h1 : gLim y = f ⟨y, hys⟩ := by rw [hgLim_def]; exact dite_eq_left hys
    have h2 : g n y = Fb n ⟨y, hys⟩ := (hgeq n ⟨y, hys⟩).symm
    rw [h1, h2]
    exact hn ⟨y, hys⟩
  have hdiff : ∀ᶠ n in (atTop : Filter ℕ),
      DifferentiableOn ℂ ((g n) ∘ e.symm) (e '' (V : Set X)) := by
    refine Filter.Eventually.of_forall (fun n => ?_)
    have hgV : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (g n) (V : Set X) := (hgc n).mono hVS
    exact ((RS.contMDiffOn_iff_analyticOnNhd_of_subset_source (chart_mem_atlas ℂ x) hVsub
      V.2).1 hgV).differentiableOn
  have hUopen : IsOpen (e '' (V : Set X)) := e.isOpen_image_of_subset_source V.2 hVsub
  have hDiffOn : DifferentiableOn ℂ (gLim ∘ e.symm) (e '' (V : Set X)) :=
    huc.tendstoLocallyUniformlyOn.differentiableOn hdiff hUopen
  have hAnalytic : AnalyticOnNhd ℂ (gLim ∘ e.symm) (e '' (V : Set X)) :=
      hDiffOn.analyticOnNhd hUopen
  have hCV : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω gLim (V : Set X) :=
    (RS.contMDiffOn_iff_analyticOnNhd_of_subset_source (chart_mem_atlas ℂ x) hVsub V.2).2 hAnalytic
  exact (hCV.contMDiffAt (V.2.mem_nhds hxV)).contMDiffWithinAt

instance instCompleteSpaceBddHoloOn (S : Opens X) : CompleteSpace (BddHoloOn S) :=
  (isClosed_bddHoloOn S).completeSpace_coe

/-! ### `restrictCLM` -/

/-- The underlying restricted bounded continuous function. -/
noncomputable def restrictFun {S' S : Opens X} (h : S' ≤ S) (f : BddHoloOn S) :
    ↥(S' : Set X) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => (f : ↥(S : Set X) →ᵇ ℂ) (Set.inclusion h z))
    ((f : ↥(S : Set X) →ᵇ ℂ).continuous.comp (continuous_inclusion h))
    ‖(f : ↥(S : Set X) →ᵇ ℂ)‖
    (fun _z => BoundedContinuousFunction.norm_coe_le_norm _ _)

theorem restrictFun_mem {S' S : Opens X} (h : S' ≤ S) (f : BddHoloOn S) :
    restrictFun h f ∈ BddHoloOn S' :=
  ⟨f.2.choose, f.2.choose_spec.1.mono h, fun z => f.2.choose_spec.2 ⟨z.1, h z.2⟩⟩

theorem restrictFun_add {S' S : Opens X} (h : S' ≤ S) (f₁ f₂ : BddHoloOn S) :
    restrictFun h (f₁ + f₂) = restrictFun h f₁ + restrictFun h f₂ := by
  apply BoundedContinuousFunction.ext
  intro z
  change (f₁ + f₂ : BddHoloOn S).val (Set.inclusion h z)
    = (f₁ : ↥(S : Set X) →ᵇ ℂ) (Set.inclusion h z) + (f₂ : ↥(S : Set X) →ᵇ ℂ) (Set.inclusion h z)
  rfl

theorem restrictFun_smul {S' S : Opens X} (h : S' ≤ S) (c : ℂ) (f : BddHoloOn S) :
    restrictFun h (c • f) = c • restrictFun h f := by
  apply BoundedContinuousFunction.ext
  intro z
  change (c • f : BddHoloOn S).val (Set.inclusion h z) = c • (f : ↥(S : Set X) →ᵇ ℂ)
      (Set.inclusion h z)
  rfl

/-- Restriction, norm `≤ 1`. -/
noncomputable def restrictCLM {S' S : Opens X} (h : S' ≤ S) : BddHoloOn S →L[ℂ] BddHoloOn S' :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨restrictFun h f, restrictFun_mem h f⟩
      map_add' := fun f₁ f₂ => Subtype.ext (restrictFun_add h f₁ f₂)
      map_smul' := fun c f => Subtype.ext (restrictFun_smul h c f) }
    1 (fun f => by
      rw [one_mul]
      change ‖restrictFun h f‖ ≤ ‖(f : ↥(S : Set X) →ᵇ ℂ)‖
      exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _)

theorem restrictCLM_apply_coe {S' S : Opens X} (h : S' ≤ S) (f : BddHoloOn S)
    (z : ↥(S' : Set X)) :
    (restrictCLM h f : ↥(S' : Set X) →ᵇ ℂ) z = (f : ↥(S : Set X) →ᵇ ℂ) (Set.inclusion h z) := rfl

/-- Presheaf law: restrictions compose (the analogue of `MeroGermOn.restrict_restrict` /
`LinSysOn.restrictL_restrictL`, needed for the cochain-level naturality of `resNC1`). -/
theorem restrictCLM_restrictCLM {S'' S' S : Opens X} (h1 : S' ≤ S) (h2 : S'' ≤ S') (h3 : S'' ≤ S)
    (f : BddHoloOn S) : restrictCLM h2 (restrictCLM h1 f) = restrictCLM h3 f := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro z
  rfl

theorem norm_restrictCLM_apply_le {S' S : Opens X} (h : S' ≤ S) (f : BddHoloOn S) :
    ‖restrictCLM h f‖ ≤ ‖f‖ := by
  change ‖restrictFun h f‖ ≤ ‖(f : ↥(S : Set X) →ᵇ ℂ)‖
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _

/-! ### `toGerm`: germification (D5) -/

variable [T1Space X]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T1Space X] in
/-- If two meromorphic functions agree pointwise on an open set `U`, their germ classes on `U`
agree (Compat: the everywhere-on-`U` case of `mk_eq_mk`, used throughout this file's
well-definedness proofs since `Exists.choose` is otherwise opaque). -/
theorem mk_eq_mk_of_eqOn {U : Set X} (hU : IsOpen U) {f g : X → ℂ} (hf : MeromorphicOnX f U)
    (hg : MeromorphicOnX g U) (h : Set.EqOn f g U) : MeroGermOn.mk f hf = MeroGermOn.mk g hg := by
  rw [MeroGermOn.mk_eq_mk, eventuallyEq_codiscreteWithin_iff_of_isOpen hU]
  intro x hx
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hx)] with y hy
  exact h hy

/-- Germification (lands in `LinSysOn 0`). -/
noncomputable def toGerm (S : Opens X) : BddHoloOn S →ₗ[ℂ] MeroGermOn X (S : Set X) where
  toFun f := MeroGermOn.mk f.2.choose
    (fun x hx => RS.ContMDiffAt.meromorphicAtX (f.2.choose_spec.1.contMDiffAt (S.2.mem_nhds hx)))
  map_add' f₁ f₂ := by
    -- `mk_add` right-to-left as a term: neither `rw` nor `simp` matches the sum here
    refine Eq.trans (mk_eq_mk_of_eqOn S.2 _ _ ?_) MeroGermOn.mk_add.symm
    intro x hx
    change (f₁ + f₂ : BddHoloOn S).2.choose x = f₁.2.choose x + f₂.2.choose x
    have e12 := (f₁ + f₂ : BddHoloOn S).2.choose_spec.2 ⟨x, hx⟩
    have e1 := f₁.2.choose_spec.2 ⟨x, hx⟩
    have e2 := f₂.2.choose_spec.2 ⟨x, hx⟩
    have hval : (f₁ + f₂ : BddHoloOn S).val ⟨x, hx⟩
        = (f₁ : ↥(S : Set X) →ᵇ ℂ) ⟨x, hx⟩ + (f₂ : ↥(S : Set X) →ᵇ ℂ) ⟨x, hx⟩ := rfl
    rw [← e12, hval, e1, e2]
  map_smul' c f := by
    refine Eq.trans (mk_eq_mk_of_eqOn S.2 _ _ ?_) (MeroGermOn.mk_smul c).symm
    intro x hx
    change (c • f : BddHoloOn S).2.choose x = (c • f.2.choose) x
    have ecf := (c • f : BddHoloOn S).2.choose_spec.2 ⟨x, hx⟩
    have ef := f.2.choose_spec.2 ⟨x, hx⟩
    have hval : (c • f : BddHoloOn S).val ⟨x, hx⟩ = c • (f : ↥(S : Set X) →ᵇ ℂ) ⟨x, hx⟩ := rfl
    change (c • f : BddHoloOn S).2.choose x = c • f.2.choose x
    rw [← ecf, hval, ef]

omit [T1Space X] in
/-- Unfolding lemma for `toGerm` (forces the `mk`-shape syntactically, since neither
metavariable unification nor `rw` reliably unfolds the `LinearMap`/`FunLike` layers of the
named `toGerm` application on their own). -/
theorem toGerm_eq_mk {S : Opens X} (f : BddHoloOn S) :
    toGerm S f = MeroGermOn.mk f.2.choose
      (fun _x hx => RS.ContMDiffAt.meromorphicAtX (f.2.choose_spec.1.contMDiffAt (S.2.mem_nhds
          hx))) :=
  rfl

omit [T1Space X] in
theorem toGerm_mem_linSysOn {S : Opens X} (f : BddHoloOn S) :
    toGerm S f ∈ RS.LinSysOn (0 : RS.Divisor X) (S : Set X) := by
  refine (RS.mem_linSysOn_iff_of_isOpen S.2).2 (fun x hx => ?_)
  have h0 : (0 : RS.Divisor X) x = 0 := by
    simp [Function.locallyFinsuppWithin.coe_zero]
  -- routed through a fully elaborated equation: `rw` will not instantiate a metavariable
  -- standing in a proof-valued argument of `MeroGermOn.mk`
  have hord : (toGerm S f).ord x = RS.ordAtX f.2.choose x := by
    rw [toGerm_eq_mk]
    exact RS.MeroGermOn.ord_mk S.2 hx
  rw [h0, hord]
  simpa using RS.ContMDiffAt.ordAtX_nonneg (f.2.choose_spec.1.contMDiffAt (S.2.mem_nhds hx))

omit [T1Space X] in
theorem evalAt_toGerm {S : Opens X} (f : BddHoloOn S) {x : X} (hx : x ∈ S) :
    (toGerm S f).evalAt x = (f : ↥(S : Set X) →ᵇ ℂ) ⟨x, hx⟩ := by
  have heval : (toGerm S f).evalAt x = f.2.choose x := by
    rw [toGerm_eq_mk]
    exact RS.MeroGermOn.evalAt_mk_of_contMDiffAt S.2 hx
      (f.2.choose_spec.1.contMDiffAt (S.2.mem_nhds hx))
  rw [heval]
  exact (f.2.choose_spec.2 ⟨x, hx⟩).symm

omit [T1Space X] in
theorem toGerm_restrict_comm {S' S : Opens X} (h : S' ≤ S) (f : BddHoloOn S) :
    toGerm S' (restrictCLM h f) = RS.MeroGermOn.restrict h (toGerm S f) := by
  have hres : RS.MeroGermOn.restrict h (toGerm S f) =
      RS.MeroGermOn.mk f.2.choose (fun _x hx =>
        RS.ContMDiffAt.meromorphicAtX (f.2.choose_spec.1.contMDiffAt (S.2.mem_nhds (h hx)))) := by
    rw [toGerm_eq_mk]
    exact RS.MeroGermOn.restrict_mk h
  rw [toGerm_eq_mk, hres]
  apply mk_eq_mk_of_eqOn S'.2
  intro x hx
  show (restrictCLM h f).2.choose x = f.2.choose x
  have e1 := (restrictCLM h f).2.choose_spec.2 (⟨x, hx⟩ : ↥(S' : Set X))
  have e2 : (restrictCLM h f : ↥(S' : Set X) →ᵇ ℂ) ⟨x, hx⟩ = (f : ↥(S : Set X) →ᵇ ℂ) ⟨x, h hx⟩ :=
      rfl
  have e3 := f.2.choose_spec.2 (⟨x, h hx⟩ : ↥(S : Set X))
  rw [← e1, e2, e3]

/-! ### `restrictGerm`: de-germification (D5) -/

variable [T2Space X] [CompactSpace X]

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T1Space X] [T2Space X] [CompactSpace X] in
/-- A closure-nested open pair `S' ⋐ S` gives `S' ≤ S`. -/
theorem le_of_closure {S' S : Opens X} (hc : closure (S' : Set X) ⊆ (S : Set X)) : S' ≤ S :=
  subset_closure.trans hc

/-- De-germification onto a compactly-contained smaller open (uses `holoRepr`). -/
noncomputable def restrictGerm {S' S : Opens X} (hc : closure (S' : Set X) ⊆ (S : Set X))
    (φ : RS.LinSysOn (0 : RS.Divisor X) (S : Set X)) : BddHoloOn S' :=
  have hordnn : ∀ x ∈ (S : Set X), 0 ≤ (φ : RS.MeroGermOn X (S : Set X)).ord x :=
    RS.mem_linSysOn_iff_of_isOpen S.2 |>.1 φ.2
  have hCS : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (φ : RS.MeroGermOn X (S : Set X)).holoRepr (S : Set X) :=
    RS.MeroGermOn.holoRepr_contMDiffOn S.2 hordnn
  have hCS' : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (φ : RS.MeroGermOn X (S : Set X)).holoRepr (S' : Set X) :=
    hCS.mono (le_of_closure hc)
  have hcompact : IsCompact (closure (S' : Set X)) := isClosed_closure.isCompact
  have hcont : ContinuousOn (φ : RS.MeroGermOn X (S : Set X)).holoRepr (closure (S' : Set X)) :=
    (hCS.mono hc).continuousOn
  have hbdd := hcompact.exists_bound_of_continuousOn hcont
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z : ↥(S' : Set X) => (φ : RS.MeroGermOn X (S : Set X)).holoRepr z)
      (hCS'.continuousOn.comp_continuous continuous_subtype_val (fun z => z.2))
      hbdd.choose
      (fun z => hbdd.choose_spec z (subset_closure z.2)),
    ⟨(φ : RS.MeroGermOn X (S : Set X)).holoRepr, hCS', fun _ => rfl⟩⟩

omit [T1Space X] [T2Space X] in
theorem restrictGerm_apply {S' S : Opens X} (hc : closure (S' : Set X) ⊆ (S : Set X))
    (φ : RS.LinSysOn (0 : RS.Divisor X) (S : Set X)) (z : ↥(S' : Set X)) :
    (restrictGerm hc φ : ↥(S' : Set X) →ᵇ ℂ) z
      = RS.MeroGermOn.holoRepr (φ : RS.MeroGermOn X (S : Set X)) z := rfl

omit [T2Space X] [T1Space X] in
theorem toGerm_restrictGerm {S' S : Opens X} (hc : closure (S' : Set X) ⊆ (S : Set X))
    (φ : RS.LinSysOn (0 : RS.Divisor X) (S : Set X)) :
    toGerm S' (restrictGerm hc φ) =
      RS.MeroGermOn.restrict (le_of_closure hc) (φ : RS.MeroGermOn X (S : Set X)) := by
  rw [toGerm_eq_mk]
  have hRHS : RS.MeroGermOn.restrict (le_of_closure hc) (φ : RS.MeroGermOn X (S : Set X)) =
      MeroGermOn.mk (φ : RS.MeroGermOn X (S : Set X)).holoRepr
        (fun x hx => (RS.MeroGermOn.meromorphicOnX_holoRepr S.2
          (φ : RS.MeroGermOn X (S : Set X))) x (le_of_closure hc hx)) := by
    conv_lhs => rw [← RS.MeroGermOn.mk_holoRepr S.2 (φ : RS.MeroGermOn X (S : Set X))]
    exact RS.MeroGermOn.restrict_mk (le_of_closure hc)
  rw [hRHS]
  apply mk_eq_mk_of_eqOn S'.2
  intro x hx
  show (restrictGerm hc φ).2.choose x = (φ : RS.MeroGermOn X (S : Set X)).holoRepr x
  have e1 := (restrictGerm hc φ).2.choose_spec.2 (⟨x, hx⟩ : ↥(S' : Set X))
  have e2 : (restrictGerm hc φ : ↥(S' : Set X) →ᵇ ℂ) ⟨x, hx⟩
      = (φ : RS.MeroGermOn X (S : Set X)).holoRepr x := rfl
  rw [← e1, e2]

omit [T2Space X] [T1Space X] in
theorem restrictGerm_toGerm {S' S : Opens X} (hc : closure (S' : Set X) ⊆ (S : Set X))
    (f : BddHoloOn S) :
    restrictGerm hc ⟨toGerm S f, toGerm_mem_linSysOn f⟩ = restrictCLM (le_of_closure hc) f := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro z
  change (toGerm S f).evalAt z.1 = (f : ↥(S : Set X) →ᵇ ℂ) ⟨z.1, le_of_closure hc z.2⟩
  rw [evalAt_toGerm f (le_of_closure hc z.2)]

end RS.Finiteness
