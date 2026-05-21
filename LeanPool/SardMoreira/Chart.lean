/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import LeanPool.SardMoreira.ImplicitFunction
import LeanPool.SardMoreira.LocalEstimates

noncomputable section

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set Metric Function

local notation "dim" => Module.finrank ℝ

theorem fderiv_comp_prodMk {𝕜 : Type*} {E F G : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E × F → G} {a : E} {b : F} (hdf : DifferentiableAt 𝕜 f (a, b)) :
    fderiv 𝕜 (fun y ↦ f (a, y)) b = fderiv 𝕜 f (a, b) ∘L .inr 𝕜 E F :=
  hdf.hasFDerivAt.comp b (.prodMk (hasFDerivAt_const _ _) (hasFDerivAt_id _)) |>.fderiv

theorem fderiv_comp_prodMk' {𝕜 : Type*} {E F G : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E × F → G} {a : E × F} (hdf : DifferentiableAt 𝕜 f a) :
    fderiv 𝕜 (fun y ↦ f (a.fst, y)) a.snd = fderiv 𝕜 f a ∘L .inr 𝕜 E F :=
  fderiv_comp_prodMk hdf

theorem fderiv_curry {𝕜 : Type*} {E F G : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E × F → G} {a : E} {b : F} (hdf : DifferentiableAt 𝕜 f (a, b)) :
    fderiv 𝕜 (curry f a) b = fderiv 𝕜 f (a, b) ∘L .inr 𝕜 E F :=
  fderiv_comp_prodMk hdf

namespace Moreira2001

section
universe x u v w
variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {k : ℕ} {α : I} {s : Set (E × F)} {a : E × F} {f : E × F → ℝ}

-- This def almost hits the max heartbeats limit. In fact, I've adjusted the proof to avoid it.
-- Idk what makes the proof so slow.
/-- Implicit-function data used to build a local Moreira chart at a non-large point. -/
@[irreducible]
def chartImplicitData (f : E × F → ℝ) (a : E × F)
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    ImplicitFunctionData ℝ (E × F) ℝ (E × (fderiv ℝ f a ∘L .inr ℝ E F).ker) where
  leftFun := f
  leftDeriv := fderiv ℝ f a
  hasStrictFDerivAt_leftFun := hfa.contDiffAt.hasStrictFDerivAt <| mod_cast hk
  rightFun := _
  rightDeriv := .prodMap (.id _ _) (Submodule.ClosedComplemented.of_finiteDimensional _).choose
  hasStrictFDerivAt_rightFun := ContinuousLinearMap.hasStrictFDerivAt _
  pt := a
  range_leftDeriv := by
    refine IsSimpleOrder.eq_bot_or_eq_top _ |>.resolve_left ?_
    rw [LinearMap.range_eq_bot, ← ContinuousLinearMap.coe_zero, ContinuousLinearMap.coe_inj]
    contrapose! hdf
    rw [hdf, ContinuousLinearMap.zero_comp]
  range_rightDeriv := by
    have : (Submodule.ClosedComplemented.of_finiteDimensional <|
        (fderiv ℝ f a ∘L .inr ℝ E F).ker).choose.range = ⊤ := by
      apply LinearMap.range_eq_of_proj
      exact Exists.choose_spec (_ : Submodule.ClosedComplemented _)
    rw [ContinuousLinearMap.coe_prodMap, LinearMap.range_prodMap, this]
    simpa using (Submodule.prod_top :
      (Submodule.prod (⊤ : Submodule ℝ E) (⊤ : Submodule ℝ (fderiv ℝ f a ∘L .inr ℝ E F).ker)) = ⊤)
  isCompl_ker := by
    have H : (fderiv ℝ f a ∘L .inr ℝ E F).ker.ClosedComplemented :=
      .of_finiteDimensional _
    constructor
    · rw [Submodule.disjoint_def]
      rintro ⟨x, y⟩ hker hmap
      have hx : x = 0 := by
        simpa [ContinuousLinearMap.coe_prodMap] using congrArg Prod.fst hmap
      have hy : H.choose y = 0 := by
        simpa [ContinuousLinearMap.coe_prodMap] using congrArg Prod.snd hmap
      refine Prod.ext hx ?_
      lift y to (fderiv ℝ f a ∘L .inr ℝ E F).ker using by simpa [hx] using hker
      have hy' : (y : F) = 0 := by
        have hchoose : ((H.choose (y : F) : (fderiv ℝ f a ∘L .inr ℝ E F).ker) : F) = 0 := by
          simpa using congrArg Subtype.val hy
        exact (congrArg Subtype.val (H.choose_spec y)).symm.trans hchoose
      simpa using hy'
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      rintro ⟨x, y⟩
      obtain ⟨z, hz⟩ : ∃ z : F, fderiv ℝ f a (x, z) = 0 := by
        have : (fderiv ℝ f a ∘L .inr ℝ _ _).range = ⊤ := by
          refine IsSimpleOrder.eq_bot_or_eq_top _ |>.resolve_left ?_
          rwa [LinearMap.range_eq_bot, ← ContinuousLinearMap.coe_zero, ContinuousLinearMap.coe_inj]
        rw [Submodule.eq_top_iff'] at this
        refine this (-fderiv ℝ f a (x, 0)) |>.imp fun z hz ↦ ?_
        rw [← (x, z).fst_add_snd, map_add]
        simpa [eq_neg_iff_add_eq_zero, add_comm] using hz
      rcases Submodule.codisjoint_iff_exists_add_eq.mp
        (LinearMap.isCompl_of_proj H.choose_spec).codisjoint (y - z)
        with ⟨w, t, hw, ht, hsub⟩
      refine ⟨(x, w + z), (0, t), ?_, ?_, ?_⟩
      · rwa [← zero_add x, ← Prod.mk_add_mk, LinearMap.mem_ker, map_add,
          ContinuousLinearMap.coe_coe, hz, add_zero]
      · have ht0 : H.choose t = 0 := by
          simpa [LinearMap.mem_ker] using ht
        change (0, H.choose t) = (0 : E × (fderiv ℝ f a ∘L .inr ℝ E F).ker)
        exact Prod.ext rfl ht0
      · rw [Prod.mk_add_mk, add_zero, add_right_comm w z t, hsub, sub_add_cancel]

@[simp]
theorem chartImplicitData_leftFun {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    (chartImplicitData f a hfa hk hdf).leftFun = f := by
  simp [chartImplicitData]

@[simp]
theorem chartImplicitData_leftDeriv {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    (chartImplicitData f a hfa hk hdf).leftDeriv = fderiv ℝ f a := by
  simp [chartImplicitData]

@[simp]
theorem fst_rightFun_chartImplicitData {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0)
    (x : E × F) : ((chartImplicitData f a hfa hk hdf).rightFun x).1 = x.1 := by
  rcases x with ⟨x, y⟩
  simp only [chartImplicitData, ContinuousLinearMap.coe_prodMap',
    Prod.map_apply, ContinuousLinearMap.id_apply]

@[simp]
theorem chartImplicitData_pt {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    (chartImplicitData f a hfa hk hdf).pt = a := by
  simp [chartImplicitData]

theorem chartImplicitData_rightDeriv_apply_ker {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0)
    (x : E) {y : F} (hy : fderiv ℝ f a (0, y) = 0) :
    (chartImplicitData f a hfa hk hdf).rightDeriv (x, y) = (x, ⟨y, by simpa⟩) := by
  simpa only [chartImplicitData, ContinuousLinearMap.coe_prodMap',
    Prod.map_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun z => (x, z)) (Submodule.ClosedComplemented.of_finiteDimensional
        (fderiv ℝ f a ∘L .inr ℝ E F).ker |>.choose_spec ⟨y, by simpa⟩)

theorem fderiv_implicitFunction_chartImplicitData_apply_mk_zero {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0)
    (y : (fderiv ℝ f a ∘L ContinuousLinearMap.inr ℝ E F).ker) :
    fderiv ℝ ((chartImplicitData f a hfa hk hdf).implicitFunction (f a))
      ((chartImplicitData f a hfa hk hdf).rightFun a) (0, y) = (0, y.1) := by
  convert (chartImplicitData f a hfa hk hdf).fderiv_implicitFunction_apply_eq_iff.mpr _
  · simp
  · simp
  · simp
  · constructor
    · cases y with | mk y hy => simpa using hy
    · apply chartImplicitData_rightDeriv_apply_ker
      cases y with | mk y hy => simpa using hy

theorem fderiv_implicitFunction_chartImplicitData_comp_inr {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    fderiv ℝ ((chartImplicitData f a hfa hk hdf).implicitFunction (f a))
      ((chartImplicitData f a hfa hk hdf).rightFun a) ∘L .inr ℝ E _ =
      .inr ℝ E F ∘L Submodule.subtypeL _ := by
  ext1 x
  have := fderiv_implicitFunction_chartImplicitData_apply_mk_zero hfa hk hdf x
  simpa [ContinuousLinearMap.comp_apply] using this

theorem fst_implicitFunction_chartImplicitData_eventuallyEq {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    Prod.fst ∘ (chartImplicitData f a hfa hk hdf).implicitFunction (f a)
      =ᶠ[𝓝 ((chartImplicitData f a hfa hk hdf).rightFun a)] Prod.fst := by
  have := (continuousAt_const.prodMk continuousAt_id).eventually
    (chartImplicitData f a hfa hk hdf).rightFun_implicitFunction
  rw [chartImplicitData_pt] at this
  filter_upwards [this] with x hx
  simpa using congr($hx |>.1)

theorem map_implicitFunction_chartImplicitData_nhdsWithin_preimage {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0)
    (s : Set (E × F)) (hfs : f =ᶠ[𝓝[s] a] 0) (ha : a ∈ s) :
    letI ψ := chartImplicitData f a hfa hk hdf
    (𝓝[ψ.implicitFunction 0 ⁻¹' s] (ψ.rightFun a)).map (ψ.implicitFunction 0) = 𝓝[s] a := by
  set ψ := chartImplicitData f a hfa hk hdf
  convert ψ.map_implicitFunction_nhdsWithin_preimage s using 1
  · simp [ψ, hfs.self_of_nhdsWithin ha]
  · rw [nhdsWithin_inter', inf_of_le_left]
    · congr 1
      simp [ψ]
    · rw [le_principal_iff, chartImplicitData_pt]
      filter_upwards [hfs] with x hx
      simp [ψ, hx, hfs.self_of_nhdsWithin ha]

/-- The local largeness condition used in Moreira's recursive covering argument. -/
def IsLargeAt (k : ℕ) (α : I) (s : Set (E × G)) (a : E × G) : Prop :=
  ∀ f : E × G → ℝ, (∀ᶠ x in 𝓝[s] a, ContDiffMoreiraHolderAt k α f x) → f =ᶠ[𝓝[s] a] 0 →
    fderiv ℝ f a ∘L .inr ℝ E G = 0

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- Definition of `IsLargeAt` talks about `f : E × F → ℝ` only,
but it implies a similar statement for any codomain. -/
theorem _root_.Moreira2001.IsLargeAt.fderiv_comp_inr_eq_zero (h : IsLargeAt k α s a) {f : E × F → G}
    (hf : ∀ᶠ x in 𝓝[s] a, ContDiffMoreiraHolderAt k α f x) (hf₀ : f =ᶠ[𝓝[s] a] 0) :
    fderiv ℝ f a ∘L .inr ℝ E F = 0 := by
  by_cases hfa : DifferentiableAt ℝ f a
  · unfold IsLargeAt at h
    contrapose! h
    rcases ContinuousLinearMap.exists_ne_zero h with ⟨x, hx⟩
    rcases exists_dual_vector ℝ _ (norm_ne_zero_iff.mpr hx) with ⟨g, hg₁, hgx⟩
    refine ⟨g ∘ f, hf.mono fun x hx ↦ hx.continuousLinearMap_comp g,
      hf₀.mono <| by simp +contextual, ?_⟩
    rw [fderiv_comp _ (by fun_prop) hfa]
    apply ne_of_apply_ne (· x)
    simp_all
  · simp [fderiv_zero_of_not_differentiableAt hfa]

/-- A Moreira chart of depth `k` covering part of a set in a product space. -/
structure Chart (k : ℕ) (α : I) (s : Set (E × F)) where
  /-- The second-coordinate domain of the chart. -/
  Dom : Type v
  [instNormedAddCommGroupDom : NormedAddCommGroup Dom]
  [instNormedSpaceDom : NormedSpace ℝ Dom]
  [instFiniteDimensional : FiniteDimensional ℝ Dom]
  /-- The chart map into the original product space. -/
  toFun : E × Dom → E × F
  /-- The part of the chart domain covered by this chart. -/
  set : Set (E × Dom)
  fst_apply (x) : (toFun x).fst = x.fst
  contDiffMoreiraHolderAt {x} : x ∈ set → ContDiffMoreiraHolderAt k α toFun x
  injective_fderiv {x} : x ∈ set → Injective (fderiv ℝ toFun x)
  finrank_le : dim Dom ≤ dim F
  mapsTo : MapsTo toFun set s

namespace Chart

attribute [instance] instNormedAddCommGroupDom instNormedSpaceDom instFiniteDimensional
attribute [coe] toFun
attribute [simp] fst_apply

instance : CoeFun (Chart k α s) fun ψ ↦ E × ψ.Dom → E × F where
  coe := toFun

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem prodMk_fst_snd_apply (φ : Chart k α s) (x : E × φ.Dom) :
    (x.1, (φ x).2) = φ x := by
  ext <;> simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem prodMk_snd_apply_mk (φ : Chart k α s) (x : E) (y : φ.Dom) :
    (x, (φ (x, y)).snd) = φ (x, y) := by
  ext <;> simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem continuousAt (f : Chart k α s) {x : E × f.Dom} (hx : x ∈ f.set) :
    ContinuousAt f x :=
  f.contDiffMoreiraHolderAt hx |>.continuousAt

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiffAt (f : Chart k α s) {x : E × f.Dom} (hx : x ∈ f.set) :
    ContDiffAt ℝ k f x :=
  f.contDiffMoreiraHolderAt hx |>.contDiffAt

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem eventually_differentiableAt (f : Chart k α s) {x : E × f.Dom} (hx : x ∈ f.set)
      (hk : k ≠ 0) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
  f.contDiffAt hx |>.eventually (by simp) |>.mono fun y hy ↦
    hy.differentiableAt (by simpa [Nat.one_le_iff_ne_zero])

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem differentiableAt (f : Chart k α s) (hk : k ≠ 0) {x : E × f.Dom} (hx : x ∈ f.set) :
    DifferentiableAt ℝ f x :=
  f.contDiffMoreiraHolderAt hx |>.differentiableAt hk

/-- The identity chart. -/
@[simps -fullyApplied]
protected def id : Chart k α s where
  Dom := F
  toFun := id
  set := s
  fst_apply _ := rfl
  contDiffMoreiraHolderAt _ := .id
  injective_fderiv := by simp [injective_id]
  finrank_le := le_rfl
  mapsTo := mapsTo_id _

instance : Inhabited (Chart k α s) := ⟨.id⟩

theorem exists_dim_lt_map_nhdsWithin_eq (hs : ¬IsLargeAt k α s a)
    (hk : k ≠ 0) (has : a ∈ s) :
    ∃ (ψ : Chart k α s) (pt : E × ψ.Dom),
      dim ψ.Dom < dim F ∧ pt ∈ ψ.set ∧ map ψ (𝓝[ψ.set] pt) = 𝓝[s] a := by
  unfold IsLargeAt at hs
  push Not at hs
  rcases hs with ⟨f, hfk, hf₀, hdf⟩
  set ψ := chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf
  set g := ψ.implicitFunction 0
  have hae : a ∈ ψ.toOpenPartialHomeomorph.source := by
    simpa [ψ] using ψ.pt_mem_toOpenPartialHomeomorph_source
  have hfa₀ : f a = 0 := hf₀.self_of_nhdsWithin has
  have hfka : ContDiffMoreiraHolderAt k α f a := hfk.self_of_nhdsWithin has
  have hga : g (ψ.rightFun a) = a := by
    simpa [g, ψ, hfa₀] using ψ.implicitFunction_apply_image.self_of_nhds
  have hg_tendsto : Tendsto g (𝓝 (ψ.rightFun a)) (𝓝 a) := by
    convert ψ.differentiableAt_implicitFunction.continuousAt.tendsto
    · simp [ψ, hfa₀]
    · simp [ψ]
    · simpa [ψ] using ψ.implicitFunction_apply_image.self_of_nhds.symm
  have Hmem_target : ∀ᶠ x in 𝓝 (ψ.rightFun a), (0, x) ∈ ψ.toOpenPartialHomeomorph.target := by
    refine (ψ.toOpenPartialHomeomorph.open_target.preimage (by fun_prop)).eventually_mem ?_
    simpa [ψ, hfa₀] using ψ.map_pt_mem_toOpenPartialHomeomorph_target
  have Hfst : ∀ᶠ x in 𝓝 (ψ.rightFun a), (g x).fst = x.fst := by
    simpa [g, ψ, EventuallyEq, hfa₀]
      using fst_implicitFunction_chartImplicitData_eventuallyEq hfka hk hdf
  have Hcomp_inr : ∀ᶠ x in 𝓝 (ψ.rightFun a), fderiv ℝ f (g x) ∘L .inr ℝ E F ≠ 0 := by
    apply Filter.Tendsto.eventually_ne _ hdf
    refine (ContinuousLinearMap.precomp _ (.inr ℝ E F)).continuous.tendsto _ |>.comp ?_
    refine (hfka.contDiffAt.continuousAt_fderiv (mod_cast hk)).tendsto.comp hg_tendsto
  have HisInvertible : ∀ᶠ x in 𝓝 (ψ.rightFun a), (fderiv ℝ ψ.prodFun (g x)).IsInvertible := by
    suffices (fderiv ℝ ψ.prodFun ψ.pt).IsInvertible by
      simp only [ψ, chartImplicitData_pt] at this
      apply this.eventually
      refine (ContDiffAt.continuousAt_fderiv ?_ (n := k) (mod_cast hk)).tendsto.comp hg_tendsto
      simp +unfoldPartialApp only [ψ, ImplicitFunctionData.prodFun, chartImplicitData]
      exact hfka.contDiffAt.prodMk (by fun_prop)
    rw [ψ.hasStrictFDerivAt.hasFDerivAt.fderiv]
    apply ContinuousLinearMap.isInvertible_equiv
  have HcontDiff : ∀ᶠ x in 𝓝 (ψ.rightFun a), (g x ∈ s → ContDiffMoreiraHolderAt k α g x) := by
    rw [← map_implicitFunction_chartImplicitData_nhdsWithin_preimage hfka hk hdf s hf₀ has,
      eventually_map, eventually_nhdsWithin_iff] at hfk
    filter_upwards [Hmem_target, HisInvertible, hfk] with x hx₁ hx₂ hx₃ hgx
    suffices ContDiffMoreiraHolderAt k α ψ.toOpenPartialHomeomorph.symm (0, x) from
      this.comp (.prodMk .const .id) hk
    apply OpenPartialHomeomorph.contDiffMoreiraHolderAt_symm _ hx₁ hx₂
    convert (hx₃ hgx).prodMk _ using 4
    · rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [ψ]
    · simp only [ψ, chartImplicitData]
      apply ContinuousLinearMap.contDiffMoreiraHolderAt
  rcases _root_.eventually_nhds_iff.mp (Hmem_target.and <| Hfst.and <| Hcomp_inr.and <|
    HisInvertible.and HcontDiff) with ⟨U, hU, hUo, hUmem⟩
  choose hU_target hU_fst hUcomp_inr hUinv hUk using hU
  refine ⟨⟨_, fun x ↦ (x.1, (g x).2), U ∩ g ⁻¹' s, fun _ ↦ rfl, ?_, ?_, ?_, ?_⟩, ψ.rightFun a,
    ?_, ?_, ?_⟩
  · rintro x ⟨hxU, hxs⟩
    exact .prodMk .fst <| .comp .snd (hUk _ hxU hxs) hk
  · rintro x ⟨hxU, hgx⟩
    have : (fun y ↦ (y.1, (g y).2)) =ᶠ[𝓝 x] g := by
      filter_upwards [hUo.eventually_mem hxU] with y hyU
      rw [← hU_fst y hyU]
    rw [this.fderiv_eq]
    have : fderiv ℝ g x = _ :=
      ψ.toOpenPartialHomeomorph.hasFDerivAt_symm_inverse (hU_target x hxU) (hUinv x hxU)
      |>.comp x
        (ContinuousLinearMap.inr ℝ ℝ (E × (fderiv ℝ f a ∘L .inr ℝ E F).ker)).hasFDerivAt |>.fderiv
    rw [this, ContinuousLinearMap.coe_comp']
    apply Injective.comp
    · exact (hUinv _ hxU).inverse.injective
    · intro x y hxy
      simpa using congrArg Prod.snd hxy
  · exact Submodule.finrank_le _
  · rintro x ⟨hxU, hgx⟩
    simpa only [← hU_fst x hxU]
  · apply Submodule.finrank_lt
    simpa [SetLike.ext_iff, DFunLike.ext_iff] using hdf
  · refine ⟨hUmem, ?_⟩
    change g (ψ.rightFun a) ∈ s
    simpa [hga] using has
  · simp only
    rw [← map_implicitFunction_chartImplicitData_nhdsWithin_preimage hfka hk hdf _ hf₀ has,
      nhdsWithin_inter_of_mem]
    · apply Filter.map_congr
      filter_upwards [mem_nhdsWithin_of_mem_nhds <| hUo.mem_nhds hUmem] with x hxU
      rw [← hU_fst x hxU]
    · exact mem_nhdsWithin_of_mem_nhds <| hUo.mem_nhds hUmem

/-- Compose two charts of the same depth. -/
@[simps -fullyApplied]
protected def comp (g : Chart k α s) (f : Chart k α g.set) (hk : k ≠ 0) :
    Chart k α s where
  Dom := f.Dom
  toFun := g ∘ f
  set := f.set
  fst_apply := by simp
  contDiffMoreiraHolderAt {x} hx :=
    g.contDiffMoreiraHolderAt (f.mapsTo hx) |>.comp (f.contDiffMoreiraHolderAt hx) hk
  injective_fderiv {x} hx := by
    rw [fderiv_comp]
    · exact (g.injective_fderiv (f.mapsTo hx)).comp <| f.injective_fderiv hx
    · exact g.differentiableAt hk (f.mapsTo hx)
    · exact f.differentiableAt hk hx
  finrank_le := f.finrank_le.trans g.finrank_le
  mapsTo := g.mapsTo.comp f.mapsTo

/-- Restrict a chart to a smaller subset of its domain. -/
@[simps -fullyApplied]
def restr (f : Chart k α s) (t : Set (E × f.Dom)) : Chart k α s where
  Dom := f.Dom
  toFun := f
  set := f.set ∩ t
  fst_apply := by simp
  contDiffMoreiraHolderAt hx := f.contDiffMoreiraHolderAt hx.1
  injective_fderiv hx := f.injective_fderiv hx.1
  finrank_le := f.finrank_le
  mapsTo := f.mapsTo.mono_left inter_subset_left

/-- Regard a chart of depth `k` as a chart of any smaller depth. -/
@[simps -fullyApplied]
def ofLE (ψ : Chart k α s) (l : ℕ) (hl : l ≤ k) : Chart l α s where
  __ := ψ
  contDiffMoreiraHolderAt hx := ψ.contDiffMoreiraHolderAt hx |>.of_le hl

end Chart

/-- A countable family of Moreira charts covering the large part of a set. -/
structure Atlas (k : ℕ) (α : I) (s : Set (E × F)) where
  /-- The charts in the atlas. -/
  charts : Set (Chart k α s)
  /-- The atlas is countable. -/
  countable : charts.Countable
  /-- The charts cover `s` up to the recursively large parts. -/
  subset_biUnion_isLargeAt : s ⊆ ⋃ f ∈ charts, f '' {x ∈ f.set | IsLargeAt k α f.set x}

theorem nonempty_atlas {k : ℕ} (hk : k ≠ 0) (α : I) (s : Set (E × F)) :
    Nonempty (Atlas k α s) := by
  induction hF : dim F using Nat.strongRecOn generalizing F with | _ n ihn
  subst n
  set t := {x | IsLargeAt k α s x}
  choose! f pt hdim_lt hpt_mem hf_map
    using fun x (hx : x ∈ s \ t) ↦ Chart.exists_dim_lt_map_nhdsWithin_eq hx.2 hk hx.1
  have hf_mem : ∀ x ∈ s \ t, f x '' (f x).set ∈ 𝓝[s \ t] x := fun x hx ↦ by
    apply nhdsWithin_mono _ diff_subset
    rw [← hf_map x hx]
    exact image_mem_map self_mem_nhdsWithin
  rcases TopologicalSpace.countable_cover_nhdsWithin hf_mem with ⟨u, hut, huc, htu⟩
  have Ψ : ∀ x ∈ u, Atlas k α (f x).set := fun x hx ↦
    Classical.choice (ihn _ (hdim_lt x <| hut hx) _ rfl)
  refine
    ⟨insert .id (⋃ (x) (hx : x ∈ u), (fun g ↦ (f x).comp g hk) '' (Ψ x hx).charts),
    (huc.biUnion fun x hx ↦ (Ψ x hx).countable.image _).insert _, ?_⟩
  rw [biUnion_insert]
  intro x hx
  by_cases hxt : IsLargeAt k α s x
  · left
    exact ⟨x, ⟨hx, hxt⟩, rfl⟩
  · right
    simp only [biUnion_iUnion, biUnion_image, Chart.comp]
    rcases mem_iUnion₂.mp (htu ⟨hx, hxt⟩) with ⟨i, hiu, y, hy, rfl⟩
    rcases mem_iUnion₂.mp ((Ψ i hiu).subset_biUnion_isLargeAt hy) with ⟨g, hgS, z, hz, rfl⟩
    refine mem_iUnion_of_mem i <| mem_iUnion_of_mem hiu <| mem_biUnion hgS ?_
    apply mem_image_of_mem
    exact hz

end

namespace Atlas

universe x u v w

/-- Choose one atlas supplied by `nonempty_atlas`. -/
def _root_.Moreira2001.Atlas.choice {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (k : ℕ) (α : I) (s : Set (E × F)) : Atlas (k + 1) α s :=
  Classical.choice (nonempty_atlas k.succ_ne_zero α s)

/-- The recursive Moreira atlas covering construction. -/
def _root_.Moreira2001.Atlas.main {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∀ {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (_k : ℕ) (α : I) (s : Set (E × F)), Atlas 1 α s
  | _, _, _, _, 0, α, s => choice 0 α s
  | _, _, _, _, k + 1, α, s =>
    let Ψ := choice k α s
    { charts := ⋃ ψ ∈ Ψ.charts,
        (fun φ ↦
          ((ψ.ofLE 1 (by simp)).restr {x | IsLargeAt (k + 1) α ψ.set x}).comp φ one_ne_zero) ''
          (main k α {x ∈ ψ.set | IsLargeAt (k + 1) α ψ.set x}).charts
      countable := Ψ.countable.biUnion fun _ _ ↦ (main _ _ _).countable.image _
      subset_biUnion_isLargeAt := by
        refine Ψ.subset_biUnion_isLargeAt.trans ?_
        simp only [biUnion_iUnion, biUnion_image]
        gcongr with ψ hψ
        rintro _ ⟨x, hx, rfl⟩
        rcases mem_iUnion₂.mp
          ((main k α {x ∈ ψ.set | IsLargeAt (k + 1) α ψ.set x}).subset_biUnion_isLargeAt hx)
          with ⟨φ, hφ, y, hy, rfl⟩
        refine mem_biUnion hφ ?_
        aesop }

end Atlas

end Moreira2001
