/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CanonicalForms.MForm
import LeanPool.JacobianDiffgeo.ResidueCalculus

/-!
# `MFormData.ord`/`resAt` (D4), chart-invariance, and `divisor` (D6) — data layer

Unit: canonical-forms (`docs/design/canonical-forms.md` §2 D4–D6, §4.2). Everything here is
stated for the RAW data carrier `MFormData` and descends to the quotient `MForm` in
`Quotient.lean` (all reading maps are germ-at-the-chart-center facts, hence congruence-robust).

* `MFormData.ord`/`MFormData.resAt` (D4): read directly via the *fixed* `chartAt`, needing no
invariance
  proof to be well-defined; `MFormData.ord_eq_of_mem_source`/`MFormData.resAt_eq_of_mem_source`
  supply the
  "read in any maximal-atlas chart" corollary (chart-invariance, via
  `meromorphicOrderAt_comp_of_deriv_ne_zero`/`RS.resAt_comp_mul_deriv`).
* `MFormData.eventually_ord_eq_top`/`MFormData.eventually_ord_eq_zero`: local propagation of the
order,
  the chart-crossing analogues of `eventually_ordAtX_eq_top`/`eventually_ordAtX_eq_zero`
  (`Jacobian/Meromorphic/Predicates.lean`), via `compat`.
* `MFormData.divisor`/`MFormData.degree` (D6): local finiteness is connectedness-free, mirroring
  `MeroGermOn.divisorOn`'s proof exactly.
-/

open scoped ContDiff Manifold
open Set IsManifold Filter Topology

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MFormData

/-- D4: the order of `θ` at `x`, read via the (fixed) preferred chart at `x`. -/
noncomputable def ord (θ : MFormData X) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (θ.coeffAt x) (chartAt ℂ x x)

/-- D4: the residue of `θ` at `x`, read via the (fixed) preferred chart at `x`. -/
noncomputable def resAt (θ : MFormData X) (x : X) : ℂ :=
  RS.resAt (θ.coeffAt x) (chartAt ℂ x x)

theorem meromorphicAt_coeffAt (θ : MFormData X) (x : X) :
    MeromorphicAt (θ.coeffAt x) (chartAt ℂ x x) :=
  θ.meromorphicOn_coeffAt x (chartAt ℂ x x) (mem_chart_target ℂ x)

/-- A one-line corollary of `meromorphicOrderAt_eq_top_iff` (the `MFormData`-level analogue of
`ordAtX_eq_top_iff`). -/
theorem ord_eq_top_iff {θ : MFormData X} {x : X} :
    θ.ord x = ⊤ ↔ θ.coeffAt x =ᶠ[𝓝[≠] (chartAt ℂ x x)] (0 : ℂ → ℂ) :=
  meromorphicOrderAt_eq_top_iff

/-- Convenience (chart-invariance of `ord`, via `meromorphicOrderAt_comp_of_deriv_ne_zero`): the
order of `θ` at `x` may be computed reading `θ.coeffAt x` through ANY maximal-atlas chart `e`
valid at `x`, not just `chartAt ℂ x`. Not DAG-required by any current consumer, offered as a
documented, non-blocking convenience (§4.2). -/
theorem ord_eq_of_mem_source {θ : MFormData X} {x : X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source) :
    θ.ord x = meromorphicOrderAt (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z *
      θ.coeffAt x (chartAt ℂ x (e.symm z))) (e x) := by
  obtain ⟨hτ, hτ'⟩ := analyticAt_transition he (chart_mem_maximalAtlas x) hx (mem_chart_source ℂ x)
  have hgx : e.symm (e x) = x := e.left_inv hx
  have hmulEq : meromorphicOrderAt
      (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z *
        (θ.coeffAt x ∘ (⇑(chartAt ℂ x) ∘ ⇑e.symm)) z) (e x) =
      meromorphicOrderAt (θ.coeffAt x ∘ (⇑(chartAt ℂ x) ∘ ⇑e.symm)) (e x) :=
    meromorphicOrderAt_mul_of_ne_zero hτ.deriv hτ'
  have hfun : (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z *
        θ.coeffAt x (chartAt ℂ x (e.symm z))) =
      (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z *
        (θ.coeffAt x ∘ (⇑(chartAt ℂ x) ∘ ⇑e.symm)) z) := rfl
  rw [hfun, hmulEq, meromorphicOrderAt_comp_of_deriv_ne_zero hτ hτ']
  change θ.ord x = meromorphicOrderAt (θ.coeffAt x) ((⇑(chartAt ℂ x) ∘ ⇑e.symm) (e x))
  rw [Function.comp_apply, hgx]
  rfl

/-- Convenience (chart-invariance of `resAt`, via `RS.resAt_comp_mul_deriv`): the residue of `θ`
at `x` may be computed reading `θ.coeffAt x` through ANY maximal-atlas chart `e` valid at `x`. -/
theorem resAt_eq_of_mem_source {θ : MFormData X} {x : X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source) :
    θ.resAt x = RS.resAt (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z *
      θ.coeffAt x (chartAt ℂ x (e.symm z))) (e x) := by
  obtain ⟨hτ, hτ'⟩ := analyticAt_transition he (chart_mem_maximalAtlas x) hx (mem_chart_source ℂ x)
  have hφ₀ : (⇑(chartAt ℂ x) ∘ ⇑e.symm) (e x) = chartAt ℂ x x := by
    simp only [Function.comp_apply]; rw [e.left_inv hx]
  have hf : MeromorphicAt (θ.coeffAt x) (chartAt ℂ x x) := θ.meromorphicAt_coeffAt x
  have hkey := resAt_comp_mul_deriv hτ hτ' hφ₀ hf
  have hfun : (fun w => θ.coeffAt x ((⇑(chartAt ℂ x) ∘ ⇑e.symm) w) *
        deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) w) =
      (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z * θ.coeffAt x (chartAt ℂ x (e.symm z))) := by
    funext w; rw [Function.comp_apply]; ring
  rw [hfun] at hkey
  exact hkey.symm

/-- Auxiliary cross-point transport: `θ.coeffAt y`, on a whole neighborhood of its own chart
center, is given by the `compat` formula against `θ.coeffAt x` for any `x` with
`y ∈ (chartAt ℂ x).source`. The engine behind `eventually_ord_eq_top`/`eventually_ord_eq_zero`. -/
theorem coeffAt_eventuallyEq_of_mem_source (θ : MFormData X) {x y : X}
    (hy : y ∈ (chartAt ℂ x).source) :
    θ.coeffAt y =ᶠ[nhds (chartAt ℂ y y)] fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z *
      θ.coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z)) := by
  have hWopen : IsOpen (⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source)) :=
    (chartAt ℂ y).isOpen_image_of_subset_source
      ((chartAt ℂ x).open_source.inter (chartAt ℂ y).open_source) inter_subset_right
  have hzW : chartAt ℂ y y ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source) :=
    ⟨y, ⟨hy, mem_chart_source ℂ y⟩, rfl⟩
  filter_upwards [hWopen.mem_nhds hzW] with z hz
  exact θ.compat x y z hz

/-- **Cross-point order reading**: the order of `θ` at any point `p` of the chart source at `x`
is the planar order of the single coefficient function `θ.coeffAt x` at the chart image
`chartAt ℂ x p` — no transition factor survives (its order is `0`). This is the bridge that lets
`OmegaSpace`-membership (a pointwise `ord` condition at every chart CENTER) control the
coefficient at every TARGET point (D12's repair construction, `LinearSystems.lean`). -/
theorem ord_eq_meromorphicOrderAt_of_mem_source (θ : MFormData X) {x p : X}
    (hp : p ∈ (chartAt ℂ x).source) :
    θ.ord p = meromorphicOrderAt (θ.coeffAt x) (chartAt ℂ x p) := by
  obtain ⟨hσ, hσ'⟩ := analyticAt_transition (chart_mem_maximalAtlas p) (chart_mem_maximalAtlas x)
    (mem_chart_source ℂ p) hp
  -- hσ : AnalyticAt ℂ (chartAt x ∘ (chartAt p).symm) (chartAt p p), hσ' : deriv ≠ 0 there
  have hcross := θ.coeffAt_eventuallyEq_of_mem_source hp
  have hσc : (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ p).symm) (chartAt ℂ p p) = chartAt ℂ x p := by
    simp only [Function.comp_apply]
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  calc θ.ord p
      = meromorphicOrderAt (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ p).symm) z *
          θ.coeffAt x (chartAt ℂ x ((chartAt ℂ p).symm z))) (chartAt ℂ p p) :=
        meromorphicOrderAt_congr (hcross.filter_mono nhdsWithin_le_nhds)
    _ = meromorphicOrderAt (θ.coeffAt x ∘ (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ p).symm))
          (chartAt ℂ p p) :=
        meromorphicOrderAt_mul_of_ne_zero hσ.deriv hσ'
    _ = meromorphicOrderAt (θ.coeffAt x)
          ((⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ p).symm) (chartAt ℂ p p)) :=
        meromorphicOrderAt_comp_of_deriv_ne_zero hσ hσ'
    _ = meromorphicOrderAt (θ.coeffAt x) (chartAt ℂ x p) := by rw [hσc]

/-- `MFormData.ord` propagates to `⊤` on a whole neighborhood, once it is `⊤` at the center (mirrors
`eventually_ordAtX_eq_top`, `Predicates.lean:231`). -/
theorem eventually_ord_eq_top [T1Space X] {θ : MFormData X} {x : X} (h : θ.ord x = ⊤) :
    ∀ᶠ y in nhds x, θ.ord y = ⊤ := by
  have hf0 : θ.coeffAt x =ᶠ[𝓝[≠] (chartAt ℂ x x)] (0 : ℂ → ℂ) := ord_eq_top_iff.1 h
  have hf0' : ∀ᶠ w in 𝓝[≠] x, θ.coeffAt x (chartAt ℂ x w) = 0 :=
    eventually_nhdsNE_comp_chart_apply_iff.mpr hf0
  have hf0'' : ∀ᶠ w in 𝓝 x, w ≠ x → θ.coeffAt x (chartAt ℂ x w) = 0 :=
    eventually_nhdsWithin_iff.mp hf0'
  have hsrc : ∀ᶠ w in 𝓝 x, w ∈ (chartAt ℂ x).source :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  have hcomb : ∀ᶠ w in 𝓝 x,
      (w ≠ x → θ.coeffAt x (chartAt ℂ x w) = 0) ∧ w ∈ (chartAt ℂ x).source := hf0''.and hsrc
  filter_upwards [hcomb.eventually_nhds] with y hy
  rcases eq_or_ne y x with rfl | hyx
  · exact h
  · have hyxsrc : y ∈ (chartAt ℂ x).source := hy.self_of_nhds.2
    apply ord_eq_top_iff.2
    have hcross := θ.coeffAt_eventuallyEq_of_mem_source hyxsrc
    have hsymm : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hcont : ContinuousAt (⇑(chartAt ℂ y).symm) (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hxc : ({x}ᶜ : Set X) ∈ nhds ((⇑(chartAt ℂ y).symm) (chartAt ℂ y y)) := by
      rw [hsymm]; exact isOpen_compl_singleton.mem_nhds hyx
    have hxc' : (⇑(chartAt ℂ y).symm) ⁻¹' ({x}ᶜ) ∈ nhds (chartAt ℂ y y) :=
      hcont.preimage_mem_nhds hxc
    have hncomb : ∀ᶠ w in nhds y, w ≠ x → θ.coeffAt x (chartAt ℂ x w) = 0 :=
      hy.mono (fun w hw => hw.1)
    have hncomb0 : {w | w ≠ x → θ.coeffAt x (chartAt ℂ x w) = 0}
        ∈ nhds ((⇑(chartAt ℂ y).symm) (chartAt ℂ y y)) := by rw [hsymm]; exact hncomb
    have hncomb' : (⇑(chartAt ℂ y).symm) ⁻¹' {w | w ≠ x → θ.coeffAt x (chartAt ℂ x w) = 0}
        ∈ nhds (chartAt ℂ y y) := hcont.preimage_mem_nhds hncomb0
    have hall : ∀ᶠ z in nhds (chartAt ℂ y y), θ.coeffAt y z = 0 := by
      filter_upwards [hcross, hxc', hncomb'] with z hz1 hz2 hz3
      rw [hz1, hz3 hz2, mul_zero]
    exact hall.filter_mono nhdsWithin_le_nhds

/-- `MFormData.ord` is eventually `0` away from a point where it is finite (mirrors
`eventually_ordAtX_eq_zero`, `Predicates.lean:314`). Feeds the local finiteness of `divisor`. -/
theorem eventually_ord_eq_zero {θ : MFormData X} {x : X} (h : θ.ord x ≠ ⊤) :
    ∀ᶠ y in 𝓝[≠] x, θ.ord y = 0 := by
  have hf : MeromorphicAt (θ.coeffAt x) (chartAt ℂ x x) := θ.meromorphicAt_coeffAt x
  have h1 : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), AnalyticAt ℂ (θ.coeffAt x) z :=
    hf.eventually_analyticAt
  have h2 : ∀ᶠ w in 𝓝[≠] x, AnalyticAt ℂ (θ.coeffAt x) (chartAt ℂ x w) :=
    eventually_nhdsNE_comp_chart_apply_iff.mpr h1
  have h4 : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), θ.coeffAt x z ≠ 0 :=
    meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf |>.1 h
  have h4' : ∀ᶠ w in 𝓝[≠] x, θ.coeffAt x (chartAt ℂ x w) ≠ 0 :=
    eventually_nhdsNE_comp_chart_apply_iff.mpr h4
  have h3 : ∀ᶠ w in 𝓝[≠] x, w ∈ (chartAt ℂ x).source :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  filter_upwards [h2, h4', h3] with y h2y h4y h3y
  obtain ⟨hτ, hτ'⟩ := analyticAt_transition (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas x)
    (mem_chart_source ℂ y) h3y
  -- hτ : AnalyticAt ℂ (chartAt x ∘ (chartAt y).symm) (chartAt y y), hτ' : deriv (...) ≠ 0
  have hcross := θ.coeffAt_eventuallyEq_of_mem_source h3y
  have hsymm : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
    (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hcompAn : AnalyticAt ℂ (fun z => θ.coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z)))
      (chartAt ℂ y y) := by
    have hgf : AnalyticAt ℂ (θ.coeffAt x)
        ((⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y y)) := by
      rw [Function.comp_apply, hsymm]; exact h2y
    exact AnalyticAt.fun_comp hgf hτ
  have hprodAn : AnalyticAt ℂ (θ.coeffAt y) (chartAt ℂ y y) :=
    (hτ.deriv.fun_mul hcompAn).congr hcross.symm
  have hval : θ.coeffAt y (chartAt ℂ y y) ≠ 0 := by
    have heq := Filter.Eventually.self_of_nhds hcross
    rw [heq]
    change deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y y) *
      θ.coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y y))) ≠ 0
    rw [hsymm]
    exact mul_ne_zero hτ' h4y
  change meromorphicOrderAt (θ.coeffAt y) (chartAt ℂ y y) = 0
  rw [hprodAn.meromorphicOrderAt_eq, hprodAn.analyticOrderAt_eq_zero.mpr hval]
  rfl

/-- D6: the divisor of `θ` (local finiteness, connectedness-free — mirrors `MeroGermOn.divisorOn`
exactly, `Divisor.lean:134`). -/
noncomputable def divisor [T1Space X] (θ : MFormData X) : Divisor X
    where
  toFun x := (θ.ord x).untop₀
  supportWithinDomain' := by intro x _; trivial
  supportLocallyFiniteWithinDomain' := by
    intro z _
    by_cases hordz : θ.ord z = ⊤
    · have he : ∀ᶠ y in nhds z, θ.ord y = ⊤ := eventually_ord_eq_top hordz
      obtain ⟨W, hW, hWsub⟩ := Filter.eventually_iff_exists_mem.mp he
      refine ⟨W, hW, ?_⟩
      have hempty : W ∩ Function.support (fun x => (θ.ord x).untop₀) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        rintro y ⟨hyW, hyS⟩
        simp only [Function.mem_support, ne_eq] at hyS
        exact hyS (by rw [hWsub y hyW]; exact WithTop.untop₀_top)
      rw [hempty]; exact Set.finite_empty
    · have he : ∀ᶠ y in 𝓝[≠] z, θ.ord y = 0 := eventually_ord_eq_zero hordz
      rw [eventually_nhdsWithin_iff] at he
      obtain ⟨W, hW, hWsub⟩ := Filter.eventually_iff_exists_mem.mp he
      refine ⟨W, hW, ?_⟩
      have hsub : W ∩ Function.support (fun x => (θ.ord x).untop₀) ⊆ {z} := by
        rintro y ⟨hyW, hyS⟩
        simp only [Set.mem_singleton_iff]
        by_contra hyz
        simp only [Function.mem_support, ne_eq] at hyS
        exact hyS (by rw [hWsub y hyW hyz]; exact WithTop.untop₀_zero)
      exact Set.Finite.subset (Set.finite_singleton z) hsub

@[simp] theorem divisor_apply [T1Space X] (θ : MFormData X) (x : X) :
    θ.divisor x = (θ.ord x).untop₀ := rfl

/-- D6: the degree of `θ`'s divisor. -/
noncomputable def degree [T1Space X] [T2Space X] [CompactSpace X] (θ : MFormData X) : ℤ :=
  θ.divisor.degree

@[simp] theorem divisor_zero [T1Space X] :
    (0 : MFormData X).divisor = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  have h0 : (0 : MFormData X).ord y = ⊤ := by
    change meromorphicOrderAt (0 : ℂ → ℂ) (chartAt ℂ y y) = ⊤
    simp
  rw [divisor_apply, h0]
  simp

end MFormData

end RS
