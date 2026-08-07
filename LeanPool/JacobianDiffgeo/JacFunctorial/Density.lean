/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms
import LeanPool.JacobianDiffgeo.LocalMultiplicity

/-!
# `Density.lean` — the reusable "dense ⟹ everywhere" closing lemma (jacobian-functoriality §5)

Unit: jacobian-functoriality. `RS.Form1.eq_of_eqOn_dense` ("Lemma A"): two `Form1`s whose
`coeffAt`s agree on a dense set of the manifold are equal. Used downstream by `Trace.lean`'s
`compat`, the projection formula, and the comp-functoriality laws.

**Design deviation** (recorded, not silently dropped): the design sketch proposed routing this
through a standalone `Form1.continuous_coeffAt : Continuous (fun x => coeffAt x η)`. That
statement needs genuine tangent-bundle continuity theory (continuity of `mfderiv (chartAt ℂ x)`
*as its base point `x` varies*, not at a fixed point) that does not reduce to anything already
built in this project. **This is avoided entirely**: fix an arbitrary reference chart `e₀` at
`x₀`. For `x` in `e₀`'s source, `coeffAt x η = deriv (⇑e₀ ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) *
coeffIn e₀ η (e₀ x)` (`RS.coeffAt_eq_deriv_mul_coeffIn`, a pure algebraic identity via
`RS.coeffIn_trans`, no continuity-in-`x` needed). Since this transition factor is the *same*
nonzero number for `η` and `η'` (`RS.analyticAt_transition`'s nonvanishing-derivative half), the
hypothesis `coeffAt x η = coeffAt x η'` cancels it, reducing the comparison to `coeffIn e₀ η` vs.
`coeffIn e₀ η'` — two *fixed*-chart functions, continuous on `e₀.target` by
`Form1.continuousOn_coeffIn` (already built, no gap) — agreeing on a dense subset of `e₀.target`
(image of the dense hypothesis set), hence equal there by a direct filter/uniqueness-of-limits
argument (`tendsto_nhds_unique_of_eventuallyEq`).
-/

open scoped ContDiff Manifold Topology
open Set Filter IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The preferred-chart coefficient, read against a *fixed* reference chart `e₀` valid at `x`:
a pure chain-rule identity (`RS.coeffIn_trans` applied between `e₀` and `chartAt ℂ x`), no
continuity-in-`x` involved. -/
theorem coeffAt_eq_deriv_mul_coeffIn (η : Form1 X) {e₀ : OpenPartialHomeomorph X ℂ}
    (he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω X) {x : X} (hx : x ∈ e₀.source) :
    coeffAt x η =
      deriv (⇑e₀ ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) * coeffIn e₀ η (e₀ x) := by
  have hz : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' (e₀.source ∩ (chartAt ℂ x).source) :=
    ⟨x, ⟨hx, mem_chart_source ℂ x⟩, rfl⟩
  have h := coeffIn_trans he₀ (chart_mem_maximalAtlas x) η hz
  rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at h

/-- The chart-transition factor above never vanishes (a chart composed with its own inverse is
the identity; `RS.analyticAt_transition`'s nonvanishing-derivative half). -/
theorem deriv_transition_ne_zero {e₀ : OpenPartialHomeomorph X ℂ}
    (he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω X) {x : X} (hx : x ∈ e₀.source) :
    deriv (⇑e₀ ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 :=
  (analyticAt_transition (chart_mem_maximalAtlas x) he₀ (mem_chart_source ℂ x) hx).2

/-- Two continuous-on-`U` planar functions agreeing on a subset `T` whose closure covers `U`
agree on all of `U` (elementary filter/uniqueness-of-limits argument; the standard "dense ⟹
everywhere" fact specialized to an open domain, avoiding the need for global `Continuous`). -/
theorem ContinuousOn.eqOn_of_subset_closure {f g : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) {T : Set ℂ} (hTU : U ⊆ closure T)
    (heq : Set.EqOn f g T) : Set.EqOn f g U := by
  intro z hz
  have hzT : z ∈ closure T := hTU hz
  have : (𝓝[T] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzT
  have h1 : Tendsto f (𝓝[T] z) (𝓝 (f z)) :=
    ((hf.continuousAt (hUo.mem_nhds hz)).tendsto).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[T] z) (𝓝 (g z)) :=
    ((hg.continuousAt (hUo.mem_nhds hz)).tendsto).mono_left nhdsWithin_le_nhds
  have h3 : f =ᶠ[𝓝[T] z] g := eventually_nhdsWithin_of_forall (fun w hw => heq hw)
  exact tendsto_nhds_unique_of_eventuallyEq h1 h2 h3

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
/-- Density transports along a chart: if `s` is dense in `X`, then every point of `e₀.target` is
in the closure of `e₀ '' (s ∩ e₀.source)`. -/
theorem target_subset_closure_image_inter {e₀ : OpenPartialHomeomorph X ℂ} {s : Set X}
    (hs : Dense s) : e₀.target ⊆ closure (⇑e₀ '' (s ∩ e₀.source)) := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨V, hVU, hVo, hzV⟩ := mem_nhds_iff.mp hU
  have hVsrc : IsOpen (⇑e₀.symm '' (V ∩ e₀.target)) :=
    e₀.isOpen_image_symm_of_subset_target (hVo.inter e₀.open_target) inter_subset_right
  have hne : (⇑e₀.symm '' (V ∩ e₀.target)).Nonempty := ⟨e₀.symm z, ⟨z, ⟨hzV, hz⟩, rfl⟩⟩
  obtain ⟨x, hxV, hxs⟩ := hs.inter_open_nonempty _ hVsrc hne
  obtain ⟨w, ⟨hwV, hwt⟩, hwx⟩ := hxV
  have hxeq : e₀ x = w := by rw [← hwx, e₀.right_inv hwt]
  refine ⟨e₀ x, hVU (hxeq ▸ hwV), ⟨x, ⟨hxs, ?_⟩, rfl⟩⟩
  rw [← hwx]; exact e₀.map_target hwt

/-- **Lemma A.** Two holomorphic `1`-forms whose `coeffAt`s agree on a dense set (in particular,
on the cofinite complement of a *finite* set, e.g. a branch/critical locus) are equal. -/
theorem Form1.eq_of_eqOn_dense {η η' : Form1 X} {s : Set X} (hs : Dense s)
    (h : Set.EqOn (fun x => coeffAt x η) (fun x => coeffAt x η') s) : η = η' := by
  apply Form1.ext_coeffAt
  intro x₀
  set e₀ := chartAt ℂ x₀ with he₀_def
  have he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω X := chart_mem_maximalAtlas x₀
  have hcoeffIn : Set.EqOn (fun z => coeffIn e₀ η z) (fun z => coeffIn e₀ η' z) e₀.target := by
    apply ContinuousOn.eqOn_of_subset_closure e₀.open_target
      (η.continuousOn_coeffIn he₀) (η'.continuousOn_coeffIn he₀)
      (target_subset_closure_image_inter hs)
    rintro z ⟨x, ⟨hxs, hxsrc⟩, rfl⟩
    have hη := coeffAt_eq_deriv_mul_coeffIn η he₀ hxsrc
    have hη' := coeffAt_eq_deriv_mul_coeffIn η' he₀ hxsrc
    have hd := deriv_transition_ne_zero he₀ hxsrc
    have hxeq : coeffAt x η = coeffAt x η' := h hxs
    rw [hη, hη'] at hxeq
    exact mul_left_cancel₀ hd hxeq
  have := hcoeffIn (mem_chart_target ℂ x₀)
  simpa [coeffAt] using this

end RS

end
