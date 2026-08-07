/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms.Coeffs
import LeanPool.JacobianDiffgeo.Forms.Analyticity
import LeanPool.JacobianDiffgeo.Path.Planar
import Mathlib.Topology.LocallyConstant.Basic

/-!
# `IsPrimitiveAlongMap`: primitives of a 1-form along a continuous map (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §2.1–2.2). One generic predicate
serves paths, homotopy squares, and restrictions to subintervals/edges (via `comp`).

Main declarations:
* `RS.IsPrimitiveAlongMap K η F s` — near every `a ∈ s` (within `s`), `F` factors as `g ∘ e ∘ K`
  for a maximal-atlas chart `e` at `K a` and a planar local primitive `g` of `coeffIn e η`.
* Basic API: `.mono`, `.add_const`, `.congr`, `.congr_map`, `.continuousOn`, `.comp`.
* `.rechart` — the chart in the local-primitive data can be re-chosen to any maximal-atlas chart
  containing the image point (the workhorse for uniqueness/gluing/linearity/bridge).
* `.sub_eq_sub` — uniqueness up to a constant: two primitives along the same (continuous) map on
  a preconnected set differ by a constant.
* `.glue` — the junction argument: primitives on `s₁`, `s₂` agreeing at a point of the
(preconnected)
  overlap glue to a primitive on `s₁ ∪ s₂`, provided `s₁`/`s₂` cover `𝓝[s₁∪s₂]`-neighborhoods of
  every point (`hcov`).
* `isPrimitiveAlongMap_of_ball` — the constant-chart primitive `g ∘ e ∘ K` on a set mapped by `K`
  into a single chart-ball; the reusable "cell primitive" atom for the 1D chain induction
  (`Continuation.lean`) and the 2D grid (`HomotopySquare.lean`).
-/

open scoped ContDiff Manifold Topology
open IsManifold Metric Set Filter

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {α : Type*} [TopologicalSpace α]

/-- `F` is a primitive of the 1-form `η` along the map `K` on `s`: near every `a ∈ s`
(within `s`), `F` factors as `g ∘ e ∘ K` for a chart `e` at `K a` and a planar local
primitive `g` of the chart coefficient of `η`. -/
def IsPrimitiveAlongMap (K : α → X) (η : Form1 X) (F : α → ℂ) (s : Set α) : Prop :=
  ∀ a ∈ s, ∃ e : OpenPartialHomeomorph X ℂ, e ∈ maximalAtlas 𝓘(ℂ) ω X ∧ K a ∈ e.source ∧
    ∃ g : ℂ → ℂ, (∀ᶠ z in 𝓝 (e (K a)), HasDerivAt g (coeffIn e η z) z) ∧
      ∀ᶠ b in 𝓝[s] a, K b ∈ e.source ∧ F b = g (e (K b))

variable {K : α → X} {η : Form1 X} {F F₁ F₂ : α → ℂ} {s t : Set α} {a : α}

theorem IsPrimitiveAlongMap.mono (h : IsPrimitiveAlongMap K η F s) (hts : t ⊆ s) :
    IsPrimitiveAlongMap K η F t := by
  intro a ha
  obtain ⟨e, he, hKa, g, hg, hF⟩ := h a (hts ha)
  exact ⟨e, he, hKa, g, hg, hF.filter_mono (nhdsWithin_mono a hts)⟩

theorem IsPrimitiveAlongMap.add_const (h : IsPrimitiveAlongMap K η F s) (c : ℂ) :
    IsPrimitiveAlongMap K η (fun a => F a + c) s := by
  intro a ha
  obtain ⟨e, he, hKa, g, hg, hF⟩ := h a ha
  refine ⟨e, he, hKa, fun z => g z + c, ?_, ?_⟩
  · filter_upwards [hg] with z hz using hz.add_const c
  · filter_upwards [hF] with b hb using ⟨hb.1, by rw [hb.2]⟩

theorem IsPrimitiveAlongMap.congr (h : IsPrimitiveAlongMap K η F s)
    (hFF' : Set.EqOn F F₁ s) : IsPrimitiveAlongMap K η F₁ s := by
  intro a ha
  obtain ⟨e, he, hKa, g, hg, hF⟩ := h a ha
  refine ⟨e, he, hKa, g, hg, ?_⟩
  filter_upwards [hF, self_mem_nhdsWithin] with b hb hbs using ⟨hb.1, (hFF' hbs).symm.trans hb.2⟩

theorem IsPrimitiveAlongMap.congr_map {K' : α → X} (h : IsPrimitiveAlongMap K η F s)
    (hKK' : Set.EqOn K K' s) : IsPrimitiveAlongMap K' η F s := by
  intro a ha
  obtain ⟨e, he, hKa, g, hg, hF⟩ := h a ha
  have hKaa : K a = K' a := hKK' ha
  refine ⟨e, he, by rw [← hKaa]; exact hKa, g, by rw [← hKaa]; exact hg, ?_⟩
  filter_upwards [hF, self_mem_nhdsWithin] with b hb hbs
  rw [← hKK' hbs]
  exact hb

theorem IsPrimitiveAlongMap.continuousOn (h : IsPrimitiveAlongMap K η F s)
    (hK : ContinuousOn K s) : ContinuousOn F s := by
  intro a ha
  obtain ⟨e, he, hKa, g, hg, hF⟩ := h a ha
  have hgc : ContinuousAt g (e (K a)) := hg.self_of_nhds.continuousAt
  have hec : Tendsto (e ∘ K) (𝓝[s] a) (𝓝 (e (K a))) :=
    ((e.continuousOn.continuousAt (e.open_source.mem_nhds hKa)).tendsto).comp (hK a ha).tendsto
  have hcomp : Tendsto (g ∘ (e ∘ K)) (𝓝[s] a) (𝓝 (g (e (K a)))) := hgc.tendsto.comp hec
  have heq : F =ᶠ[𝓝[s] a] (g ∘ (e ∘ K)) := by
    filter_upwards [hF] with b hb using hb.2
  have hFa : F a = g (e (K a)) := (hF.self_of_nhdsWithin ha).2
  change Tendsto F (𝓝[s] a) (𝓝 (F a))
  rw [hFa]
  exact Tendsto.congr' heq.symm hcomp

/-- Composition / restriction along a continuous map of parameter spaces. -/
theorem IsPrimitiveAlongMap.comp {β : Type*} [TopologicalSpace β]
    (h : IsPrimitiveAlongMap K η F s) {φ : β → α} {t : Set β}
    (hφ : ContinuousOn φ t) (hm : MapsTo φ t s) :
    IsPrimitiveAlongMap (K ∘ φ) η (F ∘ φ) t := by
  intro b hb
  obtain ⟨e, he, hKa, g, hg, hF⟩ := h (φ b) (hm hb)
  refine ⟨e, he, hKa, g, hg, ?_⟩
  exact ((hφ b hb).tendsto_nhdsWithin hm).eventually hF

/-- The chart in the local-primitive data can be re-chosen to be any maximal-atlas chart
containing the image point. -/
theorem IsPrimitiveAlongMap.rechart (h : IsPrimitiveAlongMap K η F s) (ha : a ∈ s)
    (hK : ContinuousWithinAt K s a)
    {e' : OpenPartialHomeomorph X ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X)
    (hKa : K a ∈ e'.source) :
    ∃ g' : ℂ → ℂ, (∀ᶠ z in 𝓝 (e' (K a)), HasDerivAt g' (coeffIn e' η z) z) ∧
      ∀ᶠ b in 𝓝[s] a, K b ∈ e'.source ∧ F b = g' (e' (K b)) := by
  obtain ⟨e, he, hKae, g, hg, hF⟩ := h a ha
  set τ : ℂ → ℂ := ⇑e ∘ ⇑e'.symm with hτ_def
  refine ⟨g ∘ τ, ?_, ?_⟩
  · have hWopen : IsOpen (⇑e' '' (e.source ∩ e'.source)) :=
      e'.isOpen_image_of_subset_source (e.open_source.inter e'.open_source) inter_subset_right
    have hzW : e' (K a) ∈ ⇑e' '' (e.source ∩ e'.source) := ⟨K a, ⟨hKae, hKa⟩, rfl⟩
    have hτan : ∀ᶠ z in 𝓝 (e' (K a)), AnalyticAt ℂ τ z := by
      filter_upwards [hWopen.mem_nhds hzW] with z hz
      obtain ⟨q, hq, rfl⟩ := hz
      exact analyticAt_trans he he' (e'.map_source hq.2) (by rw [e'.left_inv hq.2]; exact hq.1)
    have hτz0 : τ (e' (K a)) = e (K a) := by
      change e (e'.symm (e' (K a))) = e (K a)
      rw [e'.left_inv hKa]
    have hτcont : ContinuousAt τ (e' (K a)) :=
      hτan.self_of_nhds.differentiableAt.continuousAt
    have htendsto : Tendsto τ (𝓝 (e' (K a))) (𝓝 (e (K a))) := by
      rw [← hτz0]; exact hτcont.tendsto
    have hg2 : ∀ᶠ z in 𝓝 (e' (K a)), HasDerivAt g (coeffIn e η (τ z)) (τ z) :=
      htendsto.eventually hg
    have hτderiv : ∀ᶠ z in 𝓝 (e' (K a)), HasDerivAt τ (deriv τ z) z := by
      filter_upwards [hτan] with z hz using hz.differentiableAt.hasDerivAt
    have hcoeff : ∀ᶠ z in 𝓝 (e' (K a)), coeffIn e' η z = deriv τ z * coeffIn e η (τ z) := by
      filter_upwards [hWopen.mem_nhds hzW] with z hz
      obtain ⟨q, hq, rfl⟩ := hz
      exact coeffIn_trans he he' η ⟨q, hq, rfl⟩
    filter_upwards [hg2, hτderiv, hcoeff] with z hz1 hz2 hz3
    have hcomp := hz1.comp z hz2
    rw [hz3, mul_comm]
    exact hcomp
  · have hWopen : IsOpen (e.source ∩ e'.source) := e.open_source.inter e'.open_source
    have hmem : K a ∈ e.source ∩ e'.source := ⟨hKae, hKa⟩
    filter_upwards [hF, hK.tendsto.eventually (hWopen.mem_nhds hmem)] with b hb hbmem
    refine ⟨hbmem.2, ?_⟩
    rw [hb.2]
    change g (e (K b)) = g (τ (e' (K b)))
    congr 1
    change e (K b) = e (e'.symm (e' (K b)))
    rw [e'.left_inv hbmem.2]

/-- **Uniqueness up to a constant.** Chart overlaps need not be connected; primitives are only
ever compared *along the parameter space* (never across an overlap directly). -/
theorem IsPrimitiveAlongMap.sub_eq_sub (hs : IsPreconnected s) (hK : ContinuousOn K s)
    (h₁ : IsPrimitiveAlongMap K η F₁ s) (h₂ : IsPrimitiveAlongMap K η F₂ s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) : F₁ b - F₂ b = F₁ a - F₂ a := by
  have hlc : IsLocallyConstant (fun x : s => F₁ (x : α) - F₂ (x : α)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨c, hc⟩
    obtain ⟨e₁, he₁, hKc, g₁, hg₁, hF₁⟩ := h₁ c hc
    obtain ⟨g₂', hg₂', hF₂⟩ := h₂.rechart hc (hK.continuousWithinAt hc) he₁ hKc
    have hFc1 : F₁ c = g₁ (e₁ (K c)) := (hF₁.self_of_nhdsWithin hc).2
    have hFc2 : F₂ c = g₂' (e₁ (K c)) := (hF₂.self_of_nhdsWithin hc).2
    set z₀ : ℂ := e₁ (K c) with hz₀_def
    set g₂'' : ℂ → ℂ := fun z => g₂' z + (g₁ z₀ - g₂' z₀) with hg₂''_def
    have hshift : ∀ᶠ z in 𝓝 z₀, HasDerivAt g₂'' (coeffIn e₁ η z) z := by
      filter_upwards [hg₂'] with z hz using hz.add_const _
    have heq : g₁ =ᶠ[𝓝 z₀] g₂'' := eventuallyEq_of_hasDerivAt_eq hg₁ hshift (by simp [hg₂''_def])
    have hcont : ContinuousWithinAt (fun b => e₁ (K b)) s c :=
      (e₁.continuousOn.continuousAt (e₁.open_source.mem_nhds hKc)).comp_continuousWithinAt
        (hK.continuousWithinAt hc)
    have heqb : ∀ᶠ b in 𝓝[s] c, F₁ b - F₂ b = F₁ c - F₂ c := by
      filter_upwards [hF₁, hF₂, hcont.tendsto.eventually heq] with b hb1 hb2 hb3
      calc F₁ b - F₂ b = g₁ (e₁ (K b)) - g₂' (e₁ (K b)) := by rw [hb1.2, hb2.2]
        _ = g₂'' (e₁ (K b)) - g₂' (e₁ (K b)) := by rw [hb3]
        _ = g₁ z₀ - g₂' z₀ := by simp [hg₂''_def]
        _ = F₁ c - F₂ c := by rw [hFc1, hFc2]
    change ∀ᶠ y : s in 𝓝 (⟨c, hc⟩ : s), F₁ (y : α) - F₂ (y : α) = F₁ c - F₂ c
    rw [nhds_subtype_eq_comap_nhdsWithin s ⟨c, hc⟩, Filter.eventually_comap]
    filter_upwards [heqb] with b hb y hy
    rw [hy]
    exact hb
  have := Subtype.preconnectedSpace hs
  exact (hlc.apply_eq_of_preconnectedSpace (⟨a, ha⟩ : s) (⟨b, hb⟩ : s)).symm

/-- The junction argument: primitives on `s₁`, `s₂` agreeing at a point of the (preconnected)
overlap glue to a primitive on `s₁ ∪ s₂`. -/
theorem IsPrimitiveAlongMap.glue [∀ a, Decidable (a ∈ s)]
    (hK : ContinuousOn K (s ∪ t))
    (h₁ : IsPrimitiveAlongMap K η F₁ s) (h₂ : IsPrimitiveAlongMap K η F₂ t)
    (hL : IsPreconnected (s ∩ t)) {a₀ : α} (ha₀ : a₀ ∈ s ∩ t) (hval : F₁ a₀ = F₂ a₀)
    (hcov : ∀ a ∈ s ∪ t, s ∈ 𝓝[s ∪ t] a ∨ t ∈ 𝓝[s ∪ t] a ∨ a ∈ s ∩ t) :
    IsPrimitiveAlongMap K η (Set.piecewise s F₁ F₂) (s ∪ t) := by
  have hCKL : ContinuousOn K (s ∩ t) := hK.mono (inter_subset_left.trans subset_union_left)
  have hFeq : Set.EqOn F₁ F₂ (s ∩ t) := by
    intro c hc
    have hsub := (h₁.mono inter_subset_left).sub_eq_sub hL hCKL (h₂.mono inter_subset_right)
      ha₀ hc
    exact sub_eq_zero.mp (by rw [hsub, hval, sub_self])
  have hpw2 : ∀ b ∈ t, Set.piecewise s F₁ F₂ b = F₂ b := by
    intro b hb2
    by_cases hb1 : b ∈ s
    · rw [Set.piecewise_eq_of_mem _ _ _ hb1, hFeq ⟨hb1, hb2⟩]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hb1]
  intro a ha
  rcases hcov a ha with hmem | hmem | hmem
  · have ha1 : a ∈ s := mem_of_mem_nhdsWithin ha hmem
    obtain ⟨e, he, hKa, g, hg, hF⟩ := h₁ a ha1
    refine ⟨e, he, hKa, g, hg, ?_⟩
    filter_upwards [hF.filter_mono (nhdsWithin_le_of_mem hmem), hmem] with b hb hbs1
    exact ⟨hb.1, by rw [Set.piecewise_eq_of_mem _ _ _ hbs1, hb.2]⟩
  · have ha2 : a ∈ t := mem_of_mem_nhdsWithin ha hmem
    obtain ⟨e, he, hKa, g, hg, hF⟩ := h₂ a ha2
    refine ⟨e, he, hKa, g, hg, ?_⟩
    filter_upwards [hF.filter_mono (nhdsWithin_le_of_mem hmem), hmem] with b hb hbt
    exact ⟨hb.1, by rw [hpw2 b hbt, hb.2]⟩
  · obtain ⟨ha1, ha2⟩ := hmem
    obtain ⟨e, he, hKa, g₁, hg₁, hF₁⟩ := h₁ a ha1
    have hKcont : ContinuousWithinAt K (s ∪ t) a := hK a ha
    obtain ⟨g₂', hg₂', hF₂⟩ :=
      h₂.rechart ha2 (hKcont.mono subset_union_right) he hKa
    have hFa1 := hF₁.self_of_nhdsWithin ha1
    have hFa2 := hF₂.self_of_nhdsWithin ha2
    have heqPt : g₁ (e (K a)) = g₂' (e (K a)) := by
      rw [← hFa1.2, ← hFa2.2, hFeq ⟨ha1, ha2⟩]
    have heq : g₁ =ᶠ[𝓝 (e (K a))] g₂' := eventuallyEq_of_hasDerivAt_eq hg₁ hg₂' heqPt
    refine ⟨e, he, hKa, g₁, hg₁, ?_⟩
    rw [nhdsWithin_union, Filter.eventually_sup]
    refine ⟨?_, ?_⟩
    · filter_upwards [hF₁, self_mem_nhdsWithin] with b hb hbs1
      exact ⟨hb.1, by rw [Set.piecewise_eq_of_mem _ _ _ hbs1, hb.2]⟩
    · have hcontK2 : ContinuousWithinAt (fun b => e (K b)) t a :=
        (e.continuousOn.continuousAt (e.open_source.mem_nhds hKa)).comp_continuousWithinAt
          (hKcont.mono subset_union_right)
      filter_upwards [hF₂, self_mem_nhdsWithin, hcontK2.tendsto.eventually heq] with b hb hbs2 hbeq
      refine ⟨hb.1, ?_⟩
      rw [hpw2 b hbs2, hb.2]
      exact hbeq.symm

/-- Constant-chart primitive: if `K` maps all of `s` into a single chart `e`, with image inside
a ball `ball c r ⊆ e.target` on which `g` is a planar primitive of `coeffIn e η`, then
`g ∘ e ∘ K` is a primitive of `η` along `K` on `s`. Used by the 1D chain-continuation induction
and the 2D grid (cell primitives). -/
theorem isPrimitiveAlongMap_of_ball {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) {c : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hg : ∀ z ∈ ball c r, HasDerivAt g (coeffIn e η z) z)
    (hmaps : ∀ a ∈ s, K a ∈ e.source ∧ e (K a) ∈ ball c r) :
    IsPrimitiveAlongMap K η (fun a => g (e (K a))) s := by
  intro a ha
  refine ⟨e, he, (hmaps a ha).1, g, ?_, ?_⟩
  · filter_upwards [isOpen_ball.mem_nhds (hmaps a ha).2] with z hz using hg z hz
  · filter_upwards [self_mem_nhdsWithin] with b hb using ⟨(hmaps b hb).1, rfl⟩

end RS

end
