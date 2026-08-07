/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacobianConstruction.Basic

/-!
# `ofCurve`, well-definedness, `ofCurve_self`, `ofCurve_contMDiff` (CC9, §8)

Unit: jacobian-construction. The Abel–Jacobi map `Jacobian.ofCurve`, its any-path recipe
(well-definedness, `ofCurve_eq_of_path`), `ofCurve_self`, and `ofCurve_contMDiff` (holomorphy).
Path-connectedness of `X` is derived locally (§8.1; filed as a request to surfaces-and-charts,
non-blocking).

`ofCurve_contMDiff` (§8.3) is gated by `[DiscreteTopology (periodSubgroup X).topologicalClosure]`,
for the same reason `ChartedSpace`/`IsManifold (Jacobian X)` are (`Basic.lean`'s ledger): the
statement itself does not elaborate without a `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)`
instance for its codomain. Modulo that (unavoidable) hypothesis, the proof is complete: fix `x₀`,
work in the chart `e := chartAt ℂ x₀`; each `coeffIn e (basis X i)` has a holomorphic primitive
`g i` on a ball around `e x₀` (planar Morera); the straight-segment path in the chart (pulled back
through `e.symm` via `Path.segment`/`Path.map'`) gives `ofCurve P z = ULift.up (mk (v₀ + g (e z)))`
near `x₀` (`hkey`); reading this through the Jacobian's own chart (the same locally-constant
lattice-shift computation as `Torus.contMDiff_add_torus`/`ULift.contMDiff_uliftUp`) makes the
chart composite affine in `g (e z)`, hence analytic.
-/

open scoped ContDiff Manifold Convex Topology
open IsManifold Metric Set Filter

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §8.1: path-connectedness of `X` (small gap, filled here; `Compat`) -/

/-- `Compat`: `X` is locally path-connected, via its charts into `ℂ` (a locally convex space).
Filed as a request to surfaces-and-charts (`docs/requests/surfaces-and-charts.md`); carried here
as a local instance since no upstream unit currently provides it. -/
instance : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := X)

/-- `Compat`: `X` is path-connected (`ConnectedSpace X` + `LocallyPathConnectedSpace X`). -/
instance : PathConnectedSpace X := .of_locallyPathConnectedSpace

/-! ### `periodVector` of a loop, at *any* basepoint, lies in `periodSubgroup X` -/

/-- Basepoint-independence of the period subgroup: for any based loop `γ` at any point `x` (not
just at `periodSubgroup`'s defining basepoint), `periodVector (basis X) γ` still lies in
`periodSubgroup X`, via conjugation by a connecting path (`RS.period_conj`). -/
theorem RS.periodVector_mem_periodSubgroup {x : X} (γ : Path x x) :
    RS.periodVector (RS.basis X) γ ∈ RS.periodSubgroup X := by
  set x₀ := Classical.arbitrary X
  set σ : Path x₀ x := PathConnectedSpace.somePath x₀ x
  have heq : RS.periodVector (RS.basis X) γ
      = RS.periodVector (RS.basis X) ((σ.trans γ).trans σ.symm) := by
    funext i
    exact (RS.period_conj σ γ (RS.basis X i)).symm
  rw [heq]
  exact AddSubgroup.subset_closure ⟨(σ.trans γ).trans σ.symm, rfl⟩

namespace Jacobian

/-! ### `ofCurve` (§8.2) -/

/-- The Abel–Jacobi map from a compact Riemann surface to its Jacobian
(`docs/Jacobian_challenge.lean:92`): integrate the basis of holomorphic `1`-forms along *some*
path from `P` to `x` (any choice; well-defined mod periods, `ofCurve_eq_of_path`). -/
noncomputable def ofCurve (P : X) : X → Jacobian X := fun x =>
  ULift.up (QuotientAddGroup.mk
    (fun i => RS.pathIntegral (PathConnectedSpace.somePath P x) (RS.basis X i)))

/-- `ofCurve` computed along *any* path `σ : Path P x`, not just the canonical
`PathConnectedSpace.somePath` — the any-path recipe, and the source of well-definedness. -/
theorem ofCurve_eq_of_path (P x : X) (σ : Path P x) :
    ofCurve P x = ULift.up (QuotientAddGroup.mk (fun i => RS.pathIntegral σ (RS.basis X i))) := by
  change ULift.up (QuotientAddGroup.mk
      (fun i => RS.pathIntegral (PathConnectedSpace.somePath P x) (RS.basis X i)))
    = ULift.up (QuotientAddGroup.mk (fun i => RS.pathIntegral σ (RS.basis X i)))
  congr 1
  set σ₀ := PathConnectedSpace.somePath P x with hσ₀_def
  rw [QuotientAddGroup.eq_iff_sub_mem]
  have hmem : RS.periodVector (RS.basis X) (σ.trans σ₀.symm) ∈ RS.periodSubgroup X :=
    RS.periodVector_mem_periodSubgroup (σ.trans σ₀.symm)
  have heq : (fun i => RS.pathIntegral σ₀ (RS.basis X i)) -
      (fun i => RS.pathIntegral σ (RS.basis X i))
      = -RS.periodVector (RS.basis X) (σ.trans σ₀.symm) := by
    funext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    change _ = -(RS.pathIntegral (σ.trans σ₀.symm) (RS.basis X i))
    rw [RS.pathIntegral_trans, RS.pathIntegral_symm]
    ring
  rw [heq]
  exact (RS.periodSubgroup X).topologicalClosure.neg_mem
    (AddSubgroup.le_topologicalClosure _ hmem)

@[simp] theorem ofCurve_self (P : X) : ofCurve P P = 0 := by
  rw [ofCurve_eq_of_path P P (Path.refl P)]
  have hzero : (fun i => RS.pathIntegral (Path.refl P) (RS.basis X i)) = (0 : Fin (genus X) → ℂ) :=
      by
    funext i
    exact RS.pathIntegral_refl P (RS.basis X i)
  rw [hzero]
  rfl

/-! ### `ofCurve_contMDiff` (§8.3) -/

variable [DiscreteTopology (RS.periodSubgroup X).topologicalClosure]

/-- Holomorphy of the Abel–Jacobi map. Fix `x₀`; work in the chart `e := chartAt ℂ x₀`. Each
`coeffIn e (basis X i)` has a holomorphic primitive `g i` on a ball around `e x₀` (planar Morera,
`exists_hasDerivAt_ball`), normalized to vanish at `e x₀`. For `z` in a further sub-neighborhood
`U` of `x₀`, the straight-segment path in the chart, pulled back through `e.symm`
(`Path.segment`/`Path.map'`), stays inside a single chart-ball, so `IsPrimitiveAlongMap` gives
`pathIntegral (segment path) (basis X i) = g i (e z)`. Composing with a fixed path `P → x₀` and
using `ofCurve_eq_of_path`, `ofCurve P z = ULift.up (mk (v₀ + g (e z)))` on `U`, where `v₀` is
constant; reading this in the Jacobian's own chart (via `Torus`'s locally-constant lattice-shift
lemma) makes the chart composite affine in `g (e z)`, hence analytic. -/
theorem ofCurve_contMDiff (P : X) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (ofCurve P) := by
  intro x₀
  set e := chartAt ℂ x₀ with he_def
  obtain ⟨r, hr, hballsub⟩ := Metric.isOpen_iff.mp e.open_target (e x₀) (mem_chart_target ℂ x₀)
  choose g hg0 hg using fun i : Fin (genus X) =>
    RS.exists_hasDerivAt_ball (z₀ := e x₀) (w := (0 : ℂ))
      ((RS.basis X i).analyticOnNhd_coeffIn (chart_mem_maximalAtlas x₀)) hballsub
      (Metric.mem_ball_self hr)
  have hganalytic : ∀ i, AnalyticOnNhd ℂ (g i) (ball (e x₀) r) := fun i =>
    DifferentiableOn.analyticOnNhd (fun z hz => (hg i z hz).differentiableAt.differentiableWithinAt)
      Metric.isOpen_ball
  set σ₀ := PathConnectedSpace.somePath P x₀ with hσ₀_def
  set v₀ : Fin (genus X) → ℂ := fun i => RS.pathIntegral σ₀ (RS.basis X i) with hv₀_def
  set U : Set X := e.source ∩ e ⁻¹' ball (e x₀) r with hU_def
  have hUopen : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
  have hx₀U : x₀ ∈ U := ⟨mem_chart_source ℂ x₀, by
    rw [Set.mem_preimage]; exact Metric.mem_ball_self hr⟩
  have hballseg : ∀ z ∈ U, [e x₀ -[ℝ] e z] ⊆ ball (e x₀) r := by
    intro z hz
    exact (convex_ball (e x₀) r).segment_subset (Metric.mem_ball_self hr) hz.2
  have hkey : ∀ z ∈ U, ofCurve P z
      = ULift.up (QuotientAddGroup.mk (fun i => v₀ i + g i (e z))) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Set.mem_preimage] at hz2
    have hsub : Set.range (Path.segment (e x₀) (e z)) ⊆ e.target := by
      rw [Path.range_segment]
      exact fun w hw => hballsub (hballseg z ⟨hz1, by rw [Set.mem_preimage]; exact hz2⟩ hw)
    have hcont : ContinuousOn e.symm (Set.range (Path.segment (e x₀) (e z))) :=
      e.continuousOn_symm.mono hsub
    set τ := (Path.segment (e x₀) (e z)).map' hcont with hτ_def
    have hxe : e.symm (e x₀) = x₀ := e.left_inv (mem_chart_source ℂ x₀)
    have hze : e.symm (e z) = z := e.left_inv hz1
    set τ' : Path x₀ z := τ.cast hxe.symm hze.symm with hτ'_def
    have hmaps : ∀ t : X, t ∈ Set.range τ' → t ∈ e.source ∧ e t ∈ ball (e x₀) r := by
      rintro t ⟨s, rfl⟩
      have hts : τ' s = e.symm (Path.segment (e x₀) (e z) s) := rfl
      have hmemtarget : Path.segment (e x₀) (e z) s ∈ e.target :=
        hsub (Set.mem_range_self s)
      have hmemball : Path.segment (e x₀) (e z) s ∈ ball (e x₀) r :=
        hballseg z ⟨hz1, by rw [Set.mem_preimage]; exact hz2⟩
          (Path.range_segment (e x₀) (e z) ▸ Set.mem_range_self s)
      rw [hts]
      exact ⟨e.map_target hmemtarget, by rw [e.right_inv hmemtarget]; exact hmemball⟩
    have hmapsAll : ∀ a : ℝ, τ'.extend a ∈ e.source ∧ e (τ'.extend a) ∈ ball (e x₀) r := by
      intro a
      exact hmaps _ (Path.extend_range τ' ▸ Set.mem_range_self a)
    have hprim : ∀ i, RS.IsPrimitiveAlong τ' (RS.basis X i)
        (fun a => g i (e (τ'.extend a))) := by
      intro i
      apply RS.isPrimitiveAlongMap_of_ball (chart_mem_maximalAtlas x₀)
        (c := e x₀) (r := r) (fun w hw => hg i w hw)
      intro a _
      exact hmapsAll a
    have hint : ∀ i, RS.pathIntegral τ' (RS.basis X i) = g i (e z) := by
      intro i
      rw [(hprim i).pathIntegral_eq]
      show g i (e (τ'.extend 1)) - g i (e (τ'.extend 0)) = g i (e z)
      rw [τ'.extend_one, τ'.extend_zero, hg0 i]
      ring
    rw [ofCurve_eq_of_path P z (σ₀.trans τ')]
    congr 2
    funext i
    show RS.pathIntegral (σ₀.trans τ') (RS.basis X i) = v₀ i + g i (e z)
    rw [RS.pathIntegral_trans, hint i]
  set L := (RS.periodSubgroup X).topologicalClosure with hL_def
  set q₀ := ofCurve P x₀ with hq₀_def
  have hg0v : (fun i => g i (e x₀)) = (0 : Fin (genus X) → ℂ) := by funext i; exact hg0 i
  have hq₀eq : q₀ = ULift.up (QuotientAddGroup.mk v₀) := by
    rw [hq₀_def, hkey x₀ hx₀U]
    congr 2
    funext i
    show v₀ i + g i (e x₀) = v₀ i
    rw [hg0 i, add_zero]
  set x' := Function.surjInv QuotientAddGroup.mk_surjective q₀.down with hx'_def
  have hx'q : (QuotientAddGroup.mk x' : RS.Jac₀ X) = q₀.down := Function.surjInv_eq _ q₀.down
  set ℓ := x' - v₀ with hℓ_def
  have hℓL : ℓ ∈ L := by
    have heq2 : (QuotientAddGroup.mk x' : RS.Jac₀ X) = QuotientAddGroup.mk v₀ := by
      rw [hx'q, hq₀eq]
    have := (QuotientAddGroup.eq_iff_sub_mem).mp heq2
    simpa [hℓ_def] using this
  -- continuity of `e` and of `z ↦ v₀ + g (e z)` at `x₀`
  have hecont : ContinuousAt e x₀ :=
    e.continuousOn.continuousAt (e.open_source.mem_nhds (mem_chart_source ℂ x₀))
  have hgicont : ∀ i, ContinuousAt (g i) (e x₀) := fun i =>
    (hganalytic i).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hr))
  have hgcont : ContinuousAt (fun z => v₀ + fun i => g i (e z)) x₀ := by
    refine continuousAt_const.add (continuousAt_pi.mpr fun i => ?_)
    exact (hgicont i).comp hecont
  -- the Jacobian's own chart, evaluated on `hkey`'s formula, is eventually `x' + g (e z)`
  have hmem_v0 : v₀ + ℓ ∈ ball x' (RS.injRadius L) := by
    have hval : v₀ + ℓ = x' := by rw [hℓ_def]; abel
    rw [hval]; exact Metric.mem_ball_self (RS.injRadius_pos L)
  have hEv : (fun w : Fin (genus X) → ℂ => RS.chartAt' L x' (QuotientAddGroup.mk w))
      =ᶠ[𝓝 v₀] (fun w => w + ℓ) := RS.chartAt'_eventuallyEq_add L hℓL hmem_v0
  -- assemble `ContMDiffAt`
  rw [contMDiffAt_iff]
  have hptdom : extChartAt 𝓘(ℂ) x₀ x₀ = e x₀ := rfl
  refine ⟨?_, ?_⟩
  · -- `ContinuousAt (ofCurve P) x₀`
    have hUev : ofCurve P =ᶠ[𝓝 x₀] fun z => ULift.up
        (QuotientAddGroup.mk (v₀ + fun i => g i (e z))) :=
      Filter.eventually_of_mem (hUopen.mem_nhds hx₀U) (fun z hz => hkey z hz)
    have hRHScont : ContinuousAt
        (fun z => ULift.up (QuotientAddGroup.mk (v₀ + fun i => g i (e z)) : RS.Jac₀ X)) x₀ :=
      ((RS.continuous_uliftUp (RS.periodSubgroup X).topologicalClosure).continuousAt.comp
        QuotientAddGroup.continuous_mk.continuousAt).comp hgcont
    exact ContinuousAt.congr hRHScont (Filter.EventuallyEq.symm hUev)
  · rw [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ, hptdom]
    -- the composite, purely as a function of the chart variable `ζ`
    have hgcont2 : ContinuousAt (fun ζ : ℂ => v₀ + fun i => g i ζ) (e x₀) :=
      continuousAt_const.add (continuousAt_pi.mpr fun i => hgicont i)
    have htendsto : Filter.Tendsto (fun ζ : ℂ => v₀ + fun i => g i ζ) (𝓝 (e x₀)) (𝓝 v₀) := by
      have h1 := hgcont2.tendsto
      rw [hg0v, add_zero] at h1
      exact h1
    have hEv2 : ∀ᶠ ζ in 𝓝 (e x₀),
        RS.chartAt' L x' (QuotientAddGroup.mk (v₀ + fun i => g i ζ)) = x' + fun i => g i ζ := by
      filter_upwards [htendsto.eventually hEv] with ζ hζ
      rw [hζ, hℓ_def]
      abel
    have hUevent : ∀ᶠ ζ in 𝓝 (e x₀), e.symm ζ ∈ U := by
      have hcont : ContinuousAt e.symm (e x₀) :=
        e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (mem_chart_target ℂ x₀))
      have htendsto2 : Filter.Tendsto e.symm (𝓝 (e x₀)) (𝓝 x₀) := by
        have h1 := hcont.tendsto
        rwa [e.left_inv (mem_chart_source ℂ x₀)] at h1
      exact htendsto2.eventually (hUopen.mem_nhds hx₀U)
    have hFeq : ∀ᶠ ζ in 𝓝 (e x₀), extChartAt 𝓘(ℂ, Fin (genus X) → ℂ) q₀
        (ofCurve P ((extChartAt 𝓘(ℂ) x₀).symm ζ)) = x' + fun i => g i ζ := by
      filter_upwards [e.open_target.mem_nhds (mem_chart_target ℂ x₀), hUevent, hEv2]
        with ζ hζtarget hζU hζEv
      have hstep : (extChartAt 𝓘(ℂ) x₀).symm ζ = e.symm ζ := rfl
      rw [hstep, hkey (e.symm ζ) hζU]
      have hze : e (e.symm ζ) = ζ := e.right_inv hζtarget
      rw [hze, RS.extChartAt_ulift_apply_eq]
      change RS.uliftChartAt L (Function.surjInv QuotientAddGroup.mk_surjective q₀.down)
          (ULift.up (QuotientAddGroup.mk (v₀ + fun i => g i ζ))) = _
      rw [← hx'_def]
      change RS.chartAt' L x' (QuotientAddGroup.mk (v₀ + fun i => g i ζ)) = _
      exact hζEv
    have hAnalytic : AnalyticAt ℂ (fun ζ : ℂ => x' + fun i => g i ζ) (e x₀) :=
      AnalyticAt.add analyticAt_const
        (AnalyticAt.pi fun i => hganalytic i (e x₀) (Metric.mem_ball_self hr))
    exact (hAnalytic.congr (Filter.EventuallyEq.symm hFeq)).contDiffAt

end Jacobian

end
