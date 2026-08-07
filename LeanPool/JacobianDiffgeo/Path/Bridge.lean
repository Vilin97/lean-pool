/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Path.Continuation
import LeanPool.JacobianDiffgeo.Forms.MDifferential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The bridge to honest integrals (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §4). On a path contained in a
single chart, `pathIntegral` is the classical interval integral of the chart coefficient against
the derivative of the chart composite (single-chart, C¹ bridge). Also: the continuous-path FTC
`∫_γ df = f(y) - f(x)` for holomorphic `f`.

Ownership decision (design §4): this unit proves the abstract single-chart C¹ bridge only;
`circleIntegral`/`curveIntegral` specializations belong to residue-calculus /
planar-stokes-atoms.

Main declarations:
* `RS.pathIntegral_eq_intervalIntegral` — the single-chart bridge.
* `RS.pathIntegral_mdifferential` — FTC along a continuous path for `d f`.
-/

open scoped ContDiff Manifold Topology
open IsManifold Metric Set Filter MeasureTheory

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {x y : X}

/-- On a path contained in a single chart, `pathIntegral` is the classical integral
`∫ coeff · (chart∘γ)'`. -/
theorem pathIntegral_eq_intervalIntegral {γ : Path x y} {η : Form1 X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    (hγ : range ⇑γ ⊆ e.source) {u' : ℝ → ℂ}
    (hu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => e (γ.extend s)) (u' t) (Icc 0 1) t)
    (hu' : ContinuousOn u' (Icc 0 1)) :
    pathIntegral γ η = ∫ t in (0:ℝ)..1, coeffIn e η (e (γ.extend t)) * u' t := by
  obtain ⟨F, hF, hF0⟩ := exists_isPrimitiveAlong γ η
  have hKmem : ∀ t : ℝ, γ.extend t ∈ e.source := fun t =>
    hγ (by rw [← Path.extend_range]; exact mem_range_self t)
  have hderiv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt F (coeffIn e η (e (γ.extend t)) * u' t) (Icc 0 1) t := by
    intro t ht
    obtain ⟨g, hg, hFg⟩ := hF.rechart (mem_univ t)
      γ.continuous_extend.continuousAt.continuousWithinAt he (hKmem t)
    rw [nhdsWithin_univ] at hFg
    have hg_at : HasDerivAt g (coeffIn e η ((fun s => e (γ.extend s)) t))
        ((fun s => e (γ.extend s)) t) := hg.self_of_nhds
    have hchain := HasDerivAt.comp_hasDerivWithinAt (h := fun s => e (γ.extend s)) (x := t)
      hg_at (hu t ht)
    have heqF : F =ᶠ[𝓝[Icc (0:ℝ) 1] t] (g ∘ fun s => e (γ.extend s)) :=
      (hFg.mono (fun b hb => hb.2)).filter_mono nhdsWithin_le_nhds
    have hFt : F t = (g ∘ fun s => e (γ.extend s)) t := (hFg.self_of_nhds).2
    exact hchain.congr_of_eventuallyEq heqF hFt
  have hcontF : ContinuousOn F (Icc (0:ℝ) 1) :=
    (hF.continuousOn γ.continuous_extend.continuousOn).mono (subset_univ _)
  have hderiv' : ∀ t ∈ Ioo (0:ℝ) 1,
      HasDerivWithinAt F (coeffIn e η (e (γ.extend t)) * u' t) (Ioi t) t := by
    intro t ht
    have hIccNhds : Icc (0:ℝ) 1 ∈ 𝓝[Ioi t] t :=
      mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    exact (hderiv t ⟨ht.1.le, ht.2.le⟩).mono_of_mem_nhdsWithin hIccNhds
  have hcont1 : ContinuousOn (fun t => e (γ.extend t)) (Icc (0:ℝ) 1) :=
    e.continuousOn.comp γ.continuous_extend.continuousOn (fun t _ => hKmem t)
  have hcont2 : ContinuousOn (fun t => coeffIn e η (e (γ.extend t))) (Icc (0:ℝ) 1) :=
    (η.continuousOn_coeffIn he).comp hcont1 (fun t _ => e.map_source (hKmem t))
  have hintegrandCont : ContinuousOn (fun t => coeffIn e η (e (γ.extend t)) * u' t)
      (Icc (0:ℝ) 1) := hcont2.mul hu'
  have hint : IntervalIntegrable (fun t => coeffIn e η (e (γ.extend t)) * u' t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le zero_le_one]
  rw [hF.pathIntegral_eq]
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hcontF hderiv' hint

/-- FTC along a path: `∫_γ df = f(end) − f(start)` (Forster 10.2, continuous-path version). -/
theorem pathIntegral_mdifferential {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : Path x y) : pathIntegral γ (mdifferential f hf) = f y - f x := by
  have hFP : IsPrimitiveAlong γ (mdifferential f hf) (f ∘ γ.extend) := by
    intro t _
    set e := chartAt ℂ (γ.extend t) with he_def
    refine ⟨e, chart_mem_maximalAtlas _, mem_chart_source ℂ _, f ∘ ⇑e.symm, ?_, ?_⟩
    · have hb : AnalyticAt ℂ (f ∘ ⇑e.symm) (e (γ.extend t)) :=
        contMDiffAt_iff_analyticAt_comp_chartAt.mp (hf (γ.extend t))
      have hbev : ∀ᶠ z in 𝓝 (e (γ.extend t)), AnalyticAt ℂ (f ∘ ⇑e.symm) z :=
        hb.eventually_analyticAt
      have hcoeff : ∀ᶠ z in 𝓝 (e (γ.extend t)),
          coeffIn e (mdifferential f hf) z = deriv (f ∘ ⇑e.symm) z := by
        filter_upwards [e.open_target.mem_nhds (mem_chart_target ℂ (γ.extend t))] with z hz
        exact coeffIn_mdifferential (chart_mem_maximalAtlas _) hf hz
      filter_upwards [hbev, hcoeff] with z hz1 hz2
      rw [hz2]
      exact hz1.differentiableAt.hasDerivAt
    · rw [nhdsWithin_univ]
      have hev : ∀ᶠ b in 𝓝 t, γ.extend b ∈ e.source :=
        γ.continuous_extend.continuousAt.eventually
          (e.open_source.mem_nhds (mem_chart_source ℂ _))
      filter_upwards [hev] with b hb
      refine ⟨hb, ?_⟩
      change f (γ.extend b) = (f ∘ ⇑e.symm) (e (γ.extend b))
      rw [Function.comp_apply, e.left_inv hb]
  rw [hFP.pathIntegral_eq]
  change f (γ.extend 1) - f (γ.extend 0) = f y - f x
  rw [γ.extend_one, γ.extend_zero]

end RS

end
