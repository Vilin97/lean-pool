/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: local-multiplicity (CC4). The multiplicity definition and its basic API.
-/
import LeanPool.JacobianDiffgeo.LocalMultiplicity.ChartBridge
import LeanPool.JacobianDiffgeo.LocalMultiplicity.PlanarNormalForm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.Order

/-!
# Local multiplicity of a holomorphic map (CC4)

* `RS.multiplicityENat F x : ℕ∞` — the vanishing order of `inChartAt F x` at `chartAt ℂ x x`.
  `⊤` iff `F` is holomorphic and locally constant at `x`; junk `0` if not holomorphic.
* `RS.multiplicity F x : ℕ` — `toNat` of the above; junk `0` for locally-constant or
  non-holomorphic `F`. `RS.IsRamifiedAt F x` means `2 ≤ multiplicity F x`.
* Junk API: `multiplicityENat_eq_top_of_eventuallyConst`, `multiplicity_of_eventuallyConst`.
* Honest API (guarded by holomorphy/nonconstancy): `multiplicityENat_ne_zero`,
  `multiplicityENat_eq_top_iff`, `natCast_multiplicity`, `one_le_multiplicity`.
* `RS.analyticOrderAt_charts_eq_multiplicityENat` — chart invariance in any maximal-atlas pair.
* Isolated fibres: `RS.eventually_ne`, `RS.exists_nhds_fiber_eq_singleton`.
* CC3 compatibility: `RS.meromorphicOrderAt_chart_sub`, `RS.meromorphicOrderAt_chart_of_eq_zero`.
-/

open Filter Set OpenPartialHomeomorph
open scoped ContDiff Manifold Topology

namespace RS

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- ℕ∞-valued local multiplicity (CC4). `⊤` iff `F` is holomorphic and locally constant at `x`;
`0` iff `inChartAt F x` is not analytic (junk). Honest value: the vanishing order `k ≥ 1`. -/
noncomputable def multiplicityENat (F : X → Y) (x : X) : ℕ∞ :=
  analyticOrderAt (inChartAt F x) (chartAt ℂ x x)

/-- CC4's `multiplicity F x : ℕ`: the order when finite; junk `0` when `F` is locally constant
at `x` (order `⊤`) or not holomorphic at `x` (order junk `0`). -/
noncomputable def multiplicity (F : X → Y) (x : X) : ℕ := (multiplicityENat F x).toNat

/-- `F` is ramified at `x` iff its local multiplicity is at least `2`. -/
def IsRamifiedAt (F : X → Y) (x : X) : Prop := 2 ≤ multiplicity F x

theorem multiplicityENat_def (F : X → Y) (x : X) :
    multiplicityENat F x = analyticOrderAt (inChartAt F x) (chartAt ℂ x x) := rfl

theorem multiplicity_def (F : X → Y) (x : X) :
    multiplicity F x = (multiplicityENat F x).toNat := rfl

/-- Planar specialization: on `ℂ` the charts are `refl`, so the multiplicity is the recentered
vanishing order itself. -/
@[simp] theorem multiplicityENat_planar (f : ℂ → ℂ) (z₀ : ℂ) :
    multiplicityENat f z₀ = analyticOrderAt (f · - f z₀) z₀ := rfl

section Junk

theorem multiplicityENat_eq_top_of_eventuallyConst {F : X → Y} {x : X}
    (h : EventuallyConst F (𝓝 x)) : multiplicityENat F x = ⊤ := by
  have h1 := eventuallyConst_inChartAt h
  rw [eventuallyConst_nhds_iff] at h1
  simp only [inChartAt_apply_chart] at h1
  rw [multiplicityENat_def, analyticOrderAt_eq_top]
  exact h1

@[simp] theorem multiplicity_of_eventuallyConst {F : X → Y} {x : X}
    (h : EventuallyConst F (𝓝 x)) : multiplicity F x = 0 := by
  rw [multiplicity_def, multiplicityENat_eq_top_of_eventuallyConst h]
  rfl

end Junk

section Honest

variable {F : X → Y} {x : X}

theorem multiplicityENat_ne_zero (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    multiplicityENat F x ≠ 0 := by
  rw [multiplicityENat_def, analyticOrderAt_ne_zero]
  exact ⟨(LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hF).2, inChartAt_apply_chart F x⟩

theorem multiplicityENat_eq_top_iff (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    multiplicityENat F x = ⊤ ↔ EventuallyConst F (𝓝 x) := by
  constructor
  · intro h
    rw [multiplicityENat_def, analyticOrderAt_eq_top] at h
    rw [← eventuallyConst_inChartAt_iff (LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hF).1,
      eventuallyConst_nhds_iff]
    simpa [inChartAt_apply_chart] using h
  · exact multiplicityENat_eq_top_of_eventuallyConst

theorem multiplicityENat_ne_top (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) : multiplicityENat F x ≠ ⊤ :=
  fun h ↦ hnc ((multiplicityENat_eq_top_iff hF).mp h)

theorem natCast_multiplicity (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) :
    (multiplicity F x : ℕ∞) = multiplicityENat F x :=
  ENat.natCast_toNat (multiplicityENat_ne_top hF hnc)

theorem one_le_multiplicity (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) : 1 ≤ multiplicity F x := by
  rw [multiplicity_def, Nat.one_le_iff_ne_zero]
  intro h0
  rw [ENat.toNat_eq_zero] at h0
  exact h0.elim (multiplicityENat_ne_zero hF) (multiplicityENat_ne_top hF hnc)

end Honest

section ChartInvariance

variable [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]

/-- CHART INVARIANCE: the defining order is the same in any admissible chart pair. -/
theorem analyticOrderAt_charts_eq_multiplicityENat
    {F : X → Y} {x : X} (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    {e : OpenPartialHomeomorph X ℂ} {e' : OpenPartialHomeomorph Y ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hxe : x ∈ e.source)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y) (hxe' : F x ∈ e'.source) :
    analyticOrderAt (fun z ↦ e' (F (e.symm z)) - e' (F x)) (e x) = multiplicityENat F x := by
  obtain ⟨hFc, hchart⟩ := LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hF
  have hxc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hxc' : F x ∈ (chartAt ℂ (F x)).source := mem_chart_source ℂ (F x)
  -- the transitions to the standard charts, analytic with nonvanishing derivative
  obtain ⟨hτ, hτ'⟩ :=
    analyticAt_transition he (IsManifold.chart_mem_maximalAtlas x) hxe hxc
  obtain ⟨hσ, hσ'⟩ :=
    analyticAt_transition (IsManifold.chart_mem_maximalAtlas (F x)) he' hxc' hxe'
  -- the uncentered composite in the standard charts
  set g : ℂ → ℂ := fun z ↦ chartAt ℂ (F x) (F ((chartAt ℂ x).symm z)) with hg_def
  have hg : AnalyticAt ℂ g (chartAt ℂ x x) := analyticAt_inChartAt_iff.mp hchart
  have hgz₀ : g (chartAt ℂ x x) = chartAt ℂ (F x) (F x) := by
    rw [hg_def]
    simp only
    rw [(chartAt ℂ x).left_inv hxc]
  -- outer recentered transition
  set A : ℂ → ℂ := fun w ↦ e' ((chartAt ℂ (F x)).symm w) - e' (F x) with hA_def
  -- Step 0: eventual factorization through the standard charts
  have hev : (fun z ↦ e' (F (e.symm z)) - e' (F x)) =ᶠ[𝓝 (e x)]
      (A ∘ g) ∘ (⇑(chartAt ℂ x) ∘ ⇑e.symm) := by
    have h1 : ∀ᶠ z in 𝓝 (e x), e.symm z ∈ (chartAt ℂ x).source := by
      apply (e.continuousAt_symm (e.map_source hxe)).preimage_mem_nhds
      rw [e.left_inv hxe]
      exact (chartAt ℂ x).open_source.mem_nhds hxc
    have hcF : ContinuousAt (F ∘ ⇑e.symm) (e x) := by
      apply ContinuousAt.comp ?_ (e.continuousAt_symm (e.map_source hxe))
      rw [e.left_inv hxe]
      exact hFc
    have h2 : ∀ᶠ z in 𝓝 (e x), F (e.symm z) ∈ (chartAt ℂ (F x)).source := by
      apply hcF.preimage_mem_nhds
      simp only [Function.comp_apply]
      rw [e.left_inv hxe]
      exact (chartAt ℂ (F x)).open_source.mem_nhds hxc'
    filter_upwards [h1, h2] with z h1z h2z
    simp only [hA_def, hg_def, Function.comp_apply]
    rw [(chartAt ℂ x).left_inv h1z, (chartAt ℂ (F x)).left_inv h2z]
  rw [analyticOrderAt_congr hev]
  -- Step 1: strip the bi-analytic source transition
  rw [analyticOrderAt_comp_of_deriv_ne_zero hτ hτ']
  have hτx : (⇑(chartAt ℂ x) ∘ ⇑e.symm) (e x) = chartAt ℂ x x := by
    simp only [Function.comp_apply]
    rw [e.left_inv hxe]
  rw [hτx]
  -- Step 2: strip the bi-analytic target transition
  have hσg : AnalyticAt ℂ (⇑e' ∘ ⇑(chartAt ℂ (F x)).symm) (g (chartAt ℂ x x)) := by
    rw [hgz₀]; exact hσ
  have hσg' : deriv (⇑e' ∘ ⇑(chartAt ℂ (F x)).symm) (g (chartAt ℂ x x)) ≠ 0 := by
    rw [hgz₀]; exact hσ'
  have hAg : (A ∘ g) =ᶠ[𝓝 (chartAt ℂ x x)]
      fun z ↦ (⇑e' ∘ ⇑(chartAt ℂ (F x)).symm) (g z)
        - (⇑e' ∘ ⇑(chartAt ℂ (F x)).symm) (g (chartAt ℂ x x)) := by
    apply Eventually.of_forall
    intro z
    simp only [hA_def, Function.comp_apply]
    rw [hgz₀, (chartAt ℂ (F x)).left_inv hxc']
  rw [analyticOrderAt_congr hAg, analyticOrderAt_left_comp_sub hσg hσg' hg]
  -- Step 3: identify with the defining order
  rw [multiplicityENat_def]
  apply analyticOrderAt_congr
  apply Eventually.of_forall
  intro z
  simp only [inChartAt, hg_def]
  rw [(chartAt ℂ x).left_inv hxc]

end ChartInvariance

section IsolatedFibers

variable {F : X → Y} {x : X}

/-- Isolated points of the fibre: near `x` (but off `x`), `F` avoids the value `F x`. -/
theorem eventually_ne (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) : ∀ᶠ y in 𝓝[≠] x, F y ≠ F x := by
  obtain ⟨hFc, hA⟩ := LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hF
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    apply hnc
    rw [← eventuallyConst_inChartAt_iff hFc, eventuallyConst_nhds_iff]
    simpa [inChartAt_apply_chart] using h
  · rw [← map_nhdsNE (chartAt ℂ x) (mem_chart_source ℂ x), eventually_map] at h
    have h1 : ∀ᶠ y in 𝓝[≠] x, (chartAt ℂ x).symm (chartAt ℂ x y) = y :=
      ((chartAt ℂ x).eventually_left_inverse (mem_chart_source ℂ x)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [h, h1] with y hy h1y
    intro hFy
    apply hy
    simp only [inChartAt, h1y, hFy, sub_self]

/-- The fibre of `F x` meets a suitable neighborhood of `x` only in `x`. -/
theorem exists_nhds_fiber_eq_singleton (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, F y = F x → y = x := by
  have h := eventually_ne hF hnc
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨U, hU, hUsub⟩ := eventually_iff_exists_mem.mp h
  refine ⟨U, hU, fun y hy hFy ↦ ?_⟩
  by_contra hyx
  exact hUsub y hy (by simpa using hyx) hFy

end IsolatedFibers

section CC3Compat

/-- CC3 COMPATIBILITY: our multiplicity vs `meromorphicOrderAt` in the chart at `x`
(for target `ℂ` the target chart is `refl`). -/
theorem meromorphicOrderAt_chart_sub {f : X → ℂ} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    meromorphicOrderAt (fun z ↦ f ((chartAt ℂ x).symm z) - f x) (chartAt ℂ x x)
      = (multiplicityENat f x).map (Nat.cast : ℕ → ℤ) := by
  have hA : AnalyticAt ℂ (inChartAt f x) (chartAt ℂ x x) :=
    (LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hf).2
  exact hA.meromorphicOrderAt_eq

/-- CC3 compatibility for functions vanishing at `x`: `meromorphic-and-divisors` reads the LHS
as `ordAtX f x`. -/
theorem meromorphicOrderAt_chart_of_eq_zero {f : X → ℂ} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) (h0 : f x = 0) :
    meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)
      = (multiplicityENat f x).map (Nat.cast : ℕ → ℤ) := by
  rw [← meromorphicOrderAt_chart_sub hf]
  congr 1
  funext z
  simp [h0]

end CC3Compat

end RS
