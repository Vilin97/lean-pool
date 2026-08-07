/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms

/-!
# `Form1.pullback` — the easy direction (jacobian-functoriality §3)

Unit: jacobian-functoriality. Pullback of a holomorphic `1`-form along *any* holomorphic
`f : X → Y` (chain rule via `mfderiv`, no branch-point subtlety).

Main declarations:
* `RS.Form1.pullback f hf : Form1 Y →ₗ[ℂ] Form1 X`.
* `RS.coeffAt_pullback` — the preferred-chart coefficient formula.
* `RS.coeffIn_pullback` — the any-maximal-atlas-chart coefficient formula.
* `RS.Form1.pullback_id`, `RS.Form1.pullback_comp` — functoriality at the `Form1` level.

## `Compat` (to be filed upstream, `docs/requests/holomorphic-forms.md`)

* `RS.analyticAt_of_mem_maximalAtlas` — reading a `ContMDiffAt f x` map through *arbitrary*
  maximal-atlas charts on source and target is analytic (mathlib's own
  `contMDiffWithinAt_iff_of_mem_maximalAtlas` specialized to `𝓘(ℂ)`/`ω`, generalizing
  `RS.contMDiffAt_iff_analyticAt_of_mem_source` from a `ℂ`-valued target to an arbitrary charted
  target).
* `RS.mfderiv_chartAt_self` — the (forward) chart map's own `mfderiv` at its base point is the
  identity (the symmetric counterpart of `RS.mfderiv_chartAt_symm_chartAt_self`).
* `RS.tangentCoord_mfderiv_chart_comp` — two-manifold generalization of
  `RS.tangentCoord_mfderiv_comp`, reading the target through its own preferred chart.
-/

open scoped ContDiff Manifold Bundle
open Set IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-! ### `Compat`: two-manifold chart bridges (requested upstream, proved locally) -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- Reading a `ContMDiffAt` map through arbitrary maximal-atlas charts on both source and target
is analytic. Generalizes `RS.contMDiffAt_iff_analyticAt_of_mem_source` (`f : X → ℂ`) to an
arbitrary charted target `Y`. -/
theorem analyticAt_of_mem_maximalAtlas {f : X → Y} {x : X} (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source)
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω Y) (hy : f x ∈ e'.source) :
    AnalyticAt ℂ (⇑e' ∘ f ∘ ⇑e.symm) (e x) := by
  have h := (contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy).mp
    (hf.contMDiffWithinAt : ContMDiffWithinAt 𝓘(ℂ) 𝓘(ℂ) ω f Set.univ x)
  simp only [preimage_univ, univ_inter, modelWithCornersSelf_coe, Set.range_id,
    contDiffWithinAt_univ] at h
  exact h.2.analyticAt

/-- The (forward) preferred chart's own `mfderiv` at its base point is the identity — the
symmetric counterpart of `RS.mfderiv_chartAt_symm_chartAt_self`. -/
theorem mfderiv_chartAt_self (y : Y) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) y = ContinuousLinearMap.id ℂ ℂ := by
  have h := mfderiv_extChartAt_self (I := 𝓘(ℂ)) (x := y)
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] at h
  exact h

omit [IsManifold 𝓘(ℂ) ω X] in
/-- Two-manifold generalization of `RS.tangentCoord_mfderiv_comp`: the composite `mfderiv`,
read in the *target's own preferred chart*, is the planar derivative of the chart-composite. -/
theorem tangentCoord_mfderiv_chart_comp {F : X → Y} {g : ℂ → X} {z : ℂ}
    (hF : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F (g z)) (hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g z) :
    tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) F (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ))) =
      deriv (⇑(chartAt ℂ (F (g z))) ∘ F ∘ g) z := by
  have hchartCM : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (F (g z))) (F (g z)) :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (F (g z)))
      (mem_chart_source ℂ (F (g z)))
  have hchart : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z))) (F (g z)) :=
    hchartCM.mdifferentiableAt (by simp)
  have hcompFg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z)) ∘ F) (g z) := hchart.comp _ hF
  have h1 : tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) F (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ))) =
      tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z))) (F (g z))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) F (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ)))) := by
    rw [mfderiv_chartAt_self]; rfl
  have h2 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z))) (F (g z))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) F (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ))) =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z)) ∘ F) (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ)) := by
    rw [mfderiv_comp (g z) hchart hF]; rfl
  rw [h1, h2]
  exact tangentCoord_mfderiv_comp hcompFg hg

/-! ### `pullbackSection` and its coefficient formula -/

/-- The pulled-back covector at `x`: precompose `η`'s covector at `f x` with the differential of
`f` at `x` (crossing the `TangentSpace ↦ Bundle.Trivial` defeq in the codomain, as in
`Form1CoeffData.toSection`/`mdifferentialSection`). -/
def pullbackSection (f : X → Y) (η : Form1 Y) (x : X) :
    TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x :=
  (η (f x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x :
    TangentSpace 𝓘(ℂ) x →L[ℂ] TangentSpace 𝓘(ℂ) (f x))

/-- Chain-rule combination: `deriv` of a composite through an intermediate (moving) preferred
chart equals the product of the two transition/reading derivatives, whenever the composite is
eventually equal to that two-step reading near the point. -/
private theorem deriv_eq_of_eventuallyEq_comp {g h k : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g (h z)) (hh : DifferentiableAt ℂ h z)
    (heq : k =ᶠ[nhds z] g ∘ h) : deriv k z = deriv g (h z) * deriv h z :=
  ((hg.hasDerivAt.comp z hh.hasDerivAt).congr_of_eventuallyEq heq).deriv

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **Master computation** (mirrors `Form1CoeffData.coeffInFun_toSection`): in any maximal-atlas
source chart `e` and target chart `e'` (with `f` mapping the relevant point into `e'.source`),
the raw coefficient of `pullbackSection f η` is the chain-rule pullback formula. -/
theorem coeffInFun_pullbackSection {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 Y)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω Y)
    {z : ℂ} (hz : z ∈ e.target) (hy : f (e.symm z) ∈ e'.source) :
    coeffInFun e (pullbackSection f η) z =
      deriv (⇑e' ∘ f ∘ ⇑e.symm) z * coeffIn e' η (e' (f (e.symm z))) := by
  set x' := e.symm z with hx'_def
  have hesymm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) z :=
    (contMDiffAt_symm_of_mem_maximalAtlas he hz).mdifferentiableAt (by simp)
  have hfx' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x' := (hf x').mdifferentiableAt (by simp)
  have hstep1 : coeffInFun e (pullbackSection f η) z =
      tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x' (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) z (1 : ℂ))) *
        coeffAt (f x') η := by
    change (pullbackSection f η x') (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) z (1 : ℂ)) = _
    change (η (f x')) (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x' (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) z (1 : ℂ))) = _
    exact Form1.apply_eq_smul_coeffAt η (f x') _
  have hstep2 : tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x' (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) z (1 : ℂ))) =
      deriv (⇑(chartAt ℂ (f x')) ∘ f ∘ ⇑e.symm) z :=
    tangentCoord_mfderiv_chart_comp hfx' hesymm
  have hstep3 : coeffAt (f x') η =
      deriv (⇑e' ∘ ⇑(chartAt ℂ (f x')).symm) (chartAt ℂ (f x') (f x')) *
        coeffIn e' η (e' (f x')) := by
    have hzmem : chartAt ℂ (f x') (f x') ∈
        ⇑(chartAt ℂ (f x')) '' (e'.source ∩ (chartAt ℂ (f x')).source) :=
      ⟨f x', ⟨hy, mem_chart_source ℂ (f x')⟩, rfl⟩
    have h := coeffIn_trans he' (chart_mem_maximalAtlas (f x')) η hzmem
    rwa [(chartAt ℂ (f x')).left_inv (mem_chart_source ℂ (f x'))] at h
  have hg1 : DifferentiableAt ℂ (⇑e' ∘ ⇑(chartAt ℂ (f x')).symm) (chartAt ℂ (f x') (f x')) :=
    (analyticAt_trans he' (chart_mem_maximalAtlas (f x'))
      ((chartAt ℂ (f x')).map_source (mem_chart_source ℂ (f x')))
      (by rw [(chartAt ℂ (f x')).left_inv (mem_chart_source ℂ (f x'))]; exact hy)).differentiableAt
  have hh1 : DifferentiableAt ℂ (⇑(chartAt ℂ (f x')) ∘ f ∘ ⇑e.symm) z := by
    have hA := analyticAt_of_mem_maximalAtlas (hf x') he (e.map_target hz)
      (chart_mem_maximalAtlas (f x')) (mem_chart_source ℂ (f x'))
    rw [e.right_inv hz] at hA
    exact hA.differentiableAt
  have heq : (⇑e' ∘ f ∘ ⇑e.symm) =ᶠ[nhds z]
      (⇑e' ∘ ⇑(chartAt ℂ (f x')).symm) ∘ (⇑(chartAt ℂ (f x')) ∘ f ∘ ⇑e.symm) := by
    have hcont : ContinuousAt (f ∘ ⇑e.symm) z :=
      (hf x').continuousAt.comp (e.continuousAt_symm hz)
    filter_upwards [hcont.preimage_mem_nhds
      ((chartAt ℂ (f x')).open_source.mem_nhds (mem_chart_source ℂ (f x')))] with w hw
    have hw' : f (e.symm w) ∈ (chartAt ℂ (f x')).source := hw
    simp only [Function.comp_apply, (chartAt ℂ (f x')).left_inv hw']
  have hstep4 : deriv (⇑e' ∘ f ∘ ⇑e.symm) z =
      deriv (⇑e' ∘ ⇑(chartAt ℂ (f x')).symm) (chartAt ℂ (f x') (f x')) *
        deriv (⇑(chartAt ℂ (f x')) ∘ f ∘ ⇑e.symm) z :=
    deriv_eq_of_eventuallyEq_comp hg1 hh1 heq
  rw [hstep1, hstep2, hstep3, hstep4]
  ring

/-! ### `Form1.pullback` -/

/-- Pullback of `η` along `f`, as a raw `Form1 X` (before packaging as a linear map). -/
def pullbackForm (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 Y) : Form1 X :=
  Form1.ofSectionAnalytic (pullbackSection f η) (fun x => by
    have hφ : AnalyticAt ℂ (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      analyticAt_of_mem_maximalAtlas (hf x) (chart_mem_maximalAtlas x) (mem_chart_source ℂ x)
        (chart_mem_maximalAtlas (f x)) (mem_chart_source ℂ (f x))
    have hcont : ContinuousAt (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
      have hg : ContinuousAt f (⇑(chartAt ℂ x).symm (chartAt ℂ x x)) := by
        rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact (hf x).continuousAt
      exact hg.comp ((chartAt ℂ x).continuousAt_symm (mem_chart_target ℂ x))
    have hpt0Eq : (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = f x := by
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    have hptEq : (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
        chartAt ℂ (f x) (f x) := by
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    have hcoeff : AnalyticAt ℂ (fun z => coeffIn (chartAt ℂ (f x)) η
        ((⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) z)) (chartAt ℂ x x) := by
      refine AnalyticAt.fun_comp ?_ hφ
      rw [hptEq]
      exact η.analyticAt_coeffAt (f x)
    have hmemF : (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ∈ (chartAt ℂ (f x)).source := by
      rw [hpt0Eq]; exact mem_chart_source ℂ (f x)
    have heq : coeffInFun (chartAt ℂ x) (pullbackSection f η) =ᶠ[nhds (chartAt ℂ x x)]
        fun z => deriv (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) z *
          coeffIn (chartAt ℂ (f x)) η
            ((⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) z) := by
      filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ (f x)).open_source.mem_nhds hmemF),
        (chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with z hz hzt
      exact coeffInFun_pullbackSection hf η (chart_mem_maximalAtlas x)
        (chart_mem_maximalAtlas (f x)) hzt hz
    exact (hφ.deriv.fun_mul hcoeff).congr heq.symm)

theorem coeffIn_pullbackForm {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 Y)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω Y)
    {z : ℂ} (hz : z ∈ e.target) (hy : f (e.symm z) ∈ e'.source) :
    coeffIn e (pullbackForm f hf η) z =
      deriv (⇑e' ∘ f ∘ ⇑e.symm) z * coeffIn e' η (e' (f (e.symm z))) :=
  coeffInFun_pullbackSection hf η he he' hz hy

/-- The preferred-chart coefficient formula (§3.1). -/
theorem coeffAt_pullbackForm (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 Y) (x : X) :
    coeffAt x (pullbackForm f hf η) =
      deriv (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) *
        coeffAt (f x) η := by
  have h := coeffIn_pullbackForm hf η (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas (f x))
    (mem_chart_target ℂ x)
    (by rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact mem_chart_source ℂ (f x))
  rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at h

/-- **`Form1.pullback` (§3.1)**: pullback of a holomorphic `1`-form along any holomorphic
`f : X → Y`, as a `ℂ`-linear map `Form1 Y →ₗ[ℂ] Form1 X`. Automatically `0` for constant `f`
(no case split: a constant map has vanishing `mfderiv`, so `pullbackSection` vanishes
identically). -/
noncomputable def Form1.pullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Form1 Y →ₗ[ℂ] Form1 X where
  toFun := pullbackForm f hf
  map_add' η η' := Form1.ext_coeffAt (fun x => by
    rw [coeffAt_add, coeffAt_pullbackForm, coeffAt_pullbackForm, coeffAt_pullbackForm,
      coeffAt_add]
    ring)
  map_smul' c η := Form1.ext_coeffAt (fun x => by
    simp only [RingHom.id_apply, coeffAt_pullbackForm, coeffAt_smul]
    ring)

@[simp] theorem Form1.pullback_apply (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 Y) :
    Form1.pullback f hf η = pullbackForm f hf η := rfl

/-- The preferred-chart coefficient formula, restated for `Form1.pullback`. -/
theorem coeffAt_pullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 Y) (x : X) :
    coeffAt x (Form1.pullback f hf η) =
      deriv (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) *
        coeffAt (f x) η :=
  coeffAt_pullbackForm f hf η x

/-- The any-maximal-atlas-chart coefficient formula, restated for `Form1.pullback` (§3.3). -/
theorem coeffIn_pullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 Y)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω Y)
    {z : ℂ} (hz : z ∈ e.target) (hy : f (e.symm z) ∈ e'.source) :
    coeffIn e (Form1.pullback f hf η) z =
      deriv (⇑e' ∘ f ∘ ⇑e.symm) z * coeffIn e' η (e' (f (e.symm z))) :=
  coeffIn_pullbackForm hf η he he' hz hy

/-! ### Functoriality (§3.4) -/

theorem Form1.pullback_id : Form1.pullback (id : X → X) contMDiff_id = LinearMap.id := by
  apply LinearMap.ext
  intro η
  apply Form1.ext_coeffAt
  intro x
  rw [coeffAt_pullback]
  have heq1 : (⇑(chartAt ℂ ((id : X → X) x)) ∘ (id : X → X) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[nhds
      (chartAt ℂ x x)] id := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with z hz
    simp only [Function.comp_apply, id_eq, (chartAt ℂ x).right_inv hz]
  rw [heq1.deriv_eq, deriv_id]
  simp

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

theorem Form1.pullback_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (g : Y → Z)
    (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    Form1.pullback (g ∘ f) (hg.comp hf) = (Form1.pullback f hf).comp (Form1.pullback g hg) := by
  apply LinearMap.ext
  intro η
  apply Form1.ext_coeffAt
  intro x
  rw [coeffAt_pullback, LinearMap.comp_apply, coeffAt_pullback, coeffAt_pullback]
  simp only [Function.comp_apply]
  have hptEq : (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
      chartAt ℂ (f x) (f x) := by
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hg1 : DifferentiableAt ℂ (⇑(chartAt ℂ (g (f x))) ∘ g ∘ ⇑(chartAt ℂ (f x)).symm)
      ((⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) := by
    rw [hptEq]
    exact (analyticAt_of_mem_maximalAtlas (hg (f x)) (chart_mem_maximalAtlas (f x))
      (mem_chart_source ℂ (f x)) (chart_mem_maximalAtlas (g (f x)))
      (mem_chart_source ℂ (g (f x)))).differentiableAt
  have hh1 : DifferentiableAt ℂ (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (analyticAt_of_mem_maximalAtlas (hf x) (chart_mem_maximalAtlas x) (mem_chart_source ℂ x)
      (chart_mem_maximalAtlas (f x)) (mem_chart_source ℂ (f x))).differentiableAt
  have heq : (⇑(chartAt ℂ (g (f x))) ∘ (g ∘ f) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[nhds (chartAt ℂ x x)]
      (⇑(chartAt ℂ (g (f x))) ∘ g ∘ ⇑(chartAt ℂ (f x)).symm) ∘
        (⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm) := by
    have hcont : ContinuousAt (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
      have hg0 : ContinuousAt f (⇑(chartAt ℂ x).symm (chartAt ℂ x x)) := by
        rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact (hf x).continuousAt
      exact hg0.comp ((chartAt ℂ x).continuousAt_symm (mem_chart_target ℂ x))
    have hmemF : (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ∈ (chartAt ℂ (f x)).source := by
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact mem_chart_source ℂ (f x)
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ (f x)).open_source.mem_nhds hmemF)]
      with w hw
    have hw' : f (⇑(chartAt ℂ x).symm w) ∈ (chartAt ℂ (f x)).source := hw
    simp only [Function.comp_apply, (chartAt ℂ (f x)).left_inv hw']
  rw [deriv_eq_of_eventuallyEq_comp hg1 hh1 heq, hptEq]
  ring

end RS

end
