/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms.Analyticity

/-!
# Constructing holomorphic 1-forms from coefficient data (CC1, design §2.3)

Unit: holomorphic-forms (`docs/design/holomorphic-forms.md`). `RS.Form1CoeffData X ι` packages a
covering family of `ω`-maximal-atlas charts together with analytic coefficient functions on the
chart targets satisfying the CC1 transition rule; `RS.Form1.ofCoeffs` assembles them into a
holomorphic 1-form whose `coeffIn` in the `i`-th chart is the given `i`-th coefficient
(`RS.Form1.coeffIn_ofCoeffs`).

The chart family is arbitrary (indexed by any `ι`), not just preferred charts: the finiteness
argument (`Jacobian/Forms/Finiteness.lean`) instantiates it with charts *restricted* to shrunk
cover sets, which stay in the maximal atlas.

Main declarations:
* `RS.Form1CoeffData` — the compatible-coefficient structure.
* `RS.Form1CoeffData.coeffInFun_toSection` — master computation: the raw coefficient of the
  assembled section in ANY maximal-atlas chart.
* `RS.Form1.ofCoeffs`, `RS.Form1.coeffIn_ofCoeffs`, `RS.Form1.coeffAt_ofCoeffs`.
-/

open scoped ContDiff Manifold Bundle
open Set IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Compatible analytic coefficient data for a holomorphic 1-form, over a covering family of
`ω`-maximal-atlas charts: on each chart target an analytic coefficient function, related on
overlaps by the CC1 transition rule. -/
structure Form1CoeffData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (ι : Type*) where
  /-- The covering chart family. -/
  chart : ι → OpenPartialHomeomorph X ℂ
  mem_maximalAtlas : ∀ i, chart i ∈ maximalAtlas 𝓘(ℂ) ω X
  exists_mem : ∀ x : X, ∃ i, x ∈ (chart i).source
  /-- The coefficient functions, one per chart. -/
  coeff : ι → ℂ → ℂ
  analyticOnNhd : ∀ i, AnalyticOnNhd ℂ (coeff i) (chart i).target
  compat : ∀ i j, ∀ x ∈ (chart i).source ∩ (chart j).source,
    coeff j (chart j x) = deriv (⇑(chart i) ∘ ⇑(chart j).symm) (chart j x) * coeff i (chart i x)

namespace Form1CoeffData

variable {ι : Type*} (D : Form1CoeffData X ι)

/-- A chosen chart index for each point. -/
def idx (x : X) : ι := (D.exists_mem x).choose

theorem mem_source_idx (x : X) : x ∈ (D.chart (D.idx x)).source := (D.exists_mem x).choose_spec

/-- The underlying covector section: at `x`, the covector `coeff · d(chart)ₓ` read through the
chosen chart (crossing the `TangentSpace ↦ Bundle.Trivial` defeq in the codomain). -/
def toSection (x : X) : TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x :=
  D.coeff (D.idx x) (D.chart (D.idx x) x) •
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (D.chart (D.idx x)) x :
      TangentSpace 𝓘(ℂ) x →L[ℂ] TangentSpace 𝓘(ℂ) (D.chart (D.idx x) x))

theorem evalC_toSection (x : X) (w : ℂ) :
    evalC D.toSection x w =
      D.coeff (D.idx x) (D.chart (D.idx x) x) *
        tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (D.chart (D.idx x)) x w) := rfl

/-- **Master computation**: in any maximal-atlas chart `e'`, at a target point `z` whose base
point lies in the `i`-th chart, the raw coefficient of `D.toSection` is the `i`-th coefficient
transported by the transition derivative. -/
theorem coeffInFun_toSection {e' : OpenPartialHomeomorph X ℂ}
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) (i : ι) {z : ℂ} (hz : z ∈ e'.target)
    (hp : e'.symm z ∈ (D.chart i).source) :
    coeffInFun e' D.toSection z =
      deriv (⇑(D.chart i) ∘ ⇑e'.symm) z * D.coeff i (D.chart i (e'.symm z)) := by
  have hpj : e'.symm z ∈ (D.chart (D.idx (e'.symm z))).source := D.mem_source_idx _
  have hesymm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑e'.symm) z :=
    (contMDiffAt_symm_of_mem_maximalAtlas he' hz).mdifferentiableAt (by simp)
  have hcj : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑(D.chart (D.idx (e'.symm z)))) (e'.symm z) :=
    (contMDiffAt_of_mem_maximalAtlas (D.mem_maximalAtlas _) hpj).mdifferentiableAt (by simp)
  have h1 : coeffInFun e' D.toSection z =
      D.coeff (D.idx (e'.symm z)) (D.chart (D.idx (e'.symm z)) (e'.symm z)) *
        tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (D.chart (D.idx (e'.symm z))) (e'.symm z)
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e'.symm) z (1 : ℂ))) := by
    -- both steps are `rfl`; `rw` cannot match `evalC`'s `w : ℂ` against a term whose type is
    -- the (defeq) `TangentSpace 𝓘(ℂ) _`
    rfl
  have h2 : tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (D.chart (D.idx (e'.symm z))) (e'.symm z)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e'.symm) z (1 : ℂ))) =
      deriv (⇑(D.chart (D.idx (e'.symm z))) ∘ ⇑e'.symm) z :=
    tangentCoord_mfderiv_comp hcj hesymm
  rw [h1, h2,
    deriv_trans_comp (D.mem_maximalAtlas i) (D.mem_maximalAtlas (D.idx (e'.symm z))) he'
      hz hp hpj,
    D.compat i (D.idx (e'.symm z)) (e'.symm z) ⟨hp, hpj⟩]
  ring

/-- The preferred-chart coefficient functions of `D.toSection` are analytic (feeds the
`Form1.ofSectionAnalytic` constructor). -/
theorem analyticAt_coeffInFun_toSection (x : X) :
    AnalyticAt ℂ (coeffInFun (chartAt ℂ x) D.toSection) (chartAt ℂ x x) := by
  obtain ⟨i, hi⟩ := D.exists_mem x
  have hchart : chartAt ℂ x ∈ maximalAtlas 𝓘(ℂ) ω X := chart_mem_maximalAtlas x
  -- the open overlap image around the chart point
  have hWopen : IsOpen (⇑(chartAt ℂ x) '' ((D.chart i).source ∩ (chartAt ℂ x).source)) :=
    (chartAt ℂ x).isOpen_image_of_subset_source
      ((D.chart i).open_source.inter (chartAt ℂ x).open_source) inter_subset_right
  have hzW : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' ((D.chart i).source ∩ (chartAt ℂ x).source) :=
    ⟨x, ⟨hi, mem_chart_source ℂ x⟩, rfl⟩
  -- on that open set the master formula applies
  have heq : coeffInFun (chartAt ℂ x) D.toSection =ᶠ[nhds (chartAt ℂ x x)]
      fun w => deriv (⇑(D.chart i) ∘ ⇑(chartAt ℂ x).symm) w *
        D.coeff i ((⇑(D.chart i) ∘ ⇑(chartAt ℂ x).symm) w) := by
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    obtain ⟨q, hq, rfl⟩ := hw
    have hwt : chartAt ℂ x q ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hq.2
    have hwp : (chartAt ℂ x).symm (chartAt ℂ x q) ∈ (D.chart i).source := by
      rw [(chartAt ℂ x).left_inv hq.2]; exact hq.1
    exact D.coeffInFun_toSection hchart i hwt hwp
  -- the transported function is analytic at the chart point
  have hxs : (chartAt ℂ x).symm (chartAt ℂ x x) ∈ (D.chart i).source := by
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hi
  have hτ : AnalyticAt ℂ (⇑(D.chart i) ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    analyticAt_trans (D.mem_maximalAtlas i) hchart (mem_chart_target ℂ x) hxs
  have hcoeff : AnalyticAt ℂ
      (fun w => D.coeff i ((⇑(D.chart i) ∘ ⇑(chartAt ℂ x).symm) w)) (chartAt ℂ x x) := by
    refine AnalyticAt.fun_comp ?_ hτ
    exact D.analyticOnNhd i _ ((D.chart i).map_source hxs)
  exact (AnalyticAt.fun_mul hτ.deriv hcoeff).congr heq.symm

end Form1CoeffData

/-- A holomorphic 1-form assembled from compatible analytic coefficient data over a covering
maximal-atlas chart family (CC1 constructor). -/
def Form1.ofCoeffs {ι : Type*} (D : Form1CoeffData X ι) : Form1 X :=
  Form1.ofSectionAnalytic D.toSection D.analyticAt_coeffInFun_toSection

/-- The coefficients of `Form1.ofCoeffs D` in the `i`-th chart of the data are the given
coefficients, on the whole chart target. -/
theorem Form1.coeffIn_ofCoeffs {ι : Type*} (D : Form1CoeffData X ι) (i : ι) :
    Set.EqOn (coeffIn (D.chart i) (Form1.ofCoeffs D)) (D.coeff i) (D.chart i).target := by
  intro z hz
  have hp : (D.chart i).symm z ∈ (D.chart i).source := (D.chart i).map_target hz
  have h : coeffIn (D.chart i) (Form1.ofCoeffs D) z =
      deriv (⇑(D.chart i) ∘ ⇑(D.chart i).symm) z * D.coeff i (D.chart i ((D.chart i).symm z)) :=
    D.coeffInFun_toSection (D.mem_maximalAtlas i) i hz hp
  have hround : deriv (⇑(D.chart i) ∘ ⇑(D.chart i).symm) z = 1 := by
    have heq : ⇑(D.chart i) ∘ ⇑(D.chart i).symm =ᶠ[nhds z] id := by
      filter_upwards [(D.chart i).open_target.mem_nhds hz] with w hw
      exact (D.chart i).right_inv hw
    rw [heq.deriv_eq, deriv_id]
  rw [h, hround, (D.chart i).right_inv hz, one_mul]

/-- The preferred-chart coefficient of `Form1.ofCoeffs D` at a point of the `i`-th chart source,
via the transition derivative (the form consumed by the finiteness argument). -/
theorem Form1.coeffAt_ofCoeffs {ι : Type*} (D : Form1CoeffData X ι) {x : X} {i : ι}
    (hx : x ∈ (D.chart i).source) :
    coeffAt x (Form1.ofCoeffs D) =
      deriv (⇑(D.chart i) ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) * D.coeff i (D.chart i x) := by
  have hz : chartAt ℂ x x ∈ (chartAt ℂ x).target := mem_chart_target ℂ x
  have hp : (chartAt ℂ x).symm (chartAt ℂ x x) ∈ (D.chart i).source := by
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hx
  have h : coeffAt x (Form1.ofCoeffs D) =
      deriv (⇑(D.chart i) ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) *
        D.coeff i (D.chart i ((chartAt ℂ x).symm (chartAt ℂ x x))) :=
    D.coeffInFun_toSection (chart_mem_maximalAtlas x) i hz hp
  rw [h, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]

end RS

end
