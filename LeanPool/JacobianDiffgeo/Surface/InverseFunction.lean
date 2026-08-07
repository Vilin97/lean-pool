/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Surface.Bridges
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Holomorphic inverse function theorem on surfaces

Unit: surfaces-and-charts (`docs/design/surfaces-and-charts.md` §3.5; Forster 2.1/2.5 local part).

* `exists_openPartialHomeomorph_of_deriv_ne_zero`: if `f : X → Y` is holomorphic at `x` with
  nonvanishing chart-derivative, there is an `OpenPartialHomeomorph X Y` around `x` agreeing
  with `f` that is holomorphic with holomorphic inverse;
* `mfderiv_ne_zero_iff_deriv_ne_zero`: the chart-free (invariant) form of the hypothesis;
* `exists_openPartialHomeomorph_of_mfderiv_ne_zero`: the IFT keyed on `mfderiv`
  (invariant interface for mapping-degree);
* `map_nhds_eq_of_deriv_ne_zero`: local-homeomorphism consequence, `f` maps neighborhoods
  onto neighborhoods.

The planar input is mathlib's analytic inverse function theorem
(`AnalyticAt.analyticAt_localInverse`, `HasStrictFDerivAt.toOpenPartialHomeomorph`).
-/

open scoped ContDiff Manifold
open Set Filter Topology IsManifold

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Holomorphic inverse function theorem on surfaces.** If `f` is holomorphic at `x` with
nonvanishing chart-derivative, there is a partial homeomorphism around `x` agreeing with `f`
that is holomorphic with holomorphic inverse. -/
theorem exists_openPartialHomeomorph_of_deriv_ne_zero {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x)
    (hf' : deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) ≠ 0) :
    ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ EqOn f e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e e.source ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e.symm e.target := by
  classical
  set g : ℂ → ℂ := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f with hgdef
  -- the chart composite is analytic with nonvanishing derivative at the chart point
  have hg : AnalyticAt ℂ g ((chartAt ℂ x) x) :=
    (contMDiffAt_iff_analyticAt_writtenInExtChartAt.1 hf).2
  have hg' : deriv g ((chartAt ℂ x) x) ≠ 0 := hf'
  -- planar analytic IFT: a planar `OpenPartialHomeomorph` realizing `g`, with analytic inverse
  obtain ⟨R, hR_coe, hxR, hRsymm_an⟩ :
      ∃ R : OpenPartialHomeomorph ℂ ℂ, (R : ℂ → ℂ) = g ∧ (chartAt ℂ x) x ∈ R.source ∧
        AnalyticAt ℂ (R.symm : ℂ → ℂ) (g ((chartAt ℂ x) x)) :=
    ⟨(hg.hasStrictDerivAt.hasStrictFDerivAt_equiv hg').toOpenPartialHomeomorph g, rfl,
      (hg.hasStrictDerivAt.hasStrictFDerivAt_equiv hg').mem_toOpenPartialHomeomorph_source,
      hg.analyticAt_localInverse hg'⟩
  -- an open `V ∋ g (κ x)` inside `R.target` on which `R.symm` is analytic
  obtain ⟨V, hVo, hVx, hVt, hVa⟩ :
      ∃ V : Set ℂ, IsOpen V ∧ g ((chartAt ℂ x) x) ∈ V ∧ V ⊆ R.target ∧
        ∀ w ∈ V, AnalyticAt ℂ (R.symm : ℂ → ℂ) w := by
    have h1 : ∀ᶠ w in 𝓝 (g ((chartAt ℂ x) x)), AnalyticAt ℂ (R.symm : ℂ → ℂ) w :=
      hRsymm_an.eventually_analyticAt
    have h2 : ∀ᶠ w in 𝓝 (g ((chartAt ℂ x) x)), w ∈ R.target := by
      have h3 : (R : ℂ → ℂ) ((chartAt ℂ x) x) ∈ R.target := R.map_source hxR
      rw [hR_coe] at h3
      exact R.open_target.mem_nhds h3
    obtain ⟨s, hs_mem, hs⟩ := (h1.and h2).exists_mem
    obtain ⟨W, hWs, hWo, hWx⟩ := mem_nhds_iff.1 hs_mem
    exact ⟨W, hWo, hWx, fun w hw => (hs w (hWs hw)).2, fun w hw => (hs w (hWs hw)).1⟩
  -- an open neighborhood of `x` on which `f` is holomorphic (hence continuous)
  obtain ⟨u, hu_mem, hu⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hf
  have hu' : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f (interior u) := hu.mono interior_subset
  have hfc : ContinuousOn f (interior u) := hu'.continuousOn
  -- key pointwise identity: `g` in the chart is `chartAt (f x) ∘ f` on the chart source
  have hgz : ∀ z ∈ (chartAt ℂ x).source,
      g ((chartAt ℂ x) z) = (chartAt ℂ (f x)) (f z) := by
    intro z hz
    simp only [hgdef, writtenInExtChartAt, Function.comp_apply, extChartAt_coe,
      extChartAt_coe_symm, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_eq]
    rw [(chartAt ℂ x).left_inv hz]
  -- the good open set U around x
  have hW₂o : IsOpen ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' R.source) :=
    (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source R.open_source
  have hW₃o : IsOpen (((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' R.source) ∩
      (fun z => (R : ℂ → ℂ) ((chartAt ℂ x) z)) ⁻¹' V) := by
    have hcont : ContinuousOn ((R : ℂ → ℂ) ∘ (chartAt ℂ x))
        ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' R.source) :=
      R.continuousOn.comp ((chartAt ℂ x).continuousOn.mono inter_subset_left)
        fun _ hz => hz.2
    exact hcont.isOpen_inter_preimage hW₂o hVo
  set U : Set X := (interior u ∩ f ⁻¹' (chartAt ℂ (f x)).source) ∩
      (((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' R.source) ∩
        (fun z => (R : ℂ → ℂ) ((chartAt ℂ x) z)) ⁻¹' V) with hUdef
  have hUo : IsOpen U :=
    (hfc.isOpen_inter_preimage isOpen_interior (chartAt ℂ (f x)).open_source).inter hW₃o
  have hxU : x ∈ U := by
    refine ⟨⟨mem_interior_iff_mem_nhds.2 hu_mem, mem_chart_source ℂ (f x)⟩,
      ⟨mem_chart_source ℂ x, hxR⟩, ?_⟩
    change (R : ℂ → ℂ) ((chartAt ℂ x) x) ∈ V
    rw [hR_coe]
    exact hVx
  -- assemble the candidate partial homeomorphism
  set e₀ : OpenPartialHomeomorph X Y :=
    ((chartAt ℂ x).trans R).trans (chartAt ℂ (f x)).symm with he₀def
  have hUsub : U ⊆ e₀.source := by
    rintro z ⟨⟨-, hzf⟩, ⟨hzs, hzR⟩, hzV⟩
    rw [he₀def]
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage, OpenPartialHomeomorph.trans_apply]
    refine ⟨⟨hzs, hzR⟩, ?_⟩
    rw [hR_coe, hgz z hzs]
    exact (chartAt ℂ (f x)).map_source hzf
  set e : OpenPartialHomeomorph X Y := e₀.restrOpen U hUo with hedef
  have hes : e.source = e₀.source ∩ U := e₀.restrOpen_source U hUo
  have hxe : x ∈ e.source := by rw [hes]; exact ⟨hUsub hxU, hxU⟩
  -- agreement with f on the source
  have heq : EqOn f e e.source := by
    intro z hz
    rw [hes] at hz
    obtain ⟨⟨-, hzf⟩, ⟨hzs, hzR⟩, hzV⟩ := hz.2
    show f z = e z
    rw [hedef]
    rw [show (⇑(e₀.restrOpen U hUo) : X → Y) = ⇑e₀ from e₀.coe_restrOpen hUo, he₀def]
    simp only [OpenPartialHomeomorph.trans_apply]
    rw [hR_coe, hgz z hzs]
    exact ((chartAt ℂ (f x)).left_inv hzf).symm
  -- holomorphy of e on the source (it equals f there)
  have hesub : e.source ⊆ interior u := by
    rw [hes]; exact fun z hz => hz.2.1.1
  have hmd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e e.source :=
    (hu'.mono hesub).congr fun z hz => (heq hz).symm
  -- holomorphy of the inverse on the target
  have hcoe_symm : (e.symm : Y → X) =
      ⇑(chartAt ℂ x).symm ∘ (R.symm : ℂ → ℂ) ∘ ⇑(chartAt ℂ (f x)) := by
    rw [hedef]
    rw [show (⇑(e₀.restrOpen U hUo).symm : Y → X) = ⇑e₀.symm from e₀.coe_restrOpen_symm hUo,
      he₀def]
    simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
      Function.comp_assoc]
  have hsymm : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e.symm e.target := by
    intro y hy
    refine ContMDiffAt.contMDiffWithinAt ?_
    -- unpack the source point z := e.symm y ∈ U and its properties
    have hz₁ : e.symm y ∈ e.source := e.map_target hy
    have hze : e (e.symm y) = y := e.right_inv hy
    have hzU : e.symm y ∈ U := by rw [hes] at hz₁; exact hz₁.2
    obtain ⟨⟨-, hzf⟩, ⟨hzs, hzR⟩, hzV⟩ := hzU
    have hyz : y = f (e.symm y) := ((heq hz₁).trans hze).symm
    -- membership facts for the three factors
    have hyl : y ∈ (chartAt ℂ (f x)).source := hyz ▸ hzf
    have hlamy : (chartAt ℂ (f x)) y ∈ V := by
      rw [hyz, ← hgz _ hzs, ← hR_coe]
      exact hzV
    have hRsl : (R.symm : ℂ → ℂ) ((chartAt ℂ (f x)) y) ∈ (chartAt ℂ x).target := by
      rw [hyz, ← hgz _ hzs, ← hR_coe, R.left_inv hzR]
      exact (chartAt ℂ x).map_source hzs
    -- assemble: chart ∘ analytic local inverse ∘ chart⁻¹
    rw [hcoe_symm]
    have h₁ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (f x)) y :=
      contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (f x)) hyl
    have h₂ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (R.symm : ℂ → ℂ) ((chartAt ℂ (f x)) y) :=
      ((hVa _ hlamy).contDiffAt).contMDiffAt
    have h₃ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm)
        ((R.symm : ℂ → ℂ) ((chartAt ℂ (f x)) y)) :=
      contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hRsl
    exact h₃.comp y (h₂.comp y h₁)
  exact ⟨e, hxe, heq, hmd, hsymm⟩

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- The chart-free (invariant) form of the nonvanishing-derivative hypothesis. -/
theorem mfderiv_ne_zero_iff_deriv_ne_zero {f : X → Y} {x : X}
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) f x ≠ 0 ↔
      deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) ≠ 0 := by
  rw [hf.mfderiv, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  refine not_congr ?_
  constructor
  · intro h
    rw [← fderiv_apply_one_eq_deriv, h]
    rfl
  · intro h
    apply ContinuousLinearMap.ext_ring
    rw [fderiv_apply_one_eq_deriv, h]
    rfl

/-- IFT keyed on `mfderiv` (invariant interface for mapping-degree). -/
theorem exists_openPartialHomeomorph_of_mfderiv_ne_zero {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) (hf' : mfderiv 𝓘(ℂ) 𝓘(ℂ) f x ≠ 0) :
    ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ EqOn f e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e e.source ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e.symm e.target :=
  exists_openPartialHomeomorph_of_deriv_ne_zero hf
    ((mfderiv_ne_zero_iff_deriv_ne_zero (hf.mdifferentiableAt (by simp))).1 hf')

/-- Local-homeomorphism consequence: `f` maps neighborhoods onto neighborhoods. -/
theorem map_nhds_eq_of_deriv_ne_zero {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x)
    (hf' : deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) ≠ 0) :
    Filter.map f (𝓝 x) = 𝓝 (f x) := by
  obtain ⟨e, hxe, heq, -, -⟩ := exists_openPartialHomeomorph_of_deriv_ne_zero hf hf'
  have h1 : Filter.map f (𝓝 x) = Filter.map e (𝓝 x) :=
    Filter.map_congr (heq.eventuallyEq_of_mem (e.open_source.mem_nhds hxe))
  rw [h1, e.map_nhds_eq hxe, heq hxe]

end RS
