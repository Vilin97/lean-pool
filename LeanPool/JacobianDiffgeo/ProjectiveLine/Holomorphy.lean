/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ProjectiveLine.Charts
import LeanPool.JacobianDiffgeo.Surface.Bridges
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Holomorphy transfer kit for `ℙ¹` (CC5)

Unit: projective-line (`docs/design/projective-line.md` §3.3). For a Riemann surface
`Z` (`ChartedSpace ℂ Z` + `IsManifold 𝓘(ℂ) ω Z`, no compactness/connectedness needed
anywhere) this file converts holomorphy of maps `Z → OnePoint ℂ` into planar
`AnalyticAt`/`MeromorphicAt` statements read in `coeChart`/`invChart`:

* `contMDiff_coe`: the coercion `ℂ → ℙ¹` is holomorphic;
* `ContMDiffAt.onePointCoe`/`ContMDiff.onePointCoe`: the "no poles" lift constructor;
* `contMDiffAt_iff_analyticAt_of_ne_infty`/`_of_eq_infty`: chart-iff lemmas at a finite value
  resp. at `∞`;
* `contMDiffAt_of_pole`: the **pole constructor** (planar; pre-`ℳ X` layer) — a function
  agreeing near `z₀` with a meromorphic `g` having a genuine pole, sent to `∞` at `z₀`, is
  holomorphic into `ℙ¹`;
* `meromorphicAt_coeChart_comp`: the converse atom — a holomorphic map into `ℙ¹` is
  chart-locally meromorphic;
* `contMDiff_inversion`/`inversionDiffeomorph`: inversion is a biholomorphic involution.
-/

open scoped ContDiff Manifold OnePoint
open Set Filter Topology OnePoint

namespace RS.P1

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

/-- The coercion `ℂ → ℙ¹` is holomorphic. -/
theorem contMDiff_coe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → OnePoint ℂ) := by
  intro z
  rw [RS.contMDiffAt_iff_analyticAt_writtenInExtChartAt]
  refine ⟨continuous_coe.continuousAt, ?_⟩
  have hchart : chartAt ℂ ((z : ℂ) : OnePoint ℂ) = coeChart := chartAt_coe z
  have hfun : writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) z ((↑) : ℂ → OnePoint ℂ) = id := by
    funext w
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.comp_id, Function.id_comp, id_eq, chartAt_self_eq, hchart]
    exact coeChart_apply_coe _
  rw [hfun]
  exact analyticAt_id

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/-- Holomorphic lift of a holomorphic function (the "no poles" constructor). -/
theorem ContMDiffAt.onePointCoe {g : Z → ℂ} {x : Z} (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g x) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun z => ((g z : ℂ) : OnePoint ℂ)) x :=
  (contMDiff_coe (g x)).comp x hg

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
theorem ContMDiff.onePointCoe {g : Z → ℂ} (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => ((g z : ℂ) : OnePoint ℂ)) :=
  fun x => ContMDiffAt.onePointCoe (hg x)

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/-- Holomorphy at a finite value, read in the `coeChart`. -/
theorem contMDiffAt_iff_analyticAt_of_ne_infty {f : Z → OnePoint ℂ} {x : Z}
    (h : f x ≠ (∞ : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ ContinuousAt f x ∧
      AnalyticAt ℂ (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
  obtain ⟨w, hw⟩ := ne_infty_iff_exists.mp h
  have hchart : chartAt ℂ (f x) = coeChart := by rw [← hw]; exact chartAt_coe w
  have hpt : extChartAt 𝓘(ℂ) x x = chartAt ℂ x x := by rw [extChartAt_coe]; simp
  rw [RS.contMDiffAt_iff_analyticAt_writtenInExtChartAt]
  have hfun : writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f = ⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm := by
    funext y
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.comp_id, Function.id_comp, hchart]
  rw [hfun, hpt]

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/-- Holomorphy at `∞`, read in the `invChart` ("`1/f` is analytic"). -/
theorem contMDiffAt_iff_analyticAt_of_eq_infty {f : Z → OnePoint ℂ} {x : Z}
    (h : f x = (∞ : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ ContinuousAt f x ∧
      AnalyticAt ℂ (⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
  have hchart : chartAt ℂ (f x) = invChart := by rw [h]; exact chartAt_infty
  have hpt : extChartAt 𝓘(ℂ) x x = chartAt ℂ x x := by rw [extChartAt_coe]; simp
  rw [RS.contMDiffAt_iff_analyticAt_writtenInExtChartAt]
  have hfun : writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f = ⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm := by
    funext y
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.comp_id, Function.id_comp, hchart]
  rw [hfun, hpt]

/-- `(↑)` sends `cobounded ℂ` to `𝓝 ∞`. -/
theorem tendsto_coe_cobounded :
    Tendsto ((↑) : ℂ → OnePoint ℂ) (Bornology.cobounded ℂ) (𝓝 (∞ : OnePoint ℂ)) := by
  rw [Metric.cobounded_eq_cocompact]
  exact tendsto_coe_cocompact

/-- **Pole constructor** (planar; the pre-`ℳ X` layer). A function agreeing near `z₀` with a
meromorphic `g` having a genuine pole, and sent to `∞` at `z₀`, is holomorphic into `ℙ¹`. -/
theorem contMDiffAt_of_pole {g : ℂ → ℂ} {z₀ : ℂ} (_hg : MeromorphicAt g z₀)
    (hord : meromorphicOrderAt g z₀ < 0) {F : ℂ → OnePoint ℂ} (hFinf : F z₀ = (∞ : OnePoint ℂ))
    (hF : ∀ᶠ z in 𝓝[≠] z₀, F z = ((g z : ℂ) : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F z₀ := by
  rw [contMDiffAt_iff_analyticAt_of_eq_infty hFinf]
  have hcobdd : Tendsto g (𝓝[≠] z₀) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg hord
  have hpunc : Tendsto F (𝓝[≠] z₀) (𝓝 (∞ : OnePoint ℂ)) :=
    (tendsto_congr' hF).2 (tendsto_coe_cobounded.comp hcobdd)
  have hpure : Tendsto F (pure z₀) (𝓝 (∞ : OnePoint ℂ)) := hFinf ▸ tendsto_pure_nhds F z₀
  have hcombine : Tendsto F (𝓝 z₀) (𝓝 (∞ : OnePoint ℂ)) := by
    rw [← nhdsNE_sup_pure z₀, tendsto_sup]
    exact ⟨hpunc, hpure⟩
  have hcontF : ContinuousAt F z₀ := by rw [ContinuousAt, hFinf]; exact hcombine
  refine ⟨hcontF, ?_⟩
  have hcompeq : (⇑invChart ∘ F ∘ ⇑(chartAt ℂ z₀).symm) =ᶠ[𝓝[≠] z₀] g⁻¹ := by
    filter_upwards [hF] with z hz
    change invChart (F ((chartAt ℂ z₀).symm z)) = (g⁻¹) z
    rw [chartAt_self_eq]
    simp [hz]
  have hordinv : meromorphicOrderAt (⇑invChart ∘ F ∘ ⇑(chartAt ℂ z₀).symm) z₀ =
      meromorphicOrderAt (g⁻¹) z₀ := meromorphicOrderAt_congr hcompeq
  have hpos : 0 < meromorphicOrderAt (⇑invChart ∘ F ∘ ⇑(chartAt ℂ z₀).symm) z₀ := by
    rw [hordinv, meromorphicOrderAt_inv]
    exact LinearOrderedAddCommGroupWithTop.neg_pos.2 (Or.inl hord)
  have hval : (⇑invChart ∘ F ∘ ⇑(chartAt ℂ z₀).symm) z₀ = 0 := by
    change invChart (F ((chartAt ℂ z₀).symm z₀)) = 0
    rw [chartAt_self_eq]
    simp [hFinf]
  exact AnalyticAt.of_meromorphicOrderAt_pos hpos hval

omit [IsManifold 𝓘(ℂ, ℂ) ω Z] in
/-- Converse atom: a holomorphic map to `ℙ¹` is chart-locally meromorphic (CC3's currency). -/
theorem meromorphicAt_coeChart_comp {f : Z → OnePoint ℂ} {x : Z}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    MeromorphicAt (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
  have hGψ : (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm : ℂ → ℂ) =
      (⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm)⁻¹ := by
    funext y
    change coeChart (f ((chartAt ℂ x).symm y)) = (invChart (f ((chartAt ℂ x).symm y)))⁻¹
    induction (f ((chartAt ℂ x).symm y)) using OnePoint.rec with
    | infty => simp
    | coe w => simp
  by_cases hfx : f x = (∞ : OnePoint ℂ)
  · have hψan : AnalyticAt ℂ (⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      ((contMDiffAt_iff_analyticAt_of_eq_infty hfx).1 hf).2
    rw [hGψ]
    exact hψan.meromorphicAt.inv
  · have hGan : AnalyticAt ℂ (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      ((contMDiffAt_iff_analyticAt_of_ne_infty hfx).1 hf).2
    exact hGan.meromorphicAt

/-- The inversion is holomorphic, hence a biholomorphic involution of `ℙ¹`. -/
theorem contMDiff_inversion : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω inversion := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
    have hval : inversion (∞ : OnePoint ℂ) ≠ (∞ : OnePoint ℂ) := by simp
    rw [contMDiffAt_iff_analyticAt_of_ne_infty hval, chartAt_infty]
    refine ⟨continuous_inversion.continuousAt, ?_⟩
    have hfun : (⇑coeChart ∘ inversion ∘ ⇑invChart.symm : ℂ → ℂ) = id := by
      funext w
      change coeChart (inversion (invChart.symm w)) = w
      rw [invChart_symm_apply, inversion_involutive]
      exact coeChart_apply_coe w
    rw [hfun]
    exact analyticAt_id
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      have hval : inversion ((0 : ℂ) : OnePoint ℂ) = (∞ : OnePoint ℂ) := by simp
      rw [contMDiffAt_iff_analyticAt_of_eq_infty hval, chartAt_coe]
      refine ⟨continuous_inversion.continuousAt, ?_⟩
      have hfun : (⇑invChart ∘ inversion ∘ ⇑coeChart.symm : ℂ → ℂ) = id := by
        funext w
        change invChart (inversion (coeChart.symm w)) = w
        rw [coeChart_symm_apply]
        exact invChart_inversion_coe w
      rw [hfun]
      exact analyticAt_id
    · have hval : inversion ((z : ℂ) : OnePoint ℂ) ≠ (∞ : OnePoint ℂ) := by simp [inversion_coe hz]
      rw [contMDiffAt_iff_analyticAt_of_ne_infty hval, chartAt_coe]
      refine ⟨continuous_inversion.continuousAt, ?_⟩
      have hfun : (⇑coeChart ∘ inversion ∘ ⇑coeChart.symm : ℂ → ℂ) = Inv.inv := by
        funext w
        change coeChart (inversion (coeChart.symm w)) = w⁻¹
        rw [coeChart_symm_apply]
        exact coeChart_inversion_coe w
      rw [hfun]
      exact analyticAt_inv hz

/-- Inversion as a self-inverse holomorphic involution of `ℙ¹`. -/
noncomputable def inversionDiffeomorph : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (OnePoint ℂ) (OnePoint ℂ) ω where
  toFun := inversion
  invFun := inversion
  left_inv := inversion_involutive
  right_inv := inversion_involutive
  contMDiff_toFun := contMDiff_inversion
  contMDiff_invFun := contMDiff_inversion

@[simp] theorem inversionDiffeomorph_apply : ⇑inversionDiffeomorph = inversion := rfl

end RS.P1
