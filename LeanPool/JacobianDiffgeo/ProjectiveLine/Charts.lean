/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ProjectiveLine.Inversion
import LeanPool.JacobianDiffgeo.Surface.ChartedSpaceKit
import Mathlib.Analysis.Analytic.Constructions

/-!
# The two-chart complex-manifold structure on `ℙ¹` (CC5)

Unit: projective-line (`docs/design/projective-line.md` §3.2). Builds `ChartedSpace ℂ (OnePoint ℂ)`
and `IsManifold 𝓘(ℂ) ω (OnePoint ℂ)` from two charts:

* `coeChart`: the identity chart on the finite part, `source = {∞}ᶜ`, junk `coeChart ∞ = 0`;
* `invChart`: the chart at infinity, `source = {(0:ℂ)}ᶜ`, `↑z ↦ z⁻¹` (unconditional),
  `∞ ↦ 0`.

`coeChart` is hand-rolled (not built from `isOpenEmbedding_coe.toOpenPartialHomeomorph`) so that
`coeChart ∞ = 0` is `rfl`; `invChart` is likewise hand-rolled (`toFun p := coeChart (inversion p)`,
`invFun w := inversion ↑w`) so that all four transition maps between `coeChart`/`invChart` are
literally `id`/`Inv.inv` as total functions (junk values aligned by construction).
-/

open scoped ContDiff Manifold OnePoint
open Set Filter Topology OnePoint

namespace RS.P1

/-- The identity chart on the finite part of `ℙ¹`: source `{∞}ᶜ`, target `univ`,
`↑z ↦ z`, junk value `coeChart ∞ = 0`. -/
noncomputable def coeChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ where
  toFun p := p.elim 0 id
  invFun := ((↑) : ℂ → OnePoint ℂ)
  source := {(∞ : OnePoint ℂ)}ᶜ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := coe_ne_infty z
  left_inv' p hp := by obtain ⟨z, rfl⟩ := ne_infty_iff_exists.mp hp; rfl
  right_inv' z _ := rfl
  open_source := isClosed_infty.isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro p hp
    obtain ⟨z, rfl⟩ := ne_infty_iff_exists.mp hp
    exact (continuousAt_coe.mpr (by exact continuousAt_id)).continuousWithinAt
  continuousOn_invFun := continuous_coe.continuousOn

@[simp] theorem coeChart_apply_coe (z : ℂ) : coeChart (z : OnePoint ℂ) = z := rfl
@[simp] theorem coeChart_apply_infty : coeChart (∞ : OnePoint ℂ) = 0 := rfl
@[simp] theorem coeChart_symm_apply (z : ℂ) : coeChart.symm z = (z : OnePoint ℂ) := rfl
@[simp] theorem coeChart_source : coeChart.source = {(∞ : OnePoint ℂ)}ᶜ := rfl
@[simp] theorem coeChart_target : coeChart.target = Set.univ := rfl

/-- `inversion` never sends a finite point to `↑(0:ℂ)`. -/
theorem inversion_coe_ne_coe_zero (w : ℂ) : inversion (w : OnePoint ℂ) ≠ ((0 : ℂ) : OnePoint ℂ) :=
    by
  by_cases hw : w = 0
  · subst hw; simp
  · rw [inversion_coe hw]
    simpa [coe_eq_coe] using inv_ne_zero hw

/-- The chart at infinity: source `{(0:ℂ)}ᶜ`, target `univ`, `↑z ↦ z⁻¹`, `∞ ↦ 0`.
Hand-rolled (`toFun p := coeChart (inversion p)`, `invFun w := inversion ↑w`), matching
`coeChart`'s style so junk values are aligned. -/
noncomputable def invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ where
  toFun p := coeChart (inversion p)
  invFun w := inversion (w : OnePoint ℂ)
  source := {((0 : ℂ) : OnePoint ℂ)}ᶜ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' w _ := inversion_coe_ne_coe_zero w
  left_inv' p hp := by
    have hp' : inversion p ≠ (∞ : OnePoint ℂ) := fun h => hp (inversion_eq_infty_iff.mp h)
    obtain ⟨z, hz⟩ := ne_infty_iff_exists.mp hp'
    change inversion ((coeChart (inversion p) : ℂ) : OnePoint ℂ) = p
    rw [← hz]
    simp only [coeChart_apply_coe]
    rw [hz, inversion_involutive]
  right_inv' w _ := by
    show coeChart (inversion (inversion (w : OnePoint ℂ))) = w
    rw [inversion_involutive]
    rfl
  open_source := isClosed_singleton.isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := by
    have hmaps : MapsTo inversion {((0 : ℂ) : OnePoint ℂ)}ᶜ coeChart.source := by
      intro p hp
      change inversion p ≠ (∞ : OnePoint ℂ)
      exact fun h => hp (inversion_eq_infty_iff.mp h)
    exact coeChart.continuousOn.comp continuous_inversion.continuousOn hmaps
  continuousOn_invFun :=
    (continuous_inversion.comp continuous_coe).continuousOn

@[simp] theorem invChart_apply_coe (z : ℂ) : invChart (z : OnePoint ℂ) = z⁻¹ := by
  change coeChart (inversion (z : OnePoint ℂ)) = z⁻¹
  by_cases hz : z = 0
  · subst hz; simp
  · rw [inversion_coe hz, coeChart_apply_coe]

@[simp] theorem invChart_apply_infty : invChart (∞ : OnePoint ℂ) = 0 := by
  change coeChart (inversion ∞) = 0
  simp

@[simp] theorem invChart_symm_apply (w : ℂ) : invChart.symm w = inversion (w : OnePoint ℂ) := rfl

@[simp] theorem invChart_source : invChart.source = {((0 : ℂ) : OnePoint ℂ)}ᶜ := rfl
@[simp] theorem invChart_target : invChart.target = Set.univ := rfl

theorem invChart_comp_coe : ⇑invChart ∘ ((↑) : ℂ → OnePoint ℂ) = Inv.inv := by
  funext z
  simp [Function.comp_apply]

/-- `inversion` read through `coeChart` on both ends is inversion itself (unconditional). -/
theorem coeChart_inversion_coe (z : ℂ) : coeChart (inversion (z : OnePoint ℂ)) = z⁻¹ := by
  by_cases hz : z = 0
  · subst hz; simp
  · rw [inversion_coe hz, coeChart_apply_coe]

/-- `inversion` read through `invChart` on both ends is the identity (unconditional;
this is `invChart.right_inv` unfolded through `invChart_symm_apply`). -/
theorem invChart_inversion_coe (z : ℂ) : invChart (inversion (z : OnePoint ℂ)) = z := by
  have h := invChart.right_inv (x := z) (Set.mem_univ z)
  rwa [invChart_symm_apply] at h

/-- The generating chart family (`false ↦ coeChart`, `true ↦ invChart`). -/
noncomputable def chartFamily : Bool → OpenPartialHomeomorph (OnePoint ℂ) ℂ
  | false => coeChart
  | true => invChart

@[simp] theorem chartFamily_false : chartFamily false = coeChart := rfl
@[simp] theorem chartFamily_true : chartFamily true = invChart := rfl

/-- Index map: `∞ ↦ true` (use `invChart`), `↑z ↦ false` (use `coeChart`). -/
def chartIndex : OnePoint ℂ → Bool := fun p => p.elim true (fun _ => false)

@[simp] theorem chartIndex_infty : chartIndex ∞ = true := rfl
@[simp] theorem chartIndex_coe (z : ℂ) : chartIndex (z : OnePoint ℂ) = false := rfl

theorem mem_chartFamily_source (p : OnePoint ℂ) : p ∈ (chartFamily (chartIndex p)).source := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z => simp

noncomputable instance instChartedSpace : ChartedSpace ℂ (OnePoint ℂ) :=
  RS.chartedSpaceOfFamily chartFamily chartIndex mem_chartFamily_source

@[simp] theorem chartAt_coe (z : ℂ) : chartAt ℂ ((z : ℂ) : OnePoint ℂ) = coeChart := by
  rw [RS.chartedSpaceOfFamily_chartAt]; simp

@[simp] theorem chartAt_infty : chartAt ℂ (∞ : OnePoint ℂ) = invChart := by
  rw [RS.chartedSpaceOfFamily_chartAt]; simp

theorem atlas_eq : atlas ℂ (OnePoint ℂ) = {coeChart, invChart} := by
  rw [RS.chartedSpaceOfFamily_atlas]
  ext e
  constructor
  · rintro ⟨b, rfl⟩
    cases b
    · exact Set.mem_insert_iff.2 (Or.inl rfl)
    · exact Set.mem_insert_iff.2 (Or.inr rfl)
  · rintro (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

private theorem htrans : ∀ i j : Bool, AnalyticOnNhd ℂ ((chartFamily i).symm ≫ₕ chartFamily j)
    ((chartFamily i).symm ≫ₕ chartFamily j).source := by
  intro i j
  cases i <;> cases j
  · -- false, false : id
    have hfun : (⇑((chartFamily false).symm ≫ₕ chartFamily false) : ℂ → ℂ) = id := by
      funext z
      change coeChart (coeChart.symm z) = z
      exact coeChart.right_inv (Set.mem_univ z)
    rw [hfun]
    exact fun z _ => analyticAt_id
  · -- false, true : Inv.inv
    have hfun : (⇑((chartFamily false).symm ≫ₕ chartFamily true) : ℂ → ℂ) = Inv.inv := by
      funext z
      change invChart (coeChart.symm z) = z⁻¹
      rw [coeChart_symm_apply, invChart_apply_coe]
    have hsub : ((chartFamily false).symm ≫ₕ chartFamily true).source ⊆ {z : ℂ | z ≠ 0} := by
      intro z hz
      rw [OpenPartialHomeomorph.trans_source] at hz
      obtain ⟨-, hz2⟩ := hz
      simp only [Set.mem_preimage, chartFamily_false, chartFamily_true, coeChart_symm_apply,
        invChart_source, Set.mem_compl_iff, Set.mem_singleton_iff, coe_eq_coe] at hz2
      exact hz2
    rw [hfun]
    exact fun z hz => analyticOnNhd_inv z (hsub hz)
  · -- true, false : Inv.inv
    have hfun : (⇑((chartFamily true).symm ≫ₕ chartFamily false) : ℂ → ℂ) = Inv.inv := by
      funext z
      change coeChart (invChart.symm z) = z⁻¹
      rw [invChart_symm_apply]
      by_cases hz : z = 0
      · subst hz; simp
      · rw [inversion_coe hz, coeChart_apply_coe]
    have hsub : ((chartFamily true).symm ≫ₕ chartFamily false).source ⊆ {z : ℂ | z ≠ 0} := by
      intro z hz
      rw [OpenPartialHomeomorph.trans_source] at hz
      obtain ⟨-, hz2⟩ := hz
      simp only [Set.mem_preimage, chartFamily_true, chartFamily_false, invChart_symm_apply,
        coeChart_source, Set.mem_compl_iff, Set.mem_singleton_iff] at hz2
      rw [inversion_eq_infty_iff] at hz2
      simpa [coe_eq_coe] using hz2
    rw [hfun]
    exact fun z hz => analyticOnNhd_inv z (hsub hz)
  · -- true, true : id
    have hfun : (⇑((chartFamily true).symm ≫ₕ chartFamily true) : ℂ → ℂ) = id := by
      funext z
      change invChart (invChart.symm z) = z
      exact invChart.right_inv (Set.mem_univ z)
    rw [hfun]
    exact fun z _ => analyticAt_id

noncomputable instance instIsManifold : IsManifold 𝓘(ℂ) ω (OnePoint ℂ) :=
  RS.isManifold_of_family chartFamily chartIndex mem_chartFamily_source htrans

open IsManifold in
theorem coeChart_mem_maximalAtlas : coeChart ∈ maximalAtlas 𝓘(ℂ) ω (OnePoint ℂ) :=
  subset_maximalAtlas (by rw [atlas_eq]; exact Set.mem_insert _ _)

open IsManifold in
theorem invChart_mem_maximalAtlas : invChart ∈ maximalAtlas 𝓘(ℂ) ω (OnePoint ℂ) :=
  subset_maximalAtlas (by rw [atlas_eq]; exact Set.mem_insert_iff.2 (Or.inr rfl))

/-- `Classical.arbitrary`-free basepoints: `∞`, `↑0`, `↑1`. -/
instance : Nontrivial (OnePoint ℂ) := ⟨⟨((0 : ℂ) : OnePoint ℂ), ∞, coe_ne_infty 0⟩⟩

-- smoke tests: all `inferInstance` (guard against instance regressions).
example : CompactSpace (OnePoint ℂ) := inferInstance
example : T2Space (OnePoint ℂ) := inferInstance
example : ConnectedSpace (OnePoint ℂ) := inferInstance
example (x : OnePoint ℂ) : (𝓝[≠] x).NeBot := inferInstance

end RS.P1
