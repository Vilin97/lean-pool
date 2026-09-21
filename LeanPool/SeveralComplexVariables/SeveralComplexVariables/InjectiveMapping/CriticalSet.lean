/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticSet.Regular
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.InjectiveMapping.CorankOne
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.InjectiveMapping.Immersion

/-!
# Excluding critical points of injective holomorphic maps

The critical set cannot have a regular hypersurface point: restriction to that hypersurface has
an immersion point, where an invertible transverse minor forces nonsingularity. The Jacobian
determinant is not identically zero, and any nonempty zero set of it has a regular hypersurface
point. Thus the critical set is empty.

## Main results

`not_isRegularAnalyticSetAt_criticalSet` excludes a regular hypersurface point of the critical
set. `analyticOnNhd_det_complexJacobian` is holomorphy of the Jacobian determinant.
`isInvertible_fderiv_of_injOn_coordinates` is nonsingularity in coordinates, by emptiness of
that critical set.
-/

public noncomputable section

open Set Filter Function Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- A critical set of an injective holomorphic map cannot contain a regular hypersurface. -/
theorem not_isRegularAnalyticSetAt_criticalSet
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) {A : Set E} (hAU : A ⊆ U)
    (hcrit : ∀ x ∈ A, ¬ (fderiv ℂ f x).IsInvertible) {a : E} :
    ¬ IsRegularAnalyticSetAt A a 1 := by
  rintro ⟨haA, e, L, he, hae, hLs, heA⟩
  let K := L.ker
  let V : Set K := K.subtypeL ⁻¹' e.target
  have hV : IsOpen V := e.open_target.preimage K.subtypeL.continuous
  have hLa : e a ∈ K := (heA a hae).mp haA
  have hVne : V.Nonempty := ⟨⟨e a, hLa⟩, e.map_source hae⟩
  let G : K → F := fun z => f (e.symm z)
  have hxA (z : K) (hz : z ∈ V) : e.symm z ∈ A := by
    apply (heA _ (e.map_target hz)).mpr
    rw [e.right_inv hz]
    exact z.property
  have hG : DifferentiableOn ℂ G V := by
    intro z hz
    exact (((hf _ (hAU (hxA z hz))).differentiableAt (hU.mem_nhds (hAU (hxA z hz)))).comp
      z ((he.symm.differentiableAt hz).comp z K.subtypeL.differentiableAt)).differentiableWithinAt
  have hGi : InjOn G V := by
    intro z hz w hw hzw
    apply Subtype.val_injective
    exact e.symm.injOn hz hw (hi (hAU (hxA z hz)) (hAU (hxA w hw)) hzw)
  obtain ⟨z, hz, hzi⟩ := exists_injective_fderiv_of_injOn hV hVne hG hGi
  let S := (fderiv ℂ e.symm (z : E)).comp K.subtypeL
  have hS : Injective S :=
    (he.symm.isInvertible_fderiv hz).injective.comp Subtype.val_injective
  have hP : Module.finrank ℂ K + 1 = Module.finrank ℂ E := by
    have hh := L.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hLs, finrank_top] at hh
    simpa [K, add_comm] using hh
  have hd : fderiv ℂ G z = (fderiv ℂ f (e.symm z)).comp S := by
    exact (((hf _ (hAU (hxA z hz))).differentiableAt
      (hU.mem_nhds (hAU (hxA z hz)))).hasFDerivAt.comp z
      ((he.symm.differentiableAt hz).hasFDerivAt.comp z K.subtypeL.hasFDerivAt)).fderiv
  exact hcrit _ (hxA z hz) (isInvertible_fderiv_of_injOn_of_hyperplane hdim hU hf hi
    (hAU (hxA z hz)) S hS hP (by rwa [← hd]))

/-- The determinant of the complex Jacobian is analytic on a holomorphic map's open domain. -/
theorem analyticOnNhd_det_complexJacobian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → ℂ)} (hU : IsOpen U) {f : (ι → ℂ) → (ι → ℂ)}
    (hf : AnalyticOnNhd ℂ f U) : AnalyticOnNhd ℂ (fun z => (complexJacobian f z).det) U := by
  classical
  intro a ha
  simp only [Matrix.det_apply', complexJacobian]
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro i _
  exact ((analyticOnNhd_pi_iff.mp hf (σ i)).partialDeriv hU i) a ha

/-- An injective holomorphic map between equal complex coordinate spaces has no critical points. -/
theorem isInvertible_fderiv_of_injOn_coordinates {ι : Type*} [Fintype ι]
    {U : Set (ι → ℂ)} (hU : IsOpen U) {f : (ι → ℂ) → (ι → ℂ)}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) {a : ι → ℂ} (ha : a ∈ U) :
    (fderiv ℂ f a).IsInvertible := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let V := Metric.ball a r
  have haV : a ∈ V := Metric.mem_ball_self hr
  have hV : IsOpen V := Metric.isOpen_ball
  have hfV := hf.mono hball
  let J := fun z => (complexJacobian f z).det
  have hJ : AnalyticOnNhd ℂ J V :=
    analyticOnNhd_det_complexJacobian hV (hfV.analyticOnNhd_of_finiteDimensional hV)
  obtain ⟨b, hb, hbi⟩ := exists_injective_fderiv_of_injOn hV ⟨a, haV⟩ hfV (hi.mono hball)
  have hJb : J b ≠ 0 := (det_complexJacobian_ne_zero_iff
    ((hfV b hb).differentiableAt (hV.mem_nhds hb))).mpr
    ⟨(LinearEquiv.ofBijective (fderiv ℂ f b).toLinearMap
      ⟨hbi, LinearMap.surjective_of_injective hbi⟩).toContinuousLinearEquiv, rfl⟩
  apply (det_complexJacobian_ne_zero_iff
    ((hf a ha).differentiableAt (hU.mem_nhds ha))).mp
  intro hJa
  obtain ⟨c, hc⟩ := exists_regularPoint_zeroSet hV isPreconnected_ball hJ
    ⟨b, hb, hJb⟩ ⟨a, haV, hJa⟩
  apply not_isRegularAnalyticSetAt_criticalSet rfl hU hf hi
    (fun z hz => hball hz.1) (a := c) _ hc
  intro z hz hinv
  exact ((det_complexJacobian_ne_zero_iff
    ((hf z (hball hz.1)).differentiableAt (hU.mem_nhds (hball hz.1)))).mpr hinv) hz.2

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
