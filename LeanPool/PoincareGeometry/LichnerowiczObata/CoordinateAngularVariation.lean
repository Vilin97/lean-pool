/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.CoordinateRadialShape
public import LeanPool.PoincareGeometry.LichnerowiczObata.ManifoldFlowCoordinates

/-! # Angularity from the radial level identity in fixed charts -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Spatial derivatives are angular when the scalar level of the family is
its time coordinate. The scalar identity, rather than angularity, is assumed. -/
theorem coordinate_variation_angular {ρ : M → ℝ} {φ : E × ℝ → E}
    (c x : M) (hx : x ∈ (chartAt H c).source) {p : E} {t : ℝ}
    (hpoint : φ (p, t) = extChartAt I c x) (hρ : MDiffAt ρ x)
    (hφ : DifferentiableAt ℝ φ (p, t))
    (hlevel : ((ρ ∘ (extChartAt I c).symm) ∘ φ) =ᶠ[𝓝 (p, t)] Prod.snd) (v : E) :
    inner ℝ (gradient (I := I) ρ x)
      ((trivializationAt E (TangentSpace I : M → Type _) c).symmL ℝ x
        (fderiv ℝ φ (p, t) (v, 0))) = 0 := by
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hi : MDiffAt (extChartAt I c).symm (extChartAt I c x) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c)
        ((extChartAt I c).map_source hx'))
  have hr : DifferentiableAt ℝ (ρ ∘ (extChartAt I c).symm) (φ (p, t)) := by
    rw [hpoint]
    exact mdifferentiableAt_iff_differentiableAt.mp
      (hρ.comp_of_eq (extChartAt I c x) hi ((extChartAt I c).left_inv hx'))
  have hd := congrArg (fun L : (E × ℝ) →L[ℝ] ℝ => L (v, 0)) hlevel.fderiv_eq
  rw [fderiv_comp (p, t) hr hφ] at hd
  simp only [ContinuousLinearMap.comp_apply, fderiv_snd] at hd
  rw [hpoint, fderiv_chart_comp ρ c x hx hρ] at hd
  rwa [inner_gradient]

/-- The actual chart representation of a manifold radial-level family has
angular spatial variations, with angularity deduced from its level identity. -/
theorem coordinate_chartFlow_variation_angular {ρ : M → ℝ} {η : M × ℝ → M}
    {U : Set M} {J : Set ℝ} (hU : IsOpen U) (hJ : IsOpen J)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η (U ×ˢ J))
    (hlevel : ∀ y ∈ U, ∀ s ∈ J, ρ (η (y, s)) = s)
    (c₀ c₁ : M) {p : E} {t : ℝ}
    (hpt : (p, t) ∈ chartFlowDomain (I := I) η (U ×ˢ J) c₀ c₁)
    (hρ : MDiffAt ρ (η ((extChartAt I c₀).symm p, t))) (v : E) :
    let x := η ((extChartAt I c₀).symm p, t)
    inner ℝ (gradient (I := I) ρ x)
      ((trivializationAt E (TangentSpace I : M → Type _) c₁).symmL ℝ x
        (fderiv ℝ (chartFlow (I := I) η c₀ c₁) (p, t) (v, 0))) = 0 := by
  dsimp only
  have hD := isOpen_chartFlowDomain (I := I) (hU.prod hJ) hη.continuousOn c₀ c₁
  have hc : DifferentiableAt ℝ (chartFlow (I := I) η c₀ c₁) (p, t) :=
    ((contDiffOn_chartFlow_domain (n := 1) hη c₀ c₁).contDiffAt
      (hD.mem_nhds hpt)).differentiableAt (by norm_num)
  apply coordinate_variation_angular c₁ _ hpt.2 rfl hρ hc _ v
  filter_upwards [hD.mem_nhds hpt] with z hz
  change ρ ((extChartAt I c₁).symm (extChartAt I c₁
    (η ((extChartAt I c₀).symm z.1, z.2)))) = z.2
  rw [(extChartAt I c₁).left_inv (by simpa using hz.2)]
  exact hlevel _ hz.1.2.1 _ hz.1.2.2

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- A genuine smooth manifold radial family has spherical metric evolution
in fixed charts. Both angularity and the linearized equation are conclusions
of its level identity and actual integral-curve equation. -/
theorem hasDerivAt_manifold_radial_chart_metric {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TangentSpace I y),
      hessian LC f y v w = -K * f y * inner ℝ v w)
    {η : M × ℝ → M} {U : Set M} {J : Set ℝ} (hU : IsOpen U) (hJ : IsOpen J)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 2 η (U ×ˢ J))
    (hode : ∀ y ∈ U, IsMIntegralCurveOn (fun s => η (y, s))
      (gradient (I := I) (obataRadial K a f)) J)
    (hlevel : ∀ y ∈ U, ∀ s ∈ J, obataRadial K a f (η (y, s)) = s)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (c₀ c₁ : M)
    {p : E} {t : ℝ} (hpt : (p, t) ∈ chartFlowDomain (I := I) η (U ×ˢ J) c₀ c₁)
    (hreg : -a < f (η ((extChartAt I c₀).symm p, t)) ∧
      f (η ((extChartAt I c₀).symm p, t)) < a) (v w : E) :
    let φ := chartFlow (I := I) η c₀ c₁
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c₁ (φ (p, s))
      (fderiv ℝ φ (p, s) (v, 0)) (fderiv ℝ φ (p, s) (w, 0)))
      (2 * (Real.sqrt K * (Real.cos (Real.sqrt K * t) / Real.sin (Real.sqrt K * t))) *
        coordinateMetricBilinear (I := I) c₁ (φ (p, t))
          (fderiv ℝ φ (p, t) (v, 0)) (fderiv ℝ φ (p, t) (w, 0))) t := by
  let x := η ((extChartAt I c₀).symm p, t)
  have hregx : -a < f x ∧ f x < a := hreg
  have hρ : MDiffAt (obataRadial K a f) x := by
    have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hregx.1])
    have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa only [one_mul] using hregx.2)
    exact (contMDiffAt_obataRadial (K := K) (hf x) hm.ne' hp.ne).mdifferentiableAt (by norm_num)
  have hη₁ := hη.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hD := isOpen_chartFlowDomain (I := I) (hU.prod hJ) hη.continuousOn c₀ c₁
  have hchart := contDiffOn_chartFlow_domain (n := 2) hη c₀ c₁
  have hchartODE : ∀ z ∈ chartFlowDomain (I := I) η (U ×ˢ J) c₀ c₁,
      HasDerivAt (fun s => chartFlow (I := I) η c₀ c₁ (z.1, s))
        (coordinateVectorField c₁ (gradient (I := I) (obataRadial K a f))
          (chartFlow (I := I) η c₀ c₁ z)) z.2 := by
    intro z hz
    exact hasDerivAt_chartFlow c₀ c₁
      ((hode _ hz.1.2.1).isMIntegralCurveAt (hJ.mem_nhds hz.1.2.2)) hz.2
  have hv := coordinate_chartFlow_variation_angular hU hJ hη₁ hlevel c₀ c₁ hpt hρ v
  have hw := coordinate_chartFlow_variation_angular hU hJ hη₁ hlevel c₀ c₁ hpt hρ w
  have hd := hasDerivAt_radial_flow_metric hK ha hf hb hH b c₁ x hpt.2 hreg
    hD hchart hchartODE hpt rfl v w hv hw
  have ht : obataRadial K a f x = t := hlevel _ hpt.1.2.1 _ hpt.1.2.2
  simpa only [ht] using hd

end LichnerowiczObata
