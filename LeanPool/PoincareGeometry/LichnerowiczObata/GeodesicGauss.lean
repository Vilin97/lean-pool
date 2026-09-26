/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicNormalRadial

/-! # Radial metric pairings of the constructed geodesic normal map -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [PreconnectedSpace M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- The normal map preserves radial metric pairings up to its fixed
time-squared factor. In particular, initial angular directions remain
orthogonal to the radial direction at the endpoint. -/
theorem coordinate_normal_endpoint_gauss
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hα : ContDiffOn ℝ 1 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, s))) s)
    {z v : E} (hq : (z, v) ∈ V)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c z v v) * t ∈ Ioo 0 Real.pi)
    (w : E) :
    coordinateMetricBilinear (I := I) c (α ((z, v), t)).1
      (fderiv ℝ (fun u => (α ((z, u), t)).1) v v)
      (fderiv ℝ (fun u => (α ((z, u), t)).1) v w) =
      t ^ 2 * coordinateMetricBilinear (I := I) c z v w := by
  let F : E → E := fun u => (α ((z, u), t)).1
  let x := (extChartAt I c).symm (F v)
  let R := obataRadial K a f
  let g := coordinateMetricBilinear (I := I) c z
  let L := (trivializationAt E TM c).symmL ℝ x
  let N := gradient (I := I) R x
  have hpoint := ((hsol _ hq).2 t htime).1
  have hx : x ∈ (chartAt H c).source := by
    simpa [x, F] using (extChartAt I c).map_target hpoint
  have hpos : F v = extChartAt I c x := ((extChartAt I c).right_inv hpoint).symm
  have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg htime
  have hinit := (hsol _ hq).1
  have hreg := coordinate_geodesic_obata_regular (α := fun s => α ((z, v), s))
    LC leviCivitaConnection_metricCompatible b hf hK.le ha hH c Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
    (fun s hs => ((hsol _ hq).2 s hs).1) (fun s hs => ((hsol _ hq).2 s hs).2)
    (by rw [hinit]; exact hcrit) (by rw [hinit]; exact hmax)
    htime (by rw [hinit]; exact hphase)
  change -a < f x ∧ f x < a at hreg
  have hlo : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hreg.1])
  have hhi : f x / a < 1 := (div_lt_iff₀ ha).2 (by nlinarith [hreg.2])
  have hR : MDiffAt R x :=
    (contMDiffAt_obataRadial (hf x) hlo.ne' hhi.ne).mdifferentiableAt (by norm_num)
  have hi : ContDiffAt ℝ 1 (fun u : E => ((z, u), t)) v :=
    (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
  have hF : DifferentiableAt ℝ F v :=
    (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds ⟨hq, htime⟩)).comp v hi).fst).differentiableAt
      (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hcurve : HasDerivAt (fun s : ℝ => F (v + s • w)) (fderiv ℝ F v w) 0 := by
    exact HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℝ) (F := E) (E := E)
      (l := F) (f := fun s : ℝ => v + s • w) 0 hF.hasFDerivAt hline (by simp)
  have hrad := hasDerivAt_chart_curve_value c x hx hR (by simpa using hpos) hcurve
  have hquad := hasFDerivAt_symmetric_metric_quadratic g
    (fun u w => real_inner_comm
      ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) w)
      ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u)) v
  have hqder := (HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℝ) (F := E) (E := ℝ)
    (l := fun u => g u u) (f := fun s : ℝ => v + s • w) 0 hquad hline (by simp)).const_mul (t ^ 2)
  have he := coordinate_normal_endpoint_radius_sq_eventually b hf hK ha hH c hV hsol
    hq hcrit hmax htime hphase
  have hlim : Filter.Tendsto (fun s : ℝ => v + s • w) (𝓝 0) (𝓝 v) := by
    simpa only [ContinuousAt, zero_smul, add_zero] using hline.continuousAt
  have heline := hlim.eventually he
  have hder := (hrad.pow 2).unique (hqder.congr_of_eventuallyEq heline)
  have hrnonneg : 0 ≤ R x := div_nonneg (Real.arccos_nonneg _) (Real.sqrt_nonneg _)
  have htnonneg : 0 ≤ t := by nlinarith [Real.sqrt_nonneg (K * g v v), hphase.1]
  have hgnonneg : 0 ≤ g v v := real_inner_self_nonneg
    (x := (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) v)
  have hrsq : R x ^ 2 = t ^ 2 * g v v := he.self_of_nhds
  have hradius : R x = t * Real.sqrt (g v v) := by
    nlinarith [Real.sq_sqrt hgnonneg, mul_nonneg htnonneg (Real.sqrt_nonneg (g v v))]
  have hnormal := coordinate_normal_endpoint_radial_gradient b hf hK ha hH c
    hV hα hsol hq hcrit hmax htime hphase
  change L (fderiv ℝ F v v) = (t * Real.sqrt (g v v)) • N at hnormal
  change inner ℝ (L (fderiv ℝ F v v)) (L (fderiv ℝ F v w)) = t ^ 2 * g v w
  rw [hnormal, real_inner_smul_left, ← hradius]
  norm_num only [zero_smul, add_zero, pow_one, smul_apply, smul_eq_mul] at hder
  change 2 * R x * inner ℝ N (L (fderiv ℝ F v w)) = t ^ 2 * (2 * g v w) at hder
  nlinarith [hder]

end LichnerowiczObata
