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

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicLinearization
public import LeanPool.PoincareGeometry.LichnerowiczObata.MetricBilinearRegularity

/-! # The pullback metric limit at the center of a geodesic normal map -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A C1 change of coordinates pulls a continuous bilinear metric back
continuously, including its value at the center. -/
theorem continuousAt_pullback_metric_pairing
    {F : E → E} {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hF : ContDiffAt ℝ 1 F x) (hg : ContinuousAt g (F x)) (u w : E) :
    ContinuousAt (fun v => g (F v) (fderiv ℝ F v u) (fderiv ℝ F v w)) x := by
  have hD : ContinuousAt (fderiv ℝ F) x :=
    (hF.fderiv_right (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).continuousAt
  exact ((hg.comp hF.continuousAt).clm_apply
    (hD.clm_apply continuousAt_const)).clm_apply (hD.clm_apply continuousAt_const)

/-- A scalar-identity derivative fixes the limiting pullback metric
without any hypothesis about an angular metric or its normalization. -/
theorem tendsto_pullback_metric_of_scalar_derivative
    {F : E → E} {g : E → E →L[ℝ] E →L[ℝ] ℝ} {z : E} {t : ℝ}
    (hF : ContDiffAt ℝ 1 F 0) (hg : ContinuousAt g z) (hzero : F 0 = z)
    (hd : HasFDerivAt F (t • ContinuousLinearMap.id ℝ E) 0) (u w : E) :
    Filter.Tendsto (fun v => g (F v) (fderiv ℝ F v u) (fderiv ℝ F v w))
      (𝓝 0) (𝓝 (t ^ 2 * g z u w)) := by
  have hc := continuousAt_pullback_metric_pairing hF (by rwa [hzero]) u w
  have he : g (F 0) (fderiv ℝ F 0 u) (fderiv ℝ F 0 w) = t ^ 2 * g z u w := by
    rw [hzero, hd.fderiv]
    simp only [smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    ring
  simpa only [ContinuousAt, he] using hc
end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The actual geodesic endpoint pullback metric tends at zero velocity
to time squared times the metric at the base point. -/
theorem tendsto_geodesic_endpoint_metric_at_zero
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V)
    (hzV : (z, (0 : E)) ∈ V) {δ : ℝ} (hδ : 0 < δ)
    (hα : ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, HasDerivAt (fun t => α (q, t))
        (coordinateGeodesicSpray cov b c (α (q, s))) s)
    (hrest : ∀ s ∈ Metric.ball 0 δ, α ((z, 0), s) = (z, 0))
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) (u w : E) :
    let F := fun v => (α ((z, v), t)).1
    Filter.Tendsto (fun v => coordinateMetricBilinear (I := I) c (F v)
      (fderiv ℝ F v u) (fderiv ℝ F v w)) (𝓝 0)
      (𝓝 (t ^ 2 * coordinateMetricBilinear (I := I) c z u w)) := by
  dsimp only
  have hinit : (fun q => α (q, 0)) =ᶠ[𝓝 (z, (0 : E))] id := by
    filter_upwards [hV.mem_nhds hzV] with q hq
    exact (hsol q hq).1
  have hd := hasFDerivAt_geodesic_endpoint_zero cov hm ht b c hz
    (hV.prod Metric.isOpen_ball) hα (fun q hq => (hsol q.1 hq.1).2 q.2 hq.2) hinit
    Metric.isOpen_ball (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
    (fun s hs => ⟨hzV, hs⟩) hrest htime
  have hi : ContDiffAt ℝ 2 (fun v : E => ((z, v), t)) 0 :=
    (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
  have hF := ((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds ⟨hzV, htime⟩)).comp 0 hi).fst
  exact tendsto_pullback_metric_of_scalar_derivative (hF.of_le (by norm_num))
    (differentiableAt_coordinateMetricBilinear (I := I) c hz).continuousAt
    (congrArg Prod.fst (hrest t htime)) hd u w

end LichnerowiczObata
