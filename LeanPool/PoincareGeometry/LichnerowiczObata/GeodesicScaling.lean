/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicEnergy
public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothODEUniqueness

/-! # Uniqueness and scaling of actual coordinate geodesics -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
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

/-- Geodesics with time-rescaled initial velocities agree with the
corresponding time-rescaled solution throughout a common connected domain. -/
theorem coordinate_geodesic_rescale_eqOn
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α β : ℝ → E × E} (r : ℝ) {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (β s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α (r * s))) (r * s))
    (hβ : ∀ s ∈ T, HasDerivAt β (coordinateGeodesicSpray cov b c (β s)) s)
    (hinit : β 0 = ((α 0).1, r • (α 0).2)) :
    EqOn β (fun s => ((α (r * s)).1, r • (α (r * s)).2)) T := by
  apply ode_eqOn_of_contDiffAt hT hconn ?_ hβ
    (fun s hs => hasDerivAt_coordinate_geodesic_rescale cov b c r (hα s hs)) hzero
    (by simpa using hinit)
  intro s hs
  exact (contDiffOn_coordinateGeodesicSpray 1 cov hm ht b c).contDiffAt
    (((isOpen_extChartAt_target c).prod isOpen_univ).mem_nhds ⟨hz s hs, mem_univ _⟩)

/-- A solution family obeys the geodesic scaling law wherever both its
original and scaled initial velocities and times lie in its solution domain. -/
theorem coordinate_geodesic_flow_scaling
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α : (E × E) × ℝ → E × E} {z v : E} (r : ℝ) {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α ((z, r • v), s)).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt (fun t => α ((z, v), t))
      (coordinateGeodesicSpray cov b c (α ((z, v), r * s))) (r * s))
    (hβ : ∀ s ∈ T, HasDerivAt (fun t => α ((z, r • v), t))
      (coordinateGeodesicSpray cov b c (α ((z, r • v), s))) s)
    (hinit : α ((z, v), 0) = (z, v)) (hscaled : α ((z, r • v), 0) = (z, r • v))
    {t : ℝ} (htime : t ∈ T) :
    α ((z, r • v), t) = ((α ((z, v), r * t)).1, r • (α ((z, v), r * t)).2) := by
  exact coordinate_geodesic_rescale_eqOn cov hm ht b c r hT hconn hzero hz hα hβ
    (by rw [hinit, hscaled]) htime

/-- On an open product solution domain, scaling holds for all factors
sufficiently close to one at any fixed interior time. -/
theorem coordinate_geodesic_flow_scaling_eventually
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V)
    {δ : ℝ}
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray cov b c (α (q, s))) s)
    {z v : E} (hq : (z, v) ∈ V) {t : ℝ} (htime : t ∈ Metric.ball 0 δ) :
    ∀ᶠ r in 𝓝 (1 : ℝ),
      α ((z, r • v), t) = ((α ((z, v), r * t)).1, r • (α ((z, v), r * t)).2) := by
  have hat : |t| < δ := by simpa [Real.dist_eq] using htime
  obtain ⟨ε, htε, hεδ⟩ := exists_between hat
  have hε : 0 < ε := (abs_nonneg t).trans_lt htε
  have hqnear : ∀ᶠ r in 𝓝 (1 : ℝ), (z, r • v) ∈ V := by
    have hc : Continuous (fun r : ℝ => (z, r • v)) :=
      continuous_const.prodMk (continuous_id.smul continuous_const)
    exact hc.continuousAt.preimage_mem_nhds (hV.mem_nhds (by simpa using hq))
  have hrnear : ∀ᶠ r in 𝓝 (1 : ℝ), |r| * ε < δ := by
    have hc : Continuous (fun r : ℝ => |r| * ε) := continuous_abs.mul continuous_const
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hεδ))
  filter_upwards [hqnear, hrnear] with r hqr hr
  have hsub : Metric.ball (0 : ℝ) ε ⊆ Metric.ball 0 δ := Metric.ball_subset_ball hεδ.le
  have hscaled (s : ℝ) (hs : s ∈ Metric.ball (0 : ℝ) ε) : r * s ∈ Metric.ball (0 : ℝ) δ := by
    have habs : |s| < ε := by simpa [Real.dist_eq] using hs
    have hle := mul_le_mul_of_nonneg_left habs.le (abs_nonneg r)
    simpa [Real.dist_eq, abs_mul] using hle.trans_lt hr
  exact coordinate_geodesic_flow_scaling cov hm ht b c r Metric.isOpen_ball
    (convex_ball (0 : ℝ) ε).isPreconnected (Metric.mem_ball_self hε)
    (fun s hs => ((hsol _ hqr).2 s (hsub hs)).1)
    (fun s hs => ((hsol _ hq).2 (r * s) (hscaled s hs)).2)
    (fun s hs => ((hsol _ hqr).2 s (hsub hs)).2)
    (hsol _ hq).1 (hsol _ hqr).1 (by simpa [Real.dist_eq] using htε)

/-- The derivative of the position endpoint in its radial initial-velocity
direction is time times its terminal velocity. The scaling identity and all
nearby domain conditions are derived from the actual solution family. -/
theorem fderiv_coordinate_geodesic_endpoint_radial
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hα : ContDiffOn ℝ 1 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray cov b c (α (q, s))) s)
    {z v : E} (hq : (z, v) ∈ V) {t : ℝ} (htime : t ∈ Metric.ball 0 δ) :
    fderiv ℝ (fun w => (α ((z, w), t)).1) v v = t • (α ((z, v), t)).2 := by
  let F : E → E := fun w => (α ((z, w), t)).1
  have hi : ContDiffAt ℝ 1 (fun w : E => ((z, w), t)) v :=
    (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
  have hF : DifferentiableAt ℝ F v :=
    (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds ⟨hq, htime⟩)).comp v hi).fst).differentiableAt
      (by norm_num)
  have hs : HasDerivAt (fun r : ℝ => r • v) v 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
  have hl := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℝ) (F := E) (E := E)
    (l := F) (f := fun r : ℝ => r • v) 1 hF.hasFDerivAt hs (by simp)
  have hp : HasDerivAt (fun s => (α ((z, v), s)).1) (α ((z, v), t)).2 t :=
    HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E × E) (E := E)
      (l := Prod.fst) (f := fun s => α ((z, v), s)) t
      (hasFDerivAt_fst (p := α ((z, v), t))) ((hsol _ hq).2 t htime).2
  have hr := hp.scomp_of_eq 1 ((hasDerivAt_id (1 : ℝ)).mul_const t) (by simp)
  have he : (fun r : ℝ => F (r • v)) =ᶠ[𝓝 1]
      (fun r => (α ((z, v), r * t)).1) :=
    (coordinate_geodesic_flow_scaling_eventually cov hm ht b c hV hsol hq htime).mono
      (fun _ he => by
        have hh := congrArg (fun q : E × E => q.1) he
        exact hh)
  have hr' : HasDerivAt (fun r : ℝ => F (r • v)) (t • (α ((z, v), t)).2) 1 := by
    convert hr.congr_of_eventuallyEq he using 1
    simp
  exact hl.unique hr'

end LichnerowiczObata
