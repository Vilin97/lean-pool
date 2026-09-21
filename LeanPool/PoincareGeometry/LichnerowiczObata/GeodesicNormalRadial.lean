/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicScaling
public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicRadial

/-! # Intrinsic radial derivatives of the geodesic normal map -/

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

/-- The normal endpoint map sends its radial initial-velocity direction
to the intrinsic radial gradient multiplied by radius. All geodesic and
radial identities are derived from the supplied solution family. -/
theorem coordinate_normal_endpoint_radial_gradient
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
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c z v v) * t ∈ Ioo 0 Real.pi) :
    (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (α ((z, v), t)).1)
      (fderiv ℝ (fun w => (α ((z, w), t)).1) v v) =
      (t * Real.sqrt (coordinateMetricBilinear (I := I) c z v v)) •
        gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (α ((z, v), t)).1) := by
  have hδ : 0 < δ := lt_of_le_of_lt (dist_nonneg) htime
  have hinit := (hsol _ hq).1
  have hv := coordinate_geodesic_velocity_eq_radial (α := fun s => α ((z, v), s))
    b hf hK ha hH c Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
    (fun s hs => ((hsol _ hq).2 s hs).1)
    (fun s hs => ((hsol _ hq).2 s hs).2)
    (by rw [hinit]; exact hcrit) (by rw [hinit]; exact hmax)
    htime (by rw [hinit]; exact hphase)
  rw [fderiv_coordinate_geodesic_endpoint_radial LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion b c hV hα hsol hq htime, map_smul, hv, smul_smul]
  simp only [hinit]

omit [PreconnectedSpace M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] in
/-- Around a regular positive-phase initial velocity, squared radial
distance of the endpoint is time squared times its initial quadratic metric
energy. The neighborhood is derived from the open solution domain. -/
theorem coordinate_normal_endpoint_radius_sq_eventually
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, s))) s)
    {z v : E} (hq : (z, v) ∈ V)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c z v v) * t ∈ Ioo 0 Real.pi) :
    ∀ᶠ w in 𝓝 v, (obataRadial K a f ((extChartAt I c).symm (α ((z, w), t)).1)) ^ 2 =
      t ^ 2 * coordinateMetricBilinear (I := I) c z w w := by
  let g := coordinateMetricBilinear (I := I) c z
  have hgc : Continuous (fun w : E => g w w) := g.continuous.clm_apply continuous_id
  have hpc : Continuous (fun w : E => Real.sqrt (K * g w w) * t) :=
    (Real.continuous_sqrt.comp (continuous_const.mul hgc)).mul continuous_const
  have hnphase : ∀ᶠ w in 𝓝 v, Real.sqrt (K * g w w) * t ∈ Ioo 0 Real.pi :=
    hpc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hphase)
  have hnV : ∀ᶠ w in 𝓝 v, (z, w) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hq)
  have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg htime
  have ht0 : 0 ≤ t := by
    nlinarith [Real.sqrt_nonneg (K * g v v), hphase.1]
  filter_upwards [hnphase, hnV] with w hwphase hwV
  have hinit := (hsol _ hwV).1
  have hr := coordinate_geodesic_obataRadial_eq (α := fun s => α ((z, w), s))
    LC leviCivitaConnection_metricCompatible b hf hK ha hH c Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
    (fun s hs => ((hsol _ hwV).2 s hs).1)
    (fun s hs => ((hsol _ hwV).2 s hs).2)
    (by rw [hinit]; exact hcrit) (by rw [hinit]; exact hmax)
    htime ht0 (by rw [hinit]; exact hwphase.2.le)
  have he : 0 ≤ coordinateMetricBilinear (I := I) c z w w := real_inner_self_nonneg
    (x := (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) w)
  rw [hinit] at hr
  rw [hr, mul_pow, Real.sq_sqrt he]
  ring

/-- Near zero initial velocity, including zero itself, the actual endpoint
radius is time times the intrinsic initial-velocity norm. -/
theorem coordinate_normal_endpoint_radius_at_zero_eventually
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, s))) s)
    {z : E} (hzV : (z, (0 : E)) ∈ V)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) (ht : 0 ≤ t) :
    ∀ᶠ w in 𝓝 (0 : E), obataRadial K a f ((extChartAt I c).symm (α ((z, w), t)).1) =
      t * ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) w‖ := by
  let g := coordinateMetricBilinear (I := I) c z
  have hgc : Continuous (fun w : E => g w w) := g.continuous.clm_apply continuous_id
  have hpc : Continuous (fun w : E => Real.sqrt (K * g w w) * t) :=
    (Real.continuous_sqrt.comp (continuous_const.mul hgc)).mul continuous_const
  have hphase : ∀ᶠ w in 𝓝 (0 : E), Real.sqrt (K * g w w) * t < Real.pi :=
    hpc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds (by simpa using Real.pi_pos))
  have hnear : ∀ᶠ w in 𝓝 (0 : E), (z, w) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)
  have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg htime
  filter_upwards [hnear, hphase] with w hw hp
  have hinit := (hsol _ hw).1
  have he := coordinate_geodesic_obataRadial_eq (α := fun s => α ((z, w), s))
    LC leviCivitaConnection_metricCompatible b hf hK ha hH c Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
    (fun s hs => ((hsol _ hw).2 s hs).1) (fun s hs => ((hsol _ hw).2 s hs).2)
    (by rw [hinit]; exact hcrit) (by rw [hinit]; exact hmax)
    htime ht (by rw [hinit]; exact hp.le)
  rw [hinit] at he
  have hn : Real.sqrt (coordinateMetricBilinear (I := I) c z w w) =
      ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) w‖ := by
    change Real.sqrt (inner ℝ
      ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) w)
      ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) w)) = _
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [he, hn, mul_comm]

/-- In intrinsic tangent-vector variables, the endpoint radial identity is
exactly the scaled norm identity needed for normal sphere-level coordinates. -/
theorem intrinsic_normal_endpoint_radius_at_zero_eventually
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, s))) s)
    {z : E} (hz : z ∈ (extChartAt I c).target) (hzV : (z, (0 : E)) ∈ V)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) (ht : 0 ≤ t) :
    let p := (extChartAt I c).symm z
    let L := (trivializationAt E TM c).continuousLinearMapAt ℝ p
    ∀ᶠ v in 𝓝 (0 : TM p),
      obataRadial K a f ((extChartAt I c).symm (α ((z, L v), t)).1) = t * ‖v‖ := by
  let p := (extChartAt I c).symm z
  let L := (trivializationAt E TM c).continuousLinearMapAt ℝ p
  have hx : p ∈ (chartAt H c).source := by simpa [p] using (extChartAt I c).map_target hz
  have hL : Filter.Tendsto L (𝓝 (0 : TM p)) (𝓝 (0 : E)) := by
    simpa only [map_zero] using L.continuous.continuousAt.tendsto (x := (0 : TM p))
  have he := hL.eventually (coordinate_normal_endpoint_radius_at_zero_eventually
    b hf hK ha hH c hV hsol hzV hcrit hmax htime ht)
  filter_upwards [he] with v hv
  change obataRadial K a f ((extChartAt I c).symm (α ((z, L v), t)).1) =
    t * ‖(trivializationAt E TM c).symmL ℝ p (L v)‖ at hv
  simpa only [L, (trivializationAt E TM c).symmL_continuousLinearMapAt hx] using hv

end LichnerowiczObata
