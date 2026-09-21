/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalRayMetric
public import LeanPool.PoincareGeometry.LichnerowiczObata.SineMetricLimit
public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialAngularDecomposition

/-! # Pole-normalized angular metric of the geodesic normal map -/

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

/-- The center derivative fixes the angular metric constant of the actual
geodesic normal map. No limiting angular metric is assumed. -/
theorem geodesic_normal_ray_metric_pole_normalized
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V)
    (hzV : (z, (0 : E)) ∈ V) {δ : ℝ} (hδ : 0 < δ)
    (hα : ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ r ∈ Metric.ball 0 δ, (α (q, r)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, r))) r)
    (hrest : ∀ r ∈ Metric.ball 0 δ, α ((z, 0), r) = (z, 0))
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) (htpos : 0 < t) {u : E}
    (hu : 0 < coordinateMetricBilinear (I := I) c z u u)
    {ε : ℝ} (hε : 0 < ε)
    (hdata : ∀ r ∈ Ioo 0 ε, (z, r • u) ∈ V ∧
      Real.sqrt (K * coordinateMetricBilinear (I := I) c z (r • u) (r • u)) * t ∈ Ioo 0 Real.pi)
    {w v : E} (hw : coordinateMetricBilinear (I := I) c z u w = 0)
    (hv : coordinateMetricBilinear (I := I) c z u v = 0)
    {s : ℝ} (hs : s ∈ Ioo 0 ε) :
    let φ := fun q : E × ℝ => (α ((z, q.2 • q.1), t)).1
    let freq := Real.sqrt K * (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u))
    coordinateMetricBilinear (I := I) c (φ (u, s))
      (fderiv ℝ φ (u, s) (w, 0)) (fderiv ℝ φ (u, s) (v, 0)) /
        Real.sin (freq * s) ^ 2 =
      coordinateMetricBilinear (I := I) c z w v /
        (K * coordinateMetricBilinear (I := I) c z u u) := by
  let F := fun y : E => (α ((z, y), t)).1
  let φ := fun q : E × ℝ => F (q.2 • q.1)
  let g := coordinateMetricBilinear (I := I) c z
  let freq := Real.sqrt K * (t * Real.sqrt (g u u))
  let G := fun r : ℝ => coordinateMetricBilinear (I := I) c (F (r • u))
    (fderiv ℝ F (r • u) w) (fderiv ℝ F (r • u) v)
  let Q := fun r => coordinateMetricBilinear (I := I) c (φ (u, r))
    (fderiv ℝ φ (u, r) (w, 0)) (fderiv ℝ φ (u, r) (v, 0))
  have hfreq : freq ≠ 0 :=
    (mul_pos (Real.sqrt_pos.mpr hK) (mul_pos htpos (Real.sqrt_pos.mpr hu))).ne'
  have hlim := tendsto_geodesic_endpoint_metric_at_zero LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion b c hz hV hzV hδ hα
    (fun q hq => ⟨(hsol q hq).1, fun r hr => ((hsol q hq).2 r hr).2⟩) hrest htime w v
  have hline : Filter.Tendsto (fun r : ℝ => r • u) (𝓝[>] 0) (𝓝 (0 : E)) := by
    have hc : ContinuousAt (fun r : ℝ => r • u) 0 := by fun_prop
    simpa only [zero_smul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hG : Filter.Tendsto G (𝓝[>] 0) (𝓝 (t ^ 2 * g w v)) := hlim.comp hline
  have hQ (r : ℝ) (hr : r ∈ Ioo 0 ε) : Q r = r ^ 2 * G r := by
    have hi : ContDiffAt ℝ 2 (fun y : E => ((z, y), t)) (r • u) :=
      (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
    have hF : DifferentiableAt ℝ F (r • u) :=
      (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds
        ⟨(hdata r hr).1, htime⟩)).comp (r • u) hi).fst).differentiableAt (by norm_num)
    exact normal_ray_spatial_metric (coordinateMetricBilinear (I := I) c) hF w v
  have he : Q s / Real.sin (freq * s) ^ 2 = (t ^ 2 * g w v) / freq ^ 2 := by
    apply sine_normalized_eq_of_pole_limit hG hfreq hε
    intro r hr
    rw [← hQ r hr]
    exact geodesic_normal_ray_metric_sine_squared_normalized_eq b hf hK ha hb hH c
      hV hα hsol hcrit hmax htime isOpen_Ioo (convex_Ioo 0 ε).isPreconnected
      (fun r hr => ⟨hr.1, hdata r hr⟩) hw hv hr hs
  change Q s / Real.sin (freq * s) ^ 2 = g w v / (K * g u u)
  rw [he]
  have hfreqsq : freq ^ 2 = K * (t ^ 2 * g u u) := by
    dsimp only [freq]
    rw [mul_pow, mul_pow, Real.sq_sqrt hK.le, Real.sq_sqrt hu.le]
  rw [hfreqsq]
  field_simp [htpos.ne', hK.ne', hu.ne']

/-- A pole-normalized angular metric interval exists for every positive-energy
initial ray. Its size is constructed from the open geodesic domain. -/
theorem exists_geodesic_normal_ray_metric_pole_normalized
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V)
    (hzV : (z, (0 : E)) ∈ V) {δ : ℝ} (hδ : 0 < δ)
    (hα : ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ r ∈ Metric.ball 0 δ, (α (q, r)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, r))) r)
    (hrest : ∀ r ∈ Metric.ball 0 δ, α ((z, 0), r) = (z, 0))
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) (htpos : 0 < t) {u : E}
    (hu : 0 < coordinateMetricBilinear (I := I) c z u u) :
    ∃ ε > 0, ∀ (s : ℝ), s ∈ Ioo 0 ε → ∀ (w v : E),
      coordinateMetricBilinear (I := I) c z u w = 0 →
      coordinateMetricBilinear (I := I) c z u v = 0 →
      let φ := fun q : E × ℝ => (α ((z, q.2 • q.1), t)).1
      let freq := Real.sqrt K * (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u))
      coordinateMetricBilinear (I := I) c (φ (u, s))
        (fderiv ℝ φ (u, s) (w, 0)) (fderiv ℝ φ (u, s) (v, 0)) /
          Real.sin (freq * s) ^ 2 =
        coordinateMetricBilinear (I := I) c z w v /
          (K * coordinateMetricBilinear (I := I) c z u u) := by
  obtain ⟨ε, hε, hdata⟩ := exists_positive_phase_ray_interval
    (coordinateMetricBilinear (I := I) c z) hV hzV hK htpos hu
  refine ⟨ε, hε, ?_⟩
  intro s hs w v hw hv
  exact geodesic_normal_ray_metric_pole_normalized b hf hK ha hb hH c hz hV hzV
    hδ hα hsol hrest hcrit hmax htime htpos hu hε hdata hw hv hs

/-- The full local normal-map metric, including radial and mixed directions,
is reconstructed from the Gauss lemma and the pole-normalized angular metric. -/
theorem geodesic_normal_ray_full_metric
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V)
    (hzV : (z, (0 : E)) ∈ V) {δ : ℝ} (hδ : 0 < δ)
    (hα : ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ r ∈ Metric.ball 0 δ, (α (q, r)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, r))) r)
    (hrest : ∀ r ∈ Metric.ball 0 δ, α ((z, 0), r) = (z, 0))
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) (htpos : 0 < t) {u : E}
    (hu : 0 < coordinateMetricBilinear (I := I) c z u u)
    {ε : ℝ} (hε : 0 < ε)
    (hdata : ∀ r ∈ Ioo 0 ε, (z, r • u) ∈ V ∧
      Real.sqrt (K * coordinateMetricBilinear (I := I) c z (r • u) (r • u)) * t ∈ Ioo 0 Real.pi)
    {s : ℝ} (hs : s ∈ Ioo 0 ε) (w v : E) :
    let F := fun y : E => (α ((z, y), t)).1
    let g := coordinateMetricBilinear (I := I) c z
    let freq := Real.sqrt K * (t * Real.sqrt (g u u))
    let angular := Real.sin (freq * s) ^ 2 / (s ^ 2 * (K * g u u))
    coordinateMetricBilinear (I := I) c (F (s • u))
      (fderiv ℝ F (s • u) w) (fderiv ℝ F (s • u) v) =
        angular * g w v + (t ^ 2 - angular) * (g u w * g u v / g u u) := by
  let F := fun y : E => (α ((z, y), t)).1
  let g := coordinateMetricBilinear (I := I) c z
  let D := fderiv ℝ F (s • u)
  let B := (coordinateMetricBilinear (I := I) c (F (s • u))).bilinearComp D D
  let freq := Real.sqrt K * (t * Real.sqrt (g u u))
  let angular := Real.sin (freq * s) ^ 2 / (s ^ 2 * (K * g u u))
  have hg : ∀ w v, g w v = g v w := by
    intro w v
    exact real_inner_comm
      ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) v)
      ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) w)
  have hB : ∀ w v, B w v = B v w := by
    intro w v
    exact real_inner_comm
      ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (F (s • u))) (D v))
      ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (F (s • u))) (D w))
  have hα1 := hα.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hrad : ∀ w, B u w = t ^ 2 * g u w := by
    intro w
    have he := coordinate_normal_endpoint_gauss b hf hK ha hH c hV hα1 hsol
      (hdata s hs).1 hcrit hmax htime (hdata s hs).2 w
    change (coordinateMetricBilinear (I := I) c (F (s • u))) (D (s • u)) (D w) =
      t ^ 2 * g (s • u) w at he
    simp only [map_smul, smul_apply, smul_eq_mul] at he
    change s * B u w = t ^ 2 * (s * g u w) at he
    nlinarith [he, hs.1]
  have hi : ContDiffAt ℝ 2 (fun y : E => ((z, y), t)) (s • u) :=
    (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
  have hF : DifferentiableAt ℝ F (s • u) :=
    (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds
      ⟨(hdata s hs).1, htime⟩)).comp (s • u) hi).fst).differentiableAt (by norm_num)
  have hang : ∀ w v, g u w = 0 → g u v = 0 → B w v = angular * g w v := by
    intro w v hw hv
    have he := geodesic_normal_ray_metric_pole_normalized b hf hK ha hb hH c hz hV hzV
      hδ hα hsol hrest hcrit hmax htime htpos hu hε hdata hw hv hs
    change _ / Real.sin (freq * s) ^ 2 = g w v / (K * g u u) at he
    rw [normal_ray_spatial_metric (coordinateMetricBilinear (I := I) c) hF w v] at he
    change s ^ 2 * B w v / Real.sin (freq * s) ^ 2 = g w v / (K * g u u) at he
    have hphase : freq * s ∈ Ioo 0 Real.pi := by
      have hquad : g (s • u) (s • u) = s ^ 2 * g u u := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      have hp := (hdata s hs).2
      change Real.sqrt (K * g (s • u) (s • u)) * t ∈ Ioo 0 Real.pi at hp
      rw [Real.sqrt_mul hK.le, hquad, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.1.le] at hp
      convert hp using 1
      dsimp only [freq]
      ring
    have hsin := (Real.sin_pos_of_pos_of_lt_pi hphase.1 hphase.2).ne'
    have hsinf : Real.sin (s * freq) ≠ 0 := by simpa only [mul_comm s freq] using hsin
    have hgu : g u u ≠ 0 := hu.ne'
    dsimp only [angular]
    field_simp [hs.1.ne', hK.ne', hgu, hsin, hsinf] at he ⊢
    nlinarith [he]
  exact bilinear_metric_of_radial_and_angular g B hg hB hu.ne' hrad hang w v

/-- One punctured velocity ball supports the full normal-map metric formula
simultaneously in all directions. Positive energy is derived from the chart
metric, and the ray intervals are constructed uniformly. -/
theorem exists_geodesic_normal_full_metric_ball
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V)
    (hzV : (z, (0 : E)) ∈ V) {δ : ℝ} (hδ : 0 < δ)
    (hα : ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ r ∈ Metric.ball 0 δ, (α (q, r)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, r))) r)
    (hrest : ∀ r ∈ Metric.ball 0 δ, α ((z, 0), r) = (z, 0))
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) (htpos : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : E, ‖u‖ < ε → u ≠ 0 → ∀ w v : E,
      let F := fun y : E => (α ((z, y), t)).1
      let g := coordinateMetricBilinear (I := I) c z
      let freq := Real.sqrt K * (t * Real.sqrt (g u u))
      let angular := Real.sin freq ^ 2 / (K * g u u)
      coordinateMetricBilinear (I := I) c (F u)
        (fderiv ℝ F u w) (fderiv ℝ F u v) =
          angular * g w v + (t ^ 2 - angular) * (g u w * g u v / g u u) := by
  let g := coordinateMetricBilinear (I := I) c z
  have hg : ∀ u : E, u ≠ 0 → 0 < g u u := by
    intro u hu
    have hx : (extChartAt I c).symm z ∈ (chartAt H c).source := by
      simpa using (extChartAt I c).map_target hz
    have hn : (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u ≠ 0 := by
      intro he
      have hh := congrArg ((trivializationAt E TM c).continuousLinearMapAt ℝ
        ((extChartAt I c).symm z)) he
      rw [(trivializationAt E TM c).continuousLinearMapAt_symmL hx, map_zero] at hh
      exact hu hh
    exact real_inner_self_pos.mpr hn
  obtain ⟨ε, hε, hdata⟩ := exists_uniform_positive_phase_ray_ball g hg hV hzV hK htpos
  refine ⟨ε, hε, ?_⟩
  intro u hu hune w v
  have he := geodesic_normal_ray_full_metric b hf hK ha hb hH c hz hV hzV hδ hα hsol
    hrest hcrit hmax htime htpos (hg u hune) (show (0 : ℝ) < 2 by norm_num)
    (hdata u hu hune) (show (1 : ℝ) ∈ Ioo 0 2 by norm_num) w v
  simpa only [one_smul, mul_one, one_pow, one_mul] using he

end LichnerowiczObata
