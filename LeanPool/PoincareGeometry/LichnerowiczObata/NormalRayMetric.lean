/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicNormalRays
public import LeanPool.PoincareGeometry.LichnerowiczObata.ScaledRadialMetric
public import LeanPool.PoincareGeometry.LichnerowiczObata.AngularMetricEvolution

/-! # Angular metric evolution along actual geodesic normal rays -/

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

/-- At every positive-phase ray point, the actual normal-map angular
metric obeys spherical evolution. Flow, regularity, speed differentiability,
and angular orthogonality are derived from the geodesic solution family. -/
theorem hasDerivAt_geodesic_normal_ray_metric
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hα : ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ r ∈ Metric.ball 0 δ, (α (q, r)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, r))) r)
    {z : E} (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ)
    {u : E} {s : ℝ} (hs : 0 < s) (hq : (z, s • u) ∈ V)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c z (s • u) (s • u)) * t ∈ Ioo 0 Real.pi)
    {w v : E}
    (hw : coordinateMetricBilinear (I := I) c z u w = 0)
    (hv : coordinateMetricBilinear (I := I) c z u v = 0) :
    let φ := fun q : E × ℝ => (α ((z, q.2 • q.1), t)).1
    let freq := Real.sqrt K * (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u))
    HasDerivAt (fun r => coordinateMetricBilinear (I := I) c (φ (u, r))
      (fderiv ℝ φ (u, r) (w, 0)) (fderiv ℝ φ (u, r) (v, 0)))
      (2 * (freq * (Real.cos (freq * s) / Real.sin (freq * s))) *
          coordinateMetricBilinear (I := I) c (φ (u, s))
            (fderiv ℝ φ (u, s) (w, 0)) (fderiv ℝ φ (u, s) (v, 0))) s := by
  let φ := fun q : E × ℝ => (α ((z, q.2 • q.1), t)).1
  let x := (extChartAt I c).symm (φ (u, s))
  let g := coordinateMetricBilinear (I := I) c z
  let σ := fun y : E => t * Real.sqrt (g y y)
  let U : Set (E × ℝ) := {q | 0 < q.2} ∩ {q | (z, q.2 • q.1) ∈ V} ∩
    {q | Real.sqrt (K * g (q.2 • q.1) (q.2 • q.1)) * t ∈ Ioo 0 Real.pi}
  have hc : Continuous (fun q : E × ℝ => q.2 • q.1) := continuous_snd.smul continuous_fst
  have hgc : Continuous (fun q : E × ℝ => g (q.2 • q.1) (q.2 • q.1)) :=
    (g.continuous.comp hc).clm_apply hc
  have hpc : Continuous (fun q : E × ℝ => Real.sqrt (K * g (q.2 • q.1) (q.2 • q.1)) * t) :=
    (Real.continuous_sqrt.comp (continuous_const.mul hgc)).mul continuous_const
  have hU : IsOpen U :=
    ((isOpen_lt continuous_const continuous_snd).inter
      (hV.preimage (continuous_const.prodMk hc))).inter (isOpen_Ioo.preimage hpc)
  have hpt : (u, s) ∈ U := ⟨⟨hs, hq⟩, hphase⟩
  have hdata : ∀ q ∈ U, 0 < q.2 ∧ (z, q.2 • q.1) ∈ V ∧
      Real.sqrt (K * g (q.2 • q.1) (q.2 • q.1)) * t ∈ Ioo 0 Real.pi :=
    fun q h => ⟨h.1.1, h.1.2, h.2⟩
  have hα1 := hα.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hφ : ContDiffOn ℝ 2 φ U := by
    intro q hqU
    have hi : ContDiffAt ℝ 2 (fun q : E × ℝ => ((z, q.2 • q.1), t)) q :=
      (contDiffAt_const.prodMk (contDiffAt_snd.smul contDiffAt_fst)).prodMk contDiffAt_const
    exact (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds
      ⟨(hdata q hqU).2.1, htime⟩)).comp q hi).fst).contDiffWithinAt
  have hode : ∀ q ∈ U, HasDerivAt (fun r => φ (q.1, r))
      (σ q.1 • coordinateVectorField c (gradient (I := I) (obataRadial K a f)) (φ q)) q.2 := by
    intro q hqU
    exact hasDerivAt_geodesic_normal_ray b hf hK ha hH c hV hα1 hsol
      (hdata q hqU).1 (hdata q hqU).2.1 hcrit hmax htime (hdata q hqU).2.2
  have henergy : g u u ≠ 0 := by
    intro he
    have hz : g (s • u) (s • u) = 0 := by
      simp only [map_smul, smul_apply, smul_eq_mul, he, mul_zero]
    have hp := hphase.1
    change 0 < Real.sqrt (K * g (s • u) (s • u)) * t at hp
    simp only [hz, mul_zero, Real.sqrt_zero, zero_mul, lt_self_iff_false] at hp
  have hσ : DifferentiableAt ℝ σ u :=
    ((g.differentiableAt.clm_apply differentiableAt_id).sqrt henergy).const_mul t
  have hpoint := ((hsol _ hq).2 t htime).1
  have hx : x ∈ (chartAt H c).source := by
    simpa [x, φ] using (extChartAt I c).map_target hpoint
  have hpos : φ (u, s) = extChartAt I c x := ((extChartAt I c).right_inv hpoint).symm
  have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg htime
  have hinit := (hsol _ hq).1
  have hreg := coordinate_geodesic_obata_regular (α := fun r => α ((z, s • u), r))
    LC leviCivitaConnection_metricCompatible b hf hK.le ha hH c Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
    (fun r hr => ((hsol _ hq).2 r hr).1) (fun r hr => ((hsol _ hq).2 r hr).2)
    (by rw [hinit]; exact hcrit) (by rw [hinit]; exact hmax)
    htime (by rw [hinit]; exact hphase)
  have hd := hasDerivAt_scaled_radial_flow_metric hK ha hf hb hH b c x hx hreg
    hU hφ hode hpt hpos hσ w v
    (geodesic_normal_ray_spatial_orthogonal b hf hK ha hH c hV hα1 hsol
      hq hcrit hmax htime hphase hw)
    (geodesic_normal_ray_spatial_orthogonal b hf hK ha hH c hV hα1 hsol
      hq hcrit hmax htime hphase hv)
  have ht0 : 0 ≤ t := by
    nlinarith [Real.sqrt_nonneg (K * g (s • u) (s • u)), hphase.1]
  have hr := coordinate_geodesic_obataRadial_eq (α := fun r => α ((z, s • u), r))
    LC leviCivitaConnection_metricCompatible b hf hK ha hH c Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
    (fun r hr => ((hsol _ hq).2 r hr).1) (fun r hr => ((hsol _ hq).2 r hr).2)
    (by rw [hinit]; exact hcrit) (by rw [hinit]; exact hmax)
    htime ht0 (by rw [hinit]; exact hphase.2.le)
  rw [hinit] at hr
  change obataRadial K a f x = Real.sqrt (g (s • u) (s • u)) * t at hr
  have hscale : Real.sqrt (g (s • u) (s • u)) = s * Real.sqrt (g u u) := by
    have he : g (s • u) (s • u) = s ^ 2 * g u u := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [he, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  have harg : Real.sqrt K * obataRadial K a f x = (Real.sqrt K * σ u) * s := by
    rw [hr, hscale]
    dsimp only [σ]
    ring
  rw [harg] at hd
  convert hd using 1
  dsimp only [σ, g]
  ring

/-- The sine-square-normalized angular metric of the actual normal map
is constant on each connected open positive-phase ray interval. -/
theorem geodesic_normal_ray_metric_sine_squared_normalized_eq
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hα : ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ r ∈ Metric.ball 0 δ, (α (q, r)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, r))) r)
    {z : E} (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) {u : E}
    {T : Set ℝ} (hT : IsOpen T) (hconn : IsPreconnected T)
    (hdata : ∀ r ∈ T, 0 < r ∧ (z, r • u) ∈ V ∧
      Real.sqrt (K * coordinateMetricBilinear (I := I) c z (r • u) (r • u)) * t ∈ Ioo 0 Real.pi)
    {w v : E} (hw : coordinateMetricBilinear (I := I) c z u w = 0)
    (hv : coordinateMetricBilinear (I := I) c z u v = 0)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ T) (hs₂ : s₂ ∈ T) :
    let φ := fun q : E × ℝ => (α ((z, q.2 • q.1), t)).1
    let freq := Real.sqrt K * (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u))
    let Q := fun r => coordinateMetricBilinear (I := I) c (φ (u, r))
      (fderiv ℝ φ (u, r) (w, 0)) (fderiv ℝ φ (u, r) (v, 0))
    Q s₁ / Real.sin (freq * s₁) ^ 2 = Q s₂ / Real.sin (freq * s₂) ^ 2 := by
  let g := coordinateMetricBilinear (I := I) c z
  let freq := Real.sqrt K * (t * Real.sqrt (g u u))
  apply sine_squared_normalized_eq_on hT hconn (freq := freq) _ _ hs₁ hs₂
  · intro r hr
    have hs := (hdata r hr).1
    have he : g (r • u) (r • u) = r ^ 2 * g u u := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hscale : Real.sqrt (g (r • u) (r • u)) = r * Real.sqrt (g u u) := by
      rw [he, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hs.le]
    have harg : Real.sqrt (K * g (r • u) (r • u)) * t = freq * r := by
      rw [Real.sqrt_mul hK.le, hscale]
      dsimp only [freq]
      ring
    exact harg ▸ (hdata r hr).2.2
  · intro r hr
    exact hasDerivAt_geodesic_normal_ray_metric b hf hK ha hb hH c hV hα hsol
      hcrit hmax htime (hdata r hr).1 (hdata r hr).2.1 (hdata r hr).2.2 hw hv

end LichnerowiczObata
