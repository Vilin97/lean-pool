/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicGauss
public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalRays

/-! # The radial flow equation for geodesic normal rays -/

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

/-- Rays in the actual normal endpoint map follow the radial gradient,
with speed equal to endpoint time times initial metric norm. The equation
is derived from the geodesic family, not assumed as flow data. -/
theorem hasDerivAt_geodesic_normal_ray
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hα : ContDiffOn ℝ 1 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ r ∈ Metric.ball 0 δ, (α (q, r)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, r))) r)
    {z u : E} {s : ℝ} (hs : 0 < s) (hq : (z, s • u) ∈ V)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c z (s • u) (s • u)) * t ∈ Ioo 0 Real.pi) :
    HasDerivAt (fun r : ℝ => (α ((z, r • u), t)).1)
      ((t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u)) •
        coordinateVectorField c (gradient (I := I) (obataRadial K a f))
          (α ((z, s • u), t)).1) s := by
  let F : E → E := fun v => (α ((z, v), t)).1
  let x := (extChartAt I c).symm (F (s • u))
  let g := coordinateMetricBilinear (I := I) c z
  let N := gradient (I := I) (obataRadial K a f)
  have hpoint := ((hsol _ hq).2 t htime).1
  have hx : x ∈ (chartAt H c).source := by
    simpa [x, F] using (extChartAt I c).map_target hpoint
  have hi : ContDiffAt ℝ 1 (fun v : E => ((z, v), t)) (s • u) :=
    (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
  have hF : DifferentiableAt ℝ F (s • u) :=
    (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds ⟨hq, htime⟩)).comp
      (s • u) hi).fst).differentiableAt (by norm_num)
  have hscale : Real.sqrt (g (s • u) (s • u)) = s * Real.sqrt (g u u) := by
    have he : g (s • u) (s • u) = s ^ 2 * g u u := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [he, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  have hrad := coordinate_normal_endpoint_radial_gradient b hf hK ha hH c
    hV hα hsol hq hcrit hmax htime hphase
  change (trivializationAt E TM c).symmL ℝ x (fderiv ℝ F (s • u) (s • u)) =
    (t * Real.sqrt (g (s • u) (s • u))) • N x at hrad
  have he := congrArg ((trivializationAt E TM c).continuousLinearMapAt ℝ x) hrad
  rw [(trivializationAt E TM c).continuousLinearMapAt_symmL hx, map_smul, hscale] at he
  have hcoord : fderiv ℝ F (s • u) (s • u) =
      (s * (t * Real.sqrt (g u u))) • coordinateVectorField c N (F (s • u)) := by
    simpa only [coordinateVectorField, x, map_smul, mul_left_comm t s] using he
  exact hasDerivAt_normal_ray_of_radial hF hs.ne' hcoord

/-- An initial angular direction gives an actual spatial ray variation
orthogonal to the radial gradient. This derives the orthogonality input
of metric evolution from the Gauss lemma. -/
theorem geodesic_normal_ray_spatial_orthogonal
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hα : ContDiffOn ℝ 1 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ r ∈ Metric.ball 0 δ, (α (q, r)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, r))) r)
    {z u : E} {s : ℝ} (hq : (z, s • u) ∈ V)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c z (s • u) (s • u)) * t ∈ Ioo 0 Real.pi)
    {w : E} (hw : coordinateMetricBilinear (I := I) c z u w = 0) :
    let φ := fun p : E × ℝ => (α ((z, p.2 • p.1), t)).1
    let x := (extChartAt I c).symm (φ (u, s))
    inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (fderiv ℝ φ (u, s) (w, 0))) = 0 := by
  let F : E → E := fun v => (α ((z, v), t)).1
  let x := (extChartAt I c).symm (F (s • u))
  let g := coordinateMetricBilinear (I := I) c z
  let L := (trivializationAt E TM c).symmL ℝ x
  let N := gradient (I := I) (obataRadial K a f) x
  have hi : ContDiffAt ℝ 1 (fun v : E => ((z, v), t)) (s • u) :=
    (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
  have hF : DifferentiableAt ℝ F (s • u) :=
    (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds ⟨hq, htime⟩)).comp
      (s • u) hi).fst).differentiableAt (by norm_num)
  have hgauss := coordinate_normal_endpoint_gauss b hf hK ha hH c hV hα hsol
    hq hcrit hmax htime hphase w
  have hrad := coordinate_normal_endpoint_radial_gradient b hf hK ha hH c
    hV hα hsol hq hcrit hmax htime hphase
  change L (fderiv ℝ F (s • u) (s • u)) =
    (t * Real.sqrt (g (s • u) (s • u))) • N at hrad
  change inner ℝ (L (fderiv ℝ F (s • u) (s • u)))
    (L (fderiv ℝ F (s • u) w)) = t ^ 2 * g (s • u) w at hgauss
  have hang : g (s • u) w = 0 := by
    change coordinateMetricBilinear (I := I) c z (s • u) w = 0
    simp only [map_smul, smul_apply, hw, smul_zero]
  rw [hrad, real_inner_smul_left, hang, mul_zero] at hgauss
  have hp := hphase.1
  change 0 < Real.sqrt (K * g (s • u) (s • u)) * t at hp
  rw [Real.sqrt_mul hK.le] at hp
  have hr : t * Real.sqrt (g (s • u) (s • u)) ≠ 0 := by
    intro hz
    have he : Real.sqrt K * Real.sqrt (g (s • u) (s • u)) * t = 0 := by
      calc
        _ = Real.sqrt K * (t * Real.sqrt (g (s • u) (s • u))) := by ring
        _ = 0 := by rw [hz, mul_zero]
    linarith
  have horth : inner ℝ N (L (fderiv ℝ F (s • u) w)) = 0 :=
    (mul_eq_zero.mp hgauss).resolve_left hr
  change inner ℝ N (L (fderiv ℝ (fun p : E × ℝ => F (p.2 • p.1)) (u, s) (w, 0))) = 0
  rw [fderiv_normal_ray_spatial hF, map_smul, real_inner_smul_right, horth, mul_zero]

end LichnerowiczObata
