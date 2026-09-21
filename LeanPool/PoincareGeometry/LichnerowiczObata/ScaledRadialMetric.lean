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

public import LeanPool.PoincareGeometry.LichnerowiczObata.CoordinateRadialShape

/-! # Angular metric evolution for parameter-dependent radial speeds -/

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
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- Angular metric evolution is unchanged by longitudinal speed variations.
The scalar speed multiplies the spherical shape coefficient. -/
theorem hasDerivAt_coordinate_scaled_radial_metric
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (hreg : -a < f x ∧ f x < a)
    {z u w : ℝ → E} {t σ d e : ℝ} (hz : z t = extChartAt I c x)
    (hd : HasDerivAt z (σ • coordinateVectorField c (gradient (I := I) (obataRadial K a f)) (z t)) t)
    (hu : HasDerivAt u
      (σ • fderiv ℝ (coordinateVectorField c (gradient (I := I) (obataRadial K a f))) (z t) (u t) +
        d • coordinateVectorField c (gradient (I := I) (obataRadial K a f)) (z t)) t)
    (hw : HasDerivAt w
      (σ • fderiv ℝ (coordinateVectorField c (gradient (I := I) (obataRadial K a f))) (z t) (w t) +
        e • coordinateVectorField c (gradient (I := I) (obataRadial K a f)) (z t)) t)
    (hTu : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (u t)) = 0)
    (hTw : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (w t)) = 0) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (z s) (u s) (w s))
      (2 * σ * (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) *
          coordinateMetricBilinear (I := I) c (z t) (u t) (w t)) t := by
  let N := gradient (I := I) (obataRadial K a f)
  let n := (trivializationAt E TM c).continuousLinearMapAt ℝ x (N x)
  let Γ := frameConnectionCoefficients LC (trivializationAt E TM c) b x
  let k := Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
    Real.sin (Real.sqrt K * obataRadial K a f x))
  have he : (extChartAt I c).symm (z t) = x := by
    rw [hz]
    exact (extChartAt I c).left_inv (by simpa using hx)
  have hn : coordinateVectorField (I := I) c N (z t) = n := by
    unfold coordinateVectorField
    convert congrArg (fun y : M => (trivializationAt E TM c).continuousLinearMapAt ℝ y (N y)) he using 1
  have hsu := coordinate_obataRadial_shape hK ha hf hb hH b c x hx hreg (u t) hTu
  have hsw := coordinate_obataRadial_shape hK ha hf hb hH b c x hx hreg (w t) hTw
  change fderiv ℝ (coordinateVectorField c N) (extChartAt I c x) (u t) + Γ n (u t) = k • u t at hsu
  change fderiv ℝ (coordinateVectorField c N) (extChartAt I c x) (w t) + Γ n (w t) = k • w t at hsw
  have hshape (j : E) (a' : ℝ)
      (hj : fderiv ℝ (coordinateVectorField c N) (extChartAt I c x) j + Γ n j = k • j) :
      (σ • fderiv ℝ (coordinateVectorField c N) (z t) j + a' • n) + Γ (σ • n) j =
        (σ * k) • j + a' • n := by
    rw [hz, map_smul, smul_apply]
    calc
      _ = σ • (fderiv ℝ (coordinateVectorField c N) (extChartAt I c x) j + Γ n j) + a' • n := by
        simp only [smul_add]
        abel
      _ = _ := by rw [hj, smul_smul]
  have hpair := hasDerivAt_coordinateMetric_pairing_connection LC
    leviCivitaConnection_metricCompatible b c x hx hz hd hu hw
  change HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (z s) (u s) (w s))
    (coordinateMetricBilinear (I := I) c (z t)
      ((σ • fderiv ℝ (coordinateVectorField c N) (z t) (u t) + d • coordinateVectorField c N (z t)) +
        Γ (σ • coordinateVectorField c N (z t)) (u t)) (w t) +
      coordinateMetricBilinear (I := I) c (z t) (u t)
      ((σ • fderiv ℝ (coordinateVectorField c N) (z t) (w t) + e • coordinateVectorField c N (z t)) +
        Γ (σ • coordinateVectorField c N (z t)) (w t))) t at hpair
  rw [hn, hshape (u t) d hsu, hshape (w t) e hsw] at hpair
  have hNw : coordinateMetricBilinear (I := I) c (z t) n (w t) = 0 := by
    rw [coordinateMetricBilinear_apply, he]
    simpa only [n, (trivializationAt E TM c).symmL_continuousLinearMapAt hx] using hTw
  have huN : coordinateMetricBilinear (I := I) c (z t) (u t) n = 0 := by
    rw [coordinateMetricBilinear_apply, he]
    simpa only [n, (trivializationAt E TM c).symmL_continuousLinearMapAt hx, real_inner_comm] using hTu
  convert hpair using 1
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul, hNw, huN, mul_zero, add_zero]
  dsimp [k]
  ring

/-- Spatial derivatives of a C2 radial flow with parameter-dependent
speed obey spherical angular metric evolution. Their variational equations
and the cancellation of longitudinal terms are conclusions. -/
theorem hasDerivAt_scaled_radial_flow_metric
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (hreg : -a < f x ∧ f x < a)
    {φ : E × ℝ → E} {σ : E → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hode : ∀ q ∈ U, HasDerivAt (fun s => φ (q.1, s))
      (σ q.1 • coordinateVectorField c (gradient (I := I) (obataRadial K a f)) (φ q)) q.2)
    {y : E} {t : ℝ} (hpt : (y, t) ∈ U) (hpos : φ (y, t) = extChartAt I c x)
    (hσ : DifferentiableAt ℝ σ y) (u w : E)
    (hTu : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (fderiv ℝ φ (y, t) (u, 0))) = 0)
    (hTw : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (fderiv ℝ φ (y, t) (w, 0))) = 0) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (φ (y, s))
      (fderiv ℝ φ (y, s) (u, 0)) (fderiv ℝ φ (y, s) (w, 0)))
      (2 * σ y * (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) *
          coordinateMetricBilinear (I := I) c (φ (y, t))
            (fderiv ℝ φ (y, t) (u, 0)) (fderiv ℝ φ (y, t) (w, 0))) t := by
  have hlo : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hreg.1])
  have hhi : f x / a < 1 := (div_lt_iff₀ ha).2 (by nlinarith [hreg.2])
  have hN := mdifferentiableAt_gradient (contMDiffAt_obataRadial (K := K) (hf x) hlo.ne' hhi.ne)
  have hNv : DifferentiableAt ℝ
      (coordinateVectorField c (gradient (I := I) (obataRadial K a f))) (φ (y, t)) := by
    rw [hpos]
    exact differentiableAt_coordinateVectorField _ c x hx hN
  have hu := hasDerivAt_scaled_flow_variation hU hφ hode hpt hσ hNv u
  have hw := hasDerivAt_scaled_flow_variation hU hφ hode hpt hσ hNv w
  exact hasDerivAt_coordinate_scaled_radial_metric hK ha hf hb hH b c x hx hreg hpos
    (hode (y, t) hpt) hu hw hTu hTw

end LichnerowiczObata
