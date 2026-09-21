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

/-! # Conservation of the actual metric energy of coordinate geodesics -/

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

/-- Metric compatibility and the actual geodesic equation imply vanishing
derivative of squared speed in the coordinate metric. -/
theorem hasDerivAt_coordinate_geodesic_energy
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α : ℝ → E × E} {t : ℝ} (hz : (α t).1 ∈ (extChartAt I c).target)
    (hα : HasDerivAt α (coordinateGeodesicSpray cov b c (α t)) t) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (α s).1 (α s).2 (α s).2)
      0 t := by
  let x := (extChartAt I c).symm (α t).1
  have hx : x ∈ (chartAt H c).source := by
    simpa [x] using (extChartAt I c).map_target hz
  have hpos : (α t).1 = extChartAt I c x :=
    ((extChartAt I c).right_inv hz).symm
  have hp : HasDerivAt (fun s => (α s).1) (α t).2 t :=
    (hasFDerivAt_fst (p := α t)).comp_hasDerivAt t hα
  have hv : HasDerivAt (fun s => (α s).2)
      (-(frameConnectionCoefficients cov (trivializationAt E TM c) b x
        (α t).2 (α t).2)) t :=
    (hasFDerivAt_snd (p := α t)).comp_hasDerivAt t hα
  have he := hasDerivAt_coordinateMetric_pairing_connection cov hm b c x hx hpos hp hv hv
  simpa using he

/-- Squared speed is constant on a connected open domain of a coordinate
geodesic; no separate energy-conservation assumption is needed. -/
theorem coordinate_geodesic_energy_eq
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α : ℝ → E × E} {T : Set ℝ} (hT : IsOpen T) (hconn : IsPreconnected T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    {s t : ℝ} (hs : s ∈ T) (ht : t ∈ T) :
    coordinateMetricBilinear (I := I) c (α s).1 (α s).2 (α s).2 =
      coordinateMetricBilinear (I := I) c (α t).1 (α t).2 (α t).2 := by
  have hd := fun s hs => hasDerivAt_coordinate_geodesic_energy cov hm b c (hz s hs) (hα s hs)
  exact hT.is_const_of_deriv_eq_zero hconn
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) hs ht

omit [I.Boundaryless] [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Rescaling time and velocity preserves the actual coordinate geodesic
equation, by bilinearity of the connection's acceleration term. -/
theorem hasDerivAt_coordinate_geodesic_rescale
    (cov : CovariantDerivative I E TM)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α : ℝ → E × E} (r : ℝ) {t : ℝ}
    (hα : HasDerivAt α (coordinateGeodesicSpray cov b c (α (r * t))) (r * t)) :
    HasDerivAt (fun s => ((α (r * s)).1, r • (α (r * s)).2))
      (coordinateGeodesicSpray cov b c ((α (r * t)).1, r • (α (r * t)).2)) t := by
  have hp : HasDerivAt (fun s => (α s).1) (α (r * t)).2 (r * t) :=
    (hasFDerivAt_fst (p := α (r * t))).comp_hasDerivAt (r * t) hα
  have hv : HasDerivAt (fun s => (α s).2)
      (-(coordinateConnection cov b c (α (r * t)).1 (α (r * t)).2 (α (r * t)).2))
      (r * t) :=
    (hasFDerivAt_snd (p := α (r * t))).comp_hasDerivAt (r * t) hα
  have htime := (hasDerivAt_id t).const_mul r
  have hd := (hp.scomp t htime).prodMk ((hv.scomp t htime).const_smul r)
  convert hd using 1 <;> first | rfl |
    simp [coordinateGeodesicSpray, coordinateConnection, map_smul, smul_smul]

end LichnerowiczObata
