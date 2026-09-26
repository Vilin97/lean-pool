/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.Geodesic
public import LeanPool.PoincareGeometry.BonnetMyers.ODEContinuation
public import LeanPool.PoincareGeometry.BonnetMyers.Transport

/-!
# Coordinate endpoint continuation for geodesics

The generic ODE restart theorem is specialized here to the chart-valued
second-order equation used for a local geodesic.  This is deliberately a
coordinate endpoint result: the separate geometric layer must still show that
the recharted base point and velocity have a joint limit.  Once it has, this
file supplies the actual new chart solution and its overlap with the old one.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
open scoped Bundle Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- Shrink an ordinary coordinate solution around its initial state until its
position component stays in the target of the chosen extended chart. -/
noncomputable def LocalSecondOrderSolution.toLocalChartSecondOrderSolution
    {F : E → E → E} {x₀ : M} {v₀ : E}
    (sol : LocalSecondOrderSolution F (extChartAt I x₀ x₀) v₀) :
    LocalChartSecondOrderSolution I F x₀ v₀ := by
  let e := extChartAt I x₀
  have htarget : e.target ∈ 𝓝 (e x₀) :=
    (isOpen_extChartAt_target (I := I) x₀).mem_nhds
      (mem_extChartAt_target (I := I) x₀)
  have hcurve0 : sol.curve 0 = e x₀ := by
    simpa [e] using sol.initial_curve
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hcont : ContinuousAt sol.curve 0 :=
    (sol.curve_hasDeriv 0 hzero).continuousAt
  have hpre : sol.curve ⁻¹' e.target ∈ 𝓝 (0 : ℝ) := by
    rw [← hcurve0] at htarget
    exact hcont.preimage_mem_nhds htarget
  let hball : ∃ δ > 0, Metric.ball (0 : ℝ) δ ⊆ sol.curve ⁻¹' e.target :=
    Metric.mem_nhds_iff.mp hpre
  let δ : ℝ := Classical.choose hball
  have hδ : 0 < δ := (Classical.choose_spec hball).1
  have hδsub : Metric.ball (0 : ℝ) δ ⊆ sol.curve ⁻¹' e.target :=
    (Classical.choose_spec hball).2
  let r : ℝ := min sol.radius (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min sol.radius_pos (by linarith)
  exact
    { coordinate := sol.curve
      velocity := sol.velocity
      radius := r
      radius_pos := hr
      coordinate_initial := sol.initial_curve
      velocity_initial := sol.initial_velocity
      coordinate_hasDeriv := by
        intro t ht
        apply sol.curve_hasDeriv t
        have hmin : r ≤ sol.radius := min_le_left _ _
        constructor <;> linarith [ht.1, ht.2]
      velocity_hasDeriv := by
        intro t ht
        apply sol.velocity_hasDeriv t
        have hmin : r ≤ sol.radius := min_le_left _ _
        constructor <;> linarith [ht.1, ht.2]
      coordinate_mem_target := by
        intro t ht
        apply hδsub
        rw [Metric.mem_ball]
        have hmin : r ≤ δ / 2 := min_le_right _ _
        have habs : |t| < r := by
          rw [abs_lt]
          constructor <;> linarith [ht.1, ht.2]
        have habsδ : |t - 0| < δ := by
          rw [sub_zero]
          linarith
        exact habsδ }

/-- A chart-coordinate second-order solution whose state converges at a
finite left endpoint restarts as an actual `LocalChartSecondOrderSolution` in
the endpoint chart. -/
theorem exists_localChartSecondOrderSolution_eventuallyEq_left_of_tendsto
    {F : E → E → E} {x₀ : M} {v₀ : E} {z u : ℝ → E} {b : ℝ}
    (hF : ContDiffAt ℝ 1 (fun q : E × E ↦ secondOrderSystem F q)
      (extChartAt I x₀ x₀, v₀))
    (hderiv : ∀ t ∈ Iio b,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem F (z t, u t)) t)
    (hlim : Tendsto (fun t ↦ (z t, u t)) (𝓝[<] b)
      (𝓝 (extChartAt I x₀ x₀, v₀))) :
    ∃ sol : LocalChartSecondOrderSolution I F x₀ v₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] b]
        (fun t ↦ (sol.coordinate (t - b), sol.velocity (t - b))) := by
  obtain ⟨sol, hsol⟩ := exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto
    hF hderiv hlim
  refine ⟨sol.toLocalChartSecondOrderSolution, ?_⟩
  filter_upwards [hsol] with t ht
  simpa [LocalSecondOrderSolution.toLocalChartSecondOrderSolution] using ht

/-- A coordinate geodesic whose position converges in its endpoint chart and
whose coordinate acceleration is bounded has a full endpoint state and hence
restarts as an actual chart solution.  This is the form needed after the
geometric continuation argument has placed the tail of a geodesic in one
endpoint chart and obtained a bound on the Christoffel acceleration there. -/
theorem exists_localChartGeodesicSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₀ : M} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {z u : ℝ → E} {t₀ C : ℝ}
    (hderiv : ∀ t ∈ Iio t₀,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov x₀ b)
          (z t, u t)) t)
    (hzlim : Tendsto z (𝓝[<] t₀) (𝓝 (extChartAt I x₀ x₀)))
    (hC : 0 ≤ C)
    (hacc : ∀ t ∈ Iio t₀,
      ‖LocalGeodesicData.coordinateAcceleration cov x₀ b (z t) (u t)‖ ≤ C) :
    ∃ u₀ : E, ∃ sol : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] t₀]
        (fun t ↦ (sol.coordinate (t - t₀), sol.velocity (t - t₀))) := by
  obtain ⟨u₀, sol, hsol⟩ :=
    exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound
      (F := LocalGeodesicData.coordinateAcceleration cov x₀ b)
      (z₀ := extChartAt I x₀ x₀)
      (fun u₀ ↦ LocalGeodesicData.coordinateAcceleration_system_contDiffAt
        (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) u₀)
      hderiv hzlim hC hacc
  refine ⟨u₀, sol.toLocalChartSecondOrderSolution, ?_⟩
  filter_upwards [hsol] with t ht
  simpa [LocalSecondOrderSolution.toLocalChartSecondOrderSolution] using ht

/-- The chart-geodesic endpoint restart only needs a coordinate acceleration
bound on the final left tail.  This matches the output of a compact
endpoint-chart argument and avoids imposing a spurious global chart bound. -/
theorem exists_localChartGeodesicSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound_eventually
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₀ : M} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {z u : ℝ → E} {t₀ C : ℝ}
    (hderiv : ∀ t ∈ Iio t₀,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov x₀ b)
          (z t, u t)) t)
    (hzlim : Tendsto z (𝓝[<] t₀) (𝓝 (extChartAt I x₀ x₀)))
    (hC : 0 ≤ C)
    (hacc : ∀ᶠ t in 𝓝[<] t₀,
      ‖LocalGeodesicData.coordinateAcceleration cov x₀ b (z t) (u t)‖ ≤ C) :
    ∃ u₀ : E, ∃ sol : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] t₀]
        (fun t ↦ (sol.coordinate (t - t₀), sol.velocity (t - t₀))) := by
  obtain ⟨u₀, sol, hsol⟩ :=
    exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound_eventually
      (F := LocalGeodesicData.coordinateAcceleration cov x₀ b)
      (z₀ := extChartAt I x₀ x₀)
      (fun u₀ ↦ LocalGeodesicData.coordinateAcceleration_system_contDiffAt
        (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) u₀)
      hderiv hzlim hC hacc
  refine ⟨u₀, sol.toLocalChartSecondOrderSolution, ?_⟩
  filter_upwards [hsol] with t ht
  simpa [LocalSecondOrderSolution.toLocalChartSecondOrderSolution] using ht

/-- The chart-geodesic endpoint restart only needs the coordinate equation on
the final tail, as happens when a maximal intrinsic geodesic is recharted at
its finite endpoint. -/
theorem exists_localChartGeodesicSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound_eventually_deriv
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₀ : M} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {z u : ℝ → E} {t₀ C : ℝ}
    (hderiv : ∀ᶠ t in 𝓝[<] t₀,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov x₀ b)
          (z t, u t)) t)
    (hzlim : Tendsto z (𝓝[<] t₀) (𝓝 (extChartAt I x₀ x₀)))
    (hC : 0 ≤ C)
    (hacc : ∀ᶠ t in 𝓝[<] t₀,
      ‖LocalGeodesicData.coordinateAcceleration cov x₀ b (z t) (u t)‖ ≤ C) :
    ∃ u₀ : E, ∃ sol : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] t₀]
        (fun t ↦ (sol.coordinate (t - t₀), sol.velocity (t - t₀))) := by
  obtain ⟨u₀, sol, hsol⟩ :=
    exists_localSecondOrderSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound_eventually_deriv
      (F := LocalGeodesicData.coordinateAcceleration cov x₀ b)
      (z₀ := extChartAt I x₀ x₀)
      (fun u₀ ↦ LocalGeodesicData.coordinateAcceleration_system_contDiffAt
        (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) u₀)
      hderiv hzlim hC hacc
  refine ⟨u₀, sol.toLocalChartSecondOrderSolution, ?_⟩
  filter_upwards [hsol] with t ht
  simpa [LocalSecondOrderSolution.toLocalChartSecondOrderSolution] using ht

/-- Once a coordinate curve converges to the centre of an endpoint chart and
its coordinate velocity is eventually bounded, compactness of a small
coordinate state box gives an eventual bound on the actual geodesic
acceleration. -/
theorem exists_eventually_norm_coordinateAcceleration_le_of_tendsto_of_norm_velocity_eventually_le
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₀ : M} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {z u : ℝ → E} {t₀ B : ℝ}
    (hzlim : Tendsto z (𝓝[<] t₀) (𝓝 (extChartAt I x₀ x₀)))
    (hu : ∀ᶠ t in 𝓝[<] t₀, ‖u t‖ ≤ B) :
    ∃ C > (0 : ℝ), ∀ᶠ t in 𝓝[<] t₀,
      ‖LocalGeodesicData.coordinateAcceleration cov x₀ b (z t) (u t)‖ ≤ C := by
  have htarget : (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ x₀) :=
    (isOpen_extChartAt_target (I := I) x₀).mem_nhds
      (mem_extChartAt_target (I := I) x₀)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp htarget
  let r : ℝ := δ / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hKtarget : ∀ w ∈ Metric.closedBall (extChartAt I x₀ x₀) r,
      w ∈ (extChartAt I x₀).target := by
    intro w hw
    apply hδsub
    rw [Metric.mem_ball]
    have hle : dist w (extChartAt I x₀ x₀) ≤ r := Metric.mem_closedBall.mp hw
    calc
      dist w (extChartAt I x₀ x₀) ≤ r := hle
      _ < δ := by dsimp [r]; linarith
  obtain ⟨C, hC, hbound⟩ :=
    LocalGeodesicData.exists_pos_norm_le_coordinateAcceleration_on_isCompact_prod
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
      (Metric.closedBall (extChartAt I x₀ x₀) r) (Metric.closedBall (0 : E) B)
      (isCompact_closedBall _ _) (isCompact_closedBall _ _) hKtarget
  have hzK : ∀ᶠ t in 𝓝[<] t₀,
      z t ∈ Metric.closedBall (extChartAt I x₀ x₀) r := by
    filter_upwards [hzlim (Metric.ball_mem_nhds (extChartAt I x₀ x₀) hr)] with t ht
    exact Metric.mem_closedBall.mpr ht.le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hzK, hu] with t hzt hut
  apply hbound (z t) hzt (u t)
  simpa [Metric.mem_closedBall, dist_zero_right, dist_zero_left] using hut

/-- A bounded intrinsic velocity has bounded coordinates in every endpoint
chart.  The estimate uses the locally bounded tangent-bundle trivialization,
and the frame identity makes the resulting coordinate vector exact. -/
theorem exists_eventually_norm_coordinateVelocity_le_of_tendsto_of_frame_velocity_bound
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    {x₀ : M} {t₀ A : ℝ} {γ : ℝ → M}
    {v : ∀ t, TangentSpace I (γ t)} {u : ℝ → E}
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hγ : Tendsto γ (𝓝[<] t₀) (𝓝 x₀))
    (hframe : ∀ᶠ t in 𝓝[<] t₀,
      v t = LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := x₀) b (u t) (γ t))
    (hvelocity : ∀ᶠ t in 𝓝[<] t₀, ‖v t‖ ≤ A) :
    ∃ B > (0 : ℝ), ∀ᶠ t in 𝓝[<] t₀, ‖u t‖ ≤ B := by
  obtain ⟨C, hC, hmap⟩ :=
    eventually_norm_trivializationAt_lt E (TangentSpace I : M → Type _) x₀
  let B : ℝ := (C + 1) * (max A 0 + 1)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hsource : (chartAt H x₀).source ∈ 𝓝 x₀ := chart_source_mem_nhds H x₀
  let e := trivializationAt E (fun x : M ↦ TangentSpace I x) x₀
  refine ⟨B, hB, ?_⟩
  filter_upwards [hγ hmap, hγ hsource, hframe, hvelocity]
    with t htmap hsrc hframe htvelocity
  change ‖e.continuousLinearMapAt ℝ (γ t)‖ < C at htmap
  have hread : e.continuousLinearMapAt ℝ (γ t) (v t) = u t := by
    dsimp [e]
    rw [hframe,
      LocalGeodesicData.coordinateFrameCombination_eq_symmL
        (I := I) (M := M) (x₀ := x₀) b hsrc (u t)]
    exact (trivializationAt E (fun x : M ↦ TangentSpace I x) x₀)
      |>.continuousLinearMapAt_symmL hsrc (u t)
  rw [← hread]
  calc
    ‖e.continuousLinearMapAt ℝ (γ t) (v t)‖ ≤
        ‖e.continuousLinearMapAt ℝ (γ t)‖ * ‖v t‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (C + 1) * (max A 0 + 1) := by
      apply mul_le_mul
      · exact le_of_lt (by linarith [htmap])
      · exact le_trans htvelocity (by linarith [le_max_left A 0])
      · exact norm_nonneg _
      · exact le_of_lt (by linarith [hC])

/-- An intrinsic finite-speed tail represented in the endpoint chart supplies
all state bounds required to restart the coordinate geodesic. -/
theorem exists_localChartGeodesicSolution_eventuallyEq_left_of_intrinsic_tendsto_of_norm_velocity_eventually_le
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₀ : M} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {z u : ℝ → E} {t₀ A : ℝ} {γ : ℝ → M}
    {v : ∀ t, TangentSpace I (γ t)}
    (hderiv : ∀ t ∈ Iio t₀,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov x₀ b)
          (z t, u t)) t)
    (hγ : Tendsto γ (𝓝[<] t₀) (𝓝 x₀))
    (hcoordinate : ∀ᶠ t in 𝓝[<] t₀,
      z t = extChartAt I x₀ (γ t))
    (hframe : ∀ᶠ t in 𝓝[<] t₀,
      v t = LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := x₀) b (u t) (γ t))
    (hvelocity : ∀ᶠ t in 𝓝[<] t₀, ‖v t‖ ≤ A) :
    ∃ u₀ : E, ∃ sol : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] t₀]
        (fun t ↦ (sol.coordinate (t - t₀), sol.velocity (t - t₀))) := by
  obtain ⟨B, hB, hu⟩ :=
    exists_eventually_norm_coordinateVelocity_le_of_tendsto_of_frame_velocity_bound
      (I := I) (M := M) (E := E) (x₀ := x₀) b hγ hframe hvelocity
  have hchart : Tendsto (fun t ↦ extChartAt I x₀ (γ t))
      (𝓝[<] t₀) (𝓝 (extChartAt I x₀ x₀)) :=
    (continuousAt_extChartAt (I := I) x₀).tendsto.comp hγ
  have hzlim : Tendsto z (𝓝[<] t₀) (𝓝 (extChartAt I x₀ x₀)) :=
    hchart.congr' (hcoordinate.mono fun _ ht ↦ ht.symm)
  obtain ⟨C, hC, hacc⟩ :=
    exists_eventually_norm_coordinateAcceleration_le_of_tendsto_of_norm_velocity_eventually_le
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) b hzlim hu
  exact
    exists_localChartGeodesicSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound_eventually
      (I := I) (M := M) (E := E) (cov := cov) b hderiv hzlim hC.le hacc

/-- Tail-local version of intrinsic endpoint continuation.  It is the bridge
from a partial geodesic's local germs to a fresh endpoint chart solution. -/
theorem exists_localChartGeodesicSolution_eventuallyEq_left_of_intrinsic_tendsto_of_norm_velocity_eventually_le_eventually_deriv
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₀ : M} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {z u : ℝ → E} {t₀ A : ℝ} {γ : ℝ → M}
    {v : ∀ t, TangentSpace I (γ t)}
    (hderiv : ∀ᶠ t in 𝓝[<] t₀,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov x₀ b)
          (z t, u t)) t)
    (hγ : Tendsto γ (𝓝[<] t₀) (𝓝 x₀))
    (hcoordinate : ∀ᶠ t in 𝓝[<] t₀,
      z t = extChartAt I x₀ (γ t))
    (hframe : ∀ᶠ t in 𝓝[<] t₀,
      v t = LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := x₀) b (u t) (γ t))
    (hvelocity : ∀ᶠ t in 𝓝[<] t₀, ‖v t‖ ≤ A) :
    ∃ u₀ : E, ∃ sol : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] t₀]
        (fun t ↦ (sol.coordinate (t - t₀), sol.velocity (t - t₀))) := by
  obtain ⟨B, hB, hu⟩ :=
    exists_eventually_norm_coordinateVelocity_le_of_tendsto_of_frame_velocity_bound
      (I := I) (M := M) (E := E) (x₀ := x₀) b hγ hframe hvelocity
  have hchart : Tendsto (fun t ↦ extChartAt I x₀ (γ t))
      (𝓝[<] t₀) (𝓝 (extChartAt I x₀ x₀)) :=
    (continuousAt_extChartAt (I := I) x₀).tendsto.comp hγ
  have hzlim : Tendsto z (𝓝[<] t₀) (𝓝 (extChartAt I x₀ x₀)) :=
    hchart.congr' (hcoordinate.mono fun _ ht ↦ ht.symm)
  obtain ⟨C, hC, hacc⟩ :=
    exists_eventually_norm_coordinateAcceleration_le_of_tendsto_of_norm_velocity_eventually_le
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) b hzlim hu
  exact
    exists_localChartGeodesicSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound_eventually_deriv
      (I := I) (M := M) (E := E) (cov := cov) b hderiv hzlim hC.le hacc

/-- Coordinate position convergence together with an eventual coordinate
velocity bound is enough to restart a chart geodesic.  The acceleration bound
is obtained internally from compactness of the endpoint-chart state box. -/
theorem exists_localChartGeodesicSolution_eventuallyEq_left_of_tendsto_of_norm_velocity_eventually_le
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₀ : M} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {z u : ℝ → E} {t₀ B : ℝ}
    (hderiv : ∀ t ∈ Iio t₀,
      HasDerivAt (fun s ↦ (z s, u s))
        (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov x₀ b)
          (z t, u t)) t)
    (hzlim : Tendsto z (𝓝[<] t₀) (𝓝 (extChartAt I x₀ x₀)))
    (hu : ∀ᶠ t in 𝓝[<] t₀, ‖u t‖ ≤ B) :
    ∃ u₀ : E, ∃ sol : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀,
      (fun t ↦ (z t, u t)) =ᶠ[𝓝[<] t₀]
        (fun t ↦ (sol.coordinate (t - t₀), sol.velocity (t - t₀))) := by
  obtain ⟨C, hC, hacc⟩ :=
    exists_eventually_norm_coordinateAcceleration_le_of_tendsto_of_norm_velocity_eventually_le
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) b hzlim hu
  exact
    exists_localChartGeodesicSolution_eventuallyEq_left_of_tendsto_curve_of_acceleration_bound_eventually
      (I := I) (M := M) (E := E) (cov := cov) b hderiv hzlim hC.le hacc

end BonnetMyersEntry
