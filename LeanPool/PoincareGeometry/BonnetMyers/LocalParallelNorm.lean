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

import LeanPool.PoincareGeometry.BonnetMyers.LocalEnergy

/-!
# Metric preservation for a local coordinate parallel field

The ODE in `Parallel` is written in a fixed model fibre, whereas the metric
lives in the tangent fibres.  This file closes that local gap.  On an interval
where the chosen chart frame agrees with the smooth frame used by the
connection-coefficient germ, a solution of the coordinate parallel equation
has constant Riemannian inner products after conversion by
`coordinateFrameCombination`.

The frame-agreement hypothesis is intentionally local.  It is the condition
that a later chart-patching or continuation argument must establish; it is not
silently promoted to a global frame.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology BigOperators

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type _)]

theorem coordinate_parallel_inner_constant
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ coordinateParallelOperator cov x₀ b
        (sol.coordinate t) (sol.velocity t)) 0 w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hframe : ∀ t ∈ Ioo (-min sol.radius wsol.radius) (min sol.radius wsol.radius),
      ∀ j : Fin (Module.finrank ℝ E),
        ∀ᶠ z in 𝓝 (LocalChartSecondOrderSolution.curve sol t),
          smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
            (trivializationAt E TM x₀).localFrame b j z) :
    ∀ t ∈ Ioo (-min sol.radius wsol.radius) (min sol.radius wsol.radius),
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (wsol.curve t) (LocalChartSecondOrderSolution.curve sol t))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (wsol.curve t) (LocalChartSecondOrderSolution.curve sol t)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w₀ x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w₀ x₀) := by
  let r : ℝ := min sol.radius wsol.radius
  let γ : ℝ → M := LocalChartSecondOrderSolution.curve sol
  let speedSq : ℝ → ℝ := fun t ↦
    inner ℝ
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (wsol.curve t) (γ t))
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (wsol.curve t) (γ t))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min sol.radius_pos wsol.radius_pos
  have hderiv : ∀ t ∈ Ioo (-r) r, HasDerivAt speedSq 0 t := by
    intro t ht
    have hrs : r ≤ sol.radius := by
      dsimp [r]
      exact min_le_left _ _
    have hrw : r ≤ wsol.radius := by
      dsimp [r]
      exact min_le_right _ _
    have htsol : t ∈ Ioo (-sol.radius) sol.radius := by
      constructor
      · exact lt_of_le_of_lt (neg_le_neg hrs) ht.1
      · exact lt_of_lt_of_le ht.2 hrs
    have htw : t ∈ Ioo (0 - wsol.radius) (0 + wsol.radius) := by
      simpa only [zero_sub, zero_add]
        using (show t ∈ Ioo (-wsol.radius) wsol.radius from by
          constructor
          · exact lt_of_le_of_lt (neg_le_neg hrw) ht.1
          · exact lt_of_lt_of_le ht.2 hrw)
    have hγ := curve_derivative_velocity
      (I := I) (M := M) (E := E) (H := H) cov x₀ b sol htsol
    have hγ' :
        (ContinuousLinearMap.toSpanSingleton ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (γ t))) 1 =
          coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (γ t) := by
      simp
    have hy : γ t ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I) x₀]
      change (extChartAt I x₀).symm (sol.coordinate t) ∈
        (extChartAt I x₀).source
      exact (extChartAt I x₀).map_target (sol.coordinate_mem_target t htsol)
    have hinner := coordinateFrameCombination_inner_hasDerivAt_variable
      (I := I) (M := M) (E := E) (H := H) cov x₀ b
      (u := sol.velocity t) (w := wsol.curve) (v := wsol.curve)
      (dw := -(coordinateParallelOperator cov x₀ b
        (sol.coordinate t) (sol.velocity t) (wsol.curve t)))
      (dv := -(coordinateParallelOperator cov x₀ b
        (sol.coordinate t) (sol.velocity t) (wsol.curve t)))
      hγ hγ' hy hmetric (hframe t ht) (wsol.hasDeriv t htw)
        (wsol.hasDeriv t htw)
    have hcoord : (extChartAt I x₀) (γ t) = sol.coordinate t := by
      exact LocalChartSecondOrderSolution.curve_eq_chart sol htsol
    have hcancel :
        -(coordinateParallelOperator cov x₀ b
          (sol.coordinate t) (sol.velocity t) (wsol.curve t)) +
          coordinateParallelOperator cov x₀ b
            ((extChartAt I x₀) (γ t)) (sol.velocity t) (wsol.curve t) = 0 := by
      rw [hcoord]
      exact neg_add_cancel _
    have hcomb_zero :
        coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (0 : E) (γ t) = 0 := by
      simp [coordinateFrameCombination]
    rw [hcancel, hcomb_zero] at hinner
    simpa only [speedSq, γ, inner_zero_left, inner_zero_right, zero_add] using hinner
  have hdiff : DifferentiableOn ℝ speedSq (Ioo (-r) r) := by
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hderiv_zero : Set.EqOn (deriv speedSq) (fun _ ↦ (0 : ℝ))
      (Ioo (-r) r) := by
    intro t ht
    exact (hderiv t ht).deriv
  have hconst : ∀ t ∈ Ioo (-r) r, speedSq 0 = speedSq t := by
    intro t ht
    have hzero : (0 : ℝ) ∈ Ioo (-r) r := by
      constructor <;> linarith
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (x := 0) (y := t)
      isPreconnected_Ioo hdiff hderiv_zero hzero ht
  intro t ht
  have h := hconst t ht
  have hzero_value : speedSq 0 =
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w₀ x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w₀ x₀) := by
    have hcurve0 : LocalChartSecondOrderSolution.curve sol 0 = x₀ :=
      LocalChartSecondOrderSolution.curve_initial sol
    have hw0 : wsol.curve 0 = w₀ := wsol.initial
    change inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (wsol.curve 0) (LocalChartSecondOrderSolution.curve sol 0))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (wsol.curve 0) (LocalChartSecondOrderSolution.curve sol 0)) = _
    rw [hw0, hcurve0]
  exact (h.symm).trans hzero_value

/-! The agreement condition in the preceding theorem is automatic at the
initial point.  We record that fact by restricting both ODE solutions to a
smaller common interval.  The restriction is important: the smooth extension
used to define `smoothFrame` agrees with the chart frame only on a
neighbourhood of the chosen base point. -/

theorem coordinate_parallel_inner_constant_near_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ coordinateParallelOperator cov x₀ b
        (sol.coordinate t) (sol.velocity t)) 0 w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), r ≤ min sol.radius wsol.radius ∧
      ∀ t ∈ Ioo (-r) r,
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (wsol.curve t) (LocalChartSecondOrderSolution.curve sol t))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (wsol.curve t) (LocalChartSecondOrderSolution.curve sol t)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w₀ x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w₀ x₀) := by
  let S : Fin (Module.finrank ℝ E) → Set M := fun j ↦
    {z | smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
      (trivializationAt E TM x₀).localFrame b j z}
  have hS : ∀ j, S j ∈ 𝓝 x₀ := by
    intro j
    change ∀ᶠ z in 𝓝 x₀,
      smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
        (trivializationAt E TM x₀).localFrame b j z
    exact smoothFrame_eventuallyEq_localFrame
      (I := I) (M := M) (E := E) x₀ b j
  have hU : (⋂ j, S j) ∈ 𝓝 x₀ :=
    (Filter.iInter_mem).2 hS
  obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.mp hU
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hcurve0 : LocalChartSecondOrderSolution.curve sol 0 = x₀ :=
    LocalChartSecondOrderSolution.curve_initial sol
  have hcurve : ContinuousAt (LocalChartSecondOrderSolution.curve sol) 0 :=
    (LocalChartSecondOrderSolution.curve_hasMFDerivAt sol hzero).continuousAt
  have hpre : (LocalChartSecondOrderSolution.curve sol) ⁻¹' O ∈ 𝓝 (0 : ℝ) := by
    apply hcurve.preimage_mem_nhds
    rw [hcurve0]
    exact hOopen.mem_nhds hxO
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r : ℝ := min (min sol.radius wsol.radius) (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (lt_min sol.radius_pos wsol.radius_pos) (by linarith)
  have hrmin : r ≤ min sol.radius wsol.radius := min_le_left _ _
  let sol' : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀ :=
    { coordinate := sol.coordinate
      velocity := sol.velocity
      radius := r
      radius_pos := hr
      coordinate_initial := sol.coordinate_initial
      velocity_initial := sol.velocity_initial
      coordinate_hasDeriv := by
        intro t ht
        apply sol.coordinate_hasDeriv t
        have hle : r ≤ sol.radius := le_trans hrmin (min_le_left _ _)
        exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
          lt_of_lt_of_le ht.2 hle⟩
      velocity_hasDeriv := by
        intro t ht
        apply sol.velocity_hasDeriv t
        have hle : r ≤ sol.radius := le_trans hrmin (min_le_left _ _)
        exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
          lt_of_lt_of_le ht.2 hle⟩
      coordinate_mem_target := by
        intro t ht
        apply sol.coordinate_mem_target t
        have hle : r ≤ sol.radius := le_trans hrmin (min_le_left _ _)
        exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
          lt_of_lt_of_le ht.2 hle⟩ }
  let wsol' : LocalLinearTransportSolution
      (fun t ↦ coordinateParallelOperator cov x₀ b
        (sol'.coordinate t) (sol'.velocity t)) 0 w₀ :=
    { curve := wsol.curve
      radius := r
      radius_pos := hr
      initial := wsol.initial
      hasDeriv := by
        intro t ht
        have ht' : t ∈ Ioo (0 - wsol.radius) (0 + wsol.radius) := by
          simp only [mem_Ioo, zero_sub, zero_add]
          have hle : r ≤ wsol.radius :=
            le_trans hrmin (min_le_right _ _)
          have htleft : -r < t := by
            simpa only [zero_sub] using ht.1
          have htright : t < r := by
            simpa only [zero_add] using ht.2
          exact ⟨lt_of_le_of_lt (neg_le_neg hle) htleft,
            lt_of_lt_of_le htright hle⟩
        simpa [sol'] using wsol.hasDeriv t ht' }
  have hframe : ∀ t ∈ Ioo (-min sol'.radius wsol'.radius)
      (min sol'.radius wsol'.radius),
      ∀ j : Fin (Module.finrank ℝ E),
        ∀ᶠ z in 𝓝 (LocalChartSecondOrderSolution.curve sol' t),
          smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
            (trivializationAt E TM x₀).localFrame b j z := by
    intro t ht j
    have ht' : t ∈ Ioo (-r) r := by
      simpa [sol', wsol'] using ht
    have hminδ : r ≤ δ / 2 := min_le_right _ _
    have habs : |t| < δ := by
      rw [abs_lt]
      constructor <;> linarith [ht'.1, ht'.2, hminδ]
    have htO : LocalChartSecondOrderSolution.curve sol' t ∈ O := by
      apply hδsub
      rw [Metric.mem_ball]
      simpa [sol', dist_zero_right] using habs
    filter_upwards [hOopen.mem_nhds htO] with z hz
    exact Set.mem_iInter.mp (hOsub hz) j
  have hconst := coordinate_parallel_inner_constant
    (I := I) (M := M) (E := E) (H := H)
    cov x₀ b sol' wsol' hmetric hframe
  refine ⟨r, hr, hrmin, ?_⟩
  intro t ht
  have ht' : t ∈ Ioo (-min sol'.radius wsol'.radius)
      (min sol'.radius wsol'.radius) := by
    simpa only [sol', wsol', min_self] using ht
  have hc := hconst t ht'
  convert hc using 1 <;> rfl

end LocalGeodesicData

end BonnetMyersEntry
