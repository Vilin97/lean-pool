/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.MetricVariable

/-! # Local Energy -/

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

lemma curve_derivative_velocity
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    let γ := LocalChartSecondOrderSolution.curve sol
    HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t
      (ContinuousLinearMap.toSpanSingleton ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity t) (γ t))) := by
  dsimp
  have h := LocalChartSecondOrderSolution.curve_hasMFDerivAt sol ht
  have htarget := sol.coordinate_mem_target t ht
  have hsource : LocalChartSecondOrderSolution.curve sol t ∈
      (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    change (extChartAt I x₀).symm (sol.coordinate t) ∈
      (extChartAt I x₀).source
    exact (extChartAt I x₀).map_target htarget
  have hcurveeq := LocalChartSecondOrderSolution.curve_eq_chart sol ht
  have hpointsource : (extChartAt I x₀).symm (sol.coordinate t) ∈
      (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact (extChartAt I x₀).map_target htarget
  have hframe := coordinateFrameCombination_eq_symmL (I := I) (M := M)
    (x₀ := x₀) b hpointsource (sol.velocity t)
  have htriv := TangentBundle.symmL_trivializationAt
    (I := I) (𝕜 := ℝ) (E := E) (x₀ := x₀)
    (x := (extChartAt I x₀).symm (sol.coordinate t)) hpointsource
  have htriv' := htriv
  rw [(extChartAt I x₀).right_inv htarget] at htriv'
  have hmf :
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.coordinate t))
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E)
            (sol.coordinate t)).symm (sol.velocity t)) =
        (trivializationAt E TM x₀).symmL ℝ
          ((extChartAt I x₀).symm (sol.coordinate t)) (sol.velocity t) := by
    rw [← htriv']
    rfl
  have hmap :
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.coordinate t)) ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity t) =
      ContinuousLinearMap.toSpanSingleton ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) ((extChartAt I x₀).symm (sol.coordinate t))) := by
    apply ContinuousLinearMap.ext
    intro s
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    change (mfderiv[range (I : H → E)] (extChartAt I x₀).symm
      (sol.coordinate t))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E)
        (sol.coordinate t)).symm (s • sol.velocity t)) =
      s • coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) ((extChartAt I x₀).symm (sol.coordinate t))
    rw [map_smul, map_smul, hmf, hframe]
  exact h.congr_mfderiv hmap

lemma local_speed_deriv
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 (LocalChartSecondOrderSolution.curve sol t),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s)))
      0 t := by
  have hγ := curve_derivative_velocity
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol ht
  have hzero :
      deriv sol.velocity t + coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ b
        (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol t))
        (sol.velocity t) (sol.velocity t) = 0 := by
    have hacc := local_solution_coordinateCovariantAcceleration_eq_zero
      (I := I) (M := M) (E := E) (H := H)
      (F := coordinateAcceleration cov x₀ b)
      (cov := cov) (x₀ := x₀) (b := b) sol ht
    have hcurveeq := LocalChartSecondOrderSolution.curve_eq_chart sol ht
    rw [coordinateCovariantAcceleration] at hacc
    rw [← hcurveeq] at hacc
    simpa [coordinateParallelOperator_apply, coordinateConnectionTerm,
      Finset.sum_smul] using hacc
  have hvel : HasDerivAt sol.velocity (deriv sol.velocity t) t := by
    rw [(sol.velocity_hasDeriv t ht).deriv]
    exact sol.velocity_hasDeriv t ht
  have hinner := coordinateFrameCombination_inner_hasDerivAt_variable
    (I := I) (M := M) (E := E) (H := H) cov x₀ b (u := sol.velocity t)
    (w := sol.velocity) (v := sol.velocity)
    (dw := deriv sol.velocity t) (dv := deriv sol.velocity t)
    (γ := LocalChartSecondOrderSolution.curve sol) (t := t)
    (hγ := hγ) (hγ' := by
      change (1 : ℝ) • coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t) = _
      simp)
    (hy := by
      rw [← extChartAt_source (I := I) x₀]
      change (extChartAt I x₀).symm (sol.coordinate t) ∈
        (extChartAt I x₀).source
      exact (extChartAt I x₀).map_target (sol.coordinate_mem_target t ht))
    hmetric hframe hvel hvel
  convert hinner using 1
  rw [hzero]
  simp [coordinateFrameCombination]

lemma local_speed_is_constant_near_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), r ≤ sol.radius ∧
      ∀ t ∈ Ioo (-r) r,
        inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 0) (LocalChartSecondOrderSolution.curve sol 0))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 0) (LocalChartSecondOrderSolution.curve sol 0)) := by
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
  let r : ℝ := min sol.radius (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min sol.radius_pos (by linarith)
  let speed : ℝ → ℝ := fun s ↦ inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
  have hderiv : ∀ t ∈ Ioo (-r) r, HasDerivAt speed 0 t := by
    intro t ht
    have hmin : r ≤ sol.radius := min_le_left _ _
    have ht_sol : t ∈ Ioo (-sol.radius) sol.radius := by
      constructor <;> linarith [ht.1, ht.2]
    have hminδ : r ≤ δ / 2 := min_le_right _ _
    have habs : |t| < δ := by
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2, hminδ]
    have htO : LocalChartSecondOrderSolution.curve sol t ∈ O := by
      apply hδsub
      rw [Metric.mem_ball]
      simpa [dist_zero_right] using habs
    have hframe : ∀ j : Fin (Module.finrank ℝ E),
        ∀ᶠ z in 𝓝 (LocalChartSecondOrderSolution.curve sol t),
          smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
            (trivializationAt E TM x₀).localFrame b j z := by
      intro j
      filter_upwards [hOopen.mem_nhds htO] with z hz
      exact Set.mem_iInter.mp (hOsub hz) j
    have h := local_speed_deriv
      (I := I) (M := M) (E := E) (H := H)
      cov x₀ b sol ht_sol hmetric hframe
    simpa [speed] using h
  have hdiff : DifferentiableOn ℝ speed (Ioo (-r) r) := by
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hderiv_eq : EqOn (deriv speed) (fun _ ↦ (0 : ℝ)) (Ioo (-r) r) := by
    intro t ht
    exact (hderiv t ht).deriv
  refine ⟨r, hr, min_le_left _ _, ?_⟩
  intro t ht
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (x := (0 : ℝ)) (y := t)
    isPreconnected_Ioo hdiff hderiv_eq
    ⟨by linarith [hr], by linarith [hr]⟩ ht
  simpa [speed] using hconst.symm

/-- The local conservation law for the Riemannian energy also gives a
conservation law for the extended norm of the velocity.  This is the form
consumed by the path-length and metric-continuation arguments. -/
lemma local_speed_enorm_is_constant_near_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), r ≤ sol.radius ∧
      ∀ t ∈ Ioo (-r) r,
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ₑ =
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 0) (LocalChartSecondOrderSolution.curve sol 0)‖ₑ := by
  obtain ⟨r, hr, hrsol, hspeed⟩ := local_speed_is_constant_near_zero
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric
  refine ⟨r, hr, hrsol, ?_⟩
  intro t ht
  let vt := coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
    (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)
  let vzero := coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
    (sol.velocity 0) (LocalChartSecondOrderSolution.curve sol 0)
  have hsq : ‖vt‖ ^ 2 = ‖vzero‖ ^ 2 := by
    simpa [vt, vzero, real_inner_self_eq_norm_sq] using hspeed t ht
  have hnorm : ‖vt‖ = ‖vzero‖ := by
    nlinarith [norm_nonneg vt, norm_nonneg vzero]
  simpa [vt, vzero, ofReal_norm] using congrArg ENNReal.ofReal hnorm

end LocalGeodesicData
end BonnetMyersEntry
