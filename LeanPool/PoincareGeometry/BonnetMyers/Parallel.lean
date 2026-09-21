/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.Geodesic

/-!
# Local parallel transport in the geodesic chart

The Christoffel germ used by `LocalGeodesicData` also gives the linear equation
for a parallel vector field.  This file keeps the construction in the same
fixed model fibre as the local geodesic ODE; the later bundle-valued transport
statement can therefore be proved by a separate chart-conversion lemma.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

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

/-- The coefficient operator in the equation for a parallel vector field.

If `u` is the coordinate velocity, then this is the linear map
`w ↦ ∇_u w` in the chosen frame.  With the coefficient convention used by
`connectionCoefficient`, the field component is the second lower index and
the velocity component is the third lower index.  Its sign is intentionally
positive: a parallel field satisfies `w' = -coordinateParallelOperator z u w`.

Keeping the lower indices in this order matters before torsion-freeness is
used: the coordinate geodesic equation happens to be insensitive to their
exchange, while the linear transport equation is not. -/
def coordinateParallelOperator
    (cov : CovariantDerivative I E TM) (x₀ : M)
  (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (z u : E) : E →L[ℝ] E :=
  ∑ i, ∑ j, ∑ k,
    ((b.repr u k) * connectionCoefficient (I := I) (M := M) (E := E) cov x₀ b i j k
      ((extChartAt I x₀).symm z)) •
      ((b.coord j).toContinuousLinearMap.smulRight (b i))

@[simp] lemma coordinateParallelOperator_apply
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (z u w : E) :
    coordinateParallelOperator cov x₀ b z u w =
      ∑ i, ∑ j, ∑ k,
        ((b.repr w j) * (b.repr u k) *
          connectionCoefficient (I := I) (M := M) (E := E) cov x₀ b i j k
            ((extChartAt I x₀).symm z)) • b i := by
  simp [coordinateParallelOperator, ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_smul]
  congr 1
  ring

/-- The coordinate parallel operator is linear in the curve velocity.  This
is the sign identity required when a parallel field is read along a
time-reversed geodesic. -/
@[simp] lemma coordinateParallelOperator_neg
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (z u : E) :
    coordinateParallelOperator cov x₀ b z (-u) =
      -coordinateParallelOperator cov x₀ b z u := by
  ext w
  simp [coordinateParallelOperator]

/-- Applying the coordinate parallel operator to the coordinate velocity is
exactly the connection term in the coordinate geodesic equation.  This is the
algebraic identity that lets the velocity itself be treated as a parallel
field along a geodesic. -/
lemma coordinateParallelOperator_self_eq_coordinateConnectionTerm
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (z u : E) :
    coordinateParallelOperator cov x₀ b z u u =
      coordinateConnectionTerm cov x₀ b z u := by
  rw [coordinateParallelOperator_apply]
  simp only [coordinateConnectionTerm]
  simp only [Finset.sum_smul]

lemma coordinateParallelOperator_contDiffAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (u₀ : E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ContDiffAt ℝ 1
      (fun q : E × E ↦ coordinateParallelOperator cov x₀ b q.1 q.2)
      (extChartAt I x₀ x₀, u₀) := by
  let p : E × E := (extChartAt I x₀ x₀, u₀)
  have hterm : ∀ (i j k : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ 1
        (fun q : E × E ↦
          ((b.repr q.2 k) *
            connectionCoefficient (I := I) (M := M) (E := E) cov x₀ b i j k
              ((extChartAt I x₀).symm q.1)) •
            ((b.coord j).toContinuousLinearMap.smulRight (b i))) p := by
    intro i j k
    have hk : ContDiffAt ℝ 1 (fun q : E × E ↦ b.repr q.2 k) p := by
      exact (b.coord k).toContinuousLinearMap.contDiff.contDiffAt.comp p
        contDiffAt_snd
    have hc := connectionCoefficient_comp_extChartAt_symm_contDiffAt
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) i j k
    have hc' : ContDiffAt ℝ 1
        (fun q : E × E ↦ connectionCoefficient (I := I) (M := M) (E := E)
          cov x₀ b i j k
          ((extChartAt I x₀).symm q.1)) p := by
      exact hc.comp p contDiffAt_fst
    exact (hk.mul hc').smul_const
      ((b.coord j).toContinuousLinearMap.smulRight (b i))
  have hsum : ContDiffAt ℝ 1
        (fun q : E × E ↦ ∑ i, ∑ j, ∑ k,
        ((b.repr q.2 k) *
          connectionCoefficient (I := I) (M := M) (E := E) cov x₀ b i j k
            ((extChartAt I x₀).symm q.1)) •
          ((b.coord j).toContinuousLinearMap.smulRight (b i))) p := by
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro j hj
    apply ContDiffAt.sum
    intro k hk
    exact hterm i j k
  simpa [coordinateParallelOperator, p] using hsum

/-- Along a local coordinate geodesic, the parallel-transport coefficient is
`C¹` at the initial time.  This packages the analytic fact used both for
existence and for uniqueness of the linear transport ODE. -/
theorem coordinateParallelOperator_contDiffAt_along_localChartSolution
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀)
    (hF : ContDiffAt ℝ 1
      (fun q : E × E ↦ secondOrderSystem
        (LocalGeodesicData.coordinateAcceleration cov x₀ b) q)
      (extChartAt I x₀ x₀, u₀))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ContDiffAt ℝ 1
      (fun t ↦ coordinateParallelOperator cov x₀ b
        (sol.coordinate t) (sol.velocity t)) 0 := by
  let base : LocalSecondOrderSolution
      (LocalGeodesicData.coordinateAcceleration cov x₀ b)
      (extChartAt I x₀ x₀) u₀ :=
    { curve := sol.coordinate
      velocity := sol.velocity
      radius := sol.radius
      radius_pos := sol.radius_pos
      initial_curve := sol.coordinate_initial
      initial_velocity := sol.velocity_initial
      curve_hasDeriv := sol.coordinate_hasDeriv
      velocity_hasDeriv := sol.velocity_hasDeriv }
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hcurve : ContDiffAt ℝ 1 sol.coordinate 0 :=
    base.contDiffAt_curve hzero
  have hvel : ContDiffAt ℝ 1 sol.velocity 0 :=
    base.contDiffAt_velocity_of_contDiffAt hF
  have hpair : ContDiffAt ℝ 1
      (fun t ↦ (sol.coordinate t, sol.velocity t)) 0 :=
    hcurve.prodMk hvel
  have hP := coordinateParallelOperator_contDiffAt
    (I := I) (M := M) (E := E) cov x₀ b u₀
  have hP0 : ContDiffAt ℝ 1
      (fun q : E × E ↦ coordinateParallelOperator cov x₀ b q.1 q.2)
      (sol.coordinate 0, sol.velocity 0) := by
    simpa [sol.coordinate_initial, sol.velocity_initial] using hP
  have hcomp := hP0.comp 0 hpair
  simpa [Function.comp_def] using hcomp

/-! ### A local parallel field along a local geodesic -/

theorem exists_local_coordinate_parallel_field
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀)
    (hF : ContDiffAt ℝ 1
      (fun q : E × E ↦ secondOrderSystem
        (LocalGeodesicData.coordinateAcceleration cov x₀ b) q)
      (extChartAt I x₀ x₀, u₀))
    (w₀ : E) [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    Nonempty (LocalLinearTransportSolution
      (fun t ↦ coordinateParallelOperator cov x₀ b
        (sol.coordinate t) (sol.velocity t)) 0 w₀) := by
  have hA := coordinateParallelOperator_contDiffAt_along_localChartSolution
    (I := I) (M := M) (E := E) cov x₀ b sol hF
  exact exists_localLinearTransportSolution_of_contDiffAt hA

/-- The coordinate velocity of a coordinate geodesic solves the same linear
parallel equation as a transported vector whose initial value is that
velocity.  This is a concrete use of the geodesic equation
`u' + Γ(u,u) = 0`, not an assumed identification between the two ODEs. -/
def localVelocityParallelSolution
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀) :
    LocalLinearTransportSolution
      (fun t ↦ coordinateParallelOperator cov x₀ b
        (sol.coordinate t) (sol.velocity t)) 0 (sol.velocity 0) where
  curve := sol.velocity
  radius := sol.radius
  radius_pos := sol.radius_pos
  initial := rfl
  hasDeriv := by
    intro t ht
    simpa only [coordinateAcceleration_eq_neg_connectionTerm,
      coordinateParallelOperator_self_eq_coordinateConnectionTerm] using
      sol.velocity_hasDeriv t (by simpa using ht)

/-! ### Conversion back to tangent fibres -/

/-- Convert a model-space parallel field into a tangent vector along the chart
curve.  The inverse extended-chart derivative is evaluated on the model-space
tangent represented by `w t`; the target membership is supplied by `sol`. -/
def tangentField
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) {u₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀)
    (w : ℝ → E) (t : ℝ) :
    TangentSpace I (BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol t) :=
  (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.coordinate t))
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E)
      (sol.coordinate t)).symm (w t))

lemma tangentField_initial_coordinateVelocity
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) {u₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u₀)
    (v : TangentSpace I x₀)
    (hu : u₀ = coordinateVelocity (I := I) (M := M) (E := E) x₀ v) :
    tangentField cov x₀ b sol (fun _ ↦
      coordinateVelocity (I := I) (M := M) (E := E) x₀ v) 0 = v := by
  have hcurve0 : BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol 0 = x₀ :=
    LocalChartSecondOrderSolution.curve_initial sol
  have hcoord0 : sol.coordinate 0 = extChartAt I x₀ x₀ := sol.coordinate_initial
  have hvel0 : sol.velocity 0 =
      coordinateVelocity (I := I) (M := M) (E := E) x₀ v :=
    sol.velocity_initial.trans hu
  rw [tangentField, hcoord0]
  change (mfderiv[range (I : H → E)] (extChartAt I x₀).symm
      (extChartAt I x₀ x₀))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E)
        (extChartAt I x₀ x₀)).symm
        (coordinateVelocity (I := I) (M := M) (E := E) x₀ v)) = v
  exact coordinateVelocity_inverse_derivative_explicit
    (I := I) (M := M) (E := E) (x₀ := x₀) v

end LocalGeodesicData

end BonnetMyersEntry
