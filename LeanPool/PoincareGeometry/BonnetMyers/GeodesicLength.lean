/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.LocalEnergy
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Length of a local coordinate geodesic

This file contains the first bridge from the coordinate ODE to the actual
Riemannian path length.  The derivative is rewritten through the tangent-bundle
trivialization; no distance or minimizing assertion is used.
-/

noncomputable section

open Bundle Manifold Set
open MeasureTheory
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

/-- A local chart solution is `C¹` on every closed interval strictly inside
its domain.  Keeping this fact explicit is important for the metric argument:
`riemannianEDist_le_pathELength` applies to `C¹` paths, whereas the ODE data
are initially packaged only as pointwise derivative certificates. -/
theorem localChartSecondOrderSolution_contMDiffOn_curve
    {F : E → E → E} {x₀ : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F x₀ v₀)
    {a c : ℝ} (ha : -sol.radius < a) (hc : c < sol.radius) (hac : a < c) :
    ContMDiffOn (𝓘(ℝ, ℝ)) I 1
      (LocalChartSecondOrderSolution.curve sol) (Icc a c) := by
  have hcoordinate : ContDiffOn ℝ 1 sol.coordinate (Icc a c) := by
    rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hac)]
    constructor
    · intro t ht
      exact (sol.coordinate_hasDeriv t (Icc_subset_Ioo ha hc ht)).differentiableAt
        |>.differentiableWithinAt
    · have hvelocity : ContinuousOn sol.velocity (Icc a c) := by
        intro t ht
        exact (sol.velocity_hasDeriv t (Icc_subset_Ioo ha hc ht)).continuousAt
          |>.continuousWithinAt
      apply hvelocity.congr
      intro t ht
      exact (sol.coordinate_hasDeriv t (Icc_subset_Ioo ha hc ht)).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc hac).uniqueDiffWithinAt ht)
  have hmaps : MapsTo sol.coordinate (Icc a c) (extChartAt I x₀).target := by
    intro t ht
    exact sol.coordinate_mem_target t (Icc_subset_Ioo ha hc ht)
  have hcurve := (contMDiffOn_extChartAt_symm (I := I) (n := (1 : WithTop ℕ∞)) x₀).comp
    hcoordinate.contMDiffOn hmaps
  simpa [LocalChartSecondOrderSolution.curve, Function.comp_def] using hcurve

/-- On an interval contained in its coordinate domain, a local solution itself
is an admissible path in the definition of Riemannian distance. -/
theorem riemannianEDist_le_localChartSecondOrderSolution_pathELength
    {F : E → E → E} {x₀ : M} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F x₀ v₀)
    {a c : ℝ} (ha : -sol.radius < a) (hc : c < sol.radius) (hac : a < c) :
    riemannianEDist I (LocalChartSecondOrderSolution.curve sol a)
      (LocalChartSecondOrderSolution.curve sol c) ≤
        pathELength I (LocalChartSecondOrderSolution.curve sol) a c := by
  exact riemannianEDist_le_pathELength
    (localChartSecondOrderSolution_contMDiffOn_curve (I := I) sol ha hc hac)
    rfl rfl hac.le

theorem local_geodesic_pathELength_eq_coordinate_speed
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    {a c : ℝ} (ha : -sol.radius < a) (hc : c < sol.radius) :
    pathELength I (LocalChartSecondOrderSolution.curve sol) a c =
      ∫⁻ t in Ioo a c, ‖coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b (sol.velocity t)
          (LocalChartSecondOrderSolution.curve sol t)‖ₑ := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht_sol : t ∈ Ioo (-sol.radius) sol.radius := by
    constructor
    · exact lt_trans ha ht.1
    · exact lt_trans ht.2 hc
  have hderiv := curve_derivative_velocity
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol ht_sol
  change ‖mfderiv% (LocalChartSecondOrderSolution.curve sol) t 1‖ₑ =
    ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ₑ
  rw [hderiv.mfderiv]
  change ‖(1 : ℝ) • coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
    (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ₑ = _
  simp

/-- A local geodesic has the expected constant-speed length formula on a
smaller interval around its centre.  The radius is retained because the
coordinate frame and the local energy identity are both genuinely local. -/
theorem exists_local_geodesic_pathELength_eq_constant_speed_mul
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), r ≤ sol.radius ∧
      ∀ {a c : ℝ}, -r < a → a < c → c < r →
        pathELength I (LocalChartSecondOrderSolution.curve sol) a c =
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 0) (LocalChartSecondOrderSolution.curve sol 0)‖ₑ *
            ENNReal.ofReal (c - a) := by
  obtain ⟨r, hr, hrsol, hspeed⟩ := local_speed_enorm_is_constant_near_zero
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric
  refine ⟨r, hr, hrsol, ?_⟩
  intro a c ha hac hc
  have hasol : -sol.radius < a :=
    lt_of_le_of_lt (neg_le_neg hrsol) ha
  have hcsol : c < sol.radius := lt_of_lt_of_le hc hrsol
  rw [local_geodesic_pathELength_eq_coordinate_speed
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hasol hcsol]
  rw [show (∫⁻ t in Ioo a c,
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ₑ) =
      ∫⁻ _t in Ioo a c,
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity 0) (LocalChartSecondOrderSolution.curve sol 0)‖ₑ by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        apply hspeed t
        constructor
        · exact lt_trans ha ht.1
        · exact lt_trans ht.2 hc]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]

/-- The local constant-speed formula bounds Riemannian distance by elapsed
time times speed.  This is the metric estimate needed to obtain a Cauchy tail
at a finite maximal time. -/
theorem exists_local_geodesic_riemannianEDist_le_constant_speed_mul
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), r ≤ sol.radius ∧
      ∀ {a c : ℝ}, -r < a → a < c → c < r →
        riemannianEDist I (LocalChartSecondOrderSolution.curve sol a)
          (LocalChartSecondOrderSolution.curve sol c) ≤
            ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity 0) (LocalChartSecondOrderSolution.curve sol 0)‖ₑ *
              ENNReal.ofReal (c - a) := by
  obtain ⟨r, hr, hrsol, hlength⟩ :=
    exists_local_geodesic_pathELength_eq_constant_speed_mul
      (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric
  refine ⟨r, hr, hrsol, ?_⟩
  intro a c ha hac hc
  have hasol : -sol.radius < a :=
    lt_of_le_of_lt (neg_le_neg hrsol) ha
  have hcsol : c < sol.radius := lt_of_lt_of_le hc hrsol
  calc
    riemannianEDist I (LocalChartSecondOrderSolution.curve sol a)
        (LocalChartSecondOrderSolution.curve sol c) ≤
      pathELength I (LocalChartSecondOrderSolution.curve sol) a c :=
        riemannianEDist_le_localChartSecondOrderSolution_pathELength
          (I := I) sol hasol hcsol hac
    _ = _ := hlength ha hac hc

end LocalGeodesicData

end BonnetMyersEntry
