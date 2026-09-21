/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RicciDerivativeTrace
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchiBridge

/-!
# Unconditional contracted Bianchi trace bridges

The preceding curvature-contraction file identifies the genuine covariant
derivative of Ricci with the metric trace of the genuine derivative of
curvature.  This file applies that identity in an orthonormal basis to remove
the two trace-commutation hypotheses from the contracted Bianchi theorem.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M] [IsManifold I ((3 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]

/-- The scalar trace bridge is a consequence of the actual Ricci/curvature
contraction identity, with no separately postulated trace commutation. -/
theorem scalarTraceBridge_of_curvatureDerivative
    [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I 1 E TM]
    (x : M) (hmetric : cov.IsMetricCompatibleTangent)
    (hRicci : raisedRicciEndomorphismMDiffAt cov x) :
    ∀ w : TM x,
      raisedRicciTraceCovariantDerivative cov x w =
        curvatureCovariantDerivativeScalarTrace cov x w := by
  intro w
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (TM x))) ℝ (TM x) :=
    stdOrthonormalBasis ℝ (TM x)
  rw [raisedRicciTraceCovariantDerivative_eq_sum_ricciDerivative_of_raisedRicci
    cov hmetric x hRicci w b]
  unfold curvatureCovariantDerivativeScalarTrace
  simp only [b]
  apply Finset.sum_congr rfl
  intro i hi
  rw [covariantTwoTensorCovariantDerivative_ricci_eq_curvatureTrace
    (I := I) (E := E) (M := M) cov x hRicci w (b i) (b i)]

/-- The Ricci-divergence trace bridge is obtained by evaluating the genuine
Ricci divergence in an orthonormal basis and using the same curvature trace
identity with the divergence direction as the derivative direction. -/
theorem ricciTraceBridge_of_curvatureDerivative
    [IsContMDiffRiemannianBundle I 1 E TM]
    (x : M) (hRicci : raisedRicciEndomorphismMDiffAt cov x) :
    ∀ w : TM x,
      ricciDivergence cov x w =
        curvatureCovariantDerivativeRicciDivergenceTrace cov x w := by
  intro w
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (TM x))) ℝ (TM x) :=
    stdOrthonormalBasis ℝ (TM x)
  have hdiv := ricciDivergence_eq_sum_orthonormalBasis cov x b
  have hdivw := congrArg (fun q : TM x →L[ℝ] ℝ => q w) hdiv
  change ricciDivergence cov x w = _ at hdivw
  rw [hdivw]
  simp only [sum_apply]
  unfold curvatureCovariantDerivativeRicciDivergenceTrace
  simp only [b]
  apply Finset.sum_congr rfl
  intro i hi
  rw [covariantTwoTensorCovariantDerivative_ricci_eq_curvatureTrace
    (I := I) (E := E) (M := M) cov x hRicci (b i) (b i) w]

/-- Contracted second Bianchi with both trace/differentiation bridges proved
from the actual geometric curvature tensor. -/
theorem ricciDivergence_eq_half_scalarDifferential_of_curvature
    [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsContMDiffRiemannianBundle I 1 E TM]
    (x : M) (hT : cov.torsion = 0)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hRicci : raisedRicciEndomorphismMDiffAt cov x) :
    ricciDivergence cov x =
      (1 / 2 : ℝ) • scalarDifferential (I := I)
        (scalarCurvature (cov := cov)) x := by
  apply ricciDivergence_eq_half_scalarDifferential_of_trace_bridges
    cov x hT hmetric
  · exact scalarDifferential_scalarCurvature_eq_curvatureTrace_of_raisedRicciTrace
      cov x hRicci (scalarTraceBridge_of_curvatureDerivative
        cov x hmetric hRicci)
  · exact ricciTraceBridge_of_curvatureDerivative cov x hRicci

/-! The regularity argument for the raised Ricci endomorphism is itself a
curvature calculation (see `DeTurckCorrectionRegularity`).  Expose the
contracted Bianchi identity with that calculation performed internally, so a
caller cannot accidentally replace it by an unrelated differentiability
hypothesis on Ricci. -/

/--
  Contracted second Bianchi, with the Ricci regularity discharged from the
  genuine curvature tensor.

  This is the API intended for geometric applications: the only analytic
  assumptions are the stated bundle/connection regularity and the actual
  torsion-free metric-compatible connection laws.
-/
theorem ricciDivergence_eq_half_scalarDifferential_of_curvature_unconditional
    [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsContMDiffRiemannianBundle I 1 E TM]
    (x : M) (hT : cov.torsion = 0)
    (hmetric : cov.IsMetricCompatibleTangent) :
  ricciDivergence cov x =
      (1 / 2 : ℝ) • scalarDifferential (I := I)
        (scalarCurvature (cov := cov)) x := by
  let hRicci : raisedRicciEndomorphismMDiffAt cov x :=
    RicciFlow.raisedRicciEndomorphismMDiffAt_of_curvature
      (I := I) (M := M) cov x
  exact ricciDivergence_eq_half_scalarDifferential_of_curvature
    cov x hT hmetric hRicci

end CovariantDerivative
