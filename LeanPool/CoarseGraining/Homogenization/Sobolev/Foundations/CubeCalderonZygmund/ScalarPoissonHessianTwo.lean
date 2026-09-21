/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.EuclideanNormalized
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Scalar Poisson Hessian estimate at the energy exponent

The centered-cube Dirichlet `H²` endpoint supplies a weak Hessian with a
dimension-only normalized Frobenius estimate.  This file restates that endpoint
for the project's Hilbert matrix realization.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

/-- The normalized `L²` Hessian estimate for zero-trace scalar Poisson
solutions on centered triadic cubes, expressed in the Hilbert matrix carrier. -/
theorem exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_two
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (F : Vec d → ℝ),
      MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
      ∀ u : H10Function (openCubeSet (originCube d m)),
        CubeDirichletWeakPoissonProblem (originCube d m) u F →
        ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
          MemLp (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) 2
              (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) 2
              (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm F 2 (normalizedCubeMeasure (originCube d m)) := by
  refine ⟨ENNReal.ofReal
    (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact d),
    ENNReal.ofReal_lt_top, ?_⟩
  intro m F hF u hweak
  let Q : TriadicCube d := originCube d m
  rcases CubeDirichletWeakPoissonProblem.exists_originCube_dirichlet_calderon_zygmund_regularity_q_two
    m u F hF hweak with
    ⟨H, hH⟩
  have hHmat : MemLp (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) 2
      (normalizedCubeMeasure Q) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    rw [MeasureTheory.memLp_piLp_iff]
    intro j
    simpa only [Function.comp_apply, HilbertMat.ofMat, HilbertVec.ofVec,
      PiLp.toLp_apply] using H.hess_memLp_normalizedCubeMeasure Q i j
  refine ⟨H, hHmat, ?_⟩
  have hnorm :
      eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) 2
          (normalizedCubeMeasure Q) =
        eLpNorm H.frobeniusMagnitude 2 (normalizedCubeMeasure Q) := by
    apply eLpNorm_congr_norm_ae
    exact ae_of_all _ fun x ↦ by
      have hnonneg : 0 ≤ matrixFrobeniusMagnitude (fun i j ↦ H.hess i j x) :=
        matrixFrobeniusMagnitude_nonneg _
      have habs : |matrixFrobeniusMagnitude (fun i j ↦ H.hess i j x)| =
          matrixFrobeniusMagnitude (fun i j ↦ H.hess i j x) :=
        abs_of_nonneg hnonneg
      simpa only [HasWeakHessianOn.frobeniusMagnitude, Real.norm_eq_abs,
        habs] using!
        (matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat
          (fun i j ↦ H.hess i j x)).symm
  have hleft :
      (eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) 2
          (normalizedCubeMeasure Q)).toReal = H.frobeniusNormalizedL2 Q := by
    rw [hnorm, H.frobeniusNormalizedL2_eq_frobeniusMagnitudeNormalizedLpNorm Q]
    unfold HasWeakHessianOn.frobeniusMagnitudeNormalizedLpNorm
      BoundedMeasurableDomain.normalizedLpNorm
      BoundedMeasurableDomain.normalizedLpFiniteENorm
      BoundedMeasurableDomain.normalizedLpENorm
    change (eLpNorm H.frobeniusMagnitude 2 (normalizedCubeMeasure Q)).toReal =
      (eLpNorm H.frobeniusMagnitude 2
        (cubeBoundedMeasurableDomain Q).normalizedVolume).toReal
    exact congrArg (fun μ ↦ (eLpNorm H.frobeniusMagnitude 2 μ).toReal)
      (cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure Q).symm
  have hright :
      H.frobeniusNormalizedL2 Q ≤
        CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact d *
          (eLpNorm F 2 (normalizedCubeMeasure Q)).toReal := by
    simpa only [Q, BoundedMeasurableDomain.normalizedLpNorm,
      BoundedMeasurableDomain.normalizedLpFiniteENorm,
      BoundedMeasurableDomain.normalizedLpENorm,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using hH
  apply (ENNReal.toReal_le_toReal hHmat.eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.eLpNorm_ne_top)).mp
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal
      (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d)]
  exact hleft.trans_le hright

end CubeCalderonZygmund

end

end Homogenization
