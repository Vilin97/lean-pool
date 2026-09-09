/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarTime
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear

/-! Time restriction and changes of time variable commute with actual smooth cylinder
representatives. -/

@[expose] public section


noncomputable section

namespace EulerLpCylinderTranslation

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerCylinderScalarPrimitive EulerMetricTransport
      EulerParameterWordGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K L : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace L] [CompactSpace L]

section Paths

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem timeComp_orbit_contDiff (p : C(K, CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p)) (φ : C(L, K)) :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (p.comp φ)) :=
  (ContinuousMap.compCLM ℝ (CylinderL2 P V) φ).contDiff.comp hp

theorem timeComp_norm (φ : C(L, K)) :
    ‖ContinuousMap.compCLM ℝ (CylinderL2 P V) φ‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg p)).2
  intro t
  exact p.norm_coe_le_norm (φ t)

theorem timeComp_block_le {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (p : C(K, CylinderL2 P V)) (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p))
    (φ : C(L, K)) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => pathTranslate P b (p.comp φ)) n a ≤
      block directions q (fun b => pathTranslate P b p) n a :=
  (block_comp_clm_le directions q (ContinuousMap.compCLM ℝ (CylinderL2 P V) φ) _ hp n a).trans
    ((mul_le_mul_of_nonneg_right (timeComp_norm P φ) (block_nonneg directions q _ n a)).trans_eq
      (one_mul _))

end Paths

theorem pointField_timeComp (p : C(K, CylinderL2 P Space))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p)) (φ : C(L, K)) (t : L) :
    pointField P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t = pointField P p hp (φ t) := by
  apply Measure.eq_of_ae_eq
    ((pointField_ae P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t).symm.trans
      (pointField_ae P p hp (φ t)))
  · exact smoothField_continuous P _ (pointField_smooth P (p.comp φ) (timeComp_orbit_contDiff P p
      hp φ) t)
  · exact smoothField_continuous P _ (pointField_smooth P p hp (φ t))

theorem scalarPointField_timeComp (p : C(K, CylinderL2 P ℝ))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p)) (φ : C(L, K)) (t : L) :
    scalarPointField P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t =
      scalarPointField P p hp (φ t) :=
  Measure.eq_of_ae_eq
    ((scalarPointField_ae P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t).symm.trans
      (scalarPointField_ae P p hp (φ t)))
    (scalarPointField_continuous P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t)
    (scalarPointField_continuous P p hp (φ t))

end EulerLpCylinderTranslation
