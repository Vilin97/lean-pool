/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOrbitSobolev

@[expose] public section

/-! Bounded point evaluation and joint continuity of reconstructed ordinary-space fields. -/

noncomputable section

namespace EulerMeanSmoothRepresentative

open MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevPointEvaluation
open scoped ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem ordinaryLift_representative_ae (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) :
    (ordinaryLift u : LiftDomain 1 → Space) =ᵐ[liftMeasure 1]
      fun x => representative u hu x.1 :=
  (ordinaryLift_ae u).trans
    (ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae (representative_ae u hu))

/-- The previously constructed bounded Sobolev evaluation is the actual ordinary representative. -/
theorem pointEvaluation_ordinary (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (x : Space) :
    pointEvaluation 1 (x, 0) (ordinarySobolev 3 u hu) = representative u hu x := by
  apply pointEvaluation_eq 1 (x, 0) (ordinarySobolev 3 u hu)
    (fun p : LiftDomain 1 => representative u hu p.1)
    ((representative_smooth u hu).continuous.comp continuous_fst)
  rw [ordinarySobolev_value]
  exact ordinaryLift_representative_ae u hu

/-- Point values are controlled by finitely many actual L² derivatives, uniformly in the spatial point. -/
theorem representative_bound (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (x : Space) :
    ‖representative u hu x‖ ≤ sobolevEmbeddingConstant 1 3 *
      ∑ n ∈ Finset.range 4,
        ‖iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a u) 0‖ := by
  have H := EulerSobolevPointEvaluation.representative_bound 1 (ordinarySobolev 3 u hu) (x, 0)
  change ‖pointEvaluation 1 (x, 0) (ordinarySobolev 3 u hu)‖ ≤
    sobolevEmbeddingConstant 1 3 * ‖ordinarySobolev 3 u hu‖ at H
  rw [pointEvaluation_ordinary] at H
  exact H.trans (mul_le_mul_of_nonneg_left (ordinarySobolev_norm_le 3 u hu)
    (sobolevEmbeddingConstant_nonneg 1 3))

/-- A family with continuous genuine L² derivatives through order three has jointly continuous values. -/
theorem representative_joint_continuous {T : Type*} [TopologicalSpace T]
    (u : T → EulerMeanSolenoidal.L2) (hu : ∀ t, SmoothOrbit (u t))
    (hjet : ∀ n ≤ 3, Continuous
      (fun t => iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a (u t)) 0)) :
    Continuous (fun p : T × Space => representative (u p.1) (hu p.1) p.2) := by
  have hc := ordinarySobolev_continuous 3 u hu hjet
  have hp : Continuous (fun p : T × Space =>
      (ordinarySobolev 3 (u p.1) (hu p.1), (p.2, (0 : AddCircle (1 : ℝ))))) :=
    (hc.comp continuous_fst).prodMk (continuous_snd.prodMk continuous_const)
  have H := (EulerSobolevJointEvaluation.pointEvaluation_joint_continuous 1).comp hp
  simpa only [Function.comp_def, pointEvaluation_ordinary] using H

end EulerMeanSmoothRepresentative
