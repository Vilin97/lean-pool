/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeContinuousTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanOrbitSobolev
import LeanPool.NavierStokesAndEuler.Euler.MeanSpatialEvaluation
import LeanPool.NavierStokesAndEuler.Euler.SobolevJointEvaluation
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! Jointly continuous ordinary spatial representatives of continuous L² paths with smooth spatial
orbits. -/

@[expose] public section


noncomputable section


namespace EulerMeanSmoothRepresentative

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevPointEvaluation
  EulerMeanTimeContinuousTranslation
open scoped ContDiff

local instance instMeanPathSpatialRepresentative1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Evaluation at time commutes with every actual spatial derivative tensor. -/
theorem path_orbit_tensor_evaluation (T : ℝ) (p : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a (p t)) 0 =
      (ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a p) 0) :=
  (ContinuousMap.evalCLM ℝ t).iteratedFDeriv_comp_left hp.contDiffAt (by simp)

/-- The finite Sobolev array is a continuous path, constructed from actual tensor evaluations.
No operator-norm continuity of the time-evaluation operators is needed. -/
theorem ordinarySobolev_path_continuous (T : ℝ) (p : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) (q : ℕ) :
    Continuous (fun t => ordinarySobolev q (p t) (pathTranslation_evaluation_contDiff T p hp t)) :=
        by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  change Continuous (fun t =>
    (ordinarySobolev q (p t) (pathTranslation_evaluation_contDiff T p hp t)).val w)
  simp_rw [ordinarySobolev_coordinate, path_orbit_tensor_evaluation T p hp]
  let K := iteratedFDeriv ℝ w.1.val (fun a : Space => pathTranslation T a p) 0 (coordinateTuple w.2)
  change Continuous (fun t => ordinaryLift (K t))
  exact ordinaryLift.continuous.comp K.continuous

/-- The reconstructed spatial field is jointly continuous in actual time and space. -/
theorem path_representative_joint_continuous (T : ℝ)
    (p : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) :
    Continuous (fun z : Icc (0 : ℝ) T × Space =>
      representative (p z.1) (pathTranslation_evaluation_contDiff T p hp z.1) z.2) := by
  have hc := ordinarySobolev_path_continuous T p hp 3
  have hpair : Continuous (fun z : Icc (0 : ℝ) T × Space =>
      (ordinarySobolev 3 (p z.1) (pathTranslation_evaluation_contDiff T p hp z.1),
        (z.2, (0 : AddCircle (1 : ℝ))))) :=
    (hc.comp continuous_fst).prodMk (continuous_snd.prodMk continuous_const)
  have H := (EulerSobolevJointEvaluation.pointEvaluation_joint_continuous 1).comp hpair
  simpa only [Function.comp_def, pointEvaluation_ordinary] using H

theorem path_representative_smooth (T : ℝ)
    (p : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (representative (p t) (pathTranslation_evaluation_contDiff T p hp t)) :=
  representative_smooth _ _

theorem path_representative_ae (T : ℝ)
    (p : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) (t : Icc (0 : ℝ) T) :
    (p t : Space → Space) =ᵐ[volume]
      representative (p t) (pathTranslation_evaluation_contDiff T p hp t) :=
  representative_ae _ _

end EulerMeanSmoothRepresentative
