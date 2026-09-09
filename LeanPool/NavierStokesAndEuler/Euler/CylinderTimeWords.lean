/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderClassicalWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlocks

@[expose] public section

/-! Every actual classical spatial/angular word differentiates in time on the closed interval. -/

noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerSobolevWordBlocks
  EulerLpCylinderTranslation EulerVolterraConvolution
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem pointField_word_eq_evaluation (p : C(K,LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (n : ℕ) (w : Fin n → Fin 4) (t : K) (x : LiftDomain P) :
    iteratedFieldDerivative P w (pointField P p hp t) x =
      EulerSobolevPointEvaluation.pointEvaluation P x
        (wordBlock P 3 n w (sobolevPath P (3+n) p hp t)) := by
  symm
  apply EulerSobolevPointEvaluation.pointEvaluation_eq
  · exact smoothField_continuous P _ (iteratedFieldDerivative_smooth P w _ (pointField_smooth P p
    hp t))
  · have he : value P (wordBlock P 3 n w (sobolevPath P (3+n) p hp t)) = strongWord P (p t) w := by
      rw [wordBlock_value]
      exact sobolev_coordinate P (3+n) (p t) (path_evaluation_smooth P p hp t)
        ⟨⟨n,by omega⟩,w⟩
    rw [he, pointField_eq_representative]
    exact strongWord_ae P (p t) (path_evaluation_smooth P p hp t) w

theorem pointField_word_joint_continuous (p : C(K,LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (n : ℕ) (w : Fin n → Fin 4) :
    Continuous (fun z : K × LiftDomain P => iteratedFieldDerivative P w (pointField P p hp z.1)
      z.2) := by
  let v : C(K,SobolevSpace P 3) := (wordBlock P 3 n w).compLeftContinuous ℝ K (sobolevPath P (3+n)
    p hp)
  have h := EulerSobolevJointEvaluation.path_representative_joint_continuous P v
  change Continuous (fun z : K × LiftDomain P => EulerSobolevPointEvaluation.pointEvaluation P z.2
    (wordBlock P 3 n w (sobolevPath P (3+n) p hp z.1))) at h
  simpa only [pointField_word_eq_evaluation] using h

variable (T : ℝ) (hT : 0 ≤ T) (p f : C(Icc (0 : ℝ) T,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hd in
/-- Time differentiation commutes with each actual spatial/angular word, including at endpoints. -/
theorem pointField_word_hasDerivWithinAt (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    HasDerivWithinAt (fun r => iteratedFieldDerivative P w (pointField P p hp (projIcc 0 T hT r)) x)
      (iteratedFieldDerivative P w (pointField P f hf t) x) (Icc (0 : ℝ) T) t := by
  let L := (EulerSobolevPointEvaluation.pointEvaluation P x).comp (wordBlock P 3 n w)
  have h := L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (sobolevPath_hasDerivWithinAt P T hT p f hp hf hd (3+n) t)
  change HasDerivWithinAt
    (fun r => EulerSobolevPointEvaluation.pointEvaluation P x
      (wordBlock P 3 n w (sobolevPath P (3+n) p hp (projIcc 0 T hT r))))
    (EulerSobolevPointEvaluation.pointEvaluation P x (wordBlock P 3 n w (sobolevPath P (3+n) f hf
      t)))
    (Icc (0 : ℝ) T) t at h
  rw [← pointField_word_eq_evaluation P f hf n w t x] at h
  apply h.congr_of_mem _ t.property
  intro r _
  exact pointField_word_eq_evaluation P p hp n w (projIcc 0 T hT r) x

end EulerCylinderSmoothOrbit
