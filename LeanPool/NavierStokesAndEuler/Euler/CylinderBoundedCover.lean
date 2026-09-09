/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.SobolevJointEvaluation

@[expose] public section

/-! The real periodic lift of a genuine cylinder H3 field is bounded and
continuous. This construction uses the cylinder norm, never an L² norm on
the full real covering space. -/

noncomputable section


namespace EulerCylinderBoundedCover

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]

private local instance : NormedAddCommGroup (SobolevSpace P 3) := inferInstance
private local instance : NormedSpace ℝ (SobolevSpace P 3) := inferInstance
private local instance : NormedAddCommGroup (LiftTangent →ᵇ Space) := inferInstance
private local instance : NormedSpace ℝ (LiftTangent →ᵇ Space) := inferInstance

def cover (u : SobolevSpace P 3) : LiftTangent →ᵇ Space :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x) u)
    ((EulerSobolevPointEvaluation.representative_continuous P u).comp
      (coveringMap_isOpenQuotient P).continuous)
    (sobolevEmbeddingConstant P 3 * ‖u‖)
    (fun x => EulerSobolevPointEvaluation.representative_bound P u (coveringMap P x))

@[simp] theorem cover_apply (u : SobolevSpace P 3) (x : LiftTangent) :
    cover P u x = EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x) u := rfl

theorem cover_norm_le (u : SobolevSpace P 3) :
    ‖cover P u‖ ≤ sobolevEmbeddingConstant P 3 * ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (sobolevEmbeddingConstant_nonneg P 3) (norm_nonneg u))).2
  intro x
  exact EulerSobolevPointEvaluation.representative_bound P u (coveringMap P x)

def coverLinear : SobolevSpace P 3 →ₗ[ℝ] (LiftTangent →ᵇ Space) where
  toFun := cover P
  map_add' u v := by
    apply BoundedContinuousFunction.ext
    intro x
    exact (EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x)).map_add u v
  map_smul' c u := by
    apply BoundedContinuousFunction.ext
    intro x
    exact (EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x)).map_smul c u

def coverMap : SobolevSpace P 3 →L[ℝ] (LiftTangent →ᵇ Space) where
  toLinearMap := coverLinear P
  cont := AddMonoidHomClass.continuous_of_bound (coverLinear P)
    (sobolevEmbeddingConstant P 3) (cover_norm_le P)

theorem coverMap_norm_le : ‖coverMap P‖ ≤ sobolevEmbeddingConstant P 3 := by
  apply opNorm_le_bound _ (sobolevEmbeddingConstant_nonneg P 3)
  exact cover_norm_le P

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup C(K, SobolevSpace P 3) := inferInstance
private local instance : NormedSpace ℝ C(K, SobolevSpace P 3) := inferInstance
private local instance : NormedAddCommGroup C(K, LiftTangent →ᵇ Space) := inferInstance
private local instance : NormedSpace ℝ C(K, LiftTangent →ᵇ Space) := inferInstance

def coverPathMap : C(K, SobolevSpace P 3) →L[ℝ] C(K, LiftTangent →ᵇ Space) :=
  (coverMap P).compLeftContinuous ℝ K

theorem coverPathMap_norm_le :
    ‖coverPathMap (K := K) P‖ ≤ sobolevEmbeddingConstant P 3 := by
  apply opNorm_le_bound _ (sobolevEmbeddingConstant_nonneg P 3)
  intro p
  apply (ContinuousMap.norm_le _
    (mul_nonneg (sobolevEmbeddingConstant_nonneg P 3) (norm_nonneg p))).2
  intro t
  exact (cover_norm_le P (p t)).trans
    (mul_le_mul_of_nonneg_left (p.norm_coe_le_norm t) (sobolevEmbeddingConstant_nonneg P 3))

def coverPath (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    C(K, LiftTangent →ᵇ Space) := coverPathMap P (sobolevPath P 3 p hp)

@[simp] theorem coverPath_apply (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (t : K) (x : LiftTangent) :
    coverPath P p hp t x = pointField P p hp t (coveringMap P x) := rfl

def coverOrbit (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (a : LiftTangent) : C(K, LiftTangent →ᵇ Space) :=
  coverPathMap P (sobolevOrbit P 3 p hp a)

theorem coverOrbit_contDiff (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (coverOrbit P p hp) :=
  (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K, SobolevSpace P 3)) (F := C(K, LiftTangent →ᵇ Space))
    (coverPathMap (K := K) P)).comp (sobolevOrbit_contDiff P 3 p hp)

theorem coverOrbit_apply (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (a : LiftTangent) (t : K) (x : LiftTangent) :
    coverOrbit P p hp a t x = coverPath P p hp t (x+a) := by
  have hc : Continuous (pointField P p hp t) :=
    EulerSobolevPointEvaluation.representative_continuous P (sobolevPath P 3 p hp t)
  have he := EulerSobolevPointEvaluation.pointEvaluation_eq P (coveringMap P x)
    (sobolevOrbit P 3 p hp a t)
    (fun y => pointField P p hp t (y + coveringMap P a))
    (hc.comp (continuous_id.add continuous_const))
    (by
      rw [sobolevOrbit_value]
      exact (translate_ae P a (p t)).trans
        ((measurePreserving_translation P (coveringMap P a)).quasiMeasurePreserving.ae
          (pointField_ae P p hp t)))
  change EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x)
    (sobolevOrbit P 3 p hp a t) = pointField P p hp t (coveringMap P (x+a))
  rw [coveringMap_add]
  exact he

@[simp] theorem coverOrbit_zero (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    coverOrbit P p hp 0 = coverPath P p hp := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  simpa only [add_zero] using coverOrbit_apply P p hp 0 t x

end EulerCylinderBoundedCover
