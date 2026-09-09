/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeTranslation
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1ReconstructionNaturality

@[expose] public section

/-!
# Spatial translations of continuous ordinary-L² time paths

The actual H¹ reconstruction commutes with spatial translation. Therefore
regularity and bounds for its two Bochner fields imply uniform-in-time
spatial orbit regularity, and evaluation at each time loses no derivative
or additional constant.
-/

noncomputable section

namespace EulerMeanTimeContinuousTranslation

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerMeanTimeTranslation
  EulerTimeLp EulerTimeH1Reconstruction EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, L2) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, L2) := inferInstance

/-- Ordinary spatial translation of every time value of a continuous L² path. -/
def pathTranslation (T : ℝ) (a : Space) :
    C(Icc (0 : ℝ) T, L2) →L[ℝ] C(Icc (0 : ℝ) T, L2) :=
  (translation a).toContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) T)

@[simp] theorem pathTranslation_apply (T : ℝ) (a : Space)
    (p : C(Icc (0 : ℝ) T, L2)) (t : Icc (0 : ℝ) T) :
    pathTranslation T a p t = translation a (p t) := rfl

/-- Translation of the actual continuous reconstruction equals reconstruction
of the translated value and derivative fields. -/
theorem pathTranslation_reconstruction (T : ℝ) (hT : 0 ≤ T) (a : Space)
    (p q : TimeLp T L2) :
    pathTranslation T a (reconstruction T hT (p,q)) =
      reconstruction T hT (timeTranslation T a p, timeTranslation T a q) := by
  apply ContinuousMap.ext
  intro t
  exact (reconstruction_timeLift T hT (translation a).toContinuousLinearMap p q t).symm

/-- Uniform-in-time spatial regularity follows from the actual two-field H¹ data. -/
theorem reconstruction_translation_contDiff (T : ℝ) (hT : 0 ≤ T)
    (p q : TimeLp T L2) {n : ℕ∞ω}
    (hp : ContDiff ℝ n (fun a : Space => timeTranslation T a p))
    (hq : ContDiff ℝ n (fun a : Space => timeTranslation T a q)) :
    ContDiff ℝ n (fun a : Space => pathTranslation T a (reconstruction T hT (p,q))) := by
  have heq : (fun a : Space => pathTranslation T a (reconstruction T hT (p,q))) =
      fun a : Space => reconstruction T hT (timeTranslation T a p, timeTranslation T a q) :=
    funext (fun a => pathTranslation_reconstruction T hT a p q)
  exact Eq.mpr (congrArg (fun g : Space → C(Icc (0 : ℝ) T, L2) => ContDiff ℝ n g) heq)
    (reconstruction_contDiff T hT (fun a : Space => timeTranslation T a p)
      (fun a : Space => timeTranslation T a q) hp hq)

/-- The true uniform-time norm of every spatial orbit derivative has only the
proved H¹ trace cost. -/
theorem reconstruction_translation_gevrey (T : ℝ) (hT : 0 < T)
    (p q : TimeLp T L2)
    (hp : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a p))
    (hq : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a q))
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (d : ℕ)
    (hbp : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b p) a‖ ≤ C*majorant R d
      n)
    (hbq : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b q) a‖ ≤ D*majorant R d
      n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space =>
      pathTranslation T b (reconstruction T hT.le (p,q))) a‖ ≤
        ((T⁻¹*Real.sqrt T)*C+(2*Real.sqrt T)*D)*majorant R d n := by
  have heq : (fun b : Space => pathTranslation T b (reconstruction T hT.le (p,q))) =
      fun b : Space => reconstruction T hT.le (timeTranslation T b p, timeTranslation T b q) :=
    funext (fun b => pathTranslation_reconstruction T hT.le b p q)
  exact (congrArg (fun g : Space → C(Icc (0 : ℝ) T, L2) => ‖iteratedFDeriv ℝ n g a‖) heq).trans_le
    (reconstruction_gevrey T hT (fun b : Space => timeTranslation T b p)
      (fun b : Space => timeTranslation T b q) hp hq R C D hR hC hD d hbp hbq n a)

/-- Time evaluation is a norm contraction on continuous ordinary-L² paths. -/
theorem evaluation_norm_le (T : ℝ) (t : Icc (0 : ℝ) T) :
    ‖(ContinuousMap.evalCLM ℝ t : C(Icc (0 : ℝ) T, L2) →L[ℝ] L2)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro p
  simpa only [ContinuousMap.evalCLM_apply, one_mul] using p.norm_coe_le_norm t

/-- Every actual time value has a smooth ordinary spatial translation orbit. -/
theorem pathTranslation_evaluation_contDiff (T : ℝ)
    (p : C(Icc (0 : ℝ) T, L2)) {n : ℕ∞ω}
    (hp : ContDiff ℝ n (fun a : Space => pathTranslation T a p)) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ n (fun a : Space => translation a (p t)) := by
  change ContDiff ℝ n ((ContinuousMap.evalCLM ℝ t) ∘ (fun a : Space => pathTranslation T a p))
  exact ContDiff.comp (g := ContinuousMap.evalCLM ℝ t) (f := fun a : Space => pathTranslation T a p)
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := C(Icc (0 : ℝ) T, L2)) (F := L2) (ContinuousMap.evalCLM ℝ t)) hp

/-- Time evaluation preserves every uniform spatial factorial bound without loss. -/
theorem pathTranslation_evaluation_gevrey (T : ℝ)
    (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b p) a‖ ≤ C*majorant R d n)
    (t : Icc (0 : ℝ) T) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translation b (p t)) a‖ ≤ C*majorant R d n :=
  contraction_bound (ContinuousMap.evalCLM ℝ t : C(Icc (0 : ℝ) T, L2) →L[ℝ] L2)
    (evaluation_norm_le T t) (fun b : Space => pathTranslation T b p) hp R C hR hC d hb n a

end EulerMeanTimeContinuousTranslation
