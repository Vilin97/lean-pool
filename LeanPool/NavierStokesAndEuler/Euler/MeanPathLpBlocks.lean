/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeContinuousTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.TimeLpMap

/-! Uniform-time spatial word bounds imply the genuine Bochner word bounds. -/

@[expose] public section


noncomputable section

namespace EulerMeanTimeContinuousTranslation

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerTimeLp EulerParameterWordGevrey
open scoped ContDiff

theorem pathLpOperator_norm_sqrt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (hT : 0 ≤ T) : ‖pathLpOperator (E := E) T hT‖ ≤ Real.sqrt T := by
  have hm : (measureUnivNNReal (timeMeasure T) : ℝ) = T := by
    change (timeMeasure T univ).toReal = T
    simp only [timeMeasure, Measure.restrict_apply_univ, Real.volume_Icc,
      sub_zero, ENNReal.toReal_ofReal hT]
  apply opNorm_le_bound _ (Real.sqrt_nonneg T)
  intro f
  simpa only [pathLpOperator_apply, hm, ← Real.sqrt_eq_rpow] using pathLp_bound T hT f

theorem timeTranslation_pathLp (T : ℝ) (hT : 0 ≤ T) (a : Space)
    (p : C(Icc (0 : ℝ) T, L2)) :
    timeTranslation T a (pathLp T hT p) = pathLp T hT (pathTranslation T a p) :=
  pathLp_map T hT (translation a).toContinuousLinearMap p

/-- The genuine Bochner embedding commutes with all external spatial words. -/
theorem pathLp_block_le {ι : Type*} [Fintype ι] (directions : ι → Space) (q : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) (n : ℕ) (x : Space) :
    block directions q (fun a : Space => timeTranslation T a (pathLp T hT p)) n x ≤
      Real.sqrt T*block directions q (fun a : Space => pathTranslation T a p) n x := by
  have he : (fun a : Space => timeTranslation T a (pathLp T hT p)) =
      (pathLpOperator T hT) ∘ (fun a : Space => pathTranslation T a p) :=
    funext (fun a => timeTranslation_pathLp T hT a p)
  have hb := block_comp_clm_le
    (E := C(Icc (0 : ℝ) T,L2)) (F := TimeLp T L2)
    directions q (pathLpOperator (E := L2) T hT)
    (fun a : Space => pathTranslation T a p) hp n x
  have hn : ‖pathLpOperator (E := L2) T hT‖ ≤ Real.sqrt T := pathLpOperator_norm_sqrt T hT
  exact (congrArg (fun f => block directions q f n x) he).trans_le
    (hb.trans (mul_le_mul_of_nonneg_right hn (block_nonneg directions q _ n x)))

end EulerMeanTimeContinuousTranslation
