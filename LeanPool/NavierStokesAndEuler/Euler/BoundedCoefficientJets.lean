/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedCoefficientSmooth
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Actual derivatives and factorial bounds for the translated multiplication operators. -/

@[expose] public section


noncomputable section

namespace EulerMeanCoefficients

open EulerSmoothLimit MeasureTheory InnerProductSpace
open scoped ContDiff BoundedContinuousFunction

section BoundedFields

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Evaluating a parameter derivative gives the ordinary spatial derivative at the translated point.
-/
theorem BoundedSmoothField.iteratedFDeriv_translation_apply (A : BoundedSmoothField V)
    (n : ℕ) (a x : Space) (v : Fin n → Space) :
    (iteratedFDeriv ℝ n (translated A.field) a v) x =
      iteratedFDeriv ℝ n (A.field : Space → V) (x+a) v := by
  let ev : (Space →ᵇ V) →L[ℝ] V := BoundedContinuousFunction.evalCLM ℝ x
  have he := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
    (E := Space) (F := Space →ᵇ V) (G := V) ev
    (A.translation_contDiff.contDiffAt (x := a)) (i := n) (by simp)
  have hv := congrArg (fun L : Space [×n]→L[ℝ] V => L v) he
  change iteratedFDeriv ℝ n (fun b => A.field (x+b)) a v =
    (iteratedFDeriv ℝ n (translated A.field) a v) x at hv
  rw [iteratedFDeriv_comp_add_left] at hv
  exact hv.symm

/-- Passing from pointwise spatial bounds to parameter derivatives in sup norm costs no constant. -/
theorem BoundedSmoothField.norm_iteratedFDeriv_translation_le (A : BoundedSmoothField V)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ n (A.field : Space → V) x‖ ≤ C) (a : Space) :
    ‖iteratedFDeriv ℝ n (translated A.field) a‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (by positivity))).2
  intro x
  rw [A.iteratedFDeriv_translation_apply]
  exact ((iteratedFDeriv ℝ n (A.field : Space → V) (x+a)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hbound (x+a)) (by positivity))

end BoundedFields

/-- Cache the standard `NormedAddCommGroup Field` instance to shorten typeclass synthesis. -/
local instance instBoundedCoefficientJets1 : NormedAddCommGroup Field := inferInstance
/-- Cache the standard `NormedSpace ℝ Field` instance to shorten typeclass synthesis. -/
local instance instBoundedCoefficientJets2 : NormedSpace ℝ Field := inferInstance
/-- Cache the standard `NormedAddCommGroup (EulerMeanSolenoidal.L2 →L[ℝ]
EulerMeanSolenoidal.L2)` instance to shorten typeclass synthesis. -/
local instance instBoundedCoefficientJets3 : NormedAddCommGroup (EulerMeanSolenoidal.L2 →L[ℝ]
    EulerMeanSolenoidal.L2)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2)`
instance to shorten typeclass synthesis. -/
local instance instBoundedCoefficientJets4 : NormedSpace ℝ (EulerMeanSolenoidal.L2 →L[ℝ]
    EulerMeanSolenoidal.L2) :=
    inferInstance

theorem multiplierMap_norm_le_one : ‖multiplierMap‖ ≤ 1 :=
  multiplierMap.opNorm_le_bound zero_le_one (fun A => by
    simpa only [one_mul, multiplierMap_apply] using multiplier_norm_le A)

theorem multiplierTranslation_contDiff (A : BoundedSmoothField (Space →L[ℝ] Space)) :
    ContDiff ℝ ∞ (fun a => multiplier (translated A.field a)) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := Field)
    (F := EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2) multiplierMap).comp
        A.translation_contDiff

theorem norm_iteratedFDeriv_multiplierTranslation_le
    (A : BoundedSmoothField (Space →L[ℝ] Space)) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖iteratedFDeriv ℝ n (A.field : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b => multiplier (translated A.field b)) a‖ ≤ C := by
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
    (F := Field) (G := EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2)
    multiplierMap (A.translation_contDiff.contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right multiplierMap_norm_le_one (norm_nonneg _)).trans
    (by simpa only [one_mul] using A.norm_iteratedFDeriv_translation_le n C hC hbound a))

end EulerMeanCoefficients
