/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
public import LeanPool.NavierStokesAndEuler.Euler.BoundedCoefficientJets
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientFrame

@[expose] public section

/-! Uniform time-path bounds for actual spatial derivatives of the multiplication operators. -/

noncomputable section

namespace EulerMeanCoefficients

open EulerSmoothLimit EulerMeanSolenoidal MeasureTheory InnerProductSpace Set
open scoped ContDiff BoundedContinuousFunction

section Paths

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V) := inferInstance

theorem SmoothCoefficientPath.iteratedFDeriv_translation_apply (A : SmoothCoefficientPath K V)
    (n : ℕ) (a : Space) (t : K) (x : Space) (v : Fin n → Space) :
    (iteratedFDeriv ℝ n (translateCoefficientPath A.field) a v) t x =
      iteratedFDeriv ℝ n (A.field t : Space → V) (x+a) v := by
  let ev : C(K, Space →ᵇ V) →L[ℝ] V :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (ContinuousMap.evalCLM ℝ t)
  have he := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
    (E := Space) (F := C(K, Space →ᵇ V)) (G := V) ev
    (A.translation_contDiff.contDiffAt (x := a)) (i := n) (by simp)
  have hv := congrArg (fun L : Space [×n]→L[ℝ] V => L v) he
  change iteratedFDeriv ℝ n (fun b => A.field t (x+b)) a v =
    (iteratedFDeriv ℝ n (translateCoefficientPath A.field) a v) t x at hv
  rw [iteratedFDeriv_comp_add_left] at hv
  exact hv.symm

/-- A pointwise coefficient-derivative bound is a bound in the actual uniform path norm. -/
theorem SmoothCoefficientPath.norm_iteratedFDeriv_translation_le (A : SmoothCoefficientPath K V)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath A.field) a‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (ContinuousMap.norm_le _ (mul_nonneg hC (by positivity))).2
  intro t
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (by positivity))).2
  intro x
  rw [A.iteratedFDeriv_translation_apply]
  exact ((iteratedFDeriv ℝ n (A.field t : Space → V) (x+a)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hbound t (x+a)) (by positivity))

end Paths

private local instance : NormedAddCommGroup Field := inferInstance
private local instance : NormedSpace ℝ Field := inferInstance
private local instance : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance

def operatorPathMap (T : ℝ) : C(Icc (0 : ℝ) T, Field) →L[ℝ]
    C(Icc (0 : ℝ) T, L2 →L[ℝ] L2) :=
  multiplierMap.compLeftContinuous ℝ (Icc (0 : ℝ) T)

@[simp] theorem operatorPathMap_apply (T : ℝ) (A : C(Icc (0 : ℝ) T, Field)) :
    operatorPathMap T A = operatorPath T A := rfl

theorem operatorPathMap_norm_le_one (T : ℝ) : ‖operatorPathMap T‖ ≤ 1 := by
  apply (operatorPathMap T).opNorm_le_bound zero_le_one
  intro A
  simpa only [one_mul, operatorPathMap_apply] using operatorPath_norm_le T A

theorem operatorPathTranslation_contDiff (T : ℝ)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)) :
    ContDiff ℝ ∞ (fun a => operatorPath T (translatedPath T A.field a)) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T, Field)) (F := C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (operatorPathMap T)).comp A.translation_contDiff

/-- The true parameter derivatives of the operator path inherit the exact pointwise bounds. -/
theorem norm_iteratedFDeriv_operatorPathTranslation_le (T : ℝ)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b => operatorPath T (translatedPath T A.field b)) a‖ ≤ C := by
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
    (F := C(Icc (0 : ℝ) T, Field)) (G := C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (operatorPathMap T) (A.translation_contDiff.contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right (operatorPathMap_norm_le_one T) (norm_nonneg _)).trans
    (by simpa only [one_mul] using A.norm_iteratedFDeriv_translation_le n C hC hbound a))

end EulerMeanCoefficients
