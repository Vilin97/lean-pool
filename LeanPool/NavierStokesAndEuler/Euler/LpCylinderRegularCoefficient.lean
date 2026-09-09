/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients

@[expose] public section

/-! A genuinely smooth translated bounded-field family lifts to actual mixed cylinder coefficients.
  -/

noncomputable section

namespace EulerLpCylinderCoefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderPaths
  EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ)
  (B : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (Supported period V S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported period V S hS) := inferInstance
private local instance : NormedAddCommGroup (Supported period V S hS →L[ℝ] Supported period V S hS)
  := inferInstance
private local instance : NormedSpace ℝ (Supported period V S hS →L[ℝ] Supported period V S hS) :=
  inferInstance

include hB in
/-- This requires only actual translated coefficient regularity, so applies to the constructed Gram generator. -/
theorem mixedCoefficient_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => liftedOperatorPath period S hS T (translateCoefficientPath
      B a.1)) :=
  (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
    (F := C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS))
    (liftedOperatorPathMap period S hS T)).comp
      (hB.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff)

include hB in
/-- All actual mixed coefficient derivatives retain the real bounded-field derivative bound. -/
theorem mixedCoefficient_bound (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => liftedOperatorPath period S hS T
      (translateCoefficientPath B b.1)) a‖ ≤ C := by
  let f := translateCoefficientPath B
  have hright : ‖iteratedFDeriv ℝ n (f ∘ ContinuousLinearMap.fst ℝ Space ℝ) a‖ ≤ C := by
    rw [(ContinuousLinearMap.fst ℝ Space ℝ).iteratedFDeriv_comp_right hB a (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    calc
      _ ≤ ‖iteratedFDeriv ℝ n f a.1‖ * ∏ _i : Fin n, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ =>
          ContinuousLinearMap.norm_fst_le ℝ Space ℝ)
      _ ≤ C := by simpa only [Finset.prod_const_one,mul_one] using hb a.1
  have hleft := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := LiftTangent)
    (F := C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
    (G := C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS))
    (liftedOperatorPathMap period S hS T)
    ((hB.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff).contDiffAt (x := a)) (n := n) (by simp)
  exact hleft.trans ((mul_le_mul_of_nonneg_right (liftedOperatorPathMap_norm period S hS T)
    (norm_nonneg _)).trans (by simpa only [one_mul] using hright))

end EulerLpCylinderCoefficients
