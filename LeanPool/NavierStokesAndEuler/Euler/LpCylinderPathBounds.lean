/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity

@[expose] public section

/-! Actual mixed coefficient jets in the uniform-time L² operator norm. -/

noncomputable section

namespace EulerLpCylinderRectangular

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)] {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup C(K,Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ C(K,Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P F) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P F) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E →L[ℝ] CylinderL2 P F) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P F) := inferInstance
private local instance : NormedAddCommGroup C(K,CylinderL2 P E →L[ℝ] CylinderL2 P F) :=
  inferInstance
private local instance : NormedSpace ℝ C(K,CylinderL2 P E →L[ℝ] CylinderL2 P F) := inferInstance

def mixedOperatorPath (A : C(K,Space →ᵇ E →L[ℝ] F)) (a : LiftTangent) :
    C(K,CylinderL2 P E →L[ℝ] CylinderL2 P F) := fullPathMap P (translateCoefficientPath A a.1)

theorem mixedOperatorPath_contDiff (A : C(K,Space →ᵇ E →L[ℝ] F))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A)) :
    ContDiff ℝ ∞ (mixedOperatorPath P A) :=
  (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K,Space →ᵇ E →L[ℝ] F)) (F := C(K,CylinderL2 P E →L[ℝ] CylinderL2 P F))
    (fullPathMap P)).comp (hA.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff)

theorem mixedOperatorPath_bound (A : C(K,Space →ᵇ E →L[ℝ] F))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A)) (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath A) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (mixedOperatorPath P A) a‖ ≤ C := by
  let f := translateCoefficientPath A
  have hright : ‖iteratedFDeriv ℝ n (f ∘ ContinuousLinearMap.fst ℝ Space ℝ) a‖ ≤ C := by
    rw [(ContinuousLinearMap.fst ℝ Space ℝ).iteratedFDeriv_comp_right hA a (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    calc
      _ ≤ ‖iteratedFDeriv ℝ n f a.1‖ * ∏ _i : Fin n, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ Space ℝ)
      _ ≤ C := by simpa only [Finset.prod_const_one,mul_one] using hb a.1
  have hleft := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := LiftTangent)
    (F := C(K,Space →ᵇ E →L[ℝ] F)) (G := C(K,CylinderL2 P E →L[ℝ] CylinderL2 P F))
    (fullPathMap P) ((hA.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff).contDiffAt (x := a))
    (n := n) (by simp)
  exact hleft.trans ((mul_le_mul_of_nonneg_right (fullPathMap_norm P)
    (norm_nonneg _)).trans (by simpa only [one_mul] using hright))

end EulerLpCylinderRectangular
