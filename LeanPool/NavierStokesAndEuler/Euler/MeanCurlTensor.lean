/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator

/-! The ordinary curl as a bounded antisymmetrization of actual L² gradient tensors. -/

@[expose] public section


noncomputable section

namespace EulerMeanCurlTensor

open MeasureTheory EulerSmoothLimit EulerVectorCalculus EulerMeanSolenoidal
  EulerMeanCutoffCurl EulerMeanGradientTest EulerMeanBoundary
open scoped ContDiff ENNReal NNReal

/-- Coordinate insertion, given by `(EuclideanSpace.proj j).smulRight (EuclideanSpace.single i
1)`. -/
def coordinateInsertion (i j : Fin 3) : Space →L[ℝ] Space :=
  (EuclideanSpace.proj j).smulRight (EuclideanSpace.single i 1)

theorem coordinateInsertion_norm_le (i j : Fin 3) : ‖coordinateInsertion i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  simpa [coordinateInsertion, ContinuousLinearMap.smulRight_apply, norm_smul] using
      PiLp.norm_apply_le v j

/-- Coordinate L², given by `(coordinateInsertion i j).compLpL 2 volume`. -/
def coordinateL2 (i j : Fin 3) : L2 →L[ℝ] L2 :=
  (coordinateInsertion i j).compLpL 2 volume

theorem coordinateL2_ae (i j : Fin 3) (u : L2) :
    coordinateL2 i j u =ᵐ[volume] fun x => (u x j) • EuclideanSpace.single i 1 :=
  (coordinateInsertion i j).coeFn_compLpL (p := 2) (μ := volume) u

theorem coordinateL2_apply_norm_le (i j : Fin 3) (u : L2) : ‖coordinateL2 i j u‖ ≤ ‖u‖ := by
  refine ((coordinateInsertion i j).norm_compLp_le u).trans ?_
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (coordinateInsertion_norm_le i j)
      (norm_nonneg u)

/-- Each output component is the difference of the two off-diagonal derivative entries. -/
def curlTensor : GradientTensor →L[ℝ] L2 :=
  ∑ i : Fin 3,
    ((coordinateL2 i (i+2)).comp (PiLp.proj 2 (fun _ : Fin 3 => L2) (i+1)) -
      (coordinateL2 i (i+1)).comp (PiLp.proj 2 (fun _ : Fin 3 => L2) (i+2)))

theorem curlTensor_apply (G : GradientTensor) :
    curlTensor G = ∑ i : Fin 3,
      (coordinateL2 i (i+2) (G (i+1)) - coordinateL2 i (i+1) (G (i+2))) := by
  simp [curlTensor]

/-- A fixed universal contraction bound; sharpness is not needed for localization. -/
theorem curlTensor_norm_le (G : GradientTensor) : ‖curlTensor G‖ ≤ 6 * ‖G‖ := by
  rw [curlTensor_apply]
  calc
    _ ≤ ∑ i : Fin 3, ‖coordinateL2 i (i+2) (G (i+1)) - coordinateL2 i (i+1) (G (i+2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 2 * ‖G‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := (coordinateL2_apply_norm_le i (i+2) (G (i+1))).trans (PiLp.norm_apply_le G (i+1))
      have h2 := (coordinateL2_apply_norm_le i (i+1) (G (i+2))).trans (PiLp.norm_apply_le G (i+2))
      exact (norm_sub_le _ _).trans (by linarith)
    _ = 6 * ‖G‖ := by simp; ring

theorem curlTensor_ae (G : GradientTensor) :
    curlTensor G =ᵐ[volume] fun x => WithLp.toLp 2 (fun i : Fin 3 =>
      (G (i+1) x) (i+2) - (G (i+2) x) (i+1)) := by
  rw [curlTensor_apply]
  have hpart (i : Fin 3) :
      (coordinateL2 i (i+2) (G (i+1)) - coordinateL2 i (i+1) (G (i+2))) =ᵐ[volume]
        fun x => ((G (i+1) x) (i+2) - (G (i+2) x) (i+1)) • EuclideanSpace.single i 1 := by
    filter_upwards [Lp.coeFn_sub (coordinateL2 i (i+2) (G (i+1)))
      (coordinateL2 i (i+1) (G (i+2))), coordinateL2_ae i (i+2) (G (i+1)),
      coordinateL2_ae i (i+1) (G (i+2))] with x hs h1 h2
    simp only [Pi.sub_apply] at hs
    rw [hs, h1, h2, sub_smul]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin 3 => coordinateL2 i (i+2) (G (i+1)) - coordinateL2 i (i+1) (G (i+2))),
    ae_all_iff.mpr hpart] with x hs hp
  simp only [Finset.sum_apply] at hs
  rw [hs]
  simp_rw [hp]
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three]

/-- On genuine test gradients the tensor operator is exactly the ordinary classical curl. -/
theorem curlTensor_test_ae (f : Test) :
    curlTensor (testGradient f) =ᵐ[volume] vectorCurl (f : Space → Space) := by
  filter_upwards [curlTensor_ae (testGradient f),
    ae_all_iff.mpr (fun i => derivativeColumn_ae f i)] with x hc hd
  rw [hc, vectorCurl_eq_matrix _ x ((f.smooth.differentiable (by simp)).differentiableAt)]
  ext i
  change (derivativeColumn f (i+1) x) (i+2) - (derivativeColumn f (i+2) x) (i+1) = _
  rw [hd, hd]
  rfl

/-- The source's field `w`, formed directly from the weak potential's gradient tensor. -/
def harmonicPart (χ : Cutoff) (z : L2) : L2 :=
  curlTensor (weakPotential χ z : GradientTensor)

theorem harmonicPart_norm_le (χ : Cutoff) (z : L2) :
    ‖harmonicPart χ z‖ ≤ 6 * ‖weakPotential χ z‖ :=
  curlTensor_norm_le (weakPotential χ z : GradientTensor)

end EulerMeanCurlTensor
