/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVorticity
import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! Scalar components of genuine smooth velocity and vorticity fields,
their exact elliptic identity, and a fixed coordinate operator bound. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap Laplacian
  EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerVectorCalculus EulerMeanCutoffCurl EulerMeanVectorIdentities Finset
open scoped ContDiff

/-- Component field, given by `mapField (EuclideanSpace.proj j) A`. -/
def componentField (A : SmoothL2Field Space) (j : Fin 3) : SmoothL2Field ℝ :=
  mapField (EuclideanSpace.proj j) A

@[simp] theorem componentField_apply (A : SmoothL2Field Space) (j : Fin 3) (x : Space) :
    (componentField A j).field x=A.field x j := rfl

theorem componentField_toLp_norm (A : SmoothL2Field Space) (j : Fin 3) :
    ‖(componentField A j).toLp‖ ≤ ‖A.toLp‖ :=
  (mapField_norm_le (EuclideanSpace.proj j : Space →L[ℝ] ℝ) A).trans
    ((mul_le_mul_of_nonneg_right (norm_coordinate_le j) (norm_nonneg _)).trans_eq (one_mul _))

theorem componentField_jetLp_norm (A : SmoothL2Field Space) (j : Fin 3) (n : ℕ) :
    ‖(componentField A j).jetLp n‖ ≤ ‖A.jetLp n‖ := by
  have hJ : ‖jetPostcompose (EuclideanSpace.proj j : Space →L[ℝ] ℝ) n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro F
    change ‖(EuclideanSpace.proj j).compContinuousMultilinearMap F‖ ≤ 1*‖F‖
    exact ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).norm_compContinuousMultilinearMap_le F).trans
      (mul_le_mul_of_nonneg_right (norm_coordinate_le j) (norm_nonneg _))
  change ‖(mapField (EuclideanSpace.proj j) A).jetLp n‖ ≤ _
  rw [jetLp_mapField]
  exact ((jetPostcompose (EuclideanSpace.proj j : Space →L[ℝ] ℝ) n).norm_compLp_le (A.jetLp
      n)).trans
    ((mul_le_mul_of_nonneg_right hJ (norm_nonneg _)).trans_eq (one_mul _))

theorem componentField_partial (A : SmoothL2Field Space) (j i : Fin 3) (x : Space) :
    partialDerivative (componentField A j).field i x=(fderiv ℝ A.field x (axis i)) j :=
  EulerVectorCalculus.fderiv_coordinate A.field x (A.smooth.differentiable (by simp) x) j (axis i)

theorem componentField_laplacian (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (j : Fin 3) (x : Space) :
    Δ (componentField A j).field x =
      partialDerivative (componentField (vorticityField A) (j+1)).field (j+2) x -
        partialDerivative (componentField (vorticityField A) (j+2)).field (j+1) x := by
  have hz : _root_.gradient (divergence A.field) x=0 := by
    rw [show divergence A.field=(fun _ : Space => (0 : ℝ)) from funext hdiv]
    exact gradient_fun_const x 0
  have hc := congrArg (fun y : Space => y j) (congrFun (vectorCurl_vectorCurl A.field A.smooth) x)
  change (vectorCurl (vectorCurl A.field) x) j=(_root_.gradient (divergence A.field) x-Δ A.field x)
      j at hc
  rw [hz,zero_sub,PiLp.neg_apply,vector_laplacian_coordinate A.field A.smooth x j] at hc
  have hv (i : Fin 3) : (componentField (vorticityField A) i).field =
      fun y => vectorCurl A.field y i := by
    funext y
    rw [componentField_apply,vorticityField_apply]
  rw [hv (j+1),hv (j+2)]
  change Δ (fun y => A.field y j) x=_
  change partialDerivative (fun y => vectorCurl A.field y (j+2)) (j+1) x -
      partialDerivative (fun y => vectorCurl A.field y (j+1)) (j+2) x =
        -(Δ (fun y => A.field y j) x) at hc
  linarith

theorem operator_norm_le_of_entries (L : Space →L[ℝ] Space) (K : ℝ) (hK : 0 ≤ K)
    (hentries : ∀ i j : Fin 3, ‖(L (axis i)) j‖ ≤ K) : ‖L‖ ≤ 9*K := by
  have ha (i : Fin 3) : ‖L (axis i)‖ ≤ 3*K := by
    apply (EulerMeanCutoffCurl.norm_le_sum_coordinates _).trans
    calc
      _ ≤ ∑ _j : Fin 3, K := sum_le_sum (fun j _ => hentries i j)
      _ = _ := by simp
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hK)
  intro v
  have hv : (∑ i : Fin 3, (v i) • axis i)=v := by
    ext j
    simp [axis,Pi.single_apply]
  have hLv : L v=∑ i : Fin 3, (v i) • L (axis i) := by
    calc
      L v=L (∑ i : Fin 3, (v i) • axis i) := congrArg L hv.symm
      _ = _ := by simp only [map_sum,map_smul]
  rw [hLv]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, ‖v‖*(3*K) := by
      apply sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v i) (ha i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end EulerOrdinarySobolev
