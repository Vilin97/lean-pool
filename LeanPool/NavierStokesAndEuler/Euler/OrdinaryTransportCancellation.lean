/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryL2Integration

@[expose] public section

/-! The exact ordinary transport energy cancellation on noncompact
smooth L² fields. Products and all required pairings are actual L²/L¹ objects. -/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerVectorCalculus Finset
open scoped ContDiff

theorem field_toLp_zero (A : SmoothL2Field Space) (hA : A.field=0) : A.toLp=0 := by
  apply Lp.ext
  filter_upwards [A.toLp_ae,Lp.coeFn_zero Space 2 (volume : Measure Space)] with x ha hz
  rw [ha,hA,hz]

theorem scalarProduct_inner_shift (A : SmoothL2Field ℝ) (B C : SmoothL2Field Space) :
    ⟪(scalarProduct A B).toLp,C.toLp⟫_ℝ = ⟪(scalarProduct A C).toLp,B.toLp⟫_ℝ := by
  rw [field_inner,field_inner]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [scalarProduct_field,real_inner_smul_left]
  rw [real_inner_comm (B.field x) (C.field x)]

theorem scalar_transport_pair (A : SmoothL2Field ℝ) (B : SmoothL2Field Space) (v : Space) :
    2*⟪(scalarProduct A (B.directionalField v)).toLp,B.toLp⟫_ℝ =
      -⟪(scalarProduct (A.directionalField v) B).toLp,B.toLp⟫_ℝ := by
  have h := field_directional_inner (scalarProduct A B) B v
  rw [scalarProduct_directional,toLp_addField,inner_add_left,scalarProduct_inner_shift A B] at h
  linarith

theorem coordinate_directional_field (A : SmoothL2Field Space) (i : Fin 3) (v x : Space) :
    ((mapField (EuclideanSpace.proj i) A).directionalField v).field x =
      (fderiv ℝ A.field x v) i := by
  change fderiv ℝ (fun y => A.field y i) x v=(fderiv ℝ A.field x v) i
  exact fderiv_coordinate A.field x (A.smooth.differentiable (by simp) x) i v

theorem advection_inner_zero (A B : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x=0) :
    ⟪(advectionField A B).toLp,B.toLp⟫_ℝ=0 := by
  let a := fun i : Fin 3 => mapField (EuclideanSpace.proj i) A
  let c := fun i : Fin 3 => scalarProduct ((a i).directionalField (axis i)) B
  have hcf : (sumField univ c).field=0 := by
    funext x
    simp only [sumField_field,c,scalarProduct_field,← Finset.sum_smul]
    have hs : (∑ i : Fin 3, ((a i).directionalField (axis i)).field x)=0 := by
      simp only [a,coordinate_directional_field]
      simpa only [divergence_eq_coordinate_sum,axis] using hdiv x
    rw [hs,zero_smul]
    rfl
  have hc : (∑ i : Fin 3, ⟪(c i).toLp,B.toLp⟫_ℝ)=0 := by
    rw [← sum_inner,← toLp_sumField,field_toLp_zero _ hcf,inner_zero_left]
  have hp (i : Fin 3) := scalar_transport_pair (a i) B (axis i)
  have hsum := congrArg (fun f : Fin 3 → ℝ => ∑ i, f i) (funext hp)
  simp only [← Finset.mul_sum,Finset.sum_neg_distrib] at hsum
  change 2*(∑ i : Fin 3, ⟪(coordinateProduct i A (B.directionalField (axis i))).toLp,B.toLp⟫_ℝ)=
    -(∑ i : Fin 3, ⟪(c i).toLp,B.toLp⟫_ℝ) at hsum
  rw [hc] at hsum
  rw [advectionField,toLp_sumField,sum_inner]
  linarith

end EulerOrdinarySobolev
