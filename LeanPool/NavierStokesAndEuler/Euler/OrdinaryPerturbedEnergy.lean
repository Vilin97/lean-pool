/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
import Mathlib.Algebra.Order.Star.Real

/-! Actual L² stability of projected Euler with a small additive
defect. The reference gradient is the only solution coefficient. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanClassical EulerVolterraConvolution Finset
open scoped ContDiff Topology

theorem projected_difference_energy (A B : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (hB : B.toLp ∈ solenoidalSpace)
    (K : ℝ) (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) :
    2*⟪B.toLp-A.toLp,(projectedRhs B).toLp-(projectedRhs A).toLp⟫_ℝ ≤
      2*K*‖B.toLp-A.toLp‖^2 := by
  let W := fieldSub B A
  let P := fieldSub (pressureField B) (pressureField A)
  have he : fieldSub (projectedRhs B) (projectedRhs A)=differenceRhs A W P := by
    apply field_ext
    funext x
    have hw : W.field=B.field-A.field := funext (fieldSub_field B A)
    simp only [fieldSub_field,projectedRhs_field,differenceRhs_field,hw,P]
    rw [fderiv_sub (B.smooth.differentiable (by simp) x) (A.smooth.differentiable (by simp) x)]
    simp only [Pi.sub_apply,sub_apply,map_sub]
    abel_nf
  have hd : ∀ x, divergence (addField A W).field x=0 := by
    have hw : (addField A W).field=B.field := by
      funext x
      simp only [addField_field,W,fieldSub_field]
      abel
    rw [hw]
    exact solenoidal_representative_divergence _ hB _ B.smooth B.toLp_ae
  have hs : W.toLp ∈ solenoidalSpace := by
    rw [toLp_fieldSub]
    exact solenoidalSpace.sub_mem hB hA
  have hp : P.toLp ∈ gradientSpace := by
    rw [toLp_fieldSub]
    exact gradientSpace.sub_mem (pressureField_mem_gradient B) (pressureField_mem_gradient A)
  have h := differenceRhs_l2_bound A W P K hK hd hs hp
  rw [← he] at h
  simpa only [toLp_fieldSub,W] using h

theorem perturbed_difference_energy (A B : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (hB : B.toLp ∈ solenoidalSpace)
    (RA RB : L2) (K ea eb : ℝ) (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K)
    (ha : ‖RA - (projectedRhs A).toLp‖ ≤ ea)
    (hb : ‖RB - (projectedRhs B).toLp‖ ≤ eb) :
    2*⟪B.toLp-A.toLp,RB-RA⟫_ℝ ≤ (2*K+1)*‖B.toLp-A.toLp‖^2+(ea+eb)^2 := by
  let W := B.toLp-A.toLp
  let e := (RB-(projectedRhs B).toLp)-(RA-(projectedRhs A).toLp)
  have he : RB-RA=((projectedRhs B).toLp-(projectedRhs A).toLp)+e := by dsimp [e]; abel
  have hn : ‖e‖ ≤ ea+eb := by
    exact (norm_sub_le _ _).trans ((add_le_add hb ha).trans_eq (add_comm eb ea))
  have he0 : 0 ≤ ea+eb := (norm_nonneg e).trans hn
  have hpair : 2*⟪W,e⟫_ℝ ≤ ‖W‖^2+(ea+eb)^2 := by
    have hi : ⟪W,e⟫_ℝ ≤ ‖W‖*(ea+eb) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg W))
    nlinarith [sq_nonneg (‖W‖-(ea+eb))]
  rw [he,inner_add_right,mul_add]
  exact (add_le_add (projected_difference_energy A B hA hB K hK) hpair).trans_eq (by
      dsimp [W]; ring)

theorem forced_linear_zero_bound (T C E : ℝ) (hC : 1 ≤ C)
    (X X' : ℝ → ℝ) (hX : ContinuousOn X (Icc 0 T)) (hX0 : X 0 = 0)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, X' t ≤ C * X t + E ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) : X t ≤ E^2*Real.exp (C*T) := by
  have hh := linear_stability_within (fun r => X r+E^2) X' C T
    (hX.add continuousOn_const)
    (fun r hr => (hd r ⟨hr.1,hr.2.le⟩).add_const _)
    (fun r hr => (hb r ⟨hr.1,hr.2.le⟩).trans (by nlinarith [sq_nonneg E])) t ht
  rw [hX0,zero_add] at hh
  have he : E^2*Real.exp (C*t) ≤ E^2*Real.exp (C*T) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg E)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by linarith))
  linarith [sq_nonneg E]

end EulerOrdinarySobolev
