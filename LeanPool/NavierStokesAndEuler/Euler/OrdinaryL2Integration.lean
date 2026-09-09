/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySobolevL4

@[expose] public section

/-! Ordinary integration by parts for genuine smooth L² fields. The
identity needs no compact-support premise because all three pairings
in the Haar-measure integration theorem are integrable. -/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanVectorIdentities Laplacian
open scoped ContDiff ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem field_inner_integrable (A B : SmoothL2Field V) :
    Integrable (fun x => ⟪A.field x,B.field x⟫_ℝ) := by
  apply (MeasureTheory.L2.integrable_inner A.toLp B.toLp).congr
  filter_upwards [A.toLp_ae,B.toLp_ae] with x ha hb
  rw [ha,hb]

theorem field_inner (A B : SmoothL2Field V) :
    ⟪A.toLp,B.toLp⟫_ℝ=∫ x,⟪A.field x,B.field x⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [A.toLp_ae,B.toLp_ae] with x ha hb
  rw [ha,hb]

theorem field_directional_ibp (A B : SmoothL2Field V) (v : Space) :
    (∫ x,⟪fderiv ℝ A.field x v,B.field x⟫_ℝ) =
      -∫ x,⟪A.field x,fderiv ℝ B.field x v⟫_ℝ := by
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := (volume : Measure Space)) (B := innerSL ℝ) (v := v)
    (field_inner_integrable (A.directionalField v) B)
    (field_inner_integrable A (B.directionalField v)) (field_inner_integrable A B)
    (fun x _ => A.smooth.differentiable (by simp) x)
    (fun x _ => B.smooth.differentiable (by simp) x)
  change (∫ x,⟪A.field x,fderiv ℝ B.field x v⟫_ℝ)=
    -∫ x,⟪fderiv ℝ A.field x v,B.field x⟫_ℝ at h
  linarith

theorem field_directional_inner (A B : SmoothL2Field V) (v : Space) :
    ⟪(A.directionalField v).toLp,B.toLp⟫_ℝ =
      -⟪A.toLp,(B.directionalField v).toLp⟫_ℝ := by
  rw [field_inner,field_inner]
  exact field_directional_ibp A B v

theorem field_zero_of_toLp_zero (A : SmoothL2Field V) (h : A.toLp=0) : A.field=0 := by
  have hae : A.field=ᵐ[volume] 0 := A.toLp_ae.symm.trans (by rw [h]; exact Lp.coeFn_zero V 2 volume)
  exact Measure.eq_of_ae_eq hae A.smooth.continuous continuous_const

theorem field_zero_of_derivative_zero (A : SmoothL2Field Space)
    (hD : ∀ x, fderiv ℝ A.field x=0) : A.field=0 := by
  have h6 := memLp_six A.field A.smooth A.memLp A.derivative.memLp
  have hb := eLpNorm_six_le A.field A.smooth A.memLp A.derivative.memLp
  have hz : eLpNorm (fderiv ℝ A.field) 2 (volume : Measure Space)=0 := by
    calc
      _ = eLpNorm (0 : Space → Space →L[ℝ] Space) 2 (volume : Measure Space) :=
        eLpNorm_congr_ae (Filter.Eventually.of_forall hD)
      _ = 0 := eLpNorm_zero (α := Space) (ε := Space →L[ℝ] Space)
        (p := 2) (μ := (volume : Measure Space))
  have hb0 : eLpNorm A.field 6 (volume : Measure Space) ≤ 0 := by
    exact hb.trans_eq (by rw [hz,mul_zero])
  have hae : A.field=ᵐ[volume] 0 := (eLpNorm_eq_zero_iff h6.aestronglyMeasurable
    (by norm_num : (6 : ℝ≥0∞) ≠ 0)).mp (le_antisymm hb0 bot_le)
  exact Measure.eq_of_ae_eq hae A.smooth.continuous continuous_const

theorem field_zero_of_laplacian_zero (A : SmoothL2Field Space)
    (hΔ : ∀ x, Δ A.field x=0) : A.field=0 := by
  let d := fun i : Fin 3 => A.directionalField (EuclideanSpace.single i 1)
  have hb (i : Fin 3) : ⟪A.toLp,(d i).directionalField (EuclideanSpace.single i 1) |>.toLp⟫_ℝ =
      -‖(d i).toLp‖^2 := by
    have h := field_directional_inner A (d i) (EuclideanSpace.single i 1)
    rw [real_inner_self_eq_norm_sq] at h
    linarith
  have hi : (∑ i : Fin 3, ⟪A.toLp,((d i).directionalField (EuclideanSpace.single i 1)).toLp⟫_ℝ)=0
    := by
    simp_rw [field_inner]
    rw [← integral_finsetSum Finset.univ (fun i _ => field_inner_integrable A
      ((d i).directionalField (EuclideanSpace.single i 1)))]
    have he : (fun x => ∑ i : Fin 3, ⟪A.field x,
        ((d i).directionalField (EuclideanSpace.single i 1)).field x⟫_ℝ)=0 := by
      funext x
      rw [← inner_sum]
      change ⟪A.field x,∑ i : Fin 3, vectorPartial (vectorPartial A.field i) i x⟫_ℝ=0
      rw [← congrFun (vector_laplacian_eq_sum A.field A.smooth) x,hΔ,inner_zero_right]
    rw [he]
    change (∫ _x : Space, (0 : ℝ))=0
    exact integral_zero Space ℝ
  have hs : ∑ i : Fin 3, ‖(d i).toLp‖^2=0 := by
    simp_rw [hb] at hi
    rw [Finset.sum_neg_distrib] at hi
    linarith
  have hd (i : Fin 3) : (d i).field=0 := by
    have hh : ‖(d i).toLp‖^2=0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg ‖(d j).toLp‖)).mp hs i (Finset.mem_univ i)
    exact field_zero_of_toLp_zero _ (norm_eq_zero.mp (sq_eq_zero_iff.mp hh))
  apply field_zero_of_derivative_zero A
  intro x
  apply ContinuousLinearMap.ext
  intro v
  have hz (i : Fin 3) : fderiv ℝ A.field x (EuclideanSpace.single i 1)=0 :=
    congrFun (hd i) x
  have hv : (∑ i : Fin 3, v i • (EuclideanSpace.single i 1 : Space))=v := by
    ext j
    simp [Pi.single_apply,mul_ite]
  rw [← hv,map_sum]
  simp only [map_smul,hz,smul_zero,Finset.sum_const_zero,zero_apply]

end EulerOrdinarySobolev
