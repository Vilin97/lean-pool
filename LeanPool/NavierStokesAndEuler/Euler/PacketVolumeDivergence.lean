/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentFlowDifferentiation

@[expose] public section

/-! Divergence under the actual determinant-one pushforward. Jacobi's
formula controls the derivative of the Jacobian, and symmetry of the
second derivative supplies the Piola cancellation. -/

noncomputable section

namespace EulerPacketVolumeDivergence

open Set Filter ContinuousLinearMap EulerSmoothLimit EulerPacketPiola
open scoped Topology ContDiff

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

theorem coordinateTrace_eq_matrix (A : Space →L[ℝ] Space) :
    coordinateTrace A = (operatorMatrix A).trace := by
  simp only [coordinateTrace,operatorMatrix,Matrix.trace,Matrix.diag,
    sum_apply,comp_apply,apply_apply]
  rfl

theorem operatorMatrix_det (A : Space →L[ℝ] Space) :
    (operatorMatrix A).det = A.det := by
  change (operatorMatrix A).det = LinearMap.det A.toLinearMap
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  congr 1

theorem coordinateTrace_comp_comm (A B : Space →L[ℝ] Space) :
    coordinateTrace (A.comp B) = coordinateTrace (B.comp A) := by
  rw [coordinateTrace_eq_matrix,coordinateTrace_eq_matrix,
    operatorMatrix_comp,operatorMatrix_comp]
  exact Matrix.trace_mul_comm _ _

theorem coordinateTrace_conjugate (A : Space ≃L[ℝ] Space) (B : Space →L[ℝ] Space) :
    coordinateTrace ((A.toContinuousLinearMap.comp B).comp A.symm.toContinuousLinearMap) =
      coordinateTrace B := by
  rw [coordinateTrace_comp_comm]
  congr 1
  ext v
  simp

/-- A constant unit determinant forces the true logarithmic derivative
of the frame to have zero trace in every direction. -/
theorem determinant_derivative_trace_zero (F : Space → Space →L[ℝ] Space)
    (x v : Space) (A : Space ≃L[ℝ] Space)
    (hA : F x = A.toContinuousLinearMap) (hF : DifferentiableAt ℝ F x)
    (hdet : (fun y => (operatorMatrix (F y)).det) =ᶠ[𝓝 x] fun _ => (1 : ℝ)) :
    coordinateTrace ((fderiv ℝ F x v).comp A.symm.toContinuousLinearMap) = 0 := by
  let L : ℝ → Mat3 := fun s => operatorMatrix (F (x+s•v))
  let M : Mat3 := operatorMatrix ((fderiv ℝ F x v).comp A.symm.toContinuousLinearMap)
  have hline : HasDerivAt (fun s : ℝ => F (x+s•v)) (fderiv ℝ F x v) 0 := by
    have hF' : HasFDerivAt F (fderiv ℝ F x) (x+(0 : ℝ)•v) := by
      simpa only [zero_smul,add_zero] using hF.hasFDerivAt
    have h := hF'.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const v))
    simpa only [Function.comp_def,Pi.add_apply,Pi.smul_apply,id_eq,
      zero_smul,add_zero,one_smul,zero_add] using h
  have hmat : M*L 0 = operatorMatrix (fderiv ℝ F x v) := by
    dsimp only [M,L]
    rw [zero_smul,add_zero,← operatorMatrix_comp]
    congr 1
    ext u
    simp only [comp_apply,hA,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  have hentry (i j : Fin 3) :
      HasDerivAt (fun s => L s i j) ((M*L 0) i j) 0 := by
    rw [hmat]
    exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt 0
      ((ContinuousLinearMap.apply ℝ Space (EuclideanSpace.single j 1)).hasFDerivAt.comp_hasDerivAt
        0 hline)
  have hd := EulerDeformationVolume.determinant_hasDerivAt L (fun _ => M) 0 hentry
  have hlim : Tendsto (fun s : ℝ => x+s•v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun s : ℝ => x+s•v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul,add_zero] using
      hc.tendsto (0 : ℝ)
  have he : (fun s => (L s).det) =ᶠ[𝓝 (0 : ℝ)] fun _ => (1 : ℝ) := hdet.comp_tendsto hlim
  have hzero := hd.unique ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq he)
  have hval : (L 0).det = 1 := he.eq_of_nhds
  rw [hval,mul_one] at hzero
  rw [coordinateTrace_eq_matrix]
  exact hzero

/-- The divergence of a genuine volume-preserving pushforward equals the
label-space divergence. Only local C² regularity and local determinant one
are needed at the point. -/
theorem divergence_of_pullback (X v w : Space → Space) (x : Space)
    (A : Space ≃L[ℝ] Space) (hX : ContDiffAt ℝ 2 X x)
    (hA : fderiv ℝ X x = A.toContinuousLinearMap)
    (hdet : (fun y => (operatorMatrix (fderiv ℝ X y)).det) =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (hv : DifferentiableAt ℝ v x) (hw : DifferentiableAt ℝ w (X x))
    (hpull : (w ∘ X) =ᶠ[𝓝 x] fun y => fderiv ℝ X y (v y)) :
    divergence w (X x) = divergence v x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ X) x :=
    (hX.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hs : (fderiv ℝ (fderiv ℝ X) x).flip (v x) = fderiv ℝ (fderiv ℝ X) x (v x) := by
    apply ContinuousLinearMap.ext
    intro a
    exact (hX.isSymmSndFDerivAt (by simp)).eq a (v x)
  have hXA : HasFDerivAt X A.toContinuousLinearMap x := by
    rw [← hA]
    exact (hX.differentiableAt two_ne_zero).hasFDerivAt
  have hd := EulerLagrangian.derivative_pullback_inverse w X A x hXA hw
  rw [hpull.fderiv_eq (𝕜 := ℝ),(hD.hasFDerivAt.clm_apply hv.hasFDerivAt).fderiv,
    hA,hs] at hd
  have hz := determinant_derivative_trace_zero (fderiv ℝ X) x (v x) A hA hD hdet
  rw [divergence_eq_trace,← coordinateTrace_eq_linearTrace,hd,add_comp,map_add,
    coordinateTrace_conjugate,hz,add_zero,coordinateTrace_eq_linearTrace]
  rfl

theorem divergence_pushforward (X Y v : Space → Space) (x : Space)
    (A : Space ≃L[ℝ] Space) (hX : ContDiffAt ℝ 2 X x)
    (hA : fderiv ℝ X x = A.toContinuousLinearMap)
    (hdet : (fun y => (operatorMatrix (fderiv ℝ X y)).det) =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (hleft : ∀ y, Y (X y) = y)
    (hY : DifferentiableAt ℝ Y (X x)) (hv : DifferentiableAt ℝ v x) :
    divergence (fun y => fderiv ℝ X (Y y) (v (Y y))) (X x) = divergence v x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ X) x :=
    (hX.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hw : DifferentiableAt ℝ (fun y => fderiv ℝ X (Y y) (v (Y y))) (X x) := by
    have hg : DifferentiableAt ℝ (fun y => fderiv ℝ X y (v y)) (Y (X x)) := by
      rw [hleft]
      exact hD.clm_apply hv
    exact hg.comp (X x) hY
  apply divergence_of_pullback X v _ x A hX hA hdet hv hw
  exact Filter.Eventually.of_forall (fun y => by simp only [Function.comp_apply,hleft])

end EulerPacketVolumeDivergence
