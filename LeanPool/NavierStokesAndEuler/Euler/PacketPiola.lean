/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaAlgebra
import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
The actual curl Piola identity for a determinant-one coordinate map.
The derivative of the Jacobian cancels by symmetry of the genuine second
Fréchet derivative.  No curl identity or commutation relation is assumed.
-/

@[expose] public section


noncomputable section


namespace EulerPacketPiola

open EulerSmoothLimit EulerMeanBoundary EulerMeanCutoffCurl EulerVectorCalculus
  InnerProductSpace ContinuousLinearMap EulerTransverseGramInverse
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketPiola1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketPiola2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

theorem adjoint_apply_coordinate (A : Space →L[ℝ] Space) (q : Space) (i : Fin 3) :
    (A.adjoint q) i = ⟪A (EuclideanSpace.single i 1), q⟫_ℝ := by
  simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul] using
    A.adjoint_inner_right (EuclideanSpace.single i 1) q

/-- Pull back a Euclidean covector field by the actual derivative of the coordinate map. -/
def pullbackCovector (Ξ Q : Space → Space) (x : Space) : Space :=
  (fderiv ℝ Ξ x).adjoint (Q x)

/-- Symmetric second derivatives remove the entire derivative-of-Jacobian term from curl. -/
theorem curl_pullbackCovector (Ξ Q : Space → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (x : Space) (hQ : DifferentiableAt ℝ Q x) :
    vectorCurl (pullbackCovector Ξ Q) x =
      curlMatrix ((fderiv ℝ Ξ x).adjoint.comp (fderiv ℝ Q x)) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Ξ) x :=
    ((hΞ.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have hA : HasFDerivAt (fun y => (fderiv ℝ Ξ y).adjoint)
      ((realAdjoint (U := Space) (E := Space)).comp (fderiv ℝ (fderiv ℝ Ξ) x)) x :=
    (realAdjoint (U := Space) (E := Space)).hasFDerivAt.comp x hD.hasFDerivAt
  have hp := hA.clm_apply hQ.hasFDerivAt
  have hzero : curlMatrix
      (((realAdjoint (U := Space) (E := Space)).comp
        (fderiv ℝ (fderiv ℝ Ξ) x)).flip (Q x)) = 0 := by
    ext i
    change ((fderiv ℝ (fderiv ℝ Ξ) x (EuclideanSpace.single (i + 1) 1)).adjoint (Q x)) (i + 2) -
      ((fderiv ℝ (fderiv ℝ Ξ) x (EuclideanSpace.single (i + 2) 1)).adjoint (Q x)) (i + 1) = 0
    rw [adjoint_apply_coordinate, adjoint_apply_coordinate]
    have hs := ((hΞ.contDiffAt (x := x)).isSymmSndFDerivAt (n := 2) (by simp)).eq
      (EuclideanSpace.single (i + 1) 1) (EuclideanSpace.single (i + 2) 1)
    rw [hs, sub_self]
  change vectorCurl (fun y => (fderiv ℝ Ξ y).adjoint (Q y)) x = _
  rw [vectorCurl_eq_matrix _ x hp.differentiableAt, hp.fderiv, curlMatrix_add, hzero, add_zero]

/-- The source's slow transformed curl `d × Q`, with `d=F⁻ᵀ ∇`. -/
def transformedCurl (F : Space → Space ≃L[ℝ] Space) (Q : Space → Space) (x : Space) : Space :=
  curlMatrix ((fderiv ℝ Q x).comp (F x).symm.toContinuousLinearMap)

/-- For the actual Jacobian and unit determinant, `F⁻¹(d×Q)=curl(FᵀQ)`. -/
theorem piola_curl (Ξ Q : Space → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space ≃L[ℝ] Space) (x : Space)
    (hF : fderiv ℝ Ξ x = F.toContinuousLinearMap)
    (hdet : (operatorMatrix F.toContinuousLinearMap).det = 1)
    (hQ : DifferentiableAt ℝ Q x) :
    F.symm (curlMatrix ((fderiv ℝ Q x).comp F.symm.toContinuousLinearMap)) =
      vectorCurl (pullbackCovector Ξ Q) x := by
  rw [curl_pullbackCovector Ξ Q hΞ x hQ, hF]
  exact (curlMatrix_piola F hdet (fderiv ℝ Q x)).symm

theorem pullbackCovector_smooth (Ξ Q : Space → Space)
    (hΞ : ContDiff ℝ ∞ Ξ) (hQ : ContDiff ℝ ∞ Q) :
    ContDiff ℝ ∞ (pullbackCovector Ξ Q) :=
  ((realAdjoint (U := Space) (E := Space)).contDiff.comp
    (hΞ.fderiv_right (m := ∞) (by simp))).clm_apply hQ

/-- The transformed curl produces an actually divergence-free label velocity. -/
theorem divergence_piola_curl (Ξ Q : Space → Space)
    (hΞ : ContDiff ℝ ∞ Ξ) (hQ : ContDiff ℝ ∞ Q)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ x, fderiv ℝ Ξ x = (F x).toContinuousLinearMap)
    (hdet : ∀ x, (operatorMatrix (F x).toContinuousLinearMap).det = 1) (x : Space) :
    divergence (fun y => (F y).symm (transformedCurl F Q y)) x = 0 := by
  have he : (fun y => (F y).symm (transformedCurl F Q y)) =
      vectorCurl (pullbackCovector Ξ Q) := by
    funext y
    exact piola_curl Ξ Q (hΞ.of_le (by simp)) (F y) y (hF y) (hdet y)
      ((hQ.differentiable (by simp)).differentiableAt)
  rw [he]
  exact divergence_curl (fun i y => pullbackCovector Ξ Q y i)
    ((contDiff_piLp 2).mp (pullbackCovector_smooth Ξ Q hΞ hQ)) x

end EulerPacketPiola
