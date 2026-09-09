/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalPath
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.MeanValue

/-! Jacobi's formula in every finite dimension, and determinant preservation
for the actual linear evolution with trace-free coefficient. -/

@[expose] public section


noncomputable section


namespace EulerLinearEvolutionDeterminant

open Set Matrix EulerVolterraConvolution EulerLinearDuhamel
open scoped Matrix.Norms.Elementwise

private def determinantRows (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

theorem matrixJacobi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F M : ℝ → Matrix ι ι ℝ) (S : Set ℝ) (t : ℝ)
    (hF : HasDerivWithinAt F (M t * F t) S t) :
    HasDerivWithinAt (fun s => (F s).det) ((M t).trace * (F t).det) S t := by
  have h := (determinantRows ι).hasFDerivAt (F t) |>.comp_hasDerivWithinAt t hF
  have he : (determinantRows ι).linearDeriv (F t) (M t * F t) =
      (M t).trace * (F t).det := by
    calc
      _ = ∑ i, ((F t).updateRow i ((M t * F t) i)).det :=
        (determinantRows ι).linearDeriv_apply (fun i j => F t i j)
          (fun i j => (M t * F t) i j)
      _ = _ := ?_
    rw [Matrix.trace, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hr : (M t * F t) i = ∑ j, M t i j • F t j := by
      funext j
      simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hr, Matrix.det_updateRow_sum]
    rfl
  exact h.congr_deriv he

section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private def operatorCoordinates :
    (E →L[ℝ] E) →L[ℝ] Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  ((LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)).toLinearMap.comp
    (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

private theorem operatorCoordinates_comp (A B : E →L[ℝ] E) :
    operatorCoordinates (A.comp B) = operatorCoordinates A * operatorCoordinates B := by
  exact LinearMap.toMatrix_comp (Module.finBasis ℝ E) (Module.finBasis ℝ E)
    (Module.finBasis ℝ E) A.toLinearMap B.toLinearMap

private theorem operatorCoordinates_det (A : E →L[ℝ] E) :
    (operatorCoordinates A).det = A.det :=
  LinearMap.det_toMatrix (Module.finBasis ℝ E) A.toLinearMap

private theorem operatorCoordinates_trace (A : E →L[ℝ] E) :
    (operatorCoordinates A).trace = LinearMap.trace ℝ E A.toLinearMap :=
  (LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ E) A.toLinearMap).symm

/-- The finite-dimensional Jacobi formula does not assume invertibility. -/
theorem operatorJacobi (F M : ℝ → (E →L[ℝ] E)) (S : Set ℝ) (t : ℝ)
    (hF : HasDerivWithinAt F ((M t).comp (F t)) S t) :
    HasDerivWithinAt (fun s => (F s).det)
      (LinearMap.trace ℝ E (M t).toLinearMap * (F t).det) S t := by
  have hc := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
    (E := E →L[ℝ] E)
    (F := Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (x := F t) (operatorCoordinates (E := E))
  have hm := HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ)
    (F := E →L[ℝ] E)
    (E := Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) t hc hF
  have hm' := hm.congr_deriv (operatorCoordinates_comp (M t) (F t))
  have h := matrixJacobi (fun s => operatorCoordinates (F s))
    (fun s => operatorCoordinates (M s)) S t hm'
  simpa only [operatorCoordinates_det, operatorCoordinates_trace] using h

end Operators

end EulerLinearEvolutionDeterminant

namespace EulerLinearDuhamel.Evolution

open Set EulerVolterraConvolution EulerLinearEvolutionDeterminant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T, E →L[ℝ] E)}

theorem det_forward_eq_initial (U : Evolution T hT B)
    (htrace : ∀ t, LinearMap.trace ℝ E (B t).toLinearMap = 0)
    (t : Icc (0 : ℝ) T) : (U.forward t).det = (U.forward ⟨0,le_rfl,hT⟩).det := by
  have hd : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun r => (extendPath T hT U.forward r).det) 0 (Icc 0 T) s := by
    intro s hs
    have hF := U.derivative ⟨s,hs⟩
    have h := operatorJacobi (extendPath T hT U.forward) (extendPath T hT B)
      (Icc 0 T) s (by
        simpa only [extendPath, projIcc_of_mem hT hs] using hF)
    simpa only [extendPath, projIcc_of_mem hT hs, htrace, zero_mul] using h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
    (fun s hs => by simp) (convex_Icc (0 : ℝ) T)
    (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) t.property
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero, extendPath,
    projIcc_of_mem hT t.property, projIcc_of_mem hT ⟨le_rfl,hT⟩] using h

end EulerLinearDuhamel.Evolution

namespace EulerLinearDuhamel

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem constructedEvolution_det_one (T : ℝ) (hT : 0 ≤ T)
    (B : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (htrace : ∀ t, LinearMap.trace ℝ E (B t).toLinearMap = 0)
    (t : Icc (0 : ℝ) T) : ((constructedEvolution T hT B).forward t).det = 1 := by
  rw [(constructedEvolution T hT B).det_forward_eq_initial htrace t,
    constructedEvolution_initial]
  exact LinearMap.det_id

end EulerLinearDuhamel
