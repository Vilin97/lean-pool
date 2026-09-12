/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FinitePathTensor
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral

/-! The actual tensor-path map commutes with the initial value and the
Bochner time integral. These identities permit differentiation of a
path-space integral equation at every spatial order. -/

@[expose] public section


noncomputable section


namespace EulerFinitePathTensor

open Set EulerContinuousTimeIntegral EulerVolterraConvolution

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem tensorPath_const {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (n : ℕ) (A : E [×n]→L[ℝ] V) :
    tensorPathMap n ((ContinuousLinearMap.const ℝ K).compContinuousMultilinearMap A) =
      (ContinuousLinearMap.const ℝ K) A := by
  apply ContinuousMap.ext
  intro t
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensorPathMap_apply]
  rfl

theorem tensorPath_integral (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (A : E [×n]→L[ℝ] C(Icc (0 : ℝ) T, V)) :
    tensorPathMap n ((integral T hT).compContinuousMultilinearMap A) =
      integral T hT (tensorPathMap n A) := by
  apply ContinuousMap.ext
  intro t
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensorPathMap_apply]
  let ev : (E [×n]→L[ℝ] V) →L[ℝ] V :=
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] V)).flipMultilinear v
  change (∫ s in (0 : ℝ)..(t : ℝ), extendPath T hT (A v) s) =
    ev (∫ s in (0 : ℝ)..(t : ℝ), extendPath T hT (tensorPathMap n A) s)
  have he : extendPath T hT (A v) =
      fun s => ev (extendPath T hT (tensorPathMap n A) s) := by
    funext s
    change A v (projIcc 0 T hT s) = tensorPathMap n A (projIcc 0 T hT s) v
    rw [tensorPathMap_apply]
  rw [he]
  exact ev.intervalIntegral_comp_comm
    ((extendPath_continuous T hT (tensorPathMap n A)).intervalIntegrable 0 t)

end EulerFinitePathTensor
