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
    tensorPathMap (K := K) (E := E) (V := V) n
        ((ContinuousLinearMap.const ℝ K).compContinuousMultilinearMap A) =
      (ContinuousLinearMap.const ℝ K) A := by
  apply ContinuousMap.ext
  intro t
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensorPathMap_apply]
  rfl

theorem tensorPath_integral (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (A : E [×n]→L[ℝ] C(Icc (0 : ℝ) T, V)) :
    tensorPathMap (K := Icc (0 : ℝ) T) (E := E) (V := V) n
        ((integral T hT).compContinuousMultilinearMap A) =
      integral (E := E [×n]→L[ℝ] V) T hT
        (tensorPathMap (K := Icc (0 : ℝ) T) (E := E) (V := V) n A) := by
  apply ContinuousMap.ext
  intro t
  apply ContinuousMultilinearMap.ext
  intro v
  refine (tensorPathMap_apply n _ t v).trans ?_
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) V v
  have he : extendPath T hT (A v) =
      fun s => ev (extendPath T hT
        (tensorPathMap (K := Icc (0 : ℝ) T) (E := E) (V := V) n A) s) :=
    funext fun s => (tensorPathMap_apply n A (projIcc 0 T hT s) v).symm
  exact (congrArg (fun f => ∫ s in (0 : ℝ)..(t : ℝ), f s) he).trans
    (ev.intervalIntegral_comp_comm
      ((extendPath_continuous T hT
        (tensorPathMap (K := Icc (0 : ℝ) T) (E := E) (V := V) n A)).intervalIntegrable 0 t))

end EulerFinitePathTensor
