/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.IntegralPathLimit

/-! Lifting an actual continuous evolution equation through an injective bounded linear map. -/

@[expose] public section


noncomputable section

namespace EulerInjectivePathDerivative

open MeasureTheory Set EulerVolterraConvolution EulerIntegralPathLimit
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A bounded linear map commutes with the integral of an actual continuous time path. -/
theorem map_pathIntegral (L : E →L[ℝ] F) (T : ℝ) (hT : 0 ≤ T) (a b : ℝ)
    (f : C(Icc (0 : ℝ) T, E)) :
    L (pathIntegralOperator T hT a b f) =
      pathIntegralOperator T hT a b (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) := by
  exact (L.intervalIntegral_comp_comm ((extendPath_continuous T hT f).intervalIntegrable a b)).symm

/-- An evolution equation in the weaker space gives its exact integral equation in the stronger
space when the embedding is injective and the proposed derivative is continuous there. -/
theorem integral_equation_of_injective_map (L : E →L[ℝ] F) (hL : Function.Injective L)
    (T : ℝ) (hT : 0 ≤ T) (u f : C(Icc (0 : ℝ) T, E))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt (fun r => L (extendPath T hT u r))
      (L (extendPath T hT f t)) t) (t : Icc (0 : ℝ) T) :
    u t = u ⟨0,le_rfl,hT⟩ + pathIntegralOperator T hT 0 t.val f := by
  apply hL
  rw [L.map_add,map_pathIntegral L T hT 0 t.val f]
  exact integral_equation_of_hasDerivAt T hT (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) u)
    (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) hd t

/-- A continuous stronger-space right-hand side lifts a genuine derivative equation through an
injective bounded embedding, without assuming the stronger derivative exists. -/
theorem hasDerivAt_of_injective_map (L : E →L[ℝ] F) (hL : Function.Injective L)
    (T : ℝ) (hT : 0 ≤ T) (u f : C(Icc (0 : ℝ) T, E))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt (fun r => L (extendPath T hT u r))
      (L (extendPath T hT f t)) t) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT u) (extendPath T hT f t) t := by
  exact hasDerivAt_of_integral_equation T hT u f
    (integral_equation_of_injective_map L hL T hT u f hd) t ht

end EulerInjectivePathDerivative
