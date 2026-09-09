/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelNaturality
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelWeighted

@[expose] public section

/-! Genuine scalar-profile normalization commutes with bounded linear intertwiners. -/

noncomputable section

namespace EulerLinearDuhamel.Evolution

open Set ContinuousLinearMap EulerContinuousTimeWeight EulerContinuousTimeIntegral

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {T : ℝ} {hT : 0 ≤ T}
  {B : C(Icc (0 : ℝ) T,E →L[ℝ] E)}
  {D : C(Icc (0 : ℝ) T,F →L[ℝ] F)}
  (U : Evolution T hT B) (V : Evolution T hT D)
  (L : E →L[ℝ] F) (hL : ∀ t u, D t (L u) = L (B t u))

include hL

/-- Exact naturality of the actual normalized Duhamel solution. -/
theorem weightedSolution_map (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) :
    V.weightedSolution g hg (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) (L a₀) =
      L.compLeftContinuous ℝ (Icc (0 : ℝ) T) (U.weightedSolution g hg f a₀) := by
  have hw : weight g (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) =
      L.compLeftContinuous ℝ (Icc (0 : ℝ) T) (weight g f) := by
    apply ContinuousMap.ext
    intro t
    exact (map_smul L (g t) (f t)).symm
  have hn (p : C(Icc (0 : ℝ) T,E)) :
      normalize g hg (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) p) =
        L.compLeftContinuous ℝ (Icc (0 : ℝ) T) (normalize g hg p) := by
    apply ContinuousMap.ext
    intro t
    exact (map_smul L ((g t)⁻¹) (p t)).symm
  unfold weightedSolution
  rw [hw, U.solution_map V L hL, hn]

end EulerLinearDuhamel.Evolution
