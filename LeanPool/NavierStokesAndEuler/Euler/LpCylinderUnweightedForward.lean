/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRegularForward

@[expose] public section

/-! Actual unnormalized forward solutions have smooth mixed translation orbits. -/

noncomputable section

namespace EulerLpCylinderRegularForward

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerMeanCoefficients EulerLinearDuhamel EulerContinuousTimeWeight
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (T : ℝ) (hT : 0 ≤ T) (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S)
  (B : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (f : C(Icc (0 : ℝ) T,Supported period V S hS)) (a₀ : Supported period V S hS)

include hSc hB in
/-- The constructed unnormalized path is genuinely smooth in all covering parameters.
This qualitative statement needs no propagator bound or smoothness of a time profile. -/
theorem unweighted_solution_contDiff
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period V))) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      ((constructedEvolution period S hS T hT B).solution f a₀))) := by
  let g : C(Icc (0 : ℝ) T,ℝ) := 1
  have hg : ∀ t, 0 < g t := fun _ => zero_lt_one
  have hw : weight g f = f := by
    apply ContinuousMap.ext
    intro t
    change (1 : ℝ) • f t = f t
    exact one_smul ℝ (f t)
  have he : (constructedEvolution period S hS T hT B).weightedSolution g hg f a₀ =
      (constructedEvolution period S hS T hT B).solution f a₀ := by
    change normalize g hg ((constructedEvolution period S hS T hT B).solution (weight g f) a₀) = _
    rw [hw]
    apply ContinuousMap.ext
    intro t
    change (1 : ℝ)⁻¹ • ((constructedEvolution period S hS T hT B).solution f a₀ t) =
      (constructedEvolution period S hS T hT B).solution f a₀ t
    rw [inv_one,one_smul]
  have h := source_solution_contDiff period T hT univ MeasurableSet.univ B hB
    S hS hSc isOpen_univ (subset_univ S) g hg f a₀ hf ha₀
  rwa [he] at h

end EulerLpCylinderRegularForward
