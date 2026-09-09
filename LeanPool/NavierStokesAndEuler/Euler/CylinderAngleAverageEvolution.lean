/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficientTime
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelNaturality
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelOperator

@[expose] public section

/-! The actual supported Duhamel solution preserves zero angular mean. -/

noncomputable section

namespace EulerCylinderAngleAverage

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerLpCylinderCoefficients EulerLinearDuhamel
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]

section Coefficients

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (S : Set Space) (hS : MeasurableSet S)

theorem supportedAverage_operator (A : Space →ᵇ E →L[ℝ] F) (u : Supported P E S hS) :
    supportedAverage P S hS (supportedOperatorMap P S hS A u) =
      supportedOperatorMap P S hS A (supportedAverage P S hS u) := by
  apply Subtype.ext
  exact average_fullOperator P A (u : CylinderL2 P E)

end Coefficients

section Paths

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set Space) (hS : MeasurableSet S)

private local instance : NormedAddCommGroup (Supported P V S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported P V S hS) := inferInstance
private local instance : NormedAddCommGroup C(K,Supported P V S hS) := inferInstance
private local instance : NormedSpace ℝ C(K,Supported P V S hS) := inferInstance
private local instance : NormedAddCommGroup (C(K,Supported P V S hS) →L[ℝ] C(K,Supported P V S hS))
  := inferInstance
private local instance : NormedSpace ℝ (C(K,Supported P V S hS) →L[ℝ] C(K,Supported P V S hS)) :=
  inferInstance

def supportedPathAverage : C(K,Supported P V S hS) →L[ℝ] C(K,Supported P V S hS) :=
  (supportedAverage P S hS).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem supportedPathAverage_apply (p : C(K,Supported P V S hS)) (t : K) :
    supportedPathAverage P S hS p t = supportedAverage P S hS (p t) := rfl

omit [CompactSpace K] in
theorem include_supportedPathAverage (p : C(K,Supported P V S hS)) :
    includePath P S hS (supportedPathAverage P S hS p) = pathAverage P (includePath P S hS p) := rfl

theorem supportedPathAverage_norm : ‖supportedPathAverage (K := K) (V := V) P S hS‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
  intro t
  exact (averageIntegral_norm P (p t : CylinderL2 P V)).trans (p.norm_coe_le_norm t)

end Paths

section Evolution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (B : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
  (U : Evolution T hT (liftedOperatorPath P S hS T B))

/-- Averaging the genuine forced solution equals solving with averaged data. -/
theorem solution_average (f : C(Icc (0 : ℝ) T,Supported P V S hS)) (a₀ : Supported P V S hS) :
    supportedPathAverage P S hS (U.solution f a₀) =
      U.solution (supportedPathAverage P S hS f) (supportedAverage P S hS a₀) := by
  apply (U.solution_map U (supportedAverage P S hS) _ f a₀).symm
  intro t u
  change liftedOperator P S hS (B t) (supportedAverage P S hS u) =
    supportedAverage P S hS (liftedOperator P S hS (B t) u)
  rw [← supportedOperator_eq_square]
  exact (supportedAverage_operator P S hS (B t) u).symm

/-- Zero mean of the data propagates by the proved uniqueness of the actual ODE. -/
theorem solution_average_zero (f : C(Icc (0 : ℝ) T,Supported P V S hS))
    (a₀ : Supported P V S hS)
    (hf : ∀ t, supportedAverage P S hS (f t) = 0)
    (ha₀ : supportedAverage P S hS a₀ = 0) (t : Icc (0 : ℝ) T) :
    supportedAverage P S hS (U.solution f a₀ t) = 0 := by
  have hfp : supportedPathAverage P S hS f = 0 := by
    apply ContinuousMap.ext
    exact hf
  have he := solution_average P S hS T hT B U f a₀
  have hz : U.solution 0 0 = 0 := by
    rw [U.solution_eq_operators, map_zero, map_zero, add_zero]
  rw [hfp, ha₀, hz] at he
  exact congrArg (fun p : C(Icc (0 : ℝ) T,Supported P V S hS) => p t) he

/-- The same theorem in the ordinary cylinder L² space used by the classical representatives. -/
theorem solution_full_average_zero (f : C(Icc (0 : ℝ) T,Supported P V S hS))
    (a₀ : Supported P V S hS)
    (hf : ∀ t, average P (f t : CylinderL2 P V) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P V) = 0) (t : Icc (0 : ℝ) T) :
    average P (U.solution f a₀ t : CylinderL2 P V) = 0 := by
  have hs := solution_average_zero P S hS T hT B U f a₀
    (fun s => Subtype.ext (hf s)) (Subtype.ext ha₀) t
  exact congrArg (fun u : Supported P V S hS => (u : CylinderL2 P V)) hs

end Evolution
end EulerCylinderAngleAverage
