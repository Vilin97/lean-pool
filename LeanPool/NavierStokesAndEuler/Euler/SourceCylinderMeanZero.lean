/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelNaturality
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelOperator
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficientTime

/-! The actual source transverse solve preserves the angular zero mode constraint. -/

section

/-! The actual supported Duhamel solution preserves zero angular mean. -/

@[expose] public section

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

/-- Cache the standard `NormedAddCommGroup (Supported P V S hS)` instance to shorten typeclass
synthesis. -/
local instance instCylinderAngleAverageEvolution1 : NormedAddCommGroup (Supported P V S hS) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported P V S hS)` instance to shorten typeclass
synthesis. -/
local instance instCylinderAngleAverageEvolution2 : NormedSpace ℝ (Supported P V S hS) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Supported P V S hS)` instance to shorten
typeclass synthesis. -/
local instance instCylinderAngleAverageEvolution3 : NormedAddCommGroup C(K,Supported P V S hS) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Supported P V S hS)` instance to shorten typeclass
synthesis. -/
local instance instCylinderAngleAverageEvolution4 : NormedSpace ℝ C(K,Supported P V S hS) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,Supported P V S hS) →L[ℝ] C(K,Supported P V S
hS))` instance to shorten typeclass synthesis. -/
local instance instCylinderAngleAverageEvolution5 : NormedAddCommGroup (C(K,Supported P V S hS)
    →L[ℝ] C(K,Supported P V S hS))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,Supported P V S hS) →L[ℝ] C(K,Supported P V S hS))`
instance to shorten typeclass synthesis. -/
local instance instCylinderAngleAverageEvolution6 : NormedSpace ℝ (C(K,Supported P V S hS) →L[ℝ]
    C(K,Supported P V S hS)) :=
    inferInstance

/-- Supported path average, given by `(supportedAverage P S hS).compLeftContinuous ℝ K`. -/
def supportedPathAverage : C(K,Supported P V S hS) →L[ℝ] C(K,Supported P V S hS) :=
  (supportedAverage P S hS).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem supportedPathAverage_apply (p : C(K, Supported P V S hS)) (t : K) :
    supportedPathAverage P S hS p t = supportedAverage P S hS (p t) := rfl

omit [CompactSpace K] in
theorem include_supportedPathAverage (p : C(K, Supported P V S hS)) :
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
  (B : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V))
  (U : Evolution T hT (liftedOperatorPath P S hS T B))

/-- Averaging the genuine forced solution equals solving with averaged data. -/
theorem solution_average (f : C(Icc (0 : ℝ) T, Supported P V S hS)) (a₀ : Supported P V S hS) :
    supportedPathAverage P S hS (U.solution f a₀) =
      U.solution (supportedPathAverage P S hS f) (supportedAverage P S hS a₀) := by
  apply (U.solution_map U (supportedAverage P S hS) _ f a₀).symm
  intro t u
  change liftedOperator P S hS (B t) (supportedAverage P S hS u) =
    supportedAverage P S hS (liftedOperator P S hS (B t) u)
  rw [← supportedOperator_eq_square]
  exact (supportedAverage_operator P S hS (B t) u).symm

/-- Zero mean of the data propagates by the proved uniqueness of the actual ODE. -/
theorem solution_average_zero (f : C(Icc (0 : ℝ) T, Supported P V S hS))
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
theorem solution_full_average_zero (f : C(Icc (0 : ℝ) T, Supported P V S hS))
    (a₀ : Supported P V S hS)
    (hf : ∀ t, average P (f t : CylinderL2 P V) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P V) = 0) (t : Icc (0 : ℝ) T) :
    average P (U.solution f a₀ t : CylinderL2 P V) = 0 := by
  have hs := solution_average_zero P S hS T hT B U f a₀
    (fun s => Subtype.ext (hf s)) (Subtype.ext ha₀) t
  exact congrArg (fun u : Supported P V S hS => (u : CylinderL2 P V)) hs

end Evolution
end EulerCylinderAngleAverage

end
end

end

@[expose] public section

noncomputable section

namespace EulerSourceCylinderEquation

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerSourceForwardCoefficient EulerSourceCylinderForcing
  EulerSourceCylinderForward EulerCylinderAngleAverage
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported P E S hS)) (a₀ : Supported P U S hS)

theorem projectedForcing_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0) (t : Icc (0 : ℝ) T) :
    average P (projectedForcing P S hS Q c hc hQ f t : CylinderL2 P U) = 0 := by
  change average P (fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)) = 0
  rw [average_fullOperator, hf t, map_zero]

/-- The real Gram-projected Duhamel coordinate solution has zero angular mean. -/
theorem coordinates_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) = 0 :=
  solution_full_average_zero P S hS T hT (sourceGenerator Q Q₁ c hc hQ)
    (evolution P T hT Q Q₁ c hc hQ S hS)
    (projectedForcing P S hS Q c hc hQ f) a₀
    (projectedForcing_average_zero P S hS T Q c hc hQ f hf) ha₀ t

/-- Physical reconstruction by the true frame preserves the same zero mode. -/
theorem velocity_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (velocity P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) = 0 := by
  change average P (fullOperatorMap P (Q.field t)
    (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U)) = 0
  rw [average_fullOperator, coordinates_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
    map_zero]

theorem coordinateDerivative_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) = 0 := by
  change average P (fullOperatorMap P (sourceGenerator Q Q₁ c hc hQ t)
      (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) +
    fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)) = 0
  rw [map_add, average_fullOperator, average_fullOperator,
    coordinates_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf ha₀ t, hf t,
    map_zero, map_zero, add_zero]

/-- The actual within-time derivative also has zero mean, as follows from its equation. -/
theorem velocityDerivative_average_zero
    (hf : ∀ t, average P (f t : CylinderL2 P E) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) = 0 := by
  change average P (fullOperatorMap P (Q₁.field t)
      (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) +
    fullOperatorMap P (Q.field t)
      (coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U)) = 0
  rw [map_add, average_fullOperator, average_fullOperator,
    coordinates_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
    coordinateDerivative_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
    map_zero, map_zero, add_zero]

end EulerSourceCylinderEquation
