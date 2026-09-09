/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderForwardParity
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation

@[expose] public section

/-! Reflection parity of the actual Gram-projected source evolution and its physical velocity. -/

noncomputable section

namespace EulerSourceCylinderParity

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceForwardCoefficient EulerBoundedFieldForwardGenerator EulerTransverseGramInverse
  EulerSourceCylinderForcing EulerSourceCylinderForward EulerSourceCylinderEquation
  EulerCylinderFieldReflection EulerCylinderForwardParity
open scoped BoundedContinuousFunction

section Coefficients

variable {K U E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (Q Q₁ : SmoothCoefficientPath K (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)

theorem sourceForcing_even (hE : ∀ t x, Q.field t (-x) = Q.field t x) (t : K) (x : Space) :
    sourceForcing Q c hc hQ t (-x) = sourceForcing Q c hc hQ t x := by
  simp only [sourceForcing, leftInversePath_apply, hE]

theorem sourceGenerator_even (hE : ∀ t x, Q.field t (-x) = Q.field t x)
    (hE₁ : ∀ t x, Q₁.field t (-x) = Q₁.field t x) (t : K) (x : Space) :
    sourceGenerator Q Q₁ c hc hQ t (-x) = sourceGenerator Q Q₁ c hc hQ t x := by
  simp only [sourceGenerator, generatorPath_apply, hE, hE₁]

end Coefficients

section Evolution

variable (P : ℝ) [Fact (0 < P)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (hE : ∀ t x, Q.field t (-x) = Q.field t x)
  (hE₁ : ∀ t x, Q₁.field t (-x) = Q₁.field t x)
  (f : C(Icc (0 : ℝ) T,Supported P E S hS)) (a₀ : Supported P U S hS)
  (hf : ∀ t, reflection P (f t : CylinderL2 P E) = -(f t : CylinderL2 P E))
  (ha₀ : reflection P (a₀ : CylinderL2 P U) = -(a₀ : CylinderL2 P U))

include hE hf in
theorem projectedForcing_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (projectedForcing P S hS Q c hc hQ f t : CylinderL2 P U) =
      -(projectedForcing P S hS Q c hc hQ f t : CylinderL2 P U) := by
  change reflection P (fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)) =
    -fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)
  rw [reflection_fullOperator P _ (sourceForcing_even Q c hc hQ hE t), hf, map_neg]

include hSym hE hE₁ hf ha₀ in
theorem coordinates_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) =
      -(coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) :=
  solution_full_reflection_neg P S hS hSym T hT (sourceGenerator Q Q₁ c hc hQ)
    (sourceGenerator_even Q Q₁ c hc hQ hE hE₁)
    (evolution P T hT Q Q₁ c hc hQ S hS) (projectedForcing P S hS Q c hc hQ f) a₀
    (projectedForcing_reflection_neg P S hS T Q c hc hQ hE f hf) ha₀ t

include hSym hE hE₁ hf ha₀ in
theorem velocity_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (velocity P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) =
      -(velocity P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) := by
  change reflection P (fullOperatorMap P (Q.field t)
      (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U)) = _
  rw [reflection_fullOperator P _ (hE t),
    coordinates_reflection_neg P S hS hSym T hT Q Q₁ c hc hQ hE hE₁ f a₀ hf ha₀, map_neg]
  rfl

include hSym hE hE₁ hf ha₀ in
theorem coordinateDerivative_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) =
      -(coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) := by
  change reflection P
    (fullOperatorMap P (sourceGenerator Q Q₁ c hc hQ t)
        (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) +
      fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)) = _
  rw [map_add, reflection_fullOperator P _ (sourceGenerator_even Q Q₁ c hc hQ hE hE₁ t),
    reflection_fullOperator P _ (sourceForcing_even Q c hc hQ hE t),
    coordinates_reflection_neg P S hS hSym T hT Q Q₁ c hc hQ hE hE₁ f a₀ hf ha₀,
    hf, map_neg, map_neg, ← neg_add]
  rfl

include hSym hE hE₁ hf ha₀ in
theorem velocityDerivative_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) =
      -(velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) := by
  change reflection P
    (fullOperatorMap P (Q₁.field t)
        (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) +
      fullOperatorMap P (Q.field t)
        (coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U)) = _
  rw [map_add, reflection_fullOperator P _ (hE₁ t), reflection_fullOperator P _ (hE t),
    coordinates_reflection_neg P S hS hSym T hT Q Q₁ c hc hQ hE hE₁ f a₀ hf ha₀,
    coordinateDerivative_reflection_neg P S hS hSym T hT Q Q₁ c hc hQ hE hE₁ f a₀ hf ha₀,
    map_neg, map_neg, ← neg_add]
  rfl

end Evolution
end EulerSourceCylinderParity
