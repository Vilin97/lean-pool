/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur

/-! # Solution -/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace AlmostSchurEntry.Geometry

/-- De Lellis--Topping almost-Schur inequality and Einstein equality case,
with the connection and volume constructed from the smooth Riemannian metric. -/
theorem almostSchur
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
    [MeasurableSpace M] [BorelSpace M]
    [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M] :
    geometricStatement (I := I) (M := M) := by
  exact geometricStatement_proved

end AlmostSchurEntry.Geometry
