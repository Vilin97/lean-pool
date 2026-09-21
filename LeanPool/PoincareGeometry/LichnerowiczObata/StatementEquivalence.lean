/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ClosedStatement
public import LeanPool.PoincareGeometry.LichnerowiczObata.GeometryComparison

/-! The renderer-compatible statement is definitionally equivalent to the
original theorem with every hypothesis and geometric operation unchanged. -/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators

namespace LichnerowiczObataEntry.Geometry

universe u v w

/-- Closing the parameters and inlining the definitions neither weakens nor
strengthens the original quantified statement. -/
theorem completeStatement_iff : completeStatement.{u,v,w} ↔
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
      {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
      [RiemannianBundle (TangentSpace I : M → Type _)]
      [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
      [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
      [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
      [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
      [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M],
      geometricStatement (I := I) (M := M)) := by
  rfl

/-- The original geometric proof supplies the renderer-compatible statement. -/
theorem completeStatement_proved : completeStatement.{u,v,w} := by
  apply completeStatement_iff.mpr
  intros
  exact geometricStatement_proved

end LichnerowiczObataEntry.Geometry
