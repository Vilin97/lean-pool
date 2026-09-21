/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# Time-space local-frame Gram matrices

`CovariantDerivative.localFrameGramMatrix` uses a fixed ambient
`RiemannianBundle` instance and consequently describes one metric slice. This
module turns the same construction into a time-space matrix field for a
`MetricFamily`, and proves that every slice is the corresponding ordinary
local-frame Gram matrix.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Matrix
open scoped Bundle Manifold ContDiff
namespace RicciFlow
namespace AnalyticPDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The Gram matrix of a metric family in a fixed local tangent frame, viewed
as a time-space matrix field. -/
noncomputable def timeSpaceLocalFrameGramMatrix
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ E) : ℝ × M → Matrix ι ι ℝ :=
  fun z => by
    letI : RiemannianBundle TM := ⟨(g z.1).toRiemannianMetric⟩
    exact CovariantDerivative.localFrameGramMatrix (I := I) e bas z.2

@[simp] theorem timeSpaceLocalFrameGramMatrix_apply
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ E)
    (t : ℝ) (x : M) (i j : ι) :
    timeSpaceLocalFrameGramMatrix (I := I) (M := M) g e bas (t, x) i j =
      (g t).inner x (e.localFrame bas i x) (e.localFrame bas j x) := rfl

/-- The time-space Gram matrix at a fixed time is the existing local-frame
Gram matrix for that metric slice. -/
@[simp] theorem timeSpaceLocalFrameGramMatrix_eq_slice
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ E) (t : ℝ) (x : M) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    timeSpaceLocalFrameGramMatrix (I := I) (M := M) g e bas (t, x) =
      CovariantDerivative.localFrameGramMatrix (I := I) e bas x := by
  rfl

/-- Positivity of each metric slice makes its time-space local-frame Gram
matrix nonsingular on the local frame's base set. -/
theorem timeSpaceLocalFrameGramMatrix_det_ne_zero
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bas : Module.Basis ι ℝ E) {z : ℝ × M} (hz : z.2 ∈ e.baseSet) :
    (timeSpaceLocalFrameGramMatrix (I := I) (M := M) g e bas z).det ≠ 0 := by
  let _ : RiemannianBundle TM := ⟨(g z.1).toRiemannianMetric⟩
  change (show Matrix ι ι ℝ from
    CovariantDerivative.localFrameGramMatrix (I := I) e bas z.2).det ≠ 0
  exact CovariantDerivative.localFrameGramMatrix_det_ne_zero (I := I) (E := E) e bas hz

end AnalyticPDE
end RicciFlow
