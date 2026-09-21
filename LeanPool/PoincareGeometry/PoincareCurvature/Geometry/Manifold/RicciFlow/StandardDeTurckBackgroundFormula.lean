/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurck
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckJointRegularity

/-!
# Background-connection formula for the standard DeTurck field

The standard field contracts the actual Levi-Civita correction of a fixed
background connection in both connection-input slots.  The prior
`intrinsicDeTurck...` results imported here are used only for the raw
connection-difference identity; no trace-one-form identity is reused.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The two-input tensor contracted by the standard DeTurck field is the
explicit Levi-Civita correction of the background connection, with the
direction and differentiated-vector arguments in standard order. -/
theorem standardDeTurckDifferenceBilinear_apply_eq_explicitLeviCivitaCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    standardDeTurckDifferenceBilinear (I := I) (M := M) g background t x u v =
      explicitLeviCivitaCorrection (I := I) (M := M) g background t x v u := by
  rw [standardDeTurckDifferenceBilinear_apply,
    intrinsicDeTurck_difference_apply_eq_leviCivitaCorrection]

/-- In a local frame, the standard DeTurck vector is the inverse-metric
contraction of the explicit Levi-Civita correction of the background
connection.  Its frame components are the usual
`g^{ab}(Γ(g)^k_ab - Γ(background)^k_ab)`. -/
theorem standardDeTurckVectorField_eq_sum_localFrame_inverseGram_explicitLeviCivitaCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    standardDeTurckVectorField (I := I) (M := M) g background t x =
      (letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
       ∑ i : ι, ∑ j : ι,
         CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j •
           explicitLeviCivitaCorrection (I := I) (M := M) g background t x
             (e.localFrame b j x) (e.localFrame b i x)) := by
  rw [standardDeTurckVectorField_eq_sum_localFrame_inverseGram
    (I := I) (M := M) g background t e b hx]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [intrinsicDeTurck_difference_apply_eq_leviCivitaCorrection]

end RicciFlow
