/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckJointRegularity

/-!
# Metric defect of the explicit Levi-Civita correction

This file records the pointwise identity saying that the explicit correction
from an arbitrary background affine connection to the slice Levi-Civita
connection accounts exactly for the background connection's metric defect.
It is algebraic and does not require the background connection to be
torsion-free.
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

local notation "TM" => (TangentSpace I : M → Type _)
local notation "⟪" x ", " y "⟫" => inner ℝ x y
/-- The background metric defect is the sum of the two metric pairings of the
explicit correction.  The correction uses the repository's order
`(differentiated vector, direction)`. -/
theorem metricDefect_eq_explicitLeviCivitaCorrection_pairings
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    (background t).metricDefect x v w u =
      (g t).inner x
          (explicitLeviCivitaCorrection (I := I) (M := M) g background t x v u) w +
        (g t).inner x v
          (explicitLeviCivitaCorrection (I := I) (M := M) g background t x w u) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  have hcorrected :=
    (background t).correctedConnection_metricDefect_eq_zero x v w
  have hcorrected_apply := congrArg (fun f : TM x →L[ℝ] ℝ => f u) hcorrected
  rw [CovariantDerivative.metricDefect_addOneForm_apply] at hcorrected_apply
  simp only [zero_apply] at hcorrected_apply
  have hsum :
      (background t).metricDefect x v w u =
        ⟪(background t).leviCivitaCorrection x v u, w⟫ +
          ⟪v, (background t).leviCivitaCorrection x w u⟫ := by
    linarith
  change (background t).metricDefect x v w u =
    ⟪(background t).leviCivitaCorrection x v u, w⟫ +
      ⟪v, (background t).leviCivitaCorrection x w u⟫
  exact hsum

end RicciFlow
