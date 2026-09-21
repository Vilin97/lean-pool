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

public import LeanPool.PoincareGeometry.AlmostSchur.PointwiseConnection
public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaCorrection

/-! # A constructed metric-compatible torsion-free connection

The seed is explicit, so the existence result does not assume any connection.
Regularity of the corrected connection is a separate theorem, not a property
of the point-dependent seed chart selection.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

/-- The explicit seed corrected by its actual metric defect and torsion. -/
def leviCivitaConnection : CovariantDerivative I E TM :=
  leviCivitaCorrected (pointwiseChartConnection (I := I))

/-- Metric compatibility of the constructed connection, not an input hypothesis. -/
theorem leviCivitaConnection_metricCompatible :
    tangentMetricCompatible (leviCivitaConnection (I := I) (M := M)) :=
  leviCivitaCorrected_metricCompatible _

/-- Vanishing torsion of the constructed connection, not an input hypothesis. -/
theorem leviCivitaConnection_torsion :
    (leviCivitaConnection (I := I) (M := M)).torsion = 0 :=
  leviCivitaCorrected_torsion _

/-- Existence without an assumed seed connection. Regularity is not asserted here. -/
theorem exists_metricCompatible_torsionFree_connection :
    ∃ cov : CovariantDerivative I E TM, tangentMetricCompatible cov ∧ cov.torsion = 0 :=
  ⟨leviCivitaConnection, leviCivitaConnection_metricCompatible, leviCivitaConnection_torsion⟩

end AlmostSchur
