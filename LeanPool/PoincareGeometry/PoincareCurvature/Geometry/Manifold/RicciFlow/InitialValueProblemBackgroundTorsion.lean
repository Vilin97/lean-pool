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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.InitialValueProblemBackground

/-!
# Torsion-free fixed backgrounds for Ricci--DeTurck flow

The fixed background attached to initial-value data is Levi-Civita for the
initial metric.  This small bridge exposes the torsion-free part of that fact
both for the underlying connection and for its constant time-dependent
connection family.  The latter is the form used by the background-covariant
Ricci--DeTurck decomposition.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

namespace InitialValueProblem

omit [T2Space M] [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] in
/-- The fixed Levi-Civita background connection is torsion-free. -/
theorem FixedLeviCivitaBackground.isTorsionFree
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (background : FixedLeviCivitaBackground (I := I) (M := M) ivp) :
    background.covariantDerivative.IsTorsionFree := by
  exact background.isLeviCivita.1

omit [T2Space M] [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] in
/-- Every slice of the constant connection family from a fixed Levi-Civita
background is torsion-free. -/
theorem FixedLeviCivitaBackground.constantConnection_isTorsionFree
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (background : FixedLeviCivitaBackground (I := I) (M := M) ivp) :
    ∀ t : ℝ, (background.constantConnection t).IsTorsionFree := by
  intro t
  change background.covariantDerivative.IsTorsionFree
  exact background.isTorsionFree

/-- The canonical compact-IVP fixed background supplies a torsion-free
constant connection family. -/
theorem fixedLeviCivitaBackground_constantConnection_isTorsionFree
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ∀ t : ℝ,
      ((fixedLeviCivitaBackground (I := I) (M := M) ivp).constantConnection t).IsTorsionFree :=
  (fixedLeviCivitaBackground (I := I) (M := M) ivp).constantConnection_isTorsionFree

end InitialValueProblem

end RicciFlow
