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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence
/-!
# A fixed Levi-Civita background for initial-value data

For a compact manifold and a `C²` initial metric, the static Levi-Civita
construction supplies a `C¹` covariant derivative.  This module records that
construction in a form that can be used directly as a fixed Ricci--DeTurck
background: its constant connection family has the slice regularity required
by the DeTurck vector-field regularity lemmas.

The result is deliberately only `C¹` for the connection.  A `C²` metric does
not justify asserting higher connection regularity here.
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

/-- A `C¹` Levi-Civita connection for the initial metric of an IVP. -/
structure FixedLeviCivitaBackground
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- The fixed covariant derivative. -/
  covariantDerivative : CovariantDerivative I E TM
  /-- It is Levi-Civita for the IVP's initial metric. -/
  isLeviCivita :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
    covariantDerivative.IsLeviCivita
  /-- The spatial regularity supplied by a `C²` initial metric. -/
  contMDiff : CovariantDerivative.ContMDiffCovariantDerivative covariantDerivative 1

/-- The IVP's initial metric admits a `C¹` Levi-Civita covariant derivative. -/
theorem exists_initialMetric_contMDiffLeviCivitaConnection
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ∃ cov₀ : CovariantDerivative I E TM,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       cov₀.IsLeviCivita) ∧
        CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  exact CovariantDerivative.exists_contMDiffLeviCivitaConnection
    (I := I) (E := E) (M := M)

/-- A compact IVP admits a fixed `C¹` Levi-Civita background for its initial metric. -/
theorem fixedLeviCivitaBackground_nonempty
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (FixedLeviCivitaBackground (I := I) (M := M) ivp) := by
  rcases exists_initialMetric_contMDiffLeviCivitaConnection
    (I := I) (M := M) ivp with ⟨cov₀, hLevi, hcont⟩
  exact ⟨⟨cov₀, hLevi, hcont⟩⟩

/-- A chosen fixed `C¹` Levi-Civita background for the initial metric. -/
noncomputable def fixedLeviCivitaBackground
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    FixedLeviCivitaBackground (I := I) (M := M) ivp :=
  Classical.choice (fixedLeviCivitaBackground_nonempty (I := I) (M := M) ivp)

/-- The fixed connection, viewed as the constant background family used by DeTurck. -/
def FixedLeviCivitaBackground.constantConnection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (background : FixedLeviCivitaBackground (I := I) (M := M) ivp) :
    ConnectionFamily (I := I) (M := M) :=
  CovariantDerivative.TimeDependentCovariantDerivative.const
    (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)
    background.covariantDerivative

@[simp] theorem FixedLeviCivitaBackground.constantConnection_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (background : FixedLeviCivitaBackground (I := I) (M := M) ivp) (t : ℝ) :
    background.constantConnection t = background.covariantDerivative :=
  rfl

/-- The exact fixed-time `C¹` background hypothesis used by the DeTurck regularity lemmas. -/
theorem FixedLeviCivitaBackground.constantConnection_contMDiff
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (background : FixedLeviCivitaBackground (I := I) (M := M) ivp) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (background.constantConnection t) 1 := by
  intro t
  simpa only [FixedLeviCivitaBackground.constantConnection_apply] using background.contMDiff

/-- The constant connection background is Levi-Civita for the constant initial metric family. -/
theorem FixedLeviCivitaBackground.constantConnection_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (background : FixedLeviCivitaBackground (I := I) (M := M) ivp) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.const
        (I := I) (M := M) ivp.initialMetric)
      background.constantConnection := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      background.covariantDerivative 1 := background.contMDiff
  exact const_isLeviCivita (I := I) (M := M)
    ivp.initialMetric background.covariantDerivative background.isLeviCivita

/-- The canonical IVP background retains the `C¹` slice regularity needed by DeTurck. -/
theorem fixedLeviCivitaBackground_constantConnection_contMDiff
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        ((fixedLeviCivitaBackground (I := I) (M := M) ivp).constantConnection t) 1 :=
  (fixedLeviCivitaBackground (I := I) (M := M) ivp).constantConnection_contMDiff

end InitialValueProblem

end RicciFlow
