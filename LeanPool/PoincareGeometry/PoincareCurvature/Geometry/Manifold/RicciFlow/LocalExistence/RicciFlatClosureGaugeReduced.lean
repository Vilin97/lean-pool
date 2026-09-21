/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RicciFlatClosure
/-!
# Ricci-flat closure in the DeTurck / gauge-reduced point-4 vocabulary

This thin extension module projects the positive-dimensional Ricci-flat closure of
`RicciFlatClosure.lean` into the Levi-Civita-background and gauge-reduced Ricci-DeTurck theorem
packages — the forms in which roadmap point 4 is stated — exactly mirroring
`RankOneGaugeReduced.lean` for the rank-one case.

For Ricci-flat initial data existence is unconditional (the stationary Ricci-flat solution), so the
entire remaining content of each package is the Ricci-vanishing hypothesis `hRic`, i.e. that every
intrinsic local solution stays Ricci-flat on its interval (the single residual geometric input,
Ricci-flatness preservation).  These conversions dispatch through
`IntrinsicLocalExistenceUniqueness.toLeviCivitaBackgroundIntrinsicDeTurck` and
`IntrinsicLocalExistenceUniqueness.toGaugeReduced_viaIdentityGauge`.
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
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

section Compact

variable [CompactSpace M]

/-- **Levi-Civita-background Ricci-flat closure.**  For Ricci-flat initial data (existence
unconditional) with the Ricci-vanishing hypothesis `hRic`, the Levi-Civita-background Ricci-DeTurck
point-4 package holds, obtained from the intrinsic Ricci-flat closure through
`IntrinsicLocalExistenceUniqueness.toLeviCivitaBackgroundIntrinsicDeTurck`. -/
noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) ivp hRicciFlat hRic).toLeviCivitaBackgroundIntrinsicDeTurck

/-- **Gauge-reduced Ricci-flat closure.**  The gauge-reduced Ricci-flow point-4 package for
Ricci-flat initial data with the Ricci-vanishing hypothesis, through the identity `C³` gauge. -/
noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) ivp hRicciFlat hRic).toGaugeReduced_viaIdentityGauge

/-- **Chosen-background Ricci-flat closure.**  The chosen-background (identity `C³` gauge)
Ricci-DeTurck point-4 package for Ricci-flat initial data with the Ricci-vanishing hypothesis,
obtained from the intrinsic Ricci-flat closure through
`IntrinsicLocalExistenceUniqueness.toChosenIntrinsicDeTurck`. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) ivp hRicciFlat hRic).toChosenIntrinsicDeTurck

/-- Theorem-family Levi-Civita-background Ricci-flat closure: a uniform supply of Ricci-flatness and
the uniform Ricci-vanishing hypothesis yields the whole Levi-Civita-background theorem family. -/
noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily_of_forall_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (hRicciFlat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ivp (hRicciFlat ivp) (hRic ivp)

/-- Theorem-family gauge-reduced Ricci-flat closure. -/
noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily_of_forall_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (hRicciFlat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ivp (hRicciFlat ivp) (hRic ivp)

/-- Theorem-family chosen-background Ricci-flat closure: a uniform supply of Ricci-flatness and the
uniform Ricci-vanishing hypothesis yields the whole chosen-background (identity `C³` gauge)
Ricci-DeTurck theorem family. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_forall_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (hRicciFlat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    chosenIntrinsicDeTurckLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ivp (hRicciFlat ivp) (hRic ivp)

end Compact

end RicciFlow
