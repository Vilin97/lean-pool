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
# Ricci-vanishing local-existence–uniqueness closure

This thin extension module abstracts the rank-one closure
`intrinsicLocalExistenceUniqueness_of_finrank_le_one` from `LocalExistence.lean` into a
dimension-free **Ricci-vanishing closure skeleton**.

The rank-one closure works because on tangent fibers of real dimension at most one the intrinsic
Ricci tensor of *every* metric vanishes identically, which simultaneously supplies the stationary
existence witness and — through `intrinsicLocalSolution_unique_metric_of_ricciTensor_zero` — the
metric-uniqueness half of the point-4 package.  The mechanism only ever uses the Ricci-vanishing
*fact*, never the dimension hypothesis, so it factors through a single reusable constructor:

* `intrinsicLocalExistenceUniqueness_of_forall_intrinsicRicciTensor_eq_zero` takes an existence
  witness together with the hypothesis that every intrinsic local solution has identically
  vanishing intrinsic Ricci tensor on its interval, and returns the full
  `IntrinsicLocalExistenceUniqueness` package.

Two instances are recorded:

* the **positive-dimensional Ricci-flat** instance keeps existence unconditional
  (`intrinsicLocalSolution_nonempty_of_isRicciFlat`) and isolates the single residual geometric
  input — that Ricci-flow solutions preserve Ricci-flatness — as the explicit Ricci-vanishing
  hypothesis;
* the **rank-one** instance recovers the known closure through the skeleton, discharging the
  Ricci-vanishing hypothesis for free from `intrinsicRicciTensor_eq_zero_of_finrank_le_one` and
  hence composing, unconditionally, to a genuine point-4 existence–uniqueness witness.
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

section Compact

variable [CompactSpace M]

section Intrinsic

variable [SigmaCompactSpace M]

/-- **Ricci-vanishing closure skeleton.**  If an initial value problem admits at least one
intrinsic local Ricci-flow solution and *every* intrinsic local solution has identically vanishing
intrinsic Ricci tensor on its interval, then the full intrinsic local existence–uniqueness package
holds: existence is supplied by `hexist`, and metric uniqueness follows from
`intrinsicLocalSolution_unique_metric_of_ricciTensor_zero`.

This is the dimension-free abstraction of `intrinsicLocalExistenceUniqueness_of_finrank_le_one`;
the rank-one hypothesis is only ever used to discharge `hRic`. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_forall_intrinsicRicciTensor_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hexist : Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp))
    (hRic : ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := hexist
  unique_metric := fun sol₁ sol₂ t ht x u v =>
    intrinsicLocalSolution_unique_metric_of_ricciTensor_zero
      (I := I) (M := M) sol₁ sol₂ (hRic sol₁) (hRic sol₂) ht x u v

/-- **Positive-dimensional Ricci-flat instance.**  For Ricci-flat initial data existence is
unconditional (the stationary Ricci-flat solution, `intrinsicLocalSolution_nonempty_of_isRicciFlat`),
so the entire remaining content of the point-4 package is the Ricci-vanishing hypothesis `hRic`,
i.e. that every intrinsic local solution stays Ricci-flat on its interval. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  intrinsicLocalExistenceUniqueness_of_forall_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) ivp
    (intrinsicLocalSolution_nonempty_of_isRicciFlat (I := I) (M := M) ivp hRicciFlat)
    hRic

/-- **Rank-one recovery through the skeleton.**  On compact manifolds whose tangent fibers have
real dimension at most one, both the existence witness and the Ricci-vanishing hypothesis are free,
so the skeleton reproduces `intrinsicLocalExistenceUniqueness_of_finrank_le_one` and, in particular,
composes unconditionally to a genuine intrinsic point-4 existence–uniqueness witness. -/
noncomputable def intrinsicLocalExistenceUniqueness_viaRicciZero_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  intrinsicLocalExistenceUniqueness_of_forall_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) ivp
    (intrinsicLocalSolution_nonempty_of_finrank_le_one (I := I) (M := M) hfin ivp)
    (fun sol t _ht x u v =>
      intrinsicRicciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol.toIntrinsicSolution.metric t x u v)

/-- The theorem-family version of `intrinsicLocalExistenceUniqueness_viaRicciZero_of_finrank_le_one`,
obtained by applying the Ricci-vanishing skeleton uniformly over all initial value problems. -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_viaRicciZero_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    intrinsicLocalExistenceUniqueness_viaRicciZero_of_finrank_le_one (I := I) (M := M) hfin ivp

/-- **Theorem-family Ricci-vanishing closure skeleton.**  A uniform supply of existence witnesses
together with the uniform Ricci-vanishing hypothesis (every intrinsic local solution of every
initial value problem stays Ricci-flat on its interval) yields the whole intrinsic
existence–uniqueness theorem family. -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_of_forall_intrinsicRicciTensor_eq_zero
    (hexist : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp))
    (hRic : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    intrinsicLocalExistenceUniqueness_of_forall_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ivp (hexist ivp) (hRic ivp)

/-- Ordinary (connection-parametrized) form of the Ricci-vanishing closure skeleton, obtained by
projecting the intrinsic package through `IntrinsicLocalExistenceUniqueness.toOrdinary`. -/
noncomputable def localExistenceUniqueness_of_forall_intrinsicRicciTensor_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hexist : Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp))
    (hRic : ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_forall_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) ivp hexist hRic).toOrdinary

/-- Theorem-family ordinary form of the Ricci-vanishing closure skeleton. -/
noncomputable def localExistenceUniquenessFamily_of_forall_intrinsicRicciTensor_eq_zero
    (hexist : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp))
    (hRic : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_forall_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) hexist hRic).toOrdinary

/-- **Theorem-family positive-dimensional Ricci-flat closure.**  A uniform supply of Ricci-flatness
(so existence is unconditional for every initial value problem) together with the uniform
Ricci-vanishing hypothesis yields the whole intrinsic existence–uniqueness theorem family; the only
remaining content is `hRic`, i.e. Ricci-flatness preservation along the flow. -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_of_forall_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (hRicciFlat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    intrinsicLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ivp (hRicciFlat ivp) (hRic ivp)

/-- Ordinary (connection-parametrized) positive-dimensional Ricci-flat closure: for Ricci-flat
initial data (existence unconditional) with the Ricci-vanishing hypothesis, the ordinary point-4
package holds, obtained from the intrinsic Ricci-flat closure through
`IntrinsicLocalExistenceUniqueness.toOrdinary`. -/
noncomputable def localExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) ivp hRicciFlat hRic).toOrdinary

/-- Theorem-family ordinary positive-dimensional Ricci-flat closure. -/
noncomputable def localExistenceUniquenessFamily_of_forall_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (hRicciFlat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (hRic : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_forall_isRicciFlat_of_forall_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) hRicciFlat hRic).toOrdinary

end Intrinsic

end Compact

end RicciFlow
