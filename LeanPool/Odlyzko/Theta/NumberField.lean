/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.PoissonSummation
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- An euclidean ideal lattice used in the Odlyzko-bound argument. -/
noncomputable def euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
    (mixedEmbedding.euclidean.toMixed K).toLinearMap

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (euclideanIdealLattice K I) := by
  unfold euclideanIdealLattice
  infer_instance

open Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (euclideanIdealLattice K I) := by
  unfold euclideanIdealLattice
  infer_instance

open Classical in
theorem covolume_euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclideanIdealLattice K I) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
        (2⁻¹) ^ nrComplexPlaces K * √|discr K| := by
  rw [euclideanIdealLattice,
    ZLattice.covolume_comap (mixedEmbedding.idealLattice K I)
      MeasureTheory.volume MeasureTheory.volume
      (mixedEmbedding.euclidean.volumePreserving_toMixed K),
    mixedEmbedding.covolume_idealLattice]

end NumberField.Odlyzko
