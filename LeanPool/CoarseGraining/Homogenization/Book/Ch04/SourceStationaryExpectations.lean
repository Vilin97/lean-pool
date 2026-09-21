/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLaw
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Translation
import LeanPool.CoarseGraining.Homogenization.Probability.RandomField

/-!
# Stationary expectations for the exact coarse source

This module transports deterministic set-translation covariance to the exact
coarse-source carrier, and then applies source stationarity to obtain equality
of laws and Bochner integrals.
-/

namespace Homogenization.Book.Ch04

open MeasureTheory

/-- Set-indexed covariance under the exact coarse-source carrier translation. -/
def IsSourceTranslationCovariant {β : Type*} {d : ℕ}
    (X : Set (Vec d) → Source.Coarse.Carrier d → β) : Prop :=
  ∀ (U : Set (Vec d)) (z : Fin d → ℤ) (a : Source.Coarse.Carrier d),
    X (translateSet (intVecToRealVec z) U) a = X U (Source.Coarse.Carrier.translate z a)

/-- Carrier translation projects to raw integer translation of the underlying
coefficient field. -/
theorem sourceCarrier_translate_toCoeffField {d : ℕ} (z : Fin d → ℤ)
    (a : Source.Coarse.Carrier d) :
    (Source.Coarse.Carrier.translate z a : CoeffField d) = translateByInt z a.1 :=
  rfl

/-- Raw translation covariance lifts along the exact coarse-source carrier. -/
theorem isSourceTranslationCovariant_comp_toCoeffField {β : Type*} {d : ℕ}
    {X : Set (Vec d) → CoeffField d → β} (hX : IsTranslationCovariant X) :
    IsSourceTranslationCovariant (fun U a => X U a.1) := by
  intro U z a
  change X (translateSet (intVecToRealVec z) U) a.1 =
    X U (Source.Coarse.Carrier.translate z a : CoeffField d)
  rw [hX U z a.1, sourceCarrier_translate_toCoeffField]

/-- Pointwise covariance is equivalent to a composition identity on the source
carrier. -/
theorem comp_sourceCarrier_translate_eq_of_isSourceTranslationCovariant
    {β : Type*} {d : ℕ} {X : Set (Vec d) → Source.Coarse.Carrier d → β}
    (hX : IsSourceTranslationCovariant X) (U : Set (Vec d)) (z : Fin d → ℤ) :
    X (translateSet (intVecToRealVec z) U) = X U ∘ Source.Coarse.Carrier.translate z := by
  funext a
  exact hX U z a

/-- Source stationarity identifies the laws of a measurable observable and
its precomposition with a coarse-source integer translation. -/
theorem map_comp_sourceCarrier_translate_eq_of_sourceStationaryLaw
    {β : Type*} [MeasurableSpace β] {d : ℕ} {P : SourceCoeffLaw d}
    (hP : SourceStationaryLaw P) (X : Source.Coarse.Carrier d → β)
    (hXmeas : Measurable X) (z : Fin d → ℤ) :
    Measure.map (X ∘ Source.Coarse.Carrier.translate z) P = Measure.map X P := by
  calc
    Measure.map (X ∘ Source.Coarse.Carrier.translate z) P =
        Measure.map X (Measure.map (Source.Coarse.Carrier.translate z) P) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map hXmeas (Source.Coarse.measurable_translate_globalSigma z)
              (μ := P))
    _ = Measure.map X P := by rw [hP z]

/-- Source stationarity preserves the Bochner integral of an observable
precomposed with a coarse-source integer translation. -/
theorem integral_comp_sourceCarrier_translate_eq_of_sourceStationaryLaw_aestronglyMeasurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {P : SourceCoeffLaw d} (hP : SourceStationaryLaw P)
    (z : Fin d → ℤ) (X : Source.Coarse.Carrier d → E)
    (hXmeas : AEStronglyMeasurable X P) :
    ∫ a, X (Source.Coarse.Carrier.translate z a) ∂P = ∫ a, X a ∂P :=
  integral_comp_eq_of_map_eq
    (Source.Coarse.measurable_translate_globalSigma z) (hP z) X hXmeas

/-- Measurable specialization of source stationary integral transport. -/
theorem integral_comp_sourceCarrier_translate_eq_of_sourceStationaryLaw
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {P : SourceCoeffLaw d} (hP : SourceStationaryLaw P)
    (z : Fin d → ℤ) (X : Source.Coarse.Carrier d → E)
    (hXmeas : Measurable X) :
    ∫ a, X (Source.Coarse.Carrier.translate z a) ∂P = ∫ a, X a ∂P :=
  integral_comp_sourceCarrier_translate_eq_of_sourceStationaryLaw_aestronglyMeasurable
    hP z X hXmeas.aestronglyMeasurable

/-- Source stationarity preserves integrability under precomposition with a
coarse-source integer translation. -/
theorem integrable_comp_sourceCarrier_translate_of_sourceStationaryLaw
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} {P : SourceCoeffLaw d} (hP : SourceStationaryLaw P)
    (z : Fin d → ℤ) (X : Source.Coarse.Carrier d → E)
    (hX : Integrable X P) :
    Integrable (X ∘ Source.Coarse.Carrier.translate z) P := by
  have hXmap : Integrable X (Measure.map (Source.Coarse.Carrier.translate z) P) := by
    simpa [hP z] using hX
  exact hXmap.comp_measurable (Source.Coarse.measurable_translate_globalSigma z)

/-- Source stationarity identifies the laws of a genuinely measurable
translation-covariant observable on translated sets. -/
theorem map_eq_map_sourceCarrier_translate_of_isSourceTranslationCovariant
    {β : Type*} [MeasurableSpace β] {d : ℕ} {P : SourceCoeffLaw d}
    {X : Set (Vec d) → Source.Coarse.Carrier d → β}
    (hP : SourceStationaryLaw P) {U : Set (Vec d)} (hXmeas : Measurable (X U))
    (hXcov : IsSourceTranslationCovariant X) (z : Fin d → ℤ) :
    Measure.map (X (translateSet (intVecToRealVec z) U)) P = Measure.map (X U) P := by
  calc
    Measure.map (X (translateSet (intVecToRealVec z) U)) P =
        Measure.map (X U ∘ Source.Coarse.Carrier.translate z) P := by
          rw [comp_sourceCarrier_translate_eq_of_isSourceTranslationCovariant hXcov U z]
    _ = Measure.map (X U) (Measure.map (Source.Coarse.Carrier.translate z) P) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map hXmeas (Source.Coarse.measurable_translate_globalSigma z)
              (μ := P))
    _ = Measure.map (X U) P := by rw [hP z]

/-- Source stationarity identifies Bochner integrals of translation-covariant
observables, assuming a.e.-strong measurability at the reference set. -/
theorem integral_eq_of_isSourceTranslationCovariant_of_stationary_aestronglyMeasurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {P : SourceCoeffLaw d} {X : Set (Vec d) → Source.Coarse.Carrier d → E}
    (hP : SourceStationaryLaw P) {U : Set (Vec d)}
    (hXmeas : AEStronglyMeasurable (X U) P)
    (hXcov : IsSourceTranslationCovariant X) (z : Fin d → ℤ) :
    ∫ a, X (translateSet (intVecToRealVec z) U) a ∂P = ∫ a, X U a ∂P := by
  rw [comp_sourceCarrier_translate_eq_of_isSourceTranslationCovariant hXcov U z]
  exact integral_comp_eq_of_map_eq
    (Source.Coarse.measurable_translate_globalSigma z) (hP z) (X U) hXmeas

/-- Measurable form of source stationary integral transport. -/
theorem integral_eq_of_isSourceTranslationCovariant_of_stationary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {P : SourceCoeffLaw d} {X : Set (Vec d) → Source.Coarse.Carrier d → E}
    (hP : SourceStationaryLaw P) {U : Set (Vec d)} (hXmeas : Measurable (X U))
    (hXcov : IsSourceTranslationCovariant X) (z : Fin d → ℤ) :
    ∫ a, X (translateSet (intVecToRealVec z) U) a ∂P = ∫ a, X U a ∂P :=
  integral_eq_of_isSourceTranslationCovariant_of_stationary_aestronglyMeasurable
    hP hXmeas.aestronglyMeasurable hXcov z

/-- The exact source coarse energy is translation-covariant. -/
theorem sourceMu_translation_covariant {d : ℕ} (P0 : BlockVec d) :
    IsSourceTranslationCovariant
      (fun (_U : Set (Vec d)) (a : Source.Coarse.Carrier d) => Mu _U P0 a.1) := by
  apply isSourceTranslationCovariant_comp_toCoeffField
    (X := fun (U : Set (Vec d)) (a : CoeffField d) => Mu U P0 a)
  intro U z a
  simpa [translateByInt] using
    Mu_translateSet_eq_translateCoeffField (intVecToRealVec z) U P0 a

/-- The exact source coarse block matrix is translation-covariant. -/
theorem sourceCoarseBlockMatrix_translation_covariant {d : ℕ} :
    IsSourceTranslationCovariant
      (fun (U : Set (Vec d)) (a : Source.Coarse.Carrier d) => coarseBlockMatrix U a.1) := by
  apply isSourceTranslationCovariant_comp_toCoeffField
    (X := fun (U : Set (Vec d)) (a : CoeffField d) => coarseBlockMatrix U a)
  intro U z a
  simpa [translateByInt] using
    coarseBlockMatrix_translateSet_eq_translateCoeffField (intVecToRealVec z) U a

/-- A coarse block-matrix entry is translation-covariant on the exact source. -/
theorem sourceCoarseBlockMatrix_entry_translation_covariant {d : ℕ}
    (α β : BlockCoord d) :
    IsSourceTranslationCovariant
      (fun (U : Set (Vec d)) (a : Source.Coarse.Carrier d) =>
        blockMatEntry (coarseBlockMatrix U a.1) α β) := by
  apply isSourceTranslationCovariant_comp_toCoeffField
    (X := fun (U : Set (Vec d)) (a : CoeffField d) =>
      blockMatEntry (coarseBlockMatrix U a) α β)
  intro U z a
  simpa [translateByInt] using congrArg (fun A : BlockMat d => blockMatEntry A α β)
    (coarseBlockMatrix_translateSet_eq_translateCoeffField (intVecToRealVec z) U a)

/-- The unfolded full coarse block matrix is translation-covariant on the exact
source. -/
theorem sourceFullCoarseBlockMatrix_translation_covariant {d : ℕ} :
    IsSourceTranslationCovariant
      (fun (U : Set (Vec d)) (a : Source.Coarse.Carrier d) =>
        toFullBlockMat (coarseBlockMatrix U a.1)) := by
  apply isSourceTranslationCovariant_comp_toCoeffField
    (X := fun (U : Set (Vec d)) (a : CoeffField d) =>
      toFullBlockMat (coarseBlockMatrix U a))
  intro U z a
  simpa [translateByInt] using congrArg toFullBlockMat
    (coarseBlockMatrix_translateSet_eq_translateCoeffField (intVecToRealVec z) U a)

/-- A component of the unfolded full coarse block matrix is translation-covariant
on the exact source. -/
theorem sourceFullCoarseBlockMatrix_entry_translation_covariant {d : ℕ}
    (i j : BlockCoord d) :
    IsSourceTranslationCovariant
      (fun (U : Set (Vec d)) (a : Source.Coarse.Carrier d) =>
        toFullBlockMat (coarseBlockMatrix U a.1) i j) := by
  apply isSourceTranslationCovariant_comp_toCoeffField
    (X := fun (U : Set (Vec d)) (a : CoeffField d) =>
      toFullBlockMat (coarseBlockMatrix U a) i j)
  intro U z a
  simpa [translateByInt] using congrArg (fun A : FullBlockMat d => A i j) (congrArg toFullBlockMat
    (coarseBlockMatrix_translateSet_eq_translateCoeffField (intVecToRealVec z) U a))

end Homogenization.Book.Ch04
