/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceIndependence
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassIndependence

/-! # Independence Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Canonical source-local finite independence

This module exposes the Chapter 4 finite-independence facade on the exact
source carrier. Restriction-local finite independence is available explicitly
from `RestrictionIndependence`.
-/

noncomputable section

open MeasureTheory

/-- Canonical source-local finite independence for Euclidean-unit-separated
regions. -/
theorem iIndep_localSigma_of_unitRangeDependentLaw {d : ℕ} {ι : Type*}
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P] {U : ι → Set (Vec d)}
    (hU : ∀ i, MeasurableSet (U i))
    (hP : SourceUnitRangeDependentLaw P)
    (hsep : Pairwise fun i j => Source.Coarse.EuclideanUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndep (fun i => Source.Coarse.localSigma (U i) (hU i)) P :=
  iIndep_sourceLocalSigma_of_sourceUnitRangeDependentLaw hU hP hsep

/-- Canonical source-local random-variable independence. -/
theorem iIndepFun_of_unitRangeDependentLaw_of_pairwise_separated {d : ℕ}
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P]
    {U : ι → Set (Vec d)} {X : ∀ i, Source.Coarse.Carrier d → β i}
    (hU : ∀ i, MeasurableSet (U i))
    (hP : SourceUnitRangeDependentLaw P)
    (hX : ∀ i, IsSourceLocalRandomVariable (U i) (hU i) (X i))
    (hsep : Pairwise fun i j => Source.Coarse.EuclideanUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndepFun X P :=
  iIndepFun_of_sourceLocalRandomVariable_of_sourceUnitRangeDependentLaw hU hP hX hsep

/-- Canonical source-local descendant color-class independence. -/
theorem iIndepFun_descendantsAtScaleScaleColorClass_of_unitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P]
    {β : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c} → Type*}
    [∀ R, MeasurableSpace (β R)]
    {X : ∀ R, Source.Coarse.Carrier d → β R}
    (hP : SourceUnitRangeDependentLaw P)
    (hX : ∀ R, IsSourceLocalRandomVariable (cubeSet R.1) (measurableSet_cubeSet R.1) (X R)) :
    ProbabilityTheory.iIndepFun X P :=
  iIndepFun_descendantsAtScaleScaleColorClass_of_sourceUnitRangeDependentLaw hP hX

end

end Ch04
end Book
end Homogenization
