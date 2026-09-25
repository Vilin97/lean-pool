/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceObservable

/-!
# Independence of exact coarse-source local random variables

This module promotes the coarse source's unit-range-dependence law to finite
independence of its exact local sigma algebras and observables.  It is separate
from the regular-carrier restriction-local compatibility lane.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory

/-- Source-local finite independence for Euclidean-unit-separated regions. -/
theorem iIndep_sourceLocalSigma_of_sourceUnitRangeDependentLaw {d : ℕ} {ι : Type*}
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P] {U : ι → Set (Vec d)}
    (hU : ∀ i, MeasurableSet (U i))
    (hP : SourceUnitRangeDependentLaw P)
    (hsep : Pairwise fun i j => Source.Coarse.EuclideanUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndep (fun i => Source.Coarse.localSigma (U i) (hU i)) P :=
  Source.Coarse.iIndep_localSigma_of_pairwise_euclideanUnitSeparated P hP hU hsep

/-- Source-local random variables on Euclidean-unit-separated regions are
independent. -/
theorem iIndepFun_of_sourceLocalRandomVariable_of_sourceUnitRangeDependentLaw
    {d : ℕ} {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {P : SourceCoeffLaw d} [IsProbabilityMeasure P]
    {U : ι → Set (Vec d)} {X : ∀ i, Source.Coarse.Carrier d → β i}
    (hU : ∀ i, MeasurableSet (U i))
    (hP : SourceUnitRangeDependentLaw P)
    (hX : ∀ i, IsSourceLocalRandomVariable (U i) (hU i) (X i))
    (hsep : Pairwise fun i j => Source.Coarse.EuclideanUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndepFun X P :=
  Source.Coarse.iIndepFun_of_localObservable_of_pairwise_euclideanUnitSeparated
    P hP hU hX hsep

end Homogenization.Book.Ch04
