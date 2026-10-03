/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse.Laws

/-!
# Exact coarse-source Chapter 4 laws

This is the staging law surface for the coarse-graining source.  Its carrier
and probability assumptions are deliberately separate from the existing
regular/restriction Chapter 4 lane.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory

/-- A Chapter 4 law on the exact coarse source carrier. -/
abbrev SourceCoeffLaw (d : ℕ) : Type _ :=
  Measure (Source.Coarse.Carrier d)

/-- The coarse source stationarity assumption (P1). -/
abbrev SourceStationaryLaw {d : ℕ} (P : SourceCoeffLaw d) : Prop :=
  Source.Coarse.IsStationary P

/-- The coarse source Euclidean unit-range dependence assumption (P2). -/
abbrev SourceUnitRangeDependentLaw {d : ℕ} (P : SourceCoeffLaw d) : Prop :=
  Source.Coarse.IsUnitRangeDependent P

/-- The coarse source joint isotropy and adjoint-invariance assumption (P3). -/
abbrev SourceIsotropicAndAdjointInvariantLaw {d : ℕ} (P : SourceCoeffLaw d) : Prop :=
  Source.Coarse.IsIsotropicAndAdjointInvariant P

/-- The three structural assumptions of the coarse-graining source.

Probability is intentionally not bundled here: clients state it separately as
an `IsProbabilityMeasure` instance when it is needed. -/
structure SourceStructuralLaw {d : ℕ} (P : SourceCoeffLaw d) : Prop where
  stationary : SourceStationaryLaw P
  unit_range : SourceUnitRangeDependentLaw P
  isotropic_and_adjoint_invariant : SourceIsotropicAndAdjointInvariantLaw P

end Homogenization.Book.Ch04
