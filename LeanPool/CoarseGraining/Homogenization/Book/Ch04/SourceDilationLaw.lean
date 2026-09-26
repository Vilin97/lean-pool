/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLaw
public import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse.RescaledLaws

/-!
# Dilation of exact coarse-source Chapter 4 laws

This is the thin Chapter 4 wrapper around the source-side normalized-law
kernel.  Probability remains separate from the structural-law bundle.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory

/-- Probability is preserved by exact-source triadic scale-normalization. -/
theorem isProbabilityMeasure_sourceScaleNormalizedLaw {d : ℕ} (k : ℕ)
    (P : SourceCoeffLaw d) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (Source.Coarse.scaleNormalizedLaw k P) :=
  Source.Coarse.isProbabilityMeasure_scaleNormalizedLaw k P

namespace SourceStructuralLaw

/-- The exact coarse-source structural law is preserved by triadic
scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : SourceCoeffLaw d}
    (hP : SourceStructuralLaw P) (k : ℕ) :
    SourceStructuralLaw (Source.Coarse.scaleNormalizedLaw k P) where
  stationary := Source.Coarse.IsStationary.scaleNormalized hP.stationary k
  unit_range := Source.Coarse.IsUnitRangeDependent.scaleNormalized hP.unit_range k
  isotropic_and_adjoint_invariant :=
    Source.Coarse.IsIsotropicAndAdjointInvariant.scaleNormalized
      hP.isotropic_and_adjoint_invariant k

end SourceStructuralLaw

end Homogenization.Book.Ch04
