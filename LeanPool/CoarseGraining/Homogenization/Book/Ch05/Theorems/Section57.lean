/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.QuenchedGammaEllipticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEllipticityEndpoint
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FirstQuenchedEstimate
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AnnealedLimit
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LimitNormalization
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UnitJTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AnnealedJLimit
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedMax
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FiniteBasis
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedFiniteBasis
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ProbeMax
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ProbeEnvelope
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadEventSummability
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.DeterministicThresholds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleGeometry
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadPairSelection
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ExponentCompetition
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleUnion
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadTailUnion
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.MinimalScaleTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.QuenchedLocalizedEstimate
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleSplit
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentUnion
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ExponentialKernel
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.WeightedExponentialKernel
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FiniteSupTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedMaxTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadPairNoLog
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.KernelUnion
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentRows
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentSummation
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsTop
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsHigh
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsBottom
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsCrudeBottom
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformCrudeBottom
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHighBottom
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHighTop
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEndpointDenominator
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEndpointSynchronized
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleTailCollapse
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleTailFinal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleMinimalQuantitative
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformScaleCompressionFinal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHomogenizationQuenched
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailAssembly
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleThresholds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePairTwoBranch
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePairCollapse
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailExponent
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailTwoBranch
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailDenominator
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailRaw
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailRawCrude
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailJoint
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailCollapse
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailSelected
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePrefactorGap
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePrefactorGapQuantitative
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailFinal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailFinalQuantitative
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleMinimal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleMinimalQuantitative
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompression
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompressionThreshold
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompressionFinal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.EntryScaleCompression
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FirstQuenchedEstimateCompressed
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleEntrySplit
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.SmallBottomBand
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.SmallBottomTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteBadScaleTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteMinimalScale
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteScaleCompression
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteScaleCompressionFinal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationQuenched
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorControl
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorFiniteQ
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorClosed
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.NormalizedResponseEllipticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorLowerEnvelope
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedUnitEllipticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedUnitEllipticityMinimal
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UnitEllipticityMinimalExpLogSq
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorMinimalScale
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorQuenched
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.EllipticityFromMinimalScale
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssembly
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyRHS
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyEndpoint
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyOptimized

/-! # Section57 -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Section 5.7: quenched minimal scales and perturbative consequences

This file is the scaffold for the current manuscript's Section 5.7:
the quenched coarse-grained ellipticity input, the quenched perturbative-scale
theorem, and the inhomogeneous comparison corollary.

This section should start only after the annealed algebraic convergence theorem
is green.
-/

end Section57
end Ch05
end Book
end Homogenization
