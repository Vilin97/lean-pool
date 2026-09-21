/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.QuenchedGammaEllipticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEllipticityEndpoint
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FirstQuenchedEstimate
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AnnealedLimit
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LimitNormalization
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UnitJTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AnnealedJLimit
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedMax
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FiniteBasis
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedFiniteBasis
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ProbeMax
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ProbeEnvelope
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadEventSummability
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.DeterministicThresholds
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleGeometry
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadPairSelection
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ExponentCompetition
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleUnion
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadTailUnion
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.MinimalScaleTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.QuenchedLocalizedEstimate
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleSplit
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentUnion
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ExponentialKernel
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.WeightedExponentialKernel
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FiniteSupTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedMaxTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadPairNoLog
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.KernelUnion
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentRows
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentSummation
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsTop
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsHigh
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsBottom
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsCrudeBottom
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformCrudeBottom
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHighBottom
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHighTop
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEndpointDenominator
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEndpointSynchronized
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleTailCollapse
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleTailFinal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleMinimalQuantitative
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformScaleCompressionFinal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHomogenizationQuenched
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailAssembly
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleThresholds
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePairTwoBranch
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePairCollapse
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailExponent
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailTwoBranch
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailDenominator
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailRaw
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailRawCrude
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailJoint
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailCollapse
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailSelected
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePrefactorGap
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePrefactorGapQuantitative
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailFinal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailFinalQuantitative
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleMinimal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleMinimalQuantitative
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompression
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompressionThreshold
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompressionFinal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.EntryScaleCompression
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FirstQuenchedEstimateCompressed
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleEntrySplit
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.SmallBottomBand
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.SmallBottomTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteBadScaleTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteMinimalScale
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteScaleCompression
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteScaleCompressionFinal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationQuenched
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorControl
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorFiniteQ
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorClosed
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.NormalizedResponseEllipticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorLowerEnvelope
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedUnitEllipticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedUnitEllipticityMinimal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UnitEllipticityMinimalExpLogSq
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorMinimalScale
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorQuenched
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.EllipticityFromMinimalScale
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssembly
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyRHS
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyEndpoint
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyOptimized

/-! # Section57 -/

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
