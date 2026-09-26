/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

module

public import LeanPool.Besicovitch.BesicovitchPairCondition.Basic
public import LeanPool.Besicovitch.BesicovitchPairCondition.Definitions
public import LeanPool.Besicovitch.BesicovitchPairCondition.Extraction
public import LeanPool.Besicovitch.BesicovitchPairCondition.PackingMeasure
public import LeanPool.Besicovitch.BesicovitchPairCondition.Parameters
public import LeanPool.Besicovitch.BesicovitchPairCondition.Rectifiability
public import LeanPool.Besicovitch.BesicovitchPairCondition.RootBalls
public import LeanPool.Besicovitch.BesicovitchPairCondition.SixPointTransfer
public import LeanPool.Besicovitch.Certificates.DensePolynomial
public import LeanPool.Besicovitch.Certificates.EndpointBridge
public import LeanPool.Besicovitch.Certificates.EndpointIsolation
public import LeanPool.Besicovitch.Certificates.Krawczyk
public import LeanPool.Besicovitch.Certificates.RadicalInterval
public import LeanPool.Besicovitch.Certificates.RationalInterval
public import LeanPool.Besicovitch.Example.Avoid
public import LeanPool.Besicovitch.Example.Cover
public import LeanPool.Besicovitch.Example.Density
public import LeanPool.Besicovitch.Example.Graph
public import LeanPool.Besicovitch.Example.Hull
public import LeanPool.Besicovitch.Example.LowerBound
public import LeanPool.Besicovitch.Example.LowerDensity
public import LeanPool.Besicovitch.Example.Measurable
public import LeanPool.Besicovitch.Example.Plane
public import LeanPool.Besicovitch.Example.Recursion
public import LeanPool.Besicovitch.Example.Reduction
public import LeanPool.Besicovitch.Example.Zero
public import LeanPool.Besicovitch.Geometry.BallUnion
public import LeanPool.Besicovitch.Geometry.ConvexEnlargement
public import LeanPool.Besicovitch.Main.Bound
public import LeanPool.Besicovitch.Main.RationalBound
public import LeanPool.Besicovitch.Measure.CompactExhaustion
public import LeanPool.Besicovitch.Measure.DensityBasic
public import LeanPool.Besicovitch.Measure.DensityLocalization
public import LeanPool.Besicovitch.Measure.UniformDensity
public import LeanPool.Besicovitch.Measure.UniformDensityCompact
public import LeanPool.Besicovitch.Rectifiability.AttachmentLocalization
public import LeanPool.Besicovitch.Rectifiability.BadConvexLocalization
public import LeanPool.Besicovitch.Rectifiability.BadConvexPacking
public import LeanPool.Besicovitch.Rectifiability.BadConvexSets
public import LeanPool.Besicovitch.Rectifiability.BadConvexThickening
public import LeanPool.Besicovitch.Rectifiability.Basic
public import LeanPool.Besicovitch.Rectifiability.CompactAttachmentUnion
public import LeanPool.Besicovitch.Rectifiability.ComponentDiameter
public import LeanPool.Besicovitch.Rectifiability.Continuum
public import LeanPool.Besicovitch.Rectifiability.ContinuumSurgery
public import LeanPool.Besicovitch.Rectifiability.ConvexAttachment
public import LeanPool.Besicovitch.Rectifiability.Decomposition
public import LeanPool.Besicovitch.Rectifiability.DensityPoint
public import LeanPool.Besicovitch.Rectifiability.FiniteContinuum
public import LeanPool.Besicovitch.Rectifiability.HoleMerging
public import LeanPool.Besicovitch.Rectifiability.Selection
public import LeanPool.Besicovitch.Rectifiability.Straight
public import LeanPool.Besicovitch.Rectifiability.StraightReduction
public import LeanPool.Besicovitch.Sigma.Basic
public import LeanPool.Besicovitch.SixPoint.AlgebraicBasic
public import LeanPool.Besicovitch.SixPoint.BlueChildSwap
public import LeanPool.Besicovitch.SixPoint.CanonicalTriangle
public import LeanPool.Besicovitch.SixPoint.ChildSwapPacking
public import LeanPool.Besicovitch.SixPoint.Configuration
public import LeanPool.Besicovitch.SixPoint.EndpointFailureClosed
public import LeanPool.Besicovitch.SixPoint.EndpointGeometry
public import LeanPool.Besicovitch.SixPoint.EndpointPacking
public import LeanPool.Besicovitch.SixPoint.EndpointWeights
public import LeanPool.Besicovitch.SixPoint.FailureTree
public import LeanPool.Besicovitch.SixPoint.FiniteProperty
public import LeanPool.Besicovitch.SixPoint.FourChildren
public import LeanPool.Besicovitch.SixPoint.GramCertificateCore
public import LeanPool.Besicovitch.SixPoint.GramCertificateCover
public import LeanPool.Besicovitch.SixPoint.GramCertificateData
public import LeanPool.Besicovitch.SixPoint.GramWeightedBound
public import LeanPool.Besicovitch.SixPoint.LensEndpointBalancedE0S0
public import LeanPool.Besicovitch.SixPoint.Normalization
public import LeanPool.Besicovitch.SixPoint.Packing
public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.Realization
public import LeanPool.Besicovitch.SixPoint.RootEdge
public import LeanPool.Besicovitch.SixPoint.RootEdgeClosed
public import LeanPool.Besicovitch.SixPoint.RootEdgeFailureTree
public import LeanPool.Besicovitch.SixPoint.RootEdgeType12
public import LeanPool.Besicovitch.SixPoint.RowColumnRescue
public import LeanPool.Besicovitch.SixPoint.Scaling
public import LeanPool.Besicovitch.SixPoint.Score
public import LeanPool.Besicovitch.SixPoint.SiblingFailureTree
public import LeanPool.Besicovitch.SixPoint.SiblingIncidence
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceClosed
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceLedger
public import LeanPool.Besicovitch.SixPoint.SiblingLens
public import LeanPool.Besicovitch.SixPoint.SiblingLensE1S0
public import LeanPool.Besicovitch.SixPoint.SiblingLensS0S0
public import LeanPool.Besicovitch.SixPoint.SiblingLensS0S3
public import LeanPool.Besicovitch.SixPoint.SiblingTangent
public import LeanPool.Besicovitch.SixPoint.SiblingTriangle
public import LeanPool.Besicovitch.SixPoint.WeightedFailure
public import LeanPool.Besicovitch.SixPoint.WeightedReduction
public import LeanPool.Besicovitch.Statement
public import LeanPool.Besicovitch.Topology.ConnectedComponent

/-!
# A machine-checked bound of 0.6934 for Besicovitch's 1/2-problem

Source: url:https://github.com/CoolRmal/Besicovitchs-1-2
Authors: Yongxi Lin
Status: verified
Main declarations: `LeanPool.Besicovitch.sigmaOne_plane_le_barS`
Tags: besicovitch-problem, measure-theory, rectifiability, finite-certificates, gram-matrices
MSC: 28A75, 28A78, 49Q15, 68V20, 90C05
-/
