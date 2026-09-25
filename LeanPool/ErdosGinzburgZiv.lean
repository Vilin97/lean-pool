/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ
public import LeanPool.ErdosGinzburgZiv.EGZ.Asymptotics
public import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.Existence
public import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.IntegerApproximation
public import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RationalApproximation
public import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RationalCoefficients
public import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RealCoefficients
public import LeanPool.ErdosGinzburgZiv.EGZ.BalancedCombination
public import LeanPool.ErdosGinzburgZiv.EGZ.BalancedRounding
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.ConvexHullClosure
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.FaceFlagHellyBound
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.LocalToCumulative
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.PropositionSevenOne
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.TheoremOneTwelve
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.AffineLattice
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Coordinate
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.FaceCombinations
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Faces
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.FiniteHull
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.HollowBound
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.HollowReduction
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Homogenization
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.LeastFaceInterior
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Polytope
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.VertexHull
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.VertexWeights
public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag
public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Basic
public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Centerpoint
public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.ConvexHull
public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.FaceModel
public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Helly
public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.WeakHull
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AffineImages
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedCompleteness
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedCoordinates
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDecomposition
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDiagram
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedRepresentation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.BoundedRun
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredPolytope
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Cleanup
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CommonMeasure
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteBounds
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteLevels
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompletePreparation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteRefinement
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Completeness
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Conclusion
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ConclusionBridge
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Construction
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Existence
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceLevels
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceMassChain
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FacePreservation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceRefinement
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSelection
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSupport
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSurvival
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FinalConstruction
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapCleanup
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapProgress
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Initialization
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IntervalCapacity
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationBounds
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationColorCapacity
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationCompleteCapacity
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationConstants
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationEvents
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationFaceCapacity
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationGapCapacity
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationIntervalBounds
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationLineages
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationTermination
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LargeFaceGeometry
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LargeFaceSequence
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeCoordinates
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeTransition
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LevelInjectivity
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Levels
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LiftedMass
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LineageMassMaps
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LineageOperations
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Lineages
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LocalToCumulative
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LocalizedPruning
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LowerTransfer
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Mass
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalLattice
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalParameters
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalRepresentation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Minimalization
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ModularRank
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NodeMassMap
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NodeMassMapLevels
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedComplete
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedFace
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedGap
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedMassMaps
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedOperations
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.OperationLevels
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.OperationMassMaps
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Parameters
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.PruningData
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.PruningStability
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Pullback
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.QuotientMass
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RealSupportRank
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Rebuild
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartDecomposition
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartFlag
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartMass
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartPreservation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartRepresentation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ReducedRepresentative
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Reduction
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RefinementGrowth
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RefinementProgress
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Restrict
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ScalarExtension
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SlabPruning
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.StoppedLineages
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDecomposition
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDiagram
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDiagramRepresentation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportParameters
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportRechartMass
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportRepresentation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Termination
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Thickness
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ThinDirections
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.TwoLayer
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.UniformCompleteRefinement
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.WeightedIncidence
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Affine
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.AffineApplication
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.AffineRelations
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Basic
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.CharacterLinear
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.CharacterSum
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.DilatedGrowth
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangeCompletion
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangePattern
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangeResources
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FibreSlots
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FiniteProbability
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FourierEnergy
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.GrowthIteration
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.PrescribedCounts
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Relative
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.RelativeConcentration
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.RelativeProof
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ResourceCompletion
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SampleAvailability
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SampleDistribution
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Sampling
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SetGrowth
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SlabArithmetic
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Subweights
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ThickSupport
public import LeanPool.ErdosGinzburgZiv.EGZ.Main.Assembly
public import LeanPool.ErdosGinzburgZiv.EGZ.Main.Centerpoint
public import LeanPool.ErdosGinzburgZiv.EGZ.Main.Coefficients
public import LeanPool.ErdosGinzburgZiv.EGZ.Main.Input
public import LeanPool.ErdosGinzburgZiv.EGZ.Main.Interior
public import LeanPool.ErdosGinzburgZiv.EGZ.Main.Parameters
public import LeanPool.ErdosGinzburgZiv.EGZ.Main.Selection
public import LeanPool.ErdosGinzburgZiv.EGZ.Main.UpperBound
public import LeanPool.ErdosGinzburgZiv.EGZ.MainTheorem
public import LeanPool.ErdosGinzburgZiv.EGZ.Polynomial.HollowBound
public import LeanPool.ErdosGinzburgZiv.EGZ.TheoremOneTwelve
public import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Basic
public import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Constants
public import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.DimensionOne
public import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Multiplicity
public import LeanPool.ErdosGinzburgZiv.ErdosGinzburgZivPrime
public import LeanPool.ErdosGinzburgZiv.Solution
public import LeanPool.ErdosGinzburgZiv.ZakharovTheorem12

/-!
# Convex geometry and the Erdős–Ginzburg–Ziv problem

Source: arxiv:2002.09892, doi:10.19086/da.165216, url:https://github.com/zakharov2k/egz-formal-proof
Authors: Dmitrii Zakharov
Status: verified
Main declarations: `EGZ.theorem_1_2`, `EGZ.main_upper_bound`
Tags: additive-combinatorics, zero-sum, convex-geometry
MSC: 11B30, 11H06
-/

/-
Upstream license notice for this development:

MIT License

Copyright (c) 2026 Dmitrii Zakharov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
