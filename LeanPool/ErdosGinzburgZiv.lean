/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ
import LeanPool.ErdosGinzburgZiv.EGZ.Asymptotics
import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.Existence
import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.IntegerApproximation
import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RationalApproximation
import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RationalCoefficients
import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RealCoefficients
import LeanPool.ErdosGinzburgZiv.EGZ.BalancedCombination
import LeanPool.ErdosGinzburgZiv.EGZ.BalancedRounding
import LeanPool.ErdosGinzburgZiv.EGZ.Consistency
import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.ConvexHullClosure
import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.FaceFlagHellyBound
import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.LocalToCumulative
import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.PropositionSevenOne
import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.TheoremOneTwelve
import LeanPool.ErdosGinzburgZiv.EGZ.Convex
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.AffineLattice
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Coordinate
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.FaceCombinations
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Faces
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.FiniteHull
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.HollowBound
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.HollowReduction
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Homogenization
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.LeastFaceInterior
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Polytope
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.VertexHull
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.VertexWeights
import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag
import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Basic
import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Centerpoint
import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.ConvexHull
import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.FaceModel
import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Helly
import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.WeakHull
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AffineImages
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedCompleteness
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedCoordinates
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDecomposition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDiagram
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedRepresentation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.BoundedRun
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredPolytope
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Cleanup
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CommonMeasure
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteBounds
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteLevels
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompletePreparation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteRefinement
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Completeness
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Conclusion
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ConclusionBridge
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Construction
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Existence
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceLevels
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceMassChain
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FacePreservation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceRefinement
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSelection
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSupport
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSurvival
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FinalConstruction
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapCleanup
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapProgress
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Initialization
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IntervalCapacity
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationBounds
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationColorCapacity
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationCompleteCapacity
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationConstants
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationEvents
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationFaceCapacity
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationGapCapacity
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationIntervalBounds
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationLineages
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationTermination
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LargeFaceGeometry
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LargeFaceSequence
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeCoordinates
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LatticeTransition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LevelInjectivity
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Levels
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LiftedMass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LineageMassMaps
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LineageOperations
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Lineages
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LocalToCumulative
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LocalizedPruning
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LowerTransfer
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Mass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalLattice
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalParameters
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalRepresentation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Minimalization
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ModularRank
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NodeMassMap
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NodeMassMapLevels
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedComplete
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedFace
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedGap
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedMassMaps
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedOperations
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.OperationLevels
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.OperationMassMaps
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Parameters
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.PruningData
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.PruningStability
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Pullback
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.QuotientMass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RealSupportRank
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Rebuild
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartDecomposition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartFlag
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartMass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartPreservation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartRepresentation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ReducedRepresentative
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Reduction
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RefinementGrowth
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RefinementProgress
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Restrict
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ScalarExtension
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SlabPruning
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.StoppedLineages
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDecomposition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDiagram
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDiagramRepresentation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportParameters
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportRechartMass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportRepresentation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Termination
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Thickness
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ThinDirections
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.TwoLayer
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.UniformCompleteRefinement
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.WeightedIncidence
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Affine
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.AffineApplication
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.AffineRelations
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Basic
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.CharacterLinear
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.CharacterSum
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.DilatedGrowth
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangeCompletion
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangePattern
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ExchangeResources
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FibreSlots
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FiniteProbability
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FourierEnergy
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.GrowthIteration
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.PrescribedCounts
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Relative
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.RelativeConcentration
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.RelativeProof
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ResourceCompletion
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SampleAvailability
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SampleDistribution
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Sampling
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SetGrowth
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SlabArithmetic
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Subweights
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ThickSupport
import LeanPool.ErdosGinzburgZiv.EGZ.Main.Assembly
import LeanPool.ErdosGinzburgZiv.EGZ.Main.Centerpoint
import LeanPool.ErdosGinzburgZiv.EGZ.Main.Coefficients
import LeanPool.ErdosGinzburgZiv.EGZ.Main.Input
import LeanPool.ErdosGinzburgZiv.EGZ.Main.Interior
import LeanPool.ErdosGinzburgZiv.EGZ.Main.Parameters
import LeanPool.ErdosGinzburgZiv.EGZ.Main.Selection
import LeanPool.ErdosGinzburgZiv.EGZ.Main.UpperBound
import LeanPool.ErdosGinzburgZiv.EGZ.MainTheorem
import LeanPool.ErdosGinzburgZiv.EGZ.Polynomial.HollowBound
import LeanPool.ErdosGinzburgZiv.EGZ.TheoremOneTwelve
import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Basic
import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Constants
import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.DimensionOne
import LeanPool.ErdosGinzburgZiv.EGZ.ZeroSum.Multiplicity
import LeanPool.ErdosGinzburgZiv.ErdosGinzburgZivPrime
import LeanPool.ErdosGinzburgZiv.Solution
import LeanPool.ErdosGinzburgZiv.ZakharovTheorem12

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
