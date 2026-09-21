/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D
import LeanPool.FullyDynamicMatching.FD1D.Arithmetic
import LeanPool.FullyDynamicMatching.FD1D.Averaging
import LeanPool.FullyDynamicMatching.FD1D.Basic
import LeanPool.FullyDynamicMatching.FD1D.Bellman
import LeanPool.FullyDynamicMatching.FD1D.Bounds
import LeanPool.FullyDynamicMatching.FD1D.ConcreteTransport
import LeanPool.FullyDynamicMatching.FD1D.Drift
import LeanPool.FullyDynamicMatching.FD1D.Dynamics
import LeanPool.FullyDynamicMatching.FD1D.Expectations
import LeanPool.FullyDynamicMatching.FD1D.FinalArithmetic
import LeanPool.FullyDynamicMatching.FD1D.FiniteConvergence
import LeanPool.FullyDynamicMatching.FD1D.Hazard
import LeanPool.FullyDynamicMatching.FD1D.Initialization
import LeanPool.FullyDynamicMatching.FD1D.InvariantTransport
import LeanPool.FullyDynamicMatching.FD1D.KernelBridge
import LeanPool.FullyDynamicMatching.FD1D.Markov
import LeanPool.FullyDynamicMatching.FD1D.MeasureBridge
import LeanPool.FullyDynamicMatching.FD1D.Parameters
import LeanPool.FullyDynamicMatching.FD1D.Policy
import LeanPool.FullyDynamicMatching.FD1D.PolynomialCertificate
import LeanPool.FullyDynamicMatching.FD1D.Potential
import LeanPool.FullyDynamicMatching.FD1D.PotentialBounds
import LeanPool.FullyDynamicMatching.FD1D.Realization
import LeanPool.FullyDynamicMatching.FD1D.Refresh
import LeanPool.FullyDynamicMatching.FD1D.Spatial
import LeanPool.FullyDynamicMatching.FD1D.Symmetry
import LeanPool.FullyDynamicMatching.FD1D.TrajectoryBridge
import LeanPool.FullyDynamicMatching.FD1D.Transport
import LeanPool.FullyDynamicMatching.FD1D.Tree
import LeanPool.FullyDynamicMatching.FD1D.UniformArrival
import LeanPool.FullyDynamicMatching.FD1D.V5.Balanced
import LeanPool.FullyDynamicMatching.FD1D.V5.CompleteFormalizationAudit
import LeanPool.FullyDynamicMatching.FD1D.V5.Complexity
import LeanPool.FullyDynamicMatching.FD1D.V5.ContinuousProcess
import LeanPool.FullyDynamicMatching.FD1D.V5.ContinuousState
import LeanPool.FullyDynamicMatching.FD1D.V5.CostBounds
import LeanPool.FullyDynamicMatching.FD1D.V5.Dynamics
import LeanPool.FullyDynamicMatching.FD1D.V5.Energy
import LeanPool.FullyDynamicMatching.FD1D.V5.InitialProcess
import LeanPool.FullyDynamicMatching.FD1D.V5.JoinedTrajectory
import LeanPool.FullyDynamicMatching.FD1D.V5.LocalBellman
import LeanPool.FullyDynamicMatching.FD1D.V5.LocalInvariants
import LeanPool.FullyDynamicMatching.FD1D.V5.LocalPolicy
import LeanPool.FullyDynamicMatching.FD1D.V5.Main
import LeanPool.FullyDynamicMatching.FD1D.V5.PaperStatements
import LeanPool.FullyDynamicMatching.FD1D.V5.Parameters
import LeanPool.FullyDynamicMatching.FD1D.V5.Process
import LeanPool.FullyDynamicMatching.FD1D.V5.QuantileSquared
import LeanPool.FullyDynamicMatching.FD1D.V5.SquaredCost
import LeanPool.FullyDynamicMatching.FD1D.V5.StatementModel
import LeanPool.FullyDynamicMatching.FD1D.V5.Symmetry
import LeanPool.FullyDynamicMatching.FD1D.V5.TrajectoryBounds
import LeanPool.FullyDynamicMatching.FD1D.V5.Transport
import LeanPool.FullyDynamicMatching.FD1D.V5.TreePolicy
import LeanPool.FullyDynamicMatching.Solution

/-!
# Optimal fully dynamic matching on the line

Source: url:https://github.com/ykanoria/fd1d-lean
Authors: Yash Kanoria
Status: verified
Main declarations: `FD1D.V5.Palomar.optimalDynamicMatchingUpperBound`
Tags: online-matching, probability, stochastic-optimization
MSC: 60J20, 90B15
-/

/-
Upstream attribution notices:

Optimal Fully Dynamic Matching on the Line in Lean
Copyright 2026 Yash Kanoria

This work is licensed under the Apache License, Version 2.0.
See LICENSE for the full license text.

The repository depends on Lean and Mathlib but does not vendor their source.
The manuscript records substantive OpenAI ChatGPT and Codex assistance in
developing the mathematical policy and proof, checking algebra, and drafting.
Codex also assisted with the Lean formalization and publication audit.

-/
