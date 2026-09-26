/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D
public import LeanPool.FullyDynamicMatching.FD1D.Arithmetic
public import LeanPool.FullyDynamicMatching.FD1D.Averaging
public import LeanPool.FullyDynamicMatching.FD1D.Basic
public import LeanPool.FullyDynamicMatching.FD1D.Bellman
public import LeanPool.FullyDynamicMatching.FD1D.Bounds
public import LeanPool.FullyDynamicMatching.FD1D.ConcreteTransport
public import LeanPool.FullyDynamicMatching.FD1D.Drift
public import LeanPool.FullyDynamicMatching.FD1D.Dynamics
public import LeanPool.FullyDynamicMatching.FD1D.Expectations
public import LeanPool.FullyDynamicMatching.FD1D.FinalArithmetic
public import LeanPool.FullyDynamicMatching.FD1D.FiniteConvergence
public import LeanPool.FullyDynamicMatching.FD1D.Hazard
public import LeanPool.FullyDynamicMatching.FD1D.Initialization
public import LeanPool.FullyDynamicMatching.FD1D.InvariantTransport
public import LeanPool.FullyDynamicMatching.FD1D.KernelBridge
public import LeanPool.FullyDynamicMatching.FD1D.Markov
public import LeanPool.FullyDynamicMatching.FD1D.MeasureBridge
public import LeanPool.FullyDynamicMatching.FD1D.Parameters
public import LeanPool.FullyDynamicMatching.FD1D.Policy
public import LeanPool.FullyDynamicMatching.FD1D.PolynomialCertificate
public import LeanPool.FullyDynamicMatching.FD1D.Potential
public import LeanPool.FullyDynamicMatching.FD1D.PotentialBounds
public import LeanPool.FullyDynamicMatching.FD1D.Realization
public import LeanPool.FullyDynamicMatching.FD1D.Refresh
public import LeanPool.FullyDynamicMatching.FD1D.Spatial
public import LeanPool.FullyDynamicMatching.FD1D.Symmetry
public import LeanPool.FullyDynamicMatching.FD1D.TrajectoryBridge
public import LeanPool.FullyDynamicMatching.FD1D.Transport
public import LeanPool.FullyDynamicMatching.FD1D.Tree
public import LeanPool.FullyDynamicMatching.FD1D.UniformArrival
public import LeanPool.FullyDynamicMatching.FD1D.V5
public import LeanPool.FullyDynamicMatching.FD1D.V5.Balanced
public import LeanPool.FullyDynamicMatching.FD1D.V5.CompleteFormalizationAudit
public import LeanPool.FullyDynamicMatching.FD1D.V5.Complexity
public import LeanPool.FullyDynamicMatching.FD1D.V5.ContinuousProcess
public import LeanPool.FullyDynamicMatching.FD1D.V5.ContinuousState
public import LeanPool.FullyDynamicMatching.FD1D.V5.CostBounds
public import LeanPool.FullyDynamicMatching.FD1D.V5.Dynamics
public import LeanPool.FullyDynamicMatching.FD1D.V5.Energy
public import LeanPool.FullyDynamicMatching.FD1D.V5.InitialProcess
public import LeanPool.FullyDynamicMatching.FD1D.V5.JoinedTrajectory
public import LeanPool.FullyDynamicMatching.FD1D.V5.LocalBellman
public import LeanPool.FullyDynamicMatching.FD1D.V5.LocalInvariants
public import LeanPool.FullyDynamicMatching.FD1D.V5.LocalPolicy
public import LeanPool.FullyDynamicMatching.FD1D.V5.Main
public import LeanPool.FullyDynamicMatching.FD1D.V5.PaperStatements
public import LeanPool.FullyDynamicMatching.FD1D.V5.Parameters
public import LeanPool.FullyDynamicMatching.FD1D.V5.Process
public import LeanPool.FullyDynamicMatching.FD1D.V5.QuantileSquared
public import LeanPool.FullyDynamicMatching.FD1D.V5.SquaredCost
public import LeanPool.FullyDynamicMatching.FD1D.V5.StatementModel
public import LeanPool.FullyDynamicMatching.FD1D.V5.Symmetry
public import LeanPool.FullyDynamicMatching.FD1D.V5.TrajectoryBounds
public import LeanPool.FullyDynamicMatching.FD1D.V5.Transport
public import LeanPool.FullyDynamicMatching.FD1D.V5.TreePolicy
public import LeanPool.FullyDynamicMatching.Solution

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
