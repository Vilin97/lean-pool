/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

import LeanPool.NashEmbedding.NashEmbeddingTest
import LeanPool.NashEmbedding.NashEmbeddingTest.Encoding
import LeanPool.NashEmbedding.NashEmbeddingTest.MollifierConvergence
import LeanPool.NashEmbedding.NashEmbeddingTest.NashCompact
import LeanPool.NashEmbedding.NashEmbeddingTest.NashTorus
import LeanPool.NashEmbedding.NashEmbeddingTest.RealizableMetrics
import LeanPool.NashEmbedding.NashEmbedding
import LeanPool.NashEmbedding.NashEmbedding.Compact.AmbientMetric
import LeanPool.NashEmbedding.NashEmbedding.Compact.Main
import LeanPool.NashEmbedding.NashEmbedding.Compact.Periodization
import LeanPool.NashEmbedding.NashEmbedding.Compact.WhitneyExtension
import LeanPool.NashEmbedding.NashEmbedding.Examples.FlatTorus
import LeanPool.NashEmbedding.NashEmbedding.Examples.Negative
import LeanPool.NashEmbedding.NashEmbedding.Examples.Sphere
import LeanPool.NashEmbedding.NashEmbedding.Riemannian.Induced
import LeanPool.NashEmbedding.NashEmbedding.Riemannian.Pullback
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.CoeffTransport
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.CompactInclusion
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Convolution
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.ConvolutionAlgebra
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Differentiation
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Distribution
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.FourierSynthesis
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Inequalities
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.IntegrationByParts
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Limits
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Mollifier
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Multiplication
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.MultiplicationBootstrap
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.MultiplicationSharp
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Parseval
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodicity
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodization
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.PositionSpace
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Resolvent
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.RiemannSum
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Summability
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.SynthesisRegularity
import LeanPool.NashEmbedding.NashEmbedding.Torus.Approximation.BumpConstruction
import LeanPool.NashEmbedding.NashEmbedding.Torus.Approximation.RealizeMetric
import LeanPool.NashEmbedding.NashEmbedding.Torus.Approximation.SmoothMetricApprox
import LeanPool.NashEmbedding.NashEmbedding.Torus.Assembly
import LeanPool.NashEmbedding.NashEmbedding.Torus.Basic
import LeanPool.NashEmbedding.NashEmbedding.Torus.FreeEmbedding
import LeanPool.NashEmbedding.NashEmbedding.Torus.Main
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.DualFrame
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.GuntherIdentity
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.GuntherIdentitySeq
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.GuntherIteration
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.GuntherOperator
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.Main
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.SeqVector
import LeanPool.NashEmbedding.NashEmbedding.Torus.RealizableMetrics
import LeanPool.NashEmbedding.Solution

/-!
# Nash's smooth isometric embedding theorem

Source: url:https://github.com/langlerangle/nashembedding
Authors: David Wiygul
Status: verified
Main declarations: `NashEmbeddingTheorem.nash_isometric_embedding`
Tags: differential-geometry, isometric-embedding, sobolev-spaces
MSC: 53C24
-/
