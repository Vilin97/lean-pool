/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Analysis.Calculus.ContDiff.Support
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H2
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Approximation
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Compactness
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.FrechetKolmogorov
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Kernels
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Smoothing
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Transfer
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.TranslationIntegral
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2CompactnessCriterion
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.SupportedH1
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2
import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitz
import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitzForward
import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure
import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure.Finiteness
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartData
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartDataRiemannian
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureLp
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureRiemannian
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureRiemannianVolume
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.EmbeddingL2
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.H1
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.H2
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.Localization
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.LocalizationH2
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachov
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Chartwise
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Global
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Transport
import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.ChangeMeasureLeSmul
import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.ExtendByZeroRangeEquiv
import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict
import LeanPool.RellichKondrachov.MeasureTheory.Measure.HausdorffVolume

/-!
# Rellich–Kondrachov compact embedding theorem

Source: url:https://github.com/abenenson/rellich-kondrachov
Authors: Adam Benenson
Status: verified
Main declarations: `RellichKondrachov.Geometry.Manifold.Sobolev.exists_riemannianFiniteChartData`
Tags: analysis, pde, sobolev-embedding
MSC: 46E35
-/

/-!
# Rellich–Kondrachov Compact Embedding Theorem

This is the root import file for the Rellich–Kondrachov compact embedding theorem.
-/
