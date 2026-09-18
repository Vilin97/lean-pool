/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Analysis.Calculus.ContDiff.Support
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H2
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Approximation
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Compactness
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.FrechetKolmogorov
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Kernels
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Smoothing
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Transfer
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.TranslationIntegral
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2CompactnessCriterion
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.SupportedH1
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1
public import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2
public import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitz
public import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitzForward
public import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure
public import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure.Finiteness
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartData
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartDataRiemannian
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureLp
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureRiemannian
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasureRiemannianVolume
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.EmbeddingL2
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.H1
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.H2
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.Localization
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.LocalizationH2
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachov
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Chartwise
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Global
public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Transport
public import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.ChangeMeasureLeSmul
public import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.ExtendByZeroRangeEquiv
public import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict
public import LeanPool.RellichKondrachov.MeasureTheory.Measure.HausdorffVolume

/-!
# Rellich–Kondrachov compact embedding theorem

Source: url:https://github.com/abenenson/rellich-kondrachov
Authors: Adam Benenson
Status: verified
Main declarations: `RellichKondrachov.Geometry.Manifold.Sobolev.exists_riemannianFiniteChartData`
Tags: analysis, pde, sobolev-embedding
MSC: 46E35
-/

@[expose] public section

/-!
# Rellich–Kondrachov Compact Embedding Theorem

This is the root import file for the Rellich–Kondrachov compact embedding theorem.
-/
