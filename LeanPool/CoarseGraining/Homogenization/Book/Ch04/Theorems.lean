/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CanonicalAverages
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CanonicalSolutions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ColorClassConcentration
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CoarseObservables
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Concentration
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.DescendantAverages
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.DilationLaw
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Expectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.IndependenceDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.LocalCoefficient
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Mu
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageFluctuations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageMoments
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverages
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.BlockExpectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.BlockResponseConcentration
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Scalarization
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.WidetildeTheta
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.MomentFactorBounds

/-!
# Chapter 4 theorem surface

This aggregate imports the curated public theorem endpoints for Chapter 4.

The public policy is direct theorem statements over `RestrictionLawCarrier`,
`RestrictionStructuralLaw`, local observables, and ordinary analytic hypotheses.  Callers
should not need route-specific wrapper structures.  Scalarization witnesses,
primitive route data, and proof-only bound packages remain in `Internal`
namespaces or private declarations.

The exported theorem families cover local coefficient observables, expectations,
independence and color-class concentration, partition-average fluctuations and
moments, scalarized annealed matrices, annealed subadditivity, moment-factor
comparisons, canonical averages, canonical solution measurability, and
scalar-response weak-norm measurability.
-/

@[expose] public section
