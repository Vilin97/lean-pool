/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CanonicalAverages
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CanonicalSolutions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ColorClassConcentration
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CoarseObservables
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Concentration
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.DescendantAverages
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.DilationLaw
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Expectations
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.IndependenceDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.LocalCoefficient
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Mu
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageFluctuations
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverages
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.BlockExpectations
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.BlockResponseConcentration
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Scalarization
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.WidetildeTheta
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.MomentFactorBounds

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
