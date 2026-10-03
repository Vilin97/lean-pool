/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceCanonicalMeasurability
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceCoarseObservables
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassConcentration
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassIndependence
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassMoments
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceDescendantAverages
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceDescendantMoments
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceDilationLaw
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceEllipticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceIndependence
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLaw
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLocalCoefficient
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceMeasurability
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceMu
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceObservable
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageFluctuations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageLowMoments
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageMoments
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceResponseObservables
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceResponsePartitionAverages
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceStationaryExpectations

/-!
# Exact coarse-source Chapter 4 umbrella

This module is the complete, faithful umbrella for the current Chapter 4
`Source*` modules. It deliberately contains no compatibility bridge to the
pointwise-restriction engineering lane.
-/

@[expose] public section
