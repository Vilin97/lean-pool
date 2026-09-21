/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceCanonicalMeasurability
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceCoarseObservables
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassConcentration
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassIndependence
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceColorClassMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceDescendantAverages
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceDescendantMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceDilationLaw
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceEllipticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceIndependence
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLaw
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLocalCoefficient
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceMeasurability
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceMu
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceObservable
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageFluctuations
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageLowMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceResponseObservables
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceResponsePartitionAverages
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceStationaryExpectations

/-!
# Exact coarse-source Chapter 4 umbrella

This module is the complete, faithful umbrella for the current Chapter 4
`Source*` modules. It deliberately contains no compatibility bridge to the
pointwise-restriction engineering lane.
-/
