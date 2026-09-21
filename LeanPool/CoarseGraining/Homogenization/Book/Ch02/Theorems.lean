/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Existence
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SolutionIntegrability
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.FirstVariation
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.GradientUniqueness
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.GradientLinearity
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Quadraticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixExtraction
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixPositivity
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SubadditivityScaling
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BlockMatrixField
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledMu
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledResponse
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DeterministicIdentities
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MagicIdentities
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimates
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.WrapAround
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Dilation

/-!
Public Chapter 2 theorem surface.

The `*Definitions.lean` files in this directory contain proposition-valued
theorem packages and their small accessor APIs.  The companion theorem files
import the internal proof bridges and prove those packages for the public

/-! # Theorems -/
`Domain`/`CoeffOn` interface.
-/
