/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Existence
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SolutionIntegrability
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.FirstVariation
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.GradientUniqueness
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.GradientLinearity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Quadraticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixExtraction
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SubadditivityScaling
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BlockMatrixField
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledMu
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledResponse
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DeterministicIdentities
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MagicIdentities
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimates
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.WrapAround
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Dilation

/-!
Public Chapter 2 theorem surface.

The `*Definitions.lean` files in this directory contain proposition-valued
theorem packages and their small accessor APIs.  The companion theorem files
import the internal proof bridges and prove those packages for the public

/-! # Theorems -/
`Domain`/`CoeffOn` interface.
-/

@[expose] public section
