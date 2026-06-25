/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.Basic
import LeanPool.HighDimProb.RandomMatrix.RowsCols
import LeanPool.HighDimProb.RandomMatrix.Action
import LeanPool.HighDimProb.RandomMatrix.Norms
import LeanPool.HighDimProb.RandomMatrix.Assumptions
import LeanPool.HighDimProb.RandomMatrix.SampleCovariance
import LeanPool.HighDimProb.RandomMatrix.QuadraticForm
import LeanPool.HighDimProb.RandomMatrix.Algebra
import LeanPool.HighDimProb.RandomMatrix.UnitSphere
import LeanPool.HighDimProb.RandomMatrix.OperatorNorm
import LeanPool.HighDimProb.RandomMatrix.SelfAdjoint
import LeanPool.HighDimProb.RandomMatrix.MatrixOrder
import LeanPool.HighDimProb.RandomMatrix.Expectation
import LeanPool.HighDimProb.RandomMatrix.Sums
import LeanPool.HighDimProb.RandomMatrix.VarianceProxy
import LeanPool.HighDimProb.RandomMatrix.Spectral
import LeanPool.HighDimProb.RandomMatrix.TraceExp
import LeanPool.HighDimProb.RandomMatrix.HardboneStatements
import LeanPool.HighDimProb.RandomMatrix.CStarBridge
import LeanPool.HighDimProb.RandomMatrix.Laplace
import LeanPool.HighDimProb.RandomMatrix.Statements
import LeanPool.HighDimProb.RandomMatrix.ConcentrationStatements

/-!
# Random matrices

Aggregate module for the experimental random matrix object layer.

Verified Wikipedia reference:
* Random matrix: https://en.wikipedia.org/wiki/Random_matrix
-/
