/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/

import LeanPool.SNumbers.AddOns.Approximable
import LeanPool.SNumbers.AddOns.Compact
import LeanPool.SNumbers.AddOns
import LeanPool.SNumbers.BasicResults.Auerbach
import LeanPool.SNumbers.BasicResults.Determinant
import LeanPool.SNumbers.BasicResults.GarlingGordon
import LeanPool.SNumbers.BasicResults.John
import LeanPool.SNumbers.BasicResults.JohnAux
import LeanPool.SNumbers.BasicResults.KadetsSnobar
import LeanPool.SNumbers.BasicResults.LittleGrothendieck
import LeanPool.SNumbers.BasicResults.SVD
import LeanPool.SNumbers.BasicResults.Spectral.Complexification
import LeanPool.SNumbers.BasicResults.Spectral.MonotoneConvergence
import LeanPool.SNumbers.BasicResults.Spectral.MultiplicationOperator
import LeanPool.SNumbers.BasicResults.Spectral.Projection
import LeanPool.SNumbers.BasicResults.Spectral.RealProjection
import LeanPool.SNumbers.BasicResults.Spectral.Representation
import LeanPool.SNumbers.BasicResults.Spectral
import LeanPool.SNumbers.BasicResults
import LeanPool.SNumbers.PalomarSolutions.MaxDifference
import LeanPool.SNumbers.PalomarSolutions
import LeanPool.SNumbers.SNumbers.Approximation
import LeanPool.SNumbers.SNumbers.Basic
import LeanPool.SNumbers.SNumbers.Bernstein
import LeanPool.SNumbers.SNumbers.Entropy
import LeanPool.SNumbers.SNumbers.EntropyBounds
import LeanPool.SNumbers.SNumbers.Examples.DiagonalMatrices
import LeanPool.SNumbers.SNumbers.Examples.ExHelpers
import LeanPool.SNumbers.SNumbers.Examples.Identity
import LeanPool.SNumbers.SNumbers.Examples.IdentityL1Linfty
import LeanPool.SNumbers.SNumbers.Examples
import LeanPool.SNumbers.SNumbers.Gelfand
import LeanPool.SNumbers.SNumbers.Helpers
import LeanPool.SNumbers.SNumbers.Hilbert
import LeanPool.SNumbers.SNumbers.Inequalities
import LeanPool.SNumbers.SNumbers.Injectivity
import LeanPool.SNumbers.SNumbers.Kolmogorov
import LeanPool.SNumbers.SNumbers.KolmogorovLifting
import LeanPool.SNumbers.SNumbers.MaxDifference
import LeanPool.SNumbers.SNumbers.PiLpCoordinates
import LeanPool.SNumbers.SNumbers.SingularValuesFinDim
import LeanPool.SNumbers.SNumbers.Uniqueness
import LeanPool.SNumbers.SNumbers

/-!
# Pietsch s-numbers and the maximal difference theorem

Source: url:https://github.com/mario-ullrich/lean-snumbers
Authors: Mario Ullrich
Status: verified
Main declarations: `SNumbers.approximationNumber_le_e_mul_hilbertNumber`, `SNumbers.allSNumbers_eq_on_HilbertSpace`, `John.john_decomposition`
Tags: functional-analysis, operator-theory, s-numbers
MSC: 47B06, 46B20
-/
