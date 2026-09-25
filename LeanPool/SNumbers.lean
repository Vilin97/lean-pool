/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module


public import LeanPool.SNumbers.AddOns
public import LeanPool.SNumbers.AddOns.Approximable
public import LeanPool.SNumbers.AddOns.Compact
public import LeanPool.SNumbers.BasicResults
public import LeanPool.SNumbers.BasicResults.Auerbach
public import LeanPool.SNumbers.BasicResults.Determinant
public import LeanPool.SNumbers.BasicResults.GarlingGordon
public import LeanPool.SNumbers.BasicResults.John
public import LeanPool.SNumbers.BasicResults.JohnAux
public import LeanPool.SNumbers.BasicResults.KadetsSnobar
public import LeanPool.SNumbers.BasicResults.LittleGrothendieck
public import LeanPool.SNumbers.BasicResults.SVD
public import LeanPool.SNumbers.BasicResults.Spectral
public import LeanPool.SNumbers.BasicResults.Spectral.Complexification
public import LeanPool.SNumbers.BasicResults.Spectral.MonotoneConvergence
public import LeanPool.SNumbers.BasicResults.Spectral.MultiplicationOperator
public import LeanPool.SNumbers.BasicResults.Spectral.Projection
public import LeanPool.SNumbers.BasicResults.Spectral.RealProjection
public import LeanPool.SNumbers.BasicResults.Spectral.Representation
public import LeanPool.SNumbers.PalomarSolutions
public import LeanPool.SNumbers.PalomarSolutions.MaxDifference
public import LeanPool.SNumbers.SNumbers
public import LeanPool.SNumbers.SNumbers.Approximation
public import LeanPool.SNumbers.SNumbers.Basic
public import LeanPool.SNumbers.SNumbers.Bernstein
public import LeanPool.SNumbers.SNumbers.Entropy
public import LeanPool.SNumbers.SNumbers.EntropyBounds
public import LeanPool.SNumbers.SNumbers.Examples
public import LeanPool.SNumbers.SNumbers.Examples.DiagonalMatrices
public import LeanPool.SNumbers.SNumbers.Examples.ExHelpers
public import LeanPool.SNumbers.SNumbers.Examples.Identity
public import LeanPool.SNumbers.SNumbers.Examples.IdentityL1Linfty
public import LeanPool.SNumbers.SNumbers.Gelfand
public import LeanPool.SNumbers.SNumbers.Helpers
public import LeanPool.SNumbers.SNumbers.Hilbert
public import LeanPool.SNumbers.SNumbers.Inequalities
public import LeanPool.SNumbers.SNumbers.Injectivity
public import LeanPool.SNumbers.SNumbers.Kolmogorov
public import LeanPool.SNumbers.SNumbers.KolmogorovLifting
public import LeanPool.SNumbers.SNumbers.MaxDifference
public import LeanPool.SNumbers.SNumbers.PiLpCoordinates
public import LeanPool.SNumbers.SNumbers.SingularValuesFinDim
public import LeanPool.SNumbers.SNumbers.Uniqueness

/-!
# Pietsch s-numbers and the maximal difference theorem

Source: url:https://github.com/mario-ullrich/lean-snumbers
Authors: Mario Ullrich
Status: verified
Main declarations: `SNumbers.approximationNumber_le_e_mul_hilbertNumber`
Tags: functional-analysis, operator-theory, s-numbers
MSC: 47B06, 46B20
-/
