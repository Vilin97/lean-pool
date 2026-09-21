/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/

import LeanPool.DensityHalesJewett.DensityHalesJewett
import LeanPool.DensityHalesJewett.DensityHalesJewett.Canonization
import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement
import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement.CorrelatedFibers
import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement.Parameters
import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement.StructuredCorrelation
import LeanPool.DensityHalesJewett.DensityHalesJewett.FiniteUnions
import LeanPool.DensityHalesJewett.DensityHalesJewett.GrahamRothschild
import LeanPool.DensityHalesJewett.DensityHalesJewett.Insensitive
import LeanPool.DensityHalesJewett.DensityHalesJewett.Main
import LeanPool.DensityHalesJewett.DensityHalesJewett.Subspace
import LeanPool.DensityHalesJewett.DensityHalesJewett.Szemeredi
import LeanPool.DensityHalesJewett.DensityHalesJewett.UniformFibers
import LeanPool.DensityHalesJewett.DensityHalesJewett.Varnavides
import LeanPool.DensityHalesJewett.DensityHalesJewett.Word
import LeanPool.DensityHalesJewett.Solution

/-!
# The density Hales–Jewett theorem and Szemerédi's theorem

Source: url:https://github.com/gdahia/densityhalesjewett
Authors: Gabriel Dahia
Status: verified
Main declarations: `Combinatorics.Line.exists_of_density_atTop`
Tags: combinatorics
MSC: 05D10, 05A05, 11B75, 68R15
-/
