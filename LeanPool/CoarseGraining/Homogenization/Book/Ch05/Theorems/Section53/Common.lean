/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.CutoffProduct
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SolutionIntegrability
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SubadditivityScaling
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.CoeffFamily
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CanonicalSolutions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoliCutoffProduct
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicScalarControls
public import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
public import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices.SymmetricL2
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-! # Common -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53

/-!
# Section 5.3 common imports

Shared base context for the split Section 5.3 files.  The mathematical content
lives in the three manuscript-lemma modules and their proof subdirectories.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

end Section53
end Ch05
end Book
end Homogenization
