/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoarseFluxResponseRHS
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoarseGrainingL2
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors

/-! # Public Internal Bridges -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public/internal bridges for Chapter 3

This file is the stable import surface for the Chapter 3 public/internal
bridge endpoints.  The proof bodies live in focused `PublicInternalBridges/`
submodules so downstream files can keep importing this module without pulling a
monolithic source file into the edit loop.
-/

end Ch03
end Book
end Homogenization
