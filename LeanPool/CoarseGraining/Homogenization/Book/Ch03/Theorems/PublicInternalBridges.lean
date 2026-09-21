/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoarseFluxResponseRHS
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoarseGrainingL2
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors

/-! # Public Internal Bridges -/

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
