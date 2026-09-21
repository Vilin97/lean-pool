/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedAffineMap

/-!
# Prime-equivariant coordinate maps
-/

namespace NRR
namespace FoxNeuwirthOrderComplex

variable {p : Nat}

/-- Prime-equivariance of a continuous full-coordinate map. -/
def IsEquivariantCoordinateMap
    (hp : Nat.Prime p)
    (F : RefinedAffineMap.ContinuousCoordinateMap p) : Prop :=
  ∀ (g : PrimeSymmetry p) (x : Realization p), F (g • x) = g • F x

end FoxNeuwirthOrderComplex
end NRR
