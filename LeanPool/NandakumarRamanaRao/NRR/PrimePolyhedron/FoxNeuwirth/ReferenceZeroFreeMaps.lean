/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantCoordinateHomotopy
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedReferenceApproximation

/-!
# Zero-free coordinate lifts of the two Fox--Neuwirth reference maps

This module contains the reference endpoint maps independently of any raw or stable obstruction
count.  Keeping these definitions in a neutral module separates the stable obstruction API from the
raw-count homotopy interface.
-/

namespace NRR

open Geometry
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPLPositiveRay

variable {p : Nat}

open EquivariantCoordinateHomotopy
open RefinedAffineMap

/-- Continuous coordinate map associated with an original affine vertex map. -/
noncomputable def affineZeroFreeMap
    (hp : Nat.Prime p) (F : CoordinateAffineVertexMap p)
    (heq : ∀ (g : PrimeSymmetry p) (x : Realization p),
      F.globalValue (g • x) = g • F.globalValue x)
    (hzero : ∀ x, F.globalValue x ≠ 0) : ZeroFreeMap hp where
  map := ofCoordinateAffineVertexMap F
  equivariant := heq
  zeroFree := hzero

/-- The globally positive equivariant S5 reference lift is zero-free. -/
noncomputable def positiveReferenceZeroFreeMap
    (hp : Nat.Prime p) : ZeroFreeMap hp :=
  affineZeroFreeMap hp (AAK.positiveEquivariantReferenceCoordinateMap hp)
    (AAK.positiveEquivariantReferenceCoordinateMap_global_smul hp) (by
      intro x hx
      have hpos := AAK.positiveEquivariantReferenceCoordinateMap_global_pos hp x
      have hi := congrFun hx ⟨0, hp.pos⟩
      exact (ne_of_gt (hpos ⟨0, hp.pos⟩)) (by simpa using hi))

/-- The globally negative equivariant S5 reference lift is zero-free. -/
noncomputable def negativeReferenceZeroFreeMap
    (hp : Nat.Prime p) : ZeroFreeMap hp :=
  affineZeroFreeMap hp (AAK.negativeEquivariantReferenceCoordinateMap hp)
    (AAK.negativeEquivariantReferenceCoordinateMap_global_smul hp) (by
      intro x hx
      have hneg := AAK.negativeEquivariantReferenceCoordinateMap_global_neg hp x
      have hi := congrFun hx ⟨0, hp.pos⟩
      exact (ne_of_lt (hneg ⟨0, hp.pos⟩)) (by simpa using hi))

end EquivariantPLPositiveRay
end FoxNeuwirthOrderComplex
end NRR
