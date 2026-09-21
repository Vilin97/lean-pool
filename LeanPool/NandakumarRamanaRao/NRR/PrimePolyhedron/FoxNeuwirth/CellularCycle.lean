/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ModPOrbitCycle
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceZero

/-!
# Direct Fox--Neuwirth cellular obstruction cycle

This module is the replacement for the maximal-flag determinant-cycle route.  It works directly
with the cellular generators: oriented top cells and proper codimension-one split orbits.  The
boundary coefficient of a split of sizes `k` and `p-k` is a common orientation sign times
`p.choose k`; it therefore vanishes in `ZMod p` when `p` is prime.

No barycentric maximal-flag classification is used here.
-/

namespace NRR

variable {p : Nat}

namespace FoxNeuwirth

/-- Direct finite cellular top-cycle data.  The facet type is the orbit type of a proper split;
`boundary_zero` is the actual prime-binomial cancellation theorem. -/
structure CellularTopCycle (hp : Nat.Prime p) where
  /-- The coefficient of each oriented top-dimensional cell. -/
  coefficient : BarredPermutation.TopCell p → ZMod p
  /-- The boundary coefficient associated with a barred permutation and a proper split. -/
  boundaryCoefficient : BarredPermutation p → ProperSplit p → ZMod p
  coefficient_eq : ∀ c, coefficient c = orientedTopCoefficient (c : BarredPermutation p)
  boundaryCoefficient_eq :
    ∀ a s, boundaryCoefficient a s = orientedOrbitBoundaryCoefficient a s
  boundary_zero : ∀ a s, boundaryCoefficient a s = 0

/-- The top-cell index type of a cellular cycle. -/
abbrev CellularTopCycle.TopCell {hp : Nat.Prime p} (_ : CellularTopCycle hp) : Type :=
  BarredPermutation.TopCell p

/-- The facet-orbit index type of a cellular cycle. -/
abbrev CellularTopCycle.FacetOrbit {hp : Nat.Prime p} (_ : CellularTopCycle hp) : Type :=
  ProperSplit p

/-- Canonical direct cellular cycle modulo a prime. -/
noncomputable def cellularTopCycle (hp : Nat.Prime p) : CellularTopCycle hp where
  coefficient := fun c => orientedTopCoefficient (c : BarredPermutation p)
  boundaryCoefficient := orientedOrbitBoundaryCoefficient
  coefficient_eq := by intro c; rfl
  boundaryCoefficient_eq := by intro a s; rfl
  boundary_zero := orientedOrbitBoundaryCoefficient_eq_zero hp

@[simp] theorem cellularTopCycle_coefficient
    (hp : Nat.Prime p) (c : BarredPermutation.TopCell p) :
    (cellularTopCycle hp).coefficient c =
      orientedTopCoefficient (c : BarredPermutation p) :=
  rfl

@[simp] theorem cellularTopCycle_boundary
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (s : ProperSplit p) :
    (cellularTopCycle hp).boundaryCoefficient a s = 0 :=
  (cellularTopCycle hp).boundary_zero a s

/-- The direct cellular obstruction consists of the cellular cycle and its nonzero reference
prime-symmetry orbit count. -/
structure CellularObstruction (hp : Nat.Prime p) where
  /-- The cellular top cycle underlying the obstruction. -/
  cycle : CellularTopCycle hp
  /-- The nonzero reference orbit count in the prime residue field. -/
  referenceCount : ZMod p
  referenceCount_eq : referenceCount = referenceSignedOrbitCount hp
  referenceCount_ne_zero : referenceCount ≠ 0

/-- Canonical direct Fox--Neuwirth cellular obstruction. -/
noncomputable def cellularObstruction (hp : Nat.Prime p) : CellularObstruction hp where
  cycle := cellularTopCycle hp
  referenceCount := referenceSignedOrbitCount hp
  referenceCount_eq := rfl
  referenceCount_ne_zero := referenceSignedOrbitCount_ne_zero hp

@[simp] theorem cellularObstruction_boundary
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (s : (cellularObstruction hp).cycle.FacetOrbit) :
    (cellularObstruction hp).cycle.boundaryCoefficient a s = 0 :=
  (cellularObstruction hp).cycle.boundary_zero a s

 theorem cellularObstruction_reference_ne_zero
    (hp : Nat.Prime p) :
    (cellularObstruction hp).referenceCount ≠ 0 :=
  (cellularObstruction hp).referenceCount_ne_zero

end FoxNeuwirth
end NRR
