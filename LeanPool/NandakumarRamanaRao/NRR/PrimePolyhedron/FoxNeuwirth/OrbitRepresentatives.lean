/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CellularCycle

/-!
# Explicit representatives for free finite group orbits

Orbit sums in characteristic `p` cannot be obtained by summing over the covering set and dividing
by the group order.  This module records chosen representatives together with existence and
uniqueness up to the acting group.
-/

@[expose] public section

namespace NRR

open scoped BigOperators

/-- Chosen representatives for a finite group action. -/
structure OrbitRepresentativeData (G X : Type*)
    [Group G] [MulAction G X] [Fintype G] [Fintype X]
    [DecidableEq X] where
  /-- A finite set containing exactly one representative from each symmetry orbit. -/
  representatives : Finset X
  covers : ∀ x : X, ∃ r ∈ representatives, ∃ g : G, g • r = x
  uniqueOrbit : ∀ r₁ ∈ representatives, ∀ r₂ ∈ representatives,
    (∃ g : G, g • r₁ = r₂) → r₁ = r₂

namespace OrbitRepresentativeData

variable {G X R : Type*}
  [Group G] [MulAction G X] [Fintype G] [Fintype X]
  [DecidableEq X] [CommRing R]

/-- Sum a function once per chosen orbit. -/
def orbitSum (D : OrbitRepresentativeData G X) (f : X → R) : R :=
  ∑ x ∈ D.representatives, f x

/-- Orbit sums depend only on the values at representatives. -/
theorem orbitSum_congr
    (D : OrbitRepresentativeData G X) {f g : X → R}
    (h : ∀ x ∈ D.representatives, f x = g x) :
    D.orbitSum f = D.orbitSum g := by
  classical
  exact Finset.sum_congr rfl h

/-- A nonzero orbit sum has a representative with nonzero contribution. -/
theorem exists_ne_zero_of_orbitSum_ne_zero
    (D : OrbitRepresentativeData G X) (f : X → R)
    (h : D.orbitSum f ≠ 0) :
    ∃ x ∈ D.representatives, f x ≠ 0 := by
  classical
  by_contra hzero
  push Not at hzero
  apply h
  rw [orbitSum]
  exact Finset.sum_eq_zero hzero

end OrbitRepresentativeData

namespace FoxNeuwirth

variable {p : Nat}

/-- C3 data needed for the cellular top cells.  The action is already finite; the representative
data and subgroup-index relation provide the quotient bookkeeping. -/
noncomputable instance instFintypePrimeSymmetry (p : Nat) :
    Fintype (PrimeSymmetry p) :=
  Fintype.ofFinite _

/-- Orbit-representative data for the prime action on top-dimensional cells. -/
abbrev CellularTopOrbitRepresentatives (p : Nat) :=
  OrbitRepresentativeData (PrimeSymmetry p) (BarredPermutation.TopCell p)

end FoxNeuwirth
end NRR
