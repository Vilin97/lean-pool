/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FacetShuffleEquiv
/-!
# The top two terms of the Fox--Neuwirth cellular incidence complex

The obstruction argument only uses the incidence map from top cells to codimension-one cells.
It does not require a cellular differential in every lower degree.  This distinction matters:
`FoxNeuwirth.signedIncidence` is the orientation convention used for the top-cell cycle, but the
same formula in all adjacent dimensions is not the full Fox--Neuwirth cellular differential.

This file packages the exact two-term complex needed downstream.  The lower differential is the
zero map, so the chain-complex identity is literal rather than an unproved assertion about lower
Fox--Neuwirth incidences.  The nontrivial statement is that the oriented top chain lies in the
kernel of the genuine top-to-facet incidence map; this is supplied by the facet--shuffle theorem.
-/

namespace NRR

open scoped BigOperators

variable {p : Nat}
variable {R : Type*} [CommRing R]

namespace FoxNeuwirth

/-- Coefficient vectors on top-dimensional Fox--Neuwirth cells. -/
abbrev TopCellChain (p : Nat) (R : Type*) :=
  BarredPermutation.TopCell p → R

/-- Coefficient vectors on all barred permutations.  The incidence map is automatically supported
in codimension one. -/
abbrev FacetChain (p : Nat) (R : Type*) :=
  BarredPermutation p → R

/-- The genuine top-to-facet incidence map. -/
noncomputable def topIncidenceBoundary
    (chain : TopCellChain p R) : FacetChain p R :=
  fun a => ∑ c : BarredPermutation.TopCell p,
    (signedIncidence a (c : BarredPermutation p) : R) * chain c

/-- The next differential in the minimal two-term obstruction complex. -/
def zeroFacetBoundary
    (_chain : FacetChain p R) : PUnit.{0} → R :=
  fun _ => 0

@[simp] theorem zeroFacetBoundary_apply
    (chain : FacetChain p R) (u : PUnit) :
    zeroFacetBoundary chain u = 0 :=
  rfl

/-- The minimal top-cell/facet incidence object is a chain complex in the only sense required by
finite Stokes: the composite with the following zero differential vanishes. -/
theorem zeroFacetBoundary_comp_topIncidenceBoundary
    (chain : TopCellChain p R) :
    zeroFacetBoundary (topIncidenceBoundary chain) = (fun _ => (0 : R)) := by
  funext u
  rfl

/-- The oriented sum of all top cells. -/
noncomputable def orientedTopChain
    (p : Nat) : TopCellChain p (ZMod p) :=
  fun c => orientedTopCoefficient (c : BarredPermutation p)

/-- Applying the top incidence map to the oriented top chain is exactly the previously defined
actual boundary coefficient. -/
@[simp] theorem topIncidenceBoundary_orientedTopChain_apply
    (hp : Nat.Prime p) (a : BarredPermutation p) :
    topIncidenceBoundary (orientedTopChain p) a =
      actualTopBoundaryCoefficient a :=
  rfl

/-- The oriented top chain is an unconditional cycle modulo every prime. -/
theorem topIncidenceBoundary_orientedTopChain_eq_zero
    (hp : Nat.Prime p) :
    topIncidenceBoundary (orientedTopChain p) = 0 := by
  funext a
  exact actualTopBoundaryCoefficient_eq_zero_prime hp a

/-- The two-term top incidence complex together with its distinguished prime cycle.  This is data,
not an assumption: both the composite-zero identity and the top-cycle equation are theorems above. -/
structure PrimeTopIncidenceData (hp : Nat.Prime p) where
  /-- The top chain and its identification with the canonical oriented chain. -/
  topChainData : {chain : TopCellChain p (ZMod p) // chain = orientedTopChain p}
  boundary_zero : topIncidenceBoundary topChainData.1 = 0
  boundary_squared : zeroFacetBoundary (topIncidenceBoundary topChainData.1) =
    (fun _ => (0 : ZMod p))

namespace PrimeTopIncidenceData

variable {hp : Nat.Prime p}

/-- The oriented top chain of the prime incidence certificate. -/
def topChain (D : PrimeTopIncidenceData hp) : TopCellChain p (ZMod p) :=
  D.topChainData.1

theorem topChain_eq (D : PrimeTopIncidenceData hp) : D.topChain = orientedTopChain p :=
  D.topChainData.2

end PrimeTopIncidenceData

/-- Canonical top incidence data produced by the facet--shuffle calculation. -/
noncomputable def primeTopIncidenceData
    (hp : Nat.Prime p) : PrimeTopIncidenceData hp where
  topChainData := ⟨orientedTopChain p, rfl⟩
  boundary_zero := topIncidenceBoundary_orientedTopChain_eq_zero hp
  boundary_squared := zeroFacetBoundary_comp_topIncidenceBoundary _

@[simp] theorem primeTopIncidenceData_boundary
    (hp : Nat.Prime p) :
    topIncidenceBoundary (primeTopIncidenceData hp).topChain = 0 :=
  (primeTopIncidenceData hp).boundary_zero

/-- The finite-incidence-cycle interface used by the affine Stokes layer is exactly the nonzero
part of the two-term top incidence complex. -/
noncomputable def primeTopIncidenceFiniteCycle
    (hp : Nat.Prime p) : FiniteIncidenceCycle (ZMod p) :=
  primeActualFiniteIncidenceCycle hp

end FoxNeuwirth

end NRR
