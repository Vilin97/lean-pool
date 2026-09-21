/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FiniteAffineZeroCount
/-!
# Orbit quotients of finite incidence cycles

This module turns a finite equivariant incidence cycle into a finite incidence cycle on symmetry
orbits.  Top and facet cells are represented by the standard quotient types for the group action.
The quotient incidence from a facet orbit to a top orbit is the sum of the covering incidences over
all members of the top orbit.  This is the correct finite operation for orbit zero counts: one keeps
one coefficient per top orbit, while incidence is transferred by summing over the covering orbit.

The construction does not divide by the group order.  This is essential in characteristic `p`,
where the prime symmetry group has order divisible by `p`.
-/

namespace NRR

open scoped BigOperators

namespace FiniteIncidenceCycle

variable {R G : Type*} [CommRing R] [Group G] [Fintype G]

/-- Equivariance data for a finite incidence cycle. -/
structure EquivariantData
    (C : FiniteIncidenceCycle R)
    [MulAction G C.TopCell] [MulAction G C.Facet] : Prop where
  coefficient_smul : ∀ (g : G) (c : C.TopCell), C.coefficient (g • c) = C.coefficient c
  incidence_smul : ∀ (g : G) (f : C.Facet) (c : C.TopCell),
    C.incidence (g • f) (g • c) = C.incidence f c

variable (C : FiniteIncidenceCycle R)
variable [MulAction G C.TopCell] [MulAction G C.Facet]

/-- Orbit type of top cells. -/
abbrev TopOrbit := MulAction.orbitRel.Quotient G C.TopCell

/-- Orbit type of facets. -/
abbrev FacetOrbit := MulAction.orbitRel.Quotient G C.Facet

noncomputable instance topOrbitFintype : Fintype (TopOrbit (G := G) C) :=
  Fintype.ofFinite _

noncomputable instance facetOrbitFintype : Fintype (FacetOrbit (G := G) C) :=
  Fintype.ofFinite _

noncomputable instance topOrbitDecidableEq : DecidableEq (TopOrbit (G := G) C) :=
  Classical.decEq _

noncomputable instance facetOrbitDecidableEq : DecidableEq (FacetOrbit (G := G) C) :=
  Classical.decEq _

/-- Canonical representative selected by `Quotient.out`. -/
noncomputable def topRepresentative (q : TopOrbit (G := G) C) : C.TopCell :=
  Quotient.out q

/-- Canonical facet representative selected by `Quotient.out`. -/
noncomputable def facetRepresentative (q : FacetOrbit (G := G) C) : C.Facet :=
  Quotient.out q

/-- One coefficient per top-cell orbit. -/
noncomputable def orbitCoefficient (q : TopOrbit (G := G) C) : R :=
  C.coefficient (topRepresentative (G := G) C q)

/-- Incidence from a facet orbit to a top orbit, obtained by summing the covering incidences over
that top orbit. -/
noncomputable def orbitIncidence
    (qf : FacetOrbit (G := G) C) (qt : TopOrbit (G := G) C) : R := by
  classical
  exact ∑ c : qt.orbit, C.incidence (facetRepresentative (G := G) C qf) c

/-- Coefficients are constant on every top orbit. -/
theorem coefficient_eq_representative
    (E : EquivariantData (G := G) C)
    (q : TopOrbit (G := G) C) (c : q.orbit) :
    C.coefficient c = orbitCoefficient (G := G) C q := by
  classical
  unfold orbitCoefficient topRepresentative
  have hc : (c : C.TopCell) ∈ MulAction.orbit G (Quotient.out q) := by
    rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    exact c.property
  rcases MulAction.mem_orbit_iff.mp hc with ⟨g, hg⟩
  rw [← hg, E.coefficient_smul]

/-- The quotient boundary sum is the original boundary sum at the chosen facet representative. -/
theorem orbitBoundary_eq_coveringBoundary
    (E : EquivariantData (G := G) C)
    (qf : FacetOrbit (G := G) C) :
    (∑ qt : TopOrbit (G := G) C,
      orbitIncidence (G := G) C qf qt * orbitCoefficient (G := G) C qt) =
    ∑ c : C.TopCell,
      C.incidence (facetRepresentative (G := G) C qf) c * C.coefficient c := by
  classical
  let e := MulAction.selfEquivSigmaOrbits' G C.TopCell
  calc
    (∑ qt : TopOrbit (G := G) C,
      orbitIncidence (G := G) C qf qt * orbitCoefficient (G := G) C qt) =
        ∑ qt : TopOrbit (G := G) C, ∑ c : qt.orbit,
          C.incidence (facetRepresentative (G := G) C qf) c * C.coefficient c := by
            apply Finset.sum_congr rfl
            intro qt hqt
            unfold orbitIncidence
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun c _ => ?_)
            rw [coefficient_eq_representative (G := G) C E qt c]
    _ = ∑ c : C.TopCell,
          C.incidence (facetRepresentative (G := G) C qf) c * C.coefficient c := by
            rw [← Equiv.sum_comp e.symm (fun c =>
              C.incidence (facetRepresentative (G := G) C qf) c * C.coefficient c)]
            rw [Fintype.sum_sigma (fun x =>
              C.incidence (facetRepresentative (G := G) C qf) (e.symm x) *
                C.coefficient (e.symm x))]
            rfl

/-- Orbit quotient of an equivariant finite incidence cycle. -/
noncomputable def orbitQuotient
    (E : EquivariantData (G := G) C) : FiniteIncidenceCycle R where
  TopCell := TopOrbit (G := G) C
  Facet := FacetOrbit (G := G) C
  incidence := orbitIncidence (G := G) C
  coefficient := orbitCoefficient (G := G) C
  boundary_zero := by
    intro qf
    rw [orbitBoundary_eq_coveringBoundary (G := G) C E qf]
    exact C.boundary_zero (facetRepresentative (G := G) C qf)

@[simp] theorem orbitQuotient_coefficient
    (E : EquivariantData (G := G) C)
    (q : TopOrbit (G := G) C) :
    (orbitQuotient (G := G) C E).coefficient q = orbitCoefficient (G := G) C q :=
  rfl

@[simp] theorem orbitQuotient_incidence
    (E : EquivariantData (G := G) C)
    (qf : FacetOrbit (G := G) C) (qt : TopOrbit (G := G) C) :
    (orbitQuotient (G := G) C E).incidence qf qt = orbitIncidence (G := G) C qf qt :=
  rfl

end FiniteIncidenceCycle

end NRR
