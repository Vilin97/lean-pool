/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.Orientation

/-!
# Oriented Fox--Neuwirth facet incidences

The cells are all barred permutations.  A codimension-one incidence is supported exactly on the
facet relation.  Its sign is the product of the chosen orientations of the two incident cells.
This gives a concrete finite signed incidence matrix.  Under relabelling it transforms by the two
orientation-transport signs, while its unsigned support is strictly invariant.

This module records the oriented cell model and its boundary relation. The cycle and boundary-
cancellation results are proved in the chain modules.
-/

namespace NRR

variable {p : Nat}

namespace FoxNeuwirth

noncomputable section

/-- Finite set of all faces of a cell. -/
def faces (b : BarredPermutation p) : Finset (BarredPermutation p) :=
  Finset.univ.filter fun a => a.IsFace b

/-- Finite set of all codimension-one faces of a cell. -/
def facets (b : BarredPermutation p) : Finset (BarredPermutation p) :=
  Finset.univ.filter fun a => a.IsFacet b

@[simp] theorem mem_faces_iff (a b : BarredPermutation p) :
    a ∈ faces b ↔ a.IsFace b := by
  simp [faces]

@[simp] theorem mem_facets_iff (a b : BarredPermutation p) :
    a ∈ facets b ↔ a.IsFacet b := by
  simp [facets]

/-- Unsigned incidence indicator for a codimension-one face. -/
def unsignedIncidence (a b : BarredPermutation p) : Int :=
  if a.IsFacet b then 1 else 0

/-- Signed incidence associated with the canonical orientation choices. -/
def signedIncidence (a b : BarredPermutation p) : Int :=
  if a.IsFacet b then a.orientationSign * b.orientationSign else 0

@[simp] theorem unsignedIncidence_of_facet
    {a b : BarredPermutation p} (h : a.IsFacet b) :
    unsignedIncidence a b = 1 := by
  simp [unsignedIncidence, h]

@[simp] theorem unsignedIncidence_of_not_facet
    {a b : BarredPermutation p} (h : ¬ a.IsFacet b) :
    unsignedIncidence a b = 0 := by
  simp [unsignedIncidence, h]

@[simp] theorem signedIncidence_of_facet
    {a b : BarredPermutation p} (h : a.IsFacet b) :
    signedIncidence a b = a.orientationSign * b.orientationSign := by
  simp [signedIncidence, h]

@[simp] theorem signedIncidence_of_not_facet
    {a b : BarredPermutation p} (h : ¬ a.IsFacet b) :
    signedIncidence a b = 0 := by
  simp [signedIncidence, h]

/-- The signed incidence is nonzero exactly for facets. -/
theorem signedIncidence_ne_zero_iff
    (a b : BarredPermutation p) :
    signedIncidence a b ≠ 0 ↔ a.IsFacet b := by
  by_cases h : a.IsFacet b
  · simp [signedIncidence, h]
  · simp [signedIncidence, h]

/-- Incidence can only occur in adjacent dimensions. -/
theorem signedIncidence_vanishes_unless_adjacent
    (a b : BarredPermutation p)
    (h : a.dualDimension + 1 ≠ b.dualDimension) :
    signedIncidence a b = 0 := by
  apply signedIncidence_of_not_facet
  intro hab
  exact h hab.2

/-- The unsigned incidence relation is invariant under relabelling. -/
theorem unsignedIncidence_relabel
    (sigma : Equiv.Perm (Fin p)) (a b : BarredPermutation p) :
    unsignedIncidence (a.relabel sigma) (b.relabel sigma) =
      unsignedIncidence a b := by
  simp [unsignedIncidence, BarredPermutation.isFacet_relabel_iff]

/-- Signed incidences are covariant under a change of cell orientations. -/
theorem signedIncidence_relabel
    (sigma : Equiv.Perm (Fin p)) (a b : BarredPermutation p) :
    signedIncidence (a.relabel sigma) (b.relabel sigma) =
      a.orientationTransport sigma * b.orientationTransport sigma *
        signedIncidence a b := by
  by_cases h : a.IsFacet b
  · have hr : (a.relabel sigma).IsFacet (b.relabel sigma) :=
      (BarredPermutation.isFacet_relabel_iff sigma a b).2 h
    simp only [signedIncidence_of_facet h, signedIncidence_of_facet hr]
    calc
      (a.relabel sigma).orientationSign * (b.relabel sigma).orientationSign =
          (a.relabel sigma).orientationSign * (b.relabel sigma).orientationSign *
            ((a.orientationSign * a.orientationSign) *
              (b.orientationSign * b.orientationSign)) := by simp
      _ =
          (a.orientationTransport sigma * b.orientationTransport sigma) *
            (a.orientationSign * b.orientationSign) := by
              unfold BarredPermutation.orientationTransport
              ring
  · have hr : ¬ (a.relabel sigma).IsFacet (b.relabel sigma) := by
      simpa [BarredPermutation.isFacet_relabel_iff] using h
    simp [signedIncidence, h, hr]

/-- Finite support of the signed boundary of a cell. -/
def boundarySupport (b : BarredPermutation p) : Finset (BarredPermutation p) :=
  Finset.univ.filter fun a => signedIncidence a b ≠ 0

/-- Boundary support agrees exactly with the combinatorial facet set. -/
theorem boundarySupport_eq_facets (b : BarredPermutation p) :
    boundarySupport b = facets b := by
  ext a
  simp [boundarySupport, facets, signedIncidence_ne_zero_iff]

/-- Formal cellular boundary of one oriented cell. -/
def cellularBoundary (b : BarredPermutation p) : BarredPermutation p → Int :=
  fun a => signedIncidence a b

@[simp] theorem cellularBoundary_apply
    (a b : BarredPermutation p) :
    cellularBoundary b a = signedIncidence a b :=
  rfl

/-- The support of a formal cellular boundary is exactly the set of facets. -/
theorem cellularBoundary_ne_zero_iff
    (a b : BarredPermutation p) :
    cellularBoundary b a ≠ 0 ↔ a.IsFacet b :=
  signedIncidence_ne_zero_iff a b

/-- Prime-symmetry form of signed incidence covariance. -/
theorem signedIncidence_prime_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry hp)
    (a b : BarredPermutation p) :
    signedIncidence (g • a) (g • b) =
      a.orientationTransport (PrimeSymmetry.toPerm hp g) *
        b.orientationTransport (PrimeSymmetry.toPerm hp g) *
          signedIncidence a b := by
  exact signedIncidence_relabel (PrimeSymmetry.toPerm hp g) a b

end

end FoxNeuwirth

end NRR
