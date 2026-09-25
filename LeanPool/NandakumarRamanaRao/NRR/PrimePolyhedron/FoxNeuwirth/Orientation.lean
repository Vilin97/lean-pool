/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.BarredPermutation

/-!
# Orientations for Fox--Neuwirth cells

This file chooses a concrete orientation for every barred-permutation cell.  The choice is the
parity of the inversion number of the displayed permutation.  We avoid quotienting orientations:
the chosen sign is an integer equal to `1` or `-1`, and relabelling is recorded by an explicit
orientation-transport sign.

The transport sign is deliberately part of the API.  A signed incidence matrix is not invariant
under an arbitrary change of chosen cell orientations; it is covariant by the product of the two
transport signs.  This is the correct datum needed by the later cellular mod-`p` argument.
-/

@[expose] public section

namespace NRR

variable {p : Nat}

namespace BarredPermutation

/-- Inversions of the displayed permutation, expressed using the natural order on labels and ranks.
-/
def inversionSet (c : BarredPermutation p) : Finset (Fin p × Fin p) :=
  Finset.univ.filter fun ij =>
    ij.1.1 < ij.2.1 ∧ (c.rank ij.2).1 < (c.rank ij.1).1

/-- Number of inversions of the displayed permutation. -/
def inversionCount (c : BarredPermutation p) : Nat :=
  c.inversionSet.card

/-- Canonical orientation sign of a Fox--Neuwirth cell. -/
def orientationSign (c : BarredPermutation p) : Int :=
  if Even c.inversionCount then 1 else -1

/-- Every chosen orientation is represented by one of the two units `1` and `-1`. -/
theorem orientationSign_eq_one_or_neg_one (c : BarredPermutation p) :
    c.orientationSign = 1 ∨ c.orientationSign = -1 := by
  unfold orientationSign
  split_ifs <;> simp

/-- The chosen orientation sign is a unit. -/
@[simp] theorem orientationSign_sq (c : BarredPermutation p) :
    c.orientationSign * c.orientationSign = 1 := by
  rcases c.orientationSign_eq_one_or_neg_one with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- The chosen orientation never vanishes. -/
@[simp] theorem orientationSign_ne_zero (c : BarredPermutation p) :
    c.orientationSign ≠ 0 := by
  rcases c.orientationSign_eq_one_or_neg_one with h | h
  · simp [h]
  · simp [h]

/-- Sign comparing the chosen orientation before and after relabelling. -/
def orientationTransport
    (sigma : Equiv.Perm (Fin p)) (c : BarredPermutation p) : Int :=
  (c.relabel sigma).orientationSign * c.orientationSign

/-- Orientation transport is itself a sign. -/
@[simp] theorem orientationTransport_sq
    (sigma : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    c.orientationTransport sigma * c.orientationTransport sigma = 1 := by
  unfold orientationTransport
  calc
    ((c.relabel sigma).orientationSign * c.orientationSign) *
          ((c.relabel sigma).orientationSign * c.orientationSign) =
        ((c.relabel sigma).orientationSign * (c.relabel sigma).orientationSign) *
          (c.orientationSign * c.orientationSign) := by ring
    _ = 1 := by simp

/-- Transport followed by the old orientation gives the relabelled orientation. -/
theorem orientationTransport_mul_orientationSign
    (sigma : Equiv.Perm (Fin p)) (c : BarredPermutation p) :
    c.orientationTransport sigma * c.orientationSign =
      (c.relabel sigma).orientationSign := by
  unfold orientationTransport
  calc
    ((c.relabel sigma).orientationSign * c.orientationSign) * c.orientationSign =
        (c.relabel sigma).orientationSign *
          (c.orientationSign * c.orientationSign) := by ring
    _ = (c.relabel sigma).orientationSign := by simp

/-- Relabelling reflects as well as preserves the face relation. -/
theorem isFace_relabel_iff
    (sigma : Equiv.Perm (Fin p)) (a b : BarredPermutation p) :
    (a.relabel sigma).IsFace (b.relabel sigma) ↔ a.IsFace b := by
  constructor
  · intro h
    have h' := isFace_relabel h sigma.symm
    have ha : (a.relabel sigma).relabel sigma.symm = a := by
      calc
        (a.relabel sigma).relabel sigma.symm =
            a.relabel (sigma.symm * sigma) := by
              symm
              exact relabel_mul sigma.symm sigma a
        _ = a := by
          rw [show sigma.symm * sigma = 1 by
            ext i
            exact congrArg Fin.val (sigma.symm_apply_apply i)]
          exact relabel_one a
    have hb : (b.relabel sigma).relabel sigma.symm = b := by
      calc
        (b.relabel sigma).relabel sigma.symm =
            b.relabel (sigma.symm * sigma) := by
              symm
              exact relabel_mul sigma.symm sigma b
        _ = b := by
          rw [show sigma.symm * sigma = 1 by
            ext i
            exact congrArg Fin.val (sigma.symm_apply_apply i)]
          exact relabel_one b
    simpa [ha, hb] using h'
  · intro h
    exact isFace_relabel h sigma

/-- Relabelling reflects as well as preserves the facet relation. -/
theorem isFacet_relabel_iff
    (sigma : Equiv.Perm (Fin p)) (a b : BarredPermutation p) :
    (a.relabel sigma).IsFacet (b.relabel sigma) ↔ a.IsFacet b := by
  constructor
  · intro h
    have h' := isFacet_relabel h sigma.symm
    have ha : (a.relabel sigma).relabel sigma.symm = a := by
      calc
        (a.relabel sigma).relabel sigma.symm =
            a.relabel (sigma.symm * sigma) := by
              symm
              exact relabel_mul sigma.symm sigma a
        _ = a := by
          rw [show sigma.symm * sigma = 1 by
            ext i
            exact congrArg Fin.val (sigma.symm_apply_apply i)]
          exact relabel_one a
    have hb : (b.relabel sigma).relabel sigma.symm = b := by
      calc
        (b.relabel sigma).relabel sigma.symm =
            b.relabel (sigma.symm * sigma) := by
              symm
              exact relabel_mul sigma.symm sigma b
        _ = b := by
          rw [show sigma.symm * sigma = 1 by
            ext i
            exact congrArg Fin.val (sigma.symm_apply_apply i)]
          exact relabel_one b
    simpa [ha, hb] using h'
  · intro h
    exact isFacet_relabel h sigma

end BarredPermutation

end NRR
