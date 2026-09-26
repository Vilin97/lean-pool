/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedOrbit
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas

/-! **Independent generated check.** This module provides an additional generated proof of row 04
and is not imported by the main `LowGenus` root.

Generated symmetry data for the AR row-04 fundamental domain.

The stabilizer of the row's fixed divisor inside the slot-level
automorphism group of `row04Core` has order 64.  The chamber below is a
fundamental domain for it, so a cover proved on the chamber closes the
whole orthant through `ClosedOrbit.closedConstruction_of_chamber`.

Every permutation is supplied with an explicit inverse, which keeps
`reindexLength` definitionally transparent; all endpoint laws are
`decide`d. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04Symmetry

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Utilities.Certificate.CoreOrbitReduction
open GenusFiveCoreAtlas ClosedOrbit

/-- Read an eight-vertex reindexing from a list, with vertex zero as the default for missing
entries. -/
def vfun (data : List (Fin 8)) : Fin 8 → Fin 8 := fun i => data.getD i.val 0
/-- Read a twelve-slot reindexing from a list, with slot zero as the default for missing
entries. -/
def sfun (data : List (Fin 12)) : Fin 12 → Fin 12 := fun i => data.getD i.val 0
/-- Read the orientation-reversal flags of the twelve slots, treating missing flags as false. -/
def bfun (data : List Bool) : Fin 12 → Bool := fun i => data.getD i.val false

/-- A `CoreSymmetry` literal carrying its own inverses, so that
`reindexLength` reduces without `Equiv.ofBijective`. -/
def mkSym (vmap vinv : Fin 8 → Fin 8) (smap sinv : Fin 12 → Fin 12)
    (rev : Fin 12 → Bool)
    (hv1 : ∀ x, vinv (vmap x) = x) (hv2 : ∀ x, vmap (vinv x) = x)
    (hs1 : ∀ x, sinv (smap x) = x) (hs2 : ∀ x, smap (sinv x) = x)
    (ht : ∀ e, row04Core.tail (smap e) =
      if rev e then vmap (row04Core.head e) else vmap (row04Core.tail e))
    (hh : ∀ e, row04Core.head (smap e) =
      if rev e then vmap (row04Core.tail e) else vmap (row04Core.head e)) :
    CoreSymmetry row04Core where
  vertexPerm := ⟨vmap, vinv, hv1, hv2⟩
  slotPerm := ⟨smap, sinv, hs1, hs2⟩
  reversed := rev
  tail_eq := ht
  head_eq := hh

/-- The identity symmetry of the row-04 core, preserving every vertex, slot, and orientation. -/
def blockSym0 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 block symmetry swapping vertex pairs 0 and 2, 1 and 3, 4 and 7, 5 and 6 and slot
pairs 0 and 9, 1 and 10, 2 and 8, 3 and 6, 4 and 7. It reverses every slot orientation. -/
def blockSym1 : CoreSymmetry row04Core :=
  mkSym (vfun [2, 3, 0, 1, 7, 6, 5, 4]) (vfun [2, 3, 0, 1, 7, 6, 5, 4])
    (sfun [9, 10, 8, 6, 7, 5, 3, 4, 2, 0, 1, 11]) (sfun [9, 10, 8, 6, 7, 5, 3, 4, 2, 0, 1, 11])
    (bfun [true, true, true, true, true, true, true, true, true, true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 block symmetry swapping vertex pairs 0 and 5, 1 and 4, 2 and 6, 3 and 7 and slot
pairs 0 and 3, 1 and 4, 5 and 11, 6 and 9, 7 and 10. It reverses every slot orientation. -/
def blockSym2 : CoreSymmetry row04Core :=
  mkSym (vfun [5, 4, 6, 7, 1, 0, 2, 3]) (vfun [5, 4, 6, 7, 1, 0, 2, 3])
    (sfun [3, 4, 2, 0, 1, 11, 9, 10, 8, 6, 7, 5]) (sfun [3, 4, 2, 0, 1, 11, 9, 10, 8, 6, 7, 5])
    (bfun [true, true, true, true, true, true, true, true, true, true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 block symmetry swapping vertex pairs 0 and 6, 1 and 7, 2 and 5, 3 and 4 and slot
pairs 0 and 6, 1 and 7, 2 and 8, 3 and 9, 4 and 10, 5 and 11. It preserves every slot
orientation. -/
def blockSym3 : CoreSymmetry row04Core :=
  mkSym (vfun [6, 7, 5, 4, 3, 2, 0, 1]) (vfun [6, 7, 5, 4, 3, 2, 0, 1])
    (sfun [6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5]) (sfun [6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that fixes every slot while fixing every vertex and preserving all
slot orientations. -/
def pairSym0 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 9 and 10 while fixing every
vertex and preserving all slot orientations. -/
def pairSym1 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 9, 11]) (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 9, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 6 and 7 while fixing every
vertex and preserving all slot orientations. -/
def pairSym2 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 5, 7, 6, 8, 9, 10, 11]) (sfun [0, 1, 2, 3, 4, 5, 7, 6, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 6 and 7, 9 and 10 while fixing
every vertex and preserving all slot orientations. -/
def pairSym3 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 5, 7, 6, 8, 10, 9, 11]) (sfun [0, 1, 2, 3, 4, 5, 7, 6, 8, 10, 9, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 3 and 4 while fixing every
vertex and preserving all slot orientations. -/
def pairSym4 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 11]) (sfun [0, 1, 2, 4, 3, 5, 6, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 3 and 4, 9 and 10 while fixing
every vertex and preserving all slot orientations. -/
def pairSym5 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 4, 3, 5, 6, 7, 8, 10, 9, 11]) (sfun [0, 1, 2, 4, 3, 5, 6, 7, 8, 10, 9, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 3 and 4, 6 and 7 while fixing
every vertex and preserving all slot orientations. -/
def pairSym6 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 4, 3, 5, 7, 6, 8, 9, 10, 11]) (sfun [0, 1, 2, 4, 3, 5, 7, 6, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 3 and 4, 6 and 7, 9 and 10 while
fixing every vertex and preserving all slot orientations. -/
def pairSym7 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11]) (sfun [0, 1, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 0 and 1 while fixing every
vertex and preserving all slot orientations. -/
def pairSym8 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (sfun [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 0 and 1, 9 and 10 while fixing
every vertex and preserving all slot orientations. -/
def pairSym9 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 3, 4, 5, 6, 7, 8, 10, 9, 11]) (sfun [1, 0, 2, 3, 4, 5, 6, 7, 8, 10, 9, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 0 and 1, 6 and 7 while fixing
every vertex and preserving all slot orientations. -/
def pairSym10 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 10, 11]) (sfun [1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 0 and 1, 6 and 7, 9 and 10 while
fixing every vertex and preserving all slot orientations. -/
def pairSym11 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 3, 4, 5, 7, 6, 8, 10, 9, 11]) (sfun [1, 0, 2, 3, 4, 5, 7, 6, 8, 10, 9, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 0 and 1, 3 and 4 while fixing
every vertex and preserving all slot orientations. -/
def pairSym12 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 4, 3, 5, 6, 7, 8, 9, 10, 11]) (sfun [1, 0, 2, 4, 3, 5, 6, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 0 and 1, 3 and 4, 9 and 10 while
fixing every vertex and preserving all slot orientations. -/
def pairSym13 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 4, 3, 5, 6, 7, 8, 10, 9, 11]) (sfun [1, 0, 2, 4, 3, 5, 6, 7, 8, 10, 9, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 0 and 1, 3 and 4, 6 and 7 while
fixing every vertex and preserving all slot orientations. -/
def pairSym14 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 4, 3, 5, 7, 6, 8, 9, 10, 11]) (sfun [1, 0, 2, 4, 3, 5, 7, 6, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row-04 core symmetry that exchanges parallel-slot pairs 0 and 1, 3 and 4, 6 and 7, 9 and
10 while fixing every vertex and preserving all slot orientations. -/
def pairSym15 : CoreSymmetry row04Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11]) (sfun [1, 0, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The half of the chamber normalized by the transversal. -/
def BlockConds (length : Fin 12 → ℕ) : Prop :=
  length 2 ≤ length 8 ∧ length 11 ≤ length 5

/-- The half of the chamber normalized by parallel-slot swaps. -/
def PairConds (length : Fin 12 → ℕ) : Prop :=
  length 0 ≤ length 1 ∧ length 3 ≤ length 4 ∧ length 6 ≤ length 7 ∧ length 9 ≤ length 10

/-- The fundamental domain itself. -/
def Chamber (length : Fin 12 → ℕ) : Prop :=
  PairConds length ∧ BlockConds length

/-- Some transversal element normalizes the non-parallel comparisons.
The disjunction is exactly `BlockConds` read through each element's
inverse slot map. -/
theorem block_total (length : Fin 12 → ℕ) :
    (length 2 ≤ length 8 ∧ length 11 ≤ length 5) ∨
    (length 8 ≤ length 2 ∧ length 11 ≤ length 5) ∨
    (length 2 ≤ length 8 ∧ length 5 ≤ length 11) ∨
    (length 8 ≤ length 2 ∧ length 5 ≤ length 11) := by
  omega

theorem block_normalize (length : Fin 12 → ℕ) :
    ∃ g : CoreSymmetry row04Core, BlockConds (g.reindexLength length) := by
  rcases block_total length with h | h | h | h
  · exact ⟨blockSym0, h⟩
  · exact ⟨blockSym1, h⟩
  · exact ⟨blockSym2, h⟩
  · exact ⟨blockSym3, h⟩

theorem pair_normalize (length : Fin 12 → ℕ) (hblock : BlockConds length) :
    ∃ g : CoreSymmetry row04Core, Chamber (g.reindexLength length) := by
  obtain ⟨b0, b1⟩ := hblock
  rcases le_total (length 0) (length 1) with p0 | p0 <;>
    rcases le_total (length 3) (length 4) with p1 | p1 <;>
    rcases le_total (length 6) (length 7) with p2 | p2 <;>
    rcases le_total (length 9) (length 10) with p3 | p3
  · exact ⟨pairSym0, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym1, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym2, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym3, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym4, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym5, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym6, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym7, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym8, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym9, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym10, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym11, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym12, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym13, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym14, ⟨p0, p1, p2, p3⟩, b0, b1⟩
  · exact ⟨pairSym15, ⟨p0, p1, p2, p3⟩, b0, b1⟩

/-- **Coverage.**  Every length vector is carried into the chamber by
some core symmetry. -/
theorem chamber_covers (length : Fin 12 → ℕ) :
    ∃ g : CoreSymmetry row04Core, Chamber (g.reindexLength length) := by
  obtain ⟨h, hblock⟩ := block_normalize length
  obtain ⟨b, hchamber⟩ := pair_normalize (h.reindexLength length) hblock
  exact ⟨h.trans b, hchamber⟩

end AtanasovRanganathan.GenusFiveRow04Symmetry
