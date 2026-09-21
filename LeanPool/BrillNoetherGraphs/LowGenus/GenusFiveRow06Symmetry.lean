/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedOrbit
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas

/-! **Independent generated check.** This module provides an additional generated proof of row 06 and is not imported by the main `LowGenus` root.

Generated symmetry data for the AR row-06 fundamental domain.

The stabilizer of the row's fixed divisor inside the slot-level
automorphism group of `row06Core` has order 96.  The chamber below is a
fundamental domain for it, so a cover proved on the chamber closes the
whole orthant through `ClosedOrbit.closedConstruction_of_chamber`.

Every permutation is supplied with an explicit inverse, which keeps
`reindexLength` definitionally transparent; all endpoint laws are
`decide`d. -/

namespace AtanasovRanganathan.GenusFiveRow06Symmetry

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Utilities.Certificate.CoreOrbitReduction
open GenusFiveCoreAtlas ClosedOrbit

def vfun (data : List (Fin 8)) : Fin 8 → Fin 8 := fun i => data.getD i.val 0
def sfun (data : List (Fin 12)) : Fin 12 → Fin 12 := fun i => data.getD i.val 0
def bfun (data : List Bool) : Fin 12 → Bool := fun i => data.getD i.val false

/-- A `CoreSymmetry` literal carrying its own inverses, so that
`reindexLength` reduces without `Equiv.ofBijective`. -/
def mkSym (vmap vinv : Fin 8 → Fin 8) (smap sinv : Fin 12 → Fin 12)
    (rev : Fin 12 → Bool)
    (hv1 : ∀ x, vinv (vmap x) = x) (hv2 : ∀ x, vmap (vinv x) = x)
    (hs1 : ∀ x, sinv (smap x) = x) (hs2 : ∀ x, smap (sinv x) = x)
    (ht : ∀ e, row06Core.tail (smap e) =
      if rev e then vmap (row06Core.head e) else vmap (row06Core.tail e))
    (hh : ∀ e, row06Core.head (smap e) =
      if rev e then vmap (row06Core.tail e) else vmap (row06Core.head e)) :
    CoreSymmetry row06Core where
  vertexPerm := ⟨vmap, vinv, hv1, hv2⟩
  slotPerm := ⟨smap, sinv, hs1, hs2⟩
  reversed := rev
  tail_eq := ht
  head_eq := hh

def blockSym0 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym1 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 7, 6, 5, 4]) (vfun [0, 1, 2, 3, 7, 6, 5, 4])
    (sfun [0, 1, 2, 3, 9, 10, 11, 8, 7, 4, 5, 6]) (sfun [0, 1, 2, 3, 9, 10, 11, 8, 7, 4, 5, 6])
    (bfun [false, false, false, false, false, false, false, true, true, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym2 : CoreSymmetry row06Core :=
  mkSym (vfun [1, 0, 3, 2, 5, 4, 7, 6]) (vfun [1, 0, 3, 2, 5, 4, 7, 6])
    (sfun [0, 1, 3, 2, 7, 5, 6, 4, 9, 8, 10, 11]) (sfun [0, 1, 3, 2, 7, 5, 6, 4, 9, 8, 10, 11])
    (bfun [true, true, true, true, true, true, true, true, false, false, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym3 : CoreSymmetry row06Core :=
  mkSym (vfun [1, 0, 3, 2, 6, 7, 4, 5]) (vfun [1, 0, 3, 2, 6, 7, 4, 5])
    (sfun [0, 1, 3, 2, 8, 10, 11, 9, 4, 7, 5, 6]) (sfun [0, 1, 3, 2, 8, 10, 11, 9, 4, 7, 5, 6])
    (bfun [true, true, true, true, false, true, true, true, false, true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym4 : CoreSymmetry row06Core :=
  mkSym (vfun [4, 5, 2, 3, 0, 1, 6, 7]) (vfun [4, 5, 2, 3, 0, 1, 6, 7])
    (sfun [10, 11, 9, 8, 4, 5, 6, 7, 3, 2, 0, 1]) (sfun [10, 11, 9, 8, 4, 5, 6, 7, 3, 2, 0, 1])
    (bfun [false, false, false, true, false, false, false, false, true, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym5 : CoreSymmetry row06Core :=
  mkSym (vfun [4, 5, 2, 3, 7, 6, 1, 0]) (vfun [7, 6, 2, 3, 0, 1, 5, 4])
    (sfun [10, 11, 9, 8, 2, 0, 1, 3, 7, 4, 5, 6]) (sfun [5, 6, 4, 7, 9, 10, 11, 8, 3, 2, 0, 1])
    (bfun [false, false, false, true, false, false, false, false, true, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym6 : CoreSymmetry row06Core :=
  mkSym (vfun [5, 4, 3, 2, 1, 0, 7, 6]) (vfun [5, 4, 3, 2, 1, 0, 7, 6])
    (sfun [10, 11, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1]) (sfun [10, 11, 8, 9, 7, 5, 6, 4, 2, 3, 0, 1])
    (bfun [true, true, false, true, true, true, true, true, false, true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym7 : CoreSymmetry row06Core :=
  mkSym (vfun [5, 4, 3, 2, 6, 7, 0, 1]) (vfun [6, 7, 3, 2, 1, 0, 4, 5])
    (sfun [10, 11, 8, 9, 3, 0, 1, 2, 4, 7, 5, 6]) (sfun [5, 6, 7, 4, 8, 10, 11, 9, 2, 3, 0, 1])
    (bfun [true, true, false, true, true, true, true, true, false, true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym8 : CoreSymmetry row06Core :=
  mkSym (vfun [6, 7, 3, 2, 1, 0, 4, 5]) (vfun [5, 4, 3, 2, 6, 7, 0, 1])
    (sfun [5, 6, 7, 4, 8, 10, 11, 9, 2, 3, 0, 1]) (sfun [10, 11, 8, 9, 3, 0, 1, 2, 4, 7, 5, 6])
    (bfun [true, true, true, true, false, true, true, true, false, true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym9 : CoreSymmetry row06Core :=
  mkSym (vfun [6, 7, 3, 2, 5, 4, 0, 1]) (vfun [6, 7, 3, 2, 5, 4, 0, 1])
    (sfun [5, 6, 7, 4, 3, 0, 1, 2, 9, 8, 10, 11]) (sfun [5, 6, 7, 4, 3, 0, 1, 2, 9, 8, 10, 11])
    (bfun [true, true, true, true, true, true, true, true, false, false, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym10 : CoreSymmetry row06Core :=
  mkSym (vfun [7, 6, 2, 3, 0, 1, 5, 4]) (vfun [4, 5, 2, 3, 7, 6, 1, 0])
    (sfun [5, 6, 4, 7, 9, 10, 11, 8, 3, 2, 0, 1]) (sfun [10, 11, 9, 8, 2, 0, 1, 3, 7, 4, 5, 6])
    (bfun [false, false, false, false, false, false, false, true, true, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def blockSym11 : CoreSymmetry row06Core :=
  mkSym (vfun [7, 6, 2, 3, 4, 5, 1, 0]) (vfun [7, 6, 2, 3, 4, 5, 1, 0])
    (sfun [5, 6, 4, 7, 2, 0, 1, 3, 8, 9, 10, 11]) (sfun [5, 6, 4, 7, 2, 0, 1, 3, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def pairSym0 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def pairSym1 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10]) (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def pairSym2 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 11]) (sfun [0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def pairSym3 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 11, 10]) (sfun [0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 11, 10])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def pairSym4 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (sfun [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def pairSym5 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10]) (sfun [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def pairSym6 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 3, 4, 6, 5, 7, 8, 9, 10, 11]) (sfun [1, 0, 2, 3, 4, 6, 5, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def pairSym7 : CoreSymmetry row06Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [1, 0, 2, 3, 4, 6, 5, 7, 8, 9, 11, 10]) (sfun [1, 0, 2, 3, 4, 6, 5, 7, 8, 9, 11, 10])
    (bfun [false, false, false, false, false, false, false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The half of the chamber normalized by the transversal. -/
def BlockConds (length : Fin 12 → ℕ) : Prop :=
  length 2 ≤ length 4 ∧ length 4 ≤ length 9 ∧ length 2 ≤ length 3

/-- The half of the chamber normalized by parallel-slot swaps. -/
def PairConds (length : Fin 12 → ℕ) : Prop :=
  length 0 ≤ length 1 ∧ length 5 ≤ length 6 ∧ length 10 ≤ length 11

/-- The fundamental domain itself. -/
def Chamber (length : Fin 12 → ℕ) : Prop :=
  PairConds length ∧ BlockConds length

/-- Some transversal element normalizes the non-parallel comparisons.
The disjunction is exactly `BlockConds` read through each element's
inverse slot map. -/
theorem block_total (length : Fin 12 → ℕ) :
    (length 2 ≤ length 4 ∧ length 4 ≤ length 9 ∧ length 2 ≤ length 3) ∨
    (length 2 ≤ length 9 ∧ length 9 ≤ length 4 ∧ length 2 ≤ length 3) ∨
    (length 3 ≤ length 7 ∧ length 7 ≤ length 8 ∧ length 3 ≤ length 2) ∨
    (length 3 ≤ length 8 ∧ length 8 ≤ length 7 ∧ length 3 ≤ length 2) ∨
    (length 9 ≤ length 4 ∧ length 4 ≤ length 2 ∧ length 9 ≤ length 8) ∨
    (length 4 ≤ length 9 ∧ length 9 ≤ length 2 ∧ length 4 ≤ length 7) ∨
    (length 8 ≤ length 7 ∧ length 7 ≤ length 3 ∧ length 8 ≤ length 9) ∨
    (length 7 ≤ length 8 ∧ length 8 ≤ length 3 ∧ length 7 ≤ length 4) ∨
    (length 8 ≤ length 3 ∧ length 3 ≤ length 7 ∧ length 8 ≤ length 9) ∨
    (length 7 ≤ length 3 ∧ length 3 ≤ length 8 ∧ length 7 ≤ length 4) ∨
    (length 9 ≤ length 2 ∧ length 2 ≤ length 4 ∧ length 9 ≤ length 8) ∨
    (length 4 ≤ length 2 ∧ length 2 ≤ length 9 ∧ length 4 ≤ length 7) := by
  omega

theorem block_normalize (length : Fin 12 → ℕ) :
    ∃ g : CoreSymmetry row06Core, BlockConds (g.reindexLength length) := by
  rcases block_total length with h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨blockSym0, h⟩
  · exact ⟨blockSym1, h⟩
  · exact ⟨blockSym2, h⟩
  · exact ⟨blockSym3, h⟩
  · exact ⟨blockSym4, h⟩
  · exact ⟨blockSym5, h⟩
  · exact ⟨blockSym6, h⟩
  · exact ⟨blockSym7, h⟩
  · exact ⟨blockSym8, h⟩
  · exact ⟨blockSym9, h⟩
  · exact ⟨blockSym10, h⟩
  · exact ⟨blockSym11, h⟩

theorem pair_normalize (length : Fin 12 → ℕ) (hblock : BlockConds length) :
    ∃ g : CoreSymmetry row06Core, Chamber (g.reindexLength length) := by
  obtain ⟨b0, b1, b2⟩ := hblock
  rcases le_total (length 0) (length 1) with p0 | p0 <;>
    rcases le_total (length 5) (length 6) with p1 | p1 <;>
    rcases le_total (length 10) (length 11) with p2 | p2
  · exact ⟨pairSym0, ⟨p0, p1, p2⟩, b0, b1, b2⟩
  · exact ⟨pairSym1, ⟨p0, p1, p2⟩, b0, b1, b2⟩
  · exact ⟨pairSym2, ⟨p0, p1, p2⟩, b0, b1, b2⟩
  · exact ⟨pairSym3, ⟨p0, p1, p2⟩, b0, b1, b2⟩
  · exact ⟨pairSym4, ⟨p0, p1, p2⟩, b0, b1, b2⟩
  · exact ⟨pairSym5, ⟨p0, p1, p2⟩, b0, b1, b2⟩
  · exact ⟨pairSym6, ⟨p0, p1, p2⟩, b0, b1, b2⟩
  · exact ⟨pairSym7, ⟨p0, p1, p2⟩, b0, b1, b2⟩

/-- **Coverage.**  Every length vector is carried into the chamber by
some core symmetry. -/
theorem chamber_covers (length : Fin 12 → ℕ) :
    ∃ g : CoreSymmetry row06Core, Chamber (g.reindexLength length) := by
  obtain ⟨h, hblock⟩ := block_normalize length
  obtain ⟨b, hchamber⟩ := pair_normalize (h.reindexLength length) hblock
  exact ⟨h.trans b, hchamber⟩

end AtanasovRanganathan.GenusFiveRow06Symmetry
