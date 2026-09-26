/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedOrbit

/-!
# The two leg swaps of the AR row-05 core

Row 05 is two bananas, each attached by one leg to each of the two *opposite*
vertices of a four-cycle:

```
 e0, e1 : 0 == 1            e2 : 2 -> 0     e3 : 1 -> 3
 e4 : 2 -> 5   e5 : 3 -> 5   e9 : 4 -> 3   e7 : 2 -> 4     (the square)
 e6 : 5 -> 7   e8 : 4 -> 6   e10, e11 : 6 == 7
```

Atanasov--Ranganathan's sixth family draws two of the four sign patterns of
`(|e2| - |e3|, |e6| - |e8|)`; the other two are the images of the drawn ones
under the two leg swaps

* `tauL = (0 1)(2 3)`, slots `(e2 e3)(e4 e5)(e7 e9)` -- exchanges the two left
  legs, hence `|e2| <-> |e3|`;
* `tauR = (4 5)(6 7)`, slots `(e6 e8)(e4 e7)(e5 e9)` -- exchanges the two right
  legs, hence `|e6| <-> |e8|`.

So the four chambers form a single orbit under `⟨tauL, tauR⟩` and only one has
to be proved.  Each permutation carries its own explicit inverse -- both are
involutions -- which keeps `CoreSymmetry.reindexLength` definitionally
transparent, the pattern of `GenusFiveRow04Symmetry` and
`GenusFiveRow06Symmetry`.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow05Symmetry

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Utilities.Certificate.CoreOrbitReduction
open GenusFiveCoreAtlas ClosedOrbit

/-- Read an eight-vertex reindexing from a list, using vertex zero for a missing entry. -/
def vfun (data : List (Fin 8)) : Fin 8 → Fin 8 := fun i => data.getD i.val 0
/-- Read a twelve-slot reindexing from a list, using slot zero for a missing entry. -/
def sfun (data : List (Fin 12)) : Fin 12 → Fin 12 := fun i => data.getD i.val 0
/-- Read the orientation-reversal flags of the twelve slots, with false as the default. -/
def bfun (data : List Bool) : Fin 12 → Bool := fun i => data.getD i.val false

/-- A `CoreSymmetry` literal carrying its own inverses, so that
`reindexLength` reduces without `Equiv.ofBijective`. -/
def mkSym (vmap vinv : Fin 8 → Fin 8) (smap sinv : Fin 12 → Fin 12)
    (rev : Fin 12 → Bool)
    (hv1 : ∀ x, vinv (vmap x) = x) (hv2 : ∀ x, vmap (vinv x) = x)
    (hs1 : ∀ x, sinv (smap x) = x) (hs2 : ∀ x, smap (sinv x) = x)
    (ht : ∀ e, row05Core.tail (smap e) =
      if rev e then vmap (row05Core.head e) else vmap (row05Core.tail e))
    (hh : ∀ e, row05Core.head (smap e) =
      if rev e then vmap (row05Core.tail e) else vmap (row05Core.head e)) :
    CoreSymmetry row05Core where
  vertexPerm := ⟨vmap, vinv, hv1, hv2⟩
  slotPerm := ⟨smap, sinv, hs1, hs2⟩
  reversed := rev
  tail_eq := ht
  head_eq := hh

/-- The identity, spelled in the same shape as the two swaps. -/
def idSym : CoreSymmetry row05Core :=
  mkSym (vfun [0, 1, 2, 3, 4, 5, 6, 7]) (vfun [0, 1, 2, 3, 4, 5, 6, 7])
    (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (sfun [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
    (bfun [false, false, false, false, false, false,
      false, false, false, false, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The left leg swap `(0 1)(2 3)`. -/
def tauL : CoreSymmetry row05Core :=
  mkSym (vfun [1, 0, 3, 2, 4, 5, 6, 7]) (vfun [1, 0, 3, 2, 4, 5, 6, 7])
    (sfun [0, 1, 3, 2, 5, 4, 6, 9, 8, 7, 10, 11])
    (sfun [0, 1, 3, 2, 5, 4, 6, 9, 8, 7, 10, 11])
    (bfun [true, true, true, true, false, false,
      false, true, false, true, false, false])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The right leg swap `(4 5)(6 7)`. -/
def tauR : CoreSymmetry row05Core :=
  mkSym (vfun [0, 1, 2, 3, 5, 4, 7, 6]) (vfun [0, 1, 2, 3, 5, 4, 7, 6])
    (sfun [0, 1, 2, 3, 7, 9, 8, 4, 6, 5, 10, 11])
    (sfun [0, 1, 2, 3, 7, 9, 8, 4, 6, 5, 10, 11])
    (bfun [false, false, false, false, false, true,
      false, false, false, true, true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The left leg comparison of AR's figure. -/
def LeftCond (length : Fin 12 → ℕ) : Prop := length 2 ≤ length 3

/-- The right leg comparison of AR's figure. -/
def RightCond (length : Fin 12 → ℕ) : Prop := length 6 ≤ length 8

/-- Chamber A: the scope Atanasov--Ranganathan draw first. -/
def Chamber (length : Fin 12 → ℕ) : Prop := LeftCond length ∧ RightCond length

theorem left_normalize (length : Fin 12 → ℕ) :
    ∃ g : CoreSymmetry row05Core, LeftCond (g.reindexLength length) := by
  rcases le_total (length 2) (length 3) with h | h
  · exact ⟨idSym, h⟩
  · exact ⟨tauL, h⟩

theorem right_normalize (length : Fin 12 → ℕ) (hLeft : LeftCond length) :
    ∃ g : CoreSymmetry row05Core, Chamber (g.reindexLength length) := by
  rcases le_total (length 6) (length 8) with h | h
  · exact ⟨idSym, hLeft, h⟩
  · exact ⟨tauR, hLeft, h⟩

/-- **Coverage.**  Every length vector is carried into chamber A by some core
symmetry: the two leg swaps commute and each normalizes one comparison. -/
theorem chamber_covers (length : Fin 12 → ℕ) :
    ∃ g : CoreSymmetry row05Core, Chamber (g.reindexLength length) := by
  obtain ⟨h, hLeft⟩ := left_normalize length
  obtain ⟨b, hChamber⟩ := right_normalize (h.reindexLength length) hLeft
  exact ⟨h.trans b, hChamber⟩

end AtanasovRanganathan.GenusFiveRow05Symmetry
