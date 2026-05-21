/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness
import LeanPool.TwoColoringOneRound.LowerBound.OverlapType

namespace Distributed2Coloring.LowerBound

namespace N1000000StructureConstants

open scoped BigOperators

open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000Witness

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Distributed2Coloring.LowerBound.Mask

/-- Directed overlap-type indices (0..33), in the canonical order used by the witness exporter. -/
abbrev DirIdx := Fin masks.size

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def maskAt (d : DirIdx) : Mask :=
  masks[d.1]!

lemma maskAt_lt_512 (d : DirIdx) : maskAt d < (1 <<< 9) := by
  -- All canonical masks are 9-bit masks.
  fin_cases d <;> decide

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def colMatch (m : Mask) (j : Fin 3) : Option (Fin 3) :=
  if m.testBit (0 * 3 + j.1) then some ⟨0, by decide⟩
  else if m.testBit (1 * 3 + j.1) then some ⟨1, by decide⟩
  else if m.testBit (2 * 3 + j.1) then some ⟨2, by decide⟩
  else none

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def rowMatch (m : Mask) (i : Fin 3) : Option (Fin 3) :=
  if m.testBit (i.1 * 3 + 0) then some ⟨0, by decide⟩
  else if m.testBit (i.1 * 3 + 1) then some ⟨1, by decide⟩
  else if m.testBit (i.1 * 3 + 2) then some ⟨2, by decide⟩
  else none

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def freeCols (m : Mask) : Nat :=
  (Finset.univ.filter fun j : Fin 3 => colMatch m j = none).card

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def freeCoords (a d : Mask) : Nat :=
  (Finset.univ.filter fun j : Fin 3 => colMatch a j = none ∧ rowMatch d j = none).card

/-- Compatibility check for the triple of masks `(k,a,d)` in the representative intersection number
`N[k][a][d]`: `k` is the type of `(base,u)`, `a` is the type of `(base,v)`, and `d` is the type of
`(v,u)`. -/
def consistentAt (k a d : Mask) (j : Fin 3) : Bool :=
  match colMatch a j, rowMatch d j with
  | some i, none =>
      -- `v_j = base_i` but `v_j` does not equal any coordinate of `u`.
      -- This is only possible if `u` does not contain `base_i`.
      decide (rowMatch k i = none)
  | some i, some l =>
      -- `v_j = base_i` and `v_j = u_l`, so `u_l = base_i` and hence the `base_i` row of `k`
      -- must point to `l`.
      decide (rowMatch k i = some l)
  | none, none =>
      true
  | none, some l =>
      -- `v_j = u_l`, so this must be a fresh symbol (not one of the base symbols).
      decide (colMatch k l = none)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def consistent (k a d : Mask) : Bool :=
  consistentAt k a d ⟨0, by decide⟩ &&
    consistentAt k a d ⟨1, by decide⟩ && consistentAt k a d ⟨2, by decide⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def baseTypeCount (k : DirIdx) : Nat :=
  (n - 3).descFactorial (freeCols (maskAt k))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def N (k a d : DirIdx) : Nat :=
  if consistent (maskAt k) (maskAt a) (maskAt d) then
    let used : Nat := 3 + freeCols (maskAt k)
    (n - used).descFactorial (freeCoords (maskAt a) (maskAt d))
  else
    0

end N1000000StructureConstants

end Distributed2Coloring.LowerBound
