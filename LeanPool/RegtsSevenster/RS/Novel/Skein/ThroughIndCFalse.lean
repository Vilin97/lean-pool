/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.LoopVerify

/-!
# The corrected independence interface is refutable across pairings

`ThroughIndependenceC` quantifies over *all* pairs of transition
systems, including pairs with different boundary pairings.  On the
worked one-vertex instance the two matchings `cKappa` (chords
`(0,1), (2,3)`) and its repair (chords `(0,3), (1,2)`) both carry
path-canonical orientations (`cO`, `lvO₂flip`), both with trivial
chord sign, yet the constrained summands differ: `−1` versus `0`.
The canonical value genuinely depends on the boundary pairing —
Proposition 3 for open fragments can only assert independence
*within* a pairing (`signedValueAt_samePairing`), and the
interfaces consuming `ThroughIndependenceC` must be re-based on
the pairing-resolved value.
-/

namespace RS

open scoped Classical

namespace TransposeVerify

/-- `cO` is path-canonical: both chains run low-to-high with
incoming entry edges (`isOut 0 = isOut 3 = false`). -/
theorem cO_pathCanonical : EdgeSubset.PathCanonical cO := by
  intro i j hb hint hpm hij
  fin_cases i
  · rfl
  · have h5 : (5 : Fin 8) ∈ cSubset.boundaryFlags :=
      cMem_boundary 1 rfl
    have h := (cPM_5 h5).symm.trans hpm
    fin_cases j
    · exact absurd hij (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · rfl
  · have h7 : (7 : Fin 8) ∈ cSubset.boundaryFlags :=
      cMem_boundary 3 rfl
    have h := (cPM_7 h7).symm.trans hpm
    fin_cases j
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd hij (by decide)
    · exact absurd h (by decide)

/-- `lvO₂flip` is path-canonical on the repaired system: the
repaired chords are `(0,3)` and `(1,2)`, and both low-end entry
edges are incoming (`isOut 0 = isOut 1 = false`). -/
theorem lvO₂flip_pathCanonical :
    EdgeSubset.PathCanonical lvO₂flip := by
  intro i j hb hint hpm hij
  fin_cases i
  · rfl
  · rfl
  · have h6 : (6 : Fin 8) ∈ cSubset.boundaryFlags :=
      cMem_boundary 2 rfl
    have h := (cPM'_6 h6).symm.trans hpm
    fin_cases j
    · exact absurd h (by decide)
    · exact absurd hij (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · have h7 : (7 : Fin 8) ∈ cSubset.boundaryFlags :=
      cMem_boundary 3 rfl
    have h := (cPM'_7 h7).symm.trans hpm
    fin_cases j
    · exact absurd hij (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)

/-- **The cross-pairing refutation**: the corrected independence
interface fails between path-canonical data with different
boundary pairings — the signed canonical values are `−1` and `0`. -/
theorem not_throughIndependenceC : ¬ ThroughIndependenceC := by
  intro H
  have h := H cSubset cFunctional cState cBnd
    (κ := cKappa) (κ' := lvKappa₂R) cO lvO₂flip
    cO_pathCanonical lvO₂flip_pathCanonical
  rw [cCount_zero, cCount_zero, cPathSign_kappa, cSummand_O,
    show EdgeSubset.pathSign lvKappa₂R = 1 from cPathSign_repair,
    lvSummand₂flip] at h
  norm_num at h

end TransposeVerify

end RS
