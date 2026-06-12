/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import Mathlib.Data.Matrix.Basic
import LeanPool.TwoColoringOneRound.LowerBound.Correlation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data
import LeanPool.TwoColoringOneRound.LowerBound.N1000000PairTransitivity
import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000OrbitalBasis
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000OrbitalBasis

open scoped BigOperators
open scoped Matrix

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000PairTransitivity
open Distributed2Coloring.LowerBound.N1000000StructureConstants
open Distributed2Coloring.LowerBound.N1000000Witness

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev V := Vertex n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev G := Correlation.G n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Distributed2Coloring.LowerBound.Mask
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev i0 : Fin 3 := ⟨0, by decide⟩
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev i1 : Fin 3 := ⟨1, by decide⟩
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev i2 : Fin 3 := ⟨2, by decide⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev s0 : SymN := ⟨0, by decide⟩
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev s1 : SymN := ⟨1, by decide⟩
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev s2 : SymN := ⟨2, by decide⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def baseTuple : Tuple 3 n
  | ⟨0, _⟩ => s0
  | ⟨1, _⟩ => s1
  | ⟨2, _⟩ => s2

theorem baseTuple_injective : Function.Injective baseTuple := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [baseTuple] at hij <;> cases hij <;> rfl

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def baseVertex : V :=
  ⟨baseTuple, baseTuple_injective⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def baseSet : Finset SymN :=
  insert s0 (insert s1 (insert s2 ∅))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def outside (x : SymN) : Prop := x ∉ baseSet

instance : DecidablePred outside := by
  intro x
  unfold outside
  infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev OutsideSym := { x : SymN // outside x }

-- The directed orbital basis matrices, in the `N[k][a][d]` convention:
-- `A_d[u,v] = 1` iff the directed overlap mask of the ordered pair `(v,u)` is `maskAt d`.
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def A (d : DirIdx) : Matrix V V Q :=
  fun u v => if dirMask v u = maskAt d then 1 else 0

@[simp] theorem A_apply (d : DirIdx) (u v : V) :
    A d u v = (if dirMask v u = maskAt d then 1 else 0) := rfl

-- The symmetric orbital basis element corresponding to a directed type `d`.
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def ASymm (d : DirIdx) : Matrix V V Q :=
  if h : tTr[d.1]! = d.1 then
    A d
  else
    A d + A ⟨tTr[d.1]!, by
      -- `tTr` is a permutation of the 34 indices.
      fin_cases d <;> decide⟩

end N1000000OrbitalBasis

end Distributed2Coloring.LowerBound
