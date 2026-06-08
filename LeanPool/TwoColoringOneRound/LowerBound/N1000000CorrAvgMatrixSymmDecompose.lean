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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import LeanPool.TwoColoringOneRound.LowerBound.OverlapType
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionCompute
import LeanPool.TwoColoringOneRound.LowerBound.N1000000CorrAvgMatrixDecompose
import LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskComplete
import LeanPool.TwoColoringOneRound.LowerBound.N1000000PairTransitivity
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation

/-!
This file rewrites `corrAvgMatrix` into the symmetric orbital basis:

`corrAvgMatrix = A id + ∑ i, xFromColoring i • ASymm (varOrbit i)`.

The key bookkeeping is a tiny (34-element) map from directed indices to the unique variable whose
transpose-orbit contains it (with `idDirIdx` handled separately).
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000CorrAvgMatrixSymmDecompose

open scoped BigOperators
open scoped Matrix

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000BCompressionCompute
open Distributed2Coloring.LowerBound.N1000000CorrAvgMatrixDecompose
open Distributed2Coloring.LowerBound.N1000000OrbitalBasis
open Distributed2Coloring.LowerBound.N1000000PairTransitivity
open Distributed2Coloring.LowerBound.N1000000MaskComplete
open Distributed2Coloring.LowerBound.N1000000Relaxation
open Distributed2Coloring.LowerBound.N1000000StructureConstants
open Distributed2Coloring.LowerBound.N1000000Transitivity

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev V := Vertex n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Var := N1000000WeakDuality.Var
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx


private theorem maskAt_invDir_testBit (d : DirIdx) (i j : Fin 3) :
    (maskAt (invDir d)).testBit (i.1 * 3 + j.1) = (maskAt d).testBit (j.1 * 3 + i.1) := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> decide

theorem dirMask_swap_eq_maskAt_invDir {u v : V} (d : DirIdx) (h : dirMask u v = maskAt d) :
    dirMask v u = maskAt (invDir d) := by
  classical
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 9
  · let iNat : Nat := t / 3
    let jNat : Nat := t % 3
    have hi : iNat < 3 := by
      have : t < 3 * 3 := by simpa using ht
      simpa [iNat] using (Nat.div_lt_of_lt_mul this)
    have hj : jNat < 3 := by
      have : 0 < 3 := by decide
      simpa [jNat] using Nat.mod_lt t this
    let i : Fin 3 := ⟨iNat, hi⟩
    let j : Fin 3 := ⟨jNat, hj⟩
    have htDecomp : i.1 * 3 + j.1 = t := by
      simpa [iNat, jNat, Nat.mul_comm] using (Nat.div_add_mod t 3)
    have hbit :
        (dirMask v u).testBit (i.1 * 3 + j.1) = (maskAt (invDir d)).testBit (i.1 * 3 + j.1) := by
      -- Swap the `i,j` bit using `invDir`, then use `h` to convert to `dirMask u v`, and finally
      -- `eq_comm`.
      simp [dirMask_testBit, maskAt_invDir_testBit, h.symm, eq_comm]
    simpa [htDecomp] using hbit
  · -- For `t ≥ 9`, both masks are `< 2^9`, so the `t`-th bit is `false`.
    have h9t : 9 ≤ t := Nat.le_of_not_gt ht
    have hPow : (2 : Nat) ^ 9 ≤ (2 : Nat) ^ t :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) h9t
    have hLtL : maskAt (invDir d) < (2 : Nat) ^ 9 := by
      simpa [Nat.shiftLeft_eq] using (maskAt_lt_512 (d := invDir d))
    have hLtR : dirMask v u < (2 : Nat) ^ 9 := by
      simpa [Nat.shiftLeft_eq] using (dirMask_lt (u := v) (v := u))
    have hLtL' : maskAt (invDir d) < (2 : Nat) ^ t := lt_of_lt_of_le hLtL hPow
    have hLtR' : dirMask v u < (2 : Nat) ^ t := lt_of_lt_of_le hLtR hPow
    simp [Nat.testBit_eq_false_of_lt hLtL', Nat.testBit_eq_false_of_lt hLtR']

theorem coeff_invDir (f : Coloring n) (d : DirIdx) :
    coeff (f := f) d = coeff (f := f) (invDir d) := by
  classical
  have hbase : dirMask baseVertex (repVertex d) = maskAt d := dirMask_base_repVertex d
  have hswap : dirMask (repVertex d) baseVertex = maskAt (invDir d) :=
    dirMask_swap_eq_maskAt_invDir (u := baseVertex) (v := repVertex d) d hbase
  -- Use symmetry of `corrAvg` plus orbit-constancy via the directed mask.
  calc
    coeff (f := f) d
        = corrAvg f baseVertex (repVertex d) := rfl
    _ = corrAvg f (repVertex d) baseVertex := by
          simp [corrAvg_symmetric (f := f) (u := baseVertex) (v := repVertex d)]
    _ = coeff (f := f) (invDir d) := by
          -- Apply `corrAvg_eq_coeff_of_dirMask_eq` on `(repVertex d, baseVertex)`.
          simpa using (corrAvg_eq_coeff_of_dirMask_eq (f := f) (u := repVertex d) (v := baseVertex)
            (d := invDir d) hswap)

-- A tiny lookup-table fact: for a `DirIdx`, the safe indexer `get?` is never `none`.
private theorem tTr_getD0_eq_getBang (d : DirIdx) :
    N1000000Witness.tTr[d.1]?.getD 0 = N1000000Witness.tTr[d.1]! := by
  fin_cases d <;> decide

-- The transpose constructor used in `ASymm` has the same `.1` as `invDir`, so it defines the same
-- orbital indicator matrix `A`.
private theorem A_tTr_mk_eq_A_invDir (d : DirIdx) :
    A
        (⟨N1000000Witness.tTr[d.1]!, by
          -- `tTr` is a permutation of the 34 indices.
          fin_cases d <;> decide⟩ : DirIdx)
      =
      A (invDir d) := by
  ext u v
  rfl

-- The diagonal overlap type: `dirMask baseVertex baseVertex` is the canonical `idDirIdx` mask.
theorem dirMask_baseVertex_baseVertex_eq_maskAt_idDirIdx :
    dirMask baseVertex baseVertex = maskAt idDirIdx := by
  decide

private theorem corrAvg_self (f : Coloring n) (u : V) : corrAvg f u u = (1 : Q) := by
  classical
  unfold corrAvg corr
  -- Each summand is `spin b * spin b = 1`.
  simp [spin_mul_self, Finset.sum_const]

theorem coeff_idDirIdx_eq_one (f : Coloring n) : coeff (f := f) idDirIdx = (1 : Q) := by
  classical
  have hMask1 : dirMask baseVertex (repVertex idDirIdx) = maskAt idDirIdx :=
    dirMask_base_repVertex idDirIdx
  have hMask2 : dirMask baseVertex baseVertex = maskAt idDirIdx :=
    dirMask_baseVertex_baseVertex_eq_maskAt_idDirIdx
  have hdm : dirMask baseVertex (repVertex idDirIdx) = dirMask baseVertex baseVertex := by
    simpa [hMask2] using hMask1
  have hCorr :
      corrAvg f baseVertex (repVertex idDirIdx) = corrAvg f baseVertex baseVertex :=
    corrAvg_eq_of_dirMask_eq (f := f) (u := baseVertex) (v := repVertex idDirIdx)
      (u' := baseVertex) (v' := baseVertex) hdm
  simp [coeff, hCorr, corrAvg_self (f := f) (u := baseVertex)]

-- `varRepVertexU` is always the base vertex `(0,1,2)`.
theorem varRepVertexU_eq_baseVertex (i : Var) : varRepVertexU i = baseVertex := by
  classical
  apply Subtype.ext
  funext j
  -- `varRepUAt i` is always `(0,1,2)`.
  have hU : varRepUAt i = (0, 1, 2) := by
    fin_cases i <;> decide
  -- Reduce to the three coordinates and use `Nat.mod_eq_of_lt`.
  have h0 : (0 : Nat) % n = 0 := Nat.mod_eq_of_lt (by decide : (0 : Nat) < n)
  have h1 : (1 : Nat) % n = 1 := Nat.mod_eq_of_lt (by decide : (1 : Nat) < n)
  have h2 : (2 : Nat) % n = 2 := Nat.mod_eq_of_lt (by decide : (2 : Nat) < n)
  fin_cases j <;>
    simp [varRepVertexU,
      varRepUAt,
      hU,
      N1000000Relaxation.tupleOfLabels,
      N1000000Relaxation.labelGet,
      N1000000Relaxation.symOfNat, Fin.ofNat, h0, h1, h2, baseVertex, baseTuple]

-- Compute the directed mask of each representative variable pair: it matches `varOrbit`.
theorem dirMask_base_varRepVertexV_eq_varOrbit (i : Var) :
    dirMask baseVertex (varRepVertexV i) = maskAt (varOrbit i) := by
  classical
  fin_cases i <;> decide

theorem coeff_varOrbit_eq_xFromColoring (f : Coloring n) (i : Var) :
    coeff (f := f) (varOrbit i) = xFromColoring f i := by
  classical
  have hU : varRepVertexU i = baseVertex := varRepVertexU_eq_baseVertex (i := i)
  have hMask : dirMask baseVertex (varRepVertexV i) = maskAt (varOrbit i) :=
    dirMask_base_varRepVertexV_eq_varOrbit (i := i)
  -- `xFromColoring` is defined using the same `(baseVertex, varRepVertexV i)` pair.
  have hx : xFromColoring f i = corrAvg f baseVertex (varRepVertexV i) := by
    simp [xFromColoring, hU]
  -- Replace `corrAvg` by the corresponding `coeff`.
  have hcoeff :
      corrAvg f baseVertex (varRepVertexV i) = coeff (f := f) (varOrbit i) :=
    (corrAvg_eq_coeff_of_dirMask_eq (f := f) (u := baseVertex) (v := varRepVertexV i)
      (d := varOrbit i) hMask)
  simpa [hx] using hcoeff.symm

-- Directed index → the unique variable whose transpose-orbit contains it (excluding `idDirIdx`).
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def dirToVar : Array (Option Var) :=
  #[
    some ⟨0, by decide⟩,  some ⟨1, by decide⟩,  some ⟨2, by decide⟩,  some ⟨3, by decide⟩,
    some ⟨2, by decide⟩,  some ⟨4, by decide⟩,  some ⟨5, by decide⟩,  some ⟨6, by decide⟩,
    some ⟨7, by decide⟩,  some ⟨8, by decide⟩,  some ⟨9, by decide⟩,  some ⟨10, by decide⟩,
    some ⟨11, by decide⟩, some ⟨3, by decide⟩,  some ⟨5, by decide⟩,  some ⟨12, by decide⟩,
    some ⟨8, by decide⟩,  some ⟨13, by decide⟩, some ⟨14, by decide⟩, some ⟨15, by decide⟩,
    some ⟨9, by decide⟩,  some ⟨10, by decide⟩, some ⟨14, by decide⟩, some ⟨11, by decide⟩,
    some ⟨15, by decide⟩, some ⟨16, by decide⟩, some ⟨17, by decide⟩, some ⟨18, by decide⟩,
    some ⟨19, by decide⟩, some ⟨20, by decide⟩, some ⟨20, by decide⟩, some ⟨21, by decide⟩,
    some ⟨22, by decide⟩, none
  ]

-- The table entry for a directed index.
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def varOfDirIdx (d : DirIdx) : Option Var :=
  dirToVar.getD d.1 none

theorem varOfDirIdx_eq_none_iff (d : DirIdx) : varOfDirIdx d = none ↔ d = idDirIdx := by
  classical
  fin_cases d <;> decide

theorem varOfDirIdx_eq_some_iff (d : DirIdx) (i : Var) :
    varOfDirIdx d = some i ↔ d = varOrbit i ∨ d = invDir (varOrbit i) := by
  classical
  fin_cases d <;> fin_cases i <;> decide

theorem varOfDirIdx_spec (d : DirIdx) (hd : d ≠ idDirIdx) :
    ∃ i : Var, varOfDirIdx d = some i ∧ (d = varOrbit i ∨ d = invDir (varOrbit i)) := by
  classical
  have hNone : varOfDirIdx d ≠ none := by
    intro h
    have : d = idDirIdx := (varOfDirIdx_eq_none_iff (d := d)).1 h
    exact hd this
  cases hOpt : varOfDirIdx d with
  | none =>
      cases hNone hOpt
  | some i0 =>
      refine ⟨i0, ?_, ?_⟩
      · rfl
      · exact (varOfDirIdx_eq_some_iff (d := d) (i := i0)).1 hOpt

private theorem ASymm_varOrbit_entry_one_of_orbit {u v : V} {d0 : DirIdx} {i0 : Var}
    (hd0 : dirMask v u = maskAt d0)
    (hOrb : d0 = varOrbit i0 ∨ d0 = invDir (varOrbit i0)) :
    ASymm (varOrbit i0) u v = 1 := by
  rcases hOrb with h0 | h0
  · have : dirMask v u = maskAt (varOrbit i0) := by
      simpa [h0] using hd0
    by_cases hFix : N1000000Witness.tTr[(varOrbit i0).1]! = (varOrbit i0).1
    · simp [ASymm, hFix, A, this]
    · unfold ASymm
      rw [dif_neg hFix]
      rw [A_tTr_mk_eq_A_invDir (d := varOrbit i0)]
      rw [Matrix.add_apply]
      have hNeInv : dirMask v u ≠ maskAt (invDir (varOrbit i0)) := by
        intro hEq
        have hMask : maskAt (varOrbit i0) = maskAt (invDir (varOrbit i0)) := by
          simpa [this] using hEq
        have hEqDir : varOrbit i0 = invDir (varOrbit i0) := maskAt_injective hMask
        have : N1000000Witness.tTr[(varOrbit i0).1]! = (varOrbit i0).1 := by
          have : (invDir (varOrbit i0)).1 = (varOrbit i0).1 :=
            congrArg (fun d => d.1) hEqDir.symm
          simpa [invDir] using this
        exact hFix this
      have hA1 : A (varOrbit i0) u v = 1 := by simp [A, this]
      have hA2 : A (invDir (varOrbit i0)) u v = 0 := by simp [A, hNeInv]
      rw [hA1, hA2]
      simp
  · have : dirMask v u = maskAt (invDir (varOrbit i0)) := by
      simpa [h0] using hd0
    by_cases hFix : N1000000Witness.tTr[(varOrbit i0).1]! = (varOrbit i0).1
    · have hMask : dirMask v u = maskAt (varOrbit i0) := by
        simpa [invDir, hFix] using this
      simp [ASymm, hFix, A, hMask]
    · unfold ASymm
      rw [dif_neg hFix]
      rw [A_tTr_mk_eq_A_invDir (d := varOrbit i0)]
      rw [Matrix.add_apply]
      have hNeVar : dirMask v u ≠ maskAt (varOrbit i0) := by
        intro hEq
        have hMask : maskAt (invDir (varOrbit i0)) = maskAt (varOrbit i0) := by
          simpa [hEq] using this.symm
        have hEqDir : N1000000Witness.tTr[(varOrbit i0).1]! = (varOrbit i0).1 := by
          have : invDir (varOrbit i0) = varOrbit i0 := maskAt_injective hMask
          have : (invDir (varOrbit i0)).1 = (varOrbit i0).1 := congrArg (fun d => d.1) this
          simpa [invDir] using this
        exact hFix hEqDir
      have hA2 : A (invDir (varOrbit i0)) u v = 1 := by simp [A, this]
      have hA1 : A (varOrbit i0) u v = 0 := by simp [A, hNeVar]
      rw [hA1, hA2]
      simp

-- Final symmetric decomposition into the reduced variables `xFromColoring`.
theorem corrAvgMatrix_eq_A_id_add_sum_var (f : Coloring n) :
    corrAvgMatrix (f := f) =
      A idDirIdx + ∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i) := by
  classical
  ext u v
  -- Let `d0` be the directed type of `(v,u)`.
  let d0 : DirIdx := dirIdxOfDirMask v u
  have hd0 : dirMask v u = maskAt d0 := by
    simpa [d0] using (maskAt_dirIdxOfDirMask (u := v) (v := u)).symm
  -- Compute `corrAvgMatrix` entrywise using orbit constancy + symmetry.
  have hLHS : corrAvgMatrix (f := f) u v = coeff (f := f) d0 := by
    have hSym : corrAvg f u v = corrAvg f v u := corrAvg_symmetric (f := f) u v
    have hCoeff' : corrAvg f v u = coeff (f := f) d0 :=
      corrAvg_eq_coeff_of_dirMask_eq (f := f) (u := v) (v := u) d0 hd0
    simpa [corrAvgMatrix] using hSym.trans hCoeff'
  -- Now compare with the symmetric decomposition.
  by_cases hId : d0 = idDirIdx
  · -- Diagonal directed type: only `A idDirIdx` contributes, and `coeff idDirIdx = 1`.
    have hAid : A idDirIdx u v = 1 := by
      simp [A, hd0, hId]
    have hASymmZero : ∀ i : Var, ASymm (varOrbit i) u v = 0 := by
      intro i
      -- `d0 = idDirIdx` cannot lie in a variable orbit (by the lookup table).
      have hNone : varOfDirIdx d0 = none :=
        (varOfDirIdx_eq_none_iff (d := d0)).2 hId
      have hNotOrbit : ¬(d0 = varOrbit i ∨ d0 = invDir (varOrbit i)) := by
        intro hO
        have this' : varOfDirIdx d0 = some i :=
          (varOfDirIdx_eq_some_iff (d := d0) (i := i)).2 hO
        simp [hNone] at this'
      have hNe1 : dirMask v u ≠ maskAt (varOrbit i) := by
        intro hEq
        have : d0 = varOrbit i := by
          apply maskAt_injective
          exact (hd0.symm.trans hEq)
        exact hNotOrbit (Or.inl this)
      have hNe2 : dirMask v u ≠ maskAt (invDir (varOrbit i)) := by
        intro hEq
        have : d0 = invDir (varOrbit i) := by
          apply maskAt_injective
          exact (hd0.symm.trans hEq)
        exact hNotOrbit (Or.inr this)
      by_cases hFix : N1000000Witness.tTr[(varOrbit i).1]! = (varOrbit i).1
      · -- fixed: `ASymm = A`
        simp [ASymm, hFix, A, hNe1]
      · -- not fixed: `ASymm = A + Aᵀ`
        -- Prove a `maskAt`-based inequality for the transpose index. We state it using the `get?`
        -- form
        -- since `Array.get!` unfolds to `get?.getD` in our goals.
        have hNeT :
            dirMask v u ≠
              maskAt
                (⟨N1000000Witness.tTr[(varOrbit i).1]?.getD 0, by
                  fin_cases i <;> decide⟩ : DirIdx) := by
          intro hEq
          apply hNe2
          have hMask :
              maskAt
                  (⟨N1000000Witness.tTr[(varOrbit i).1]?.getD 0, by
                    fin_cases i <;> decide⟩ : DirIdx)
                =
                maskAt (invDir (varOrbit i)) := by
            classical
            simp [N1000000StructureConstants.maskAt, invDir]
          exact hEq.trans hMask
        -- Now unfold `ASymm`, pick the non-fixed branch using `hFix`, and show both orbital
        -- indicator terms vanish at `(u,v)`.
        unfold ASymm
        -- Reduce the `dite` branch by hand (simp can struggle to rewrite the function position
        -- here).
        rw [dif_neg hFix]
        rw [Matrix.add_apply]
        -- First summand vanishes since `dirMask v u ≠ maskAt (varOrbit i)`.
        have hA1 : A (varOrbit i) u v = 0 := by simp [A, hNe1]
        rw [hA1, zero_add]
        -- For the transpose summand, unfold `A` and use the inequality `hNeT` (up to unfolding
        -- `tTr`).
        simp [A]
        · -- Discharge the inequality goal produced by `if_neg`.
          simpa [N1000000Witness.tTr] using hNeT
    have hSum0 :
        (∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) u v = 0 := by
      classical
      -- Entrywise, each summand vanishes since `ASymm (varOrbit i) u v = 0`.
      let g : Var → Matrix V V Q := fun i => (xFromColoring f i) • ASymm (varOrbit i)
      change ((Finset.univ : Finset Var).sum g) u v = 0
      rw [Matrix.sum_apply]
      simp [Matrix.smul_apply, hASymmZero]
    have hCoeff : coeff (f := f) d0 = (1 : Q) := by
      simpa [hId] using coeff_idDirIdx_eq_one (f := f)
    have hLHS1 : corrAvgMatrix (f := f) u v = (1 : Q) := by
      calc
        corrAvgMatrix (f := f) u v = coeff (f := f) d0 := hLHS
        _ = (1 : Q) := by simpa [hId] using hCoeff
    have hRHS1 :
        (A idDirIdx + ∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) u v = (1 : Q) := by
      -- Avoid unfolding `A` (which would reintroduce a `dirMask` equality goal).
      rw [Matrix.add_apply]
      rw [hAid, hSum0]
      simp
    exact hLHS1.trans hRHS1.symm
  · -- Off-diagonal: use the unique variable orbit for `d0`.
    rcases varOfDirIdx_spec (d := d0) (hd := hId) with ⟨i0, hi0, hOrb⟩
    have hAid0 : A idDirIdx u v = 0 := by
      have : dirMask v u ≠ maskAt idDirIdx := by
        intro hEq
        have : d0 = idDirIdx := by
          apply maskAt_injective
          exact (hd0.symm.trans hEq)
        exact hId this
      simp [A, this]
    -- Evaluate the variable sum: `ASymm` is the indicator of the transpose-orbit.
    have hSum :
        (∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) u v = xFromColoring f i0 := by
      -- Show only `i0` contributes.
      have hI0 : ∀ i : Var, i ≠ i0 → ASymm (varOrbit i) u v = 0 := by
        intro i hiNe
        have hNotSome : varOfDirIdx d0 ≠ some i := by
          -- `varOfDirIdx d0 = some i0`.
          have hSome : varOfDirIdx d0 = some i0 := hi0
          intro hEq
          have : i = i0 := by
            -- Both equalities describe the same `Option` value.
            exact Option.some.inj (hEq.symm.trans hSome)
          exact hiNe this
        -- If `d0` is not in the orbit of `i`, then both `A (varOrbit i)` and `A (invDir ...)`
        -- vanish.
        have hNot : ¬(d0 = varOrbit i ∨ d0 = invDir (varOrbit i)) := by
          intro hO
          have : varOfDirIdx d0 = some i :=
            (varOfDirIdx_eq_some_iff (d := d0) (i := i)).2 hO
          exact False.elim (hNotSome this)
        -- Unfold `ASymm` and simplify using `hd0`.
        by_cases hFix : N1000000Witness.tTr[(varOrbit i).1]! = (varOrbit i).1
        · have hA : A (varOrbit i) u v = 0 := by
            have : dirMask v u ≠ maskAt (varOrbit i) := by
              intro hEq
              have : d0 = varOrbit i := by
                apply maskAt_injective
                exact (hd0.symm.trans hEq)
              exact hNot (Or.inl this)
            simp [A, this]
          simpa [ASymm, hFix] using hA
        · have hNeVar : dirMask v u ≠ maskAt (varOrbit i) := by
            intro hEq
            have : d0 = varOrbit i := by
              apply maskAt_injective
              exact (hd0.symm.trans hEq)
            exact hNot (Or.inl this)
          have hNeInv : dirMask v u ≠ maskAt (invDir (varOrbit i)) := by
            intro hEq
            have : d0 = invDir (varOrbit i) := by
              apply maskAt_injective
              exact (hd0.symm.trans hEq)
            exact hNot (Or.inr this)
          -- Unfold `ASymm` into the non-fixed case and rewrite the transpose term as `invDir`.
          unfold ASymm
          rw [dif_neg hFix]
          rw [A_tTr_mk_eq_A_invDir (d := varOrbit i)]
          rw [Matrix.add_apply]
          simp [A, hNeVar, hNeInv]
      -- Use `Finset.sum_eq_single` to extract the `i0` term.
      have hASymmI0 : ASymm (varOrbit i0) u v = 1 := by
        exact ASymm_varOrbit_entry_one_of_orbit (u := u) (v := v) hd0 hOrb
      have hSum' :
          (Finset.univ : Finset Var).sum (fun i => (xFromColoring f i) * (ASymm (varOrbit i) u v))
            = (xFromColoring f i0) * (ASymm (varOrbit i0) u v) := by
        refine
          Finset.sum_eq_single i0
            (f := fun i => (xFromColoring f i) * (ASymm (varOrbit i) u v)) ?_ ?_
        · intro i _ hiNe
          have h0 : ASymm (varOrbit i) u v = 0 := hI0 i hiNe
          simp [h0]
        · intro hNotMem
          exact False.elim (hNotMem (Finset.mem_univ i0))
      -- Convert to the matrix sum.
      calc
        (∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) u v
            =
              (Finset.univ : Finset Var).sum
                (fun i => (xFromColoring f i) * (ASymm (varOrbit i) u v)) := by
                classical
                let g : Var → Matrix V V Q := fun i => (xFromColoring f i) • ASymm (varOrbit i)
                change ((Finset.univ : Finset Var).sum g) u v =
                  (Finset.univ : Finset Var).sum
                    (fun i => (xFromColoring f i) * (ASymm (varOrbit i) u v))
                rw [Matrix.sum_apply]
                simp [Matrix.smul_apply]
        _ = (xFromColoring f i0) * (ASymm (varOrbit i0) u v) := hSum'
        _ = xFromColoring f i0 := by simp [hASymmI0]
    -- Relate `coeff d0` to `xFromColoring f i0`.
    have hCoeff : coeff (f := f) d0 = xFromColoring f i0 := by
      have : d0 = varOrbit i0 ∨ d0 = invDir (varOrbit i0) := hOrb
      rcases this with h0 | h0
      · simpa [h0] using (coeff_varOrbit_eq_xFromColoring (f := f) (i := i0))
      · have hInv := coeff_invDir (f := f) (d := varOrbit i0)
        -- `coeff (invDir rep) = coeff rep`.
        have : coeff (f := f) d0 = coeff (f := f) (varOrbit i0) := by
          simpa [h0] using hInv.symm
        simpa [this] using (coeff_varOrbit_eq_xFromColoring (f := f) (i := i0))
    -- Finish.
    have hLHS' : corrAvgMatrix (f := f) u v = xFromColoring f i0 := by
      calc
        corrAvgMatrix (f := f) u v = coeff (f := f) d0 := hLHS
        _ = xFromColoring f i0 := hCoeff
    have hRHS :
        (A idDirIdx + ∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) u v =
          xFromColoring f i0 := by
      rw [Matrix.add_apply]
      rw [hAid0, hSum]
      simp
    exact hLHS'.trans hRHS.symm

end N1000000CorrAvgMatrixSymmDecompose

end Distributed2Coloring.LowerBound
