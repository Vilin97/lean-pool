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
import LeanPool.TwoColoringOneRound.LowerBound.CorrAvgMatrix
import LeanPool.TwoColoringOneRound.LowerBound.N1000000AvailFrom
import LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskComplete
import LeanPool.TwoColoringOneRound.LowerBound.N1000000OrbitalBasis
import LeanPool.TwoColoringOneRound.LowerBound.N1000000OrbitCounting
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Transitivity

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000CorrAvgMatrixDecompose
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000CorrAvgMatrixDecompose

open scoped BigOperators
open scoped Matrix

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000AvailFrom
open Distributed2Coloring.LowerBound.N1000000MaskComplete
open Distributed2Coloring.LowerBound.N1000000OrbitalBasis
open Distributed2Coloring.LowerBound.N1000000OrbitCounting
open Distributed2Coloring.LowerBound.N1000000Relaxation
open Distributed2Coloring.LowerBound.N1000000PairTransitivity
open Distributed2Coloring.LowerBound.N1000000Transitivity

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev V := Vertex n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev AvailFrom3 := AvailFrom (s := 3)

noncomputable instance : Fintype (Correlation.G n) := by infer_instance

-- A simple, canonical embedding of the free columns into the outside symbols `3,4,5`.
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def repEmb (k : DirIdx) : FreeCol k ↪ AvailFrom3 :=
  ⟨fun j =>
      let m : Nat := 3 + j.1.1
      have hm_lt : m < n := by
        -- `j.1.1 < 3`, hence `m < 6 ≤ n`.
        have : m < 6 := by
          have hj : j.1.1 < 3 := j.1.2
          -- `3 + j < 3 + 3 = 6`
          exact Nat.add_lt_add_left hj 3
        exact lt_of_lt_of_le this (by decide)
      have hm_ge : 3 ≤ (⟨m, hm_lt⟩ : SymN).1 := by
        -- `m = 3 + j` so `3 ≤ m`.
        exact Nat.le_add_right 3 j.1.1
      ⟨⟨m, hm_lt⟩, hm_ge⟩,
    by
      intro a b hab
      -- Reduce to equality in `Fin 3`.
      apply Subtype.ext
      apply Fin.ext
      -- Compare the underlying naturals `3 + a.1.1 = 3 + b.1.1`.
      have hNat : (3 + a.1.1) = (3 + b.1.1) := by
        -- `hab` is equality in `AvailFrom3`, so compare underlying `Nat` values.
        exact congrArg Fin.val (congrArg Subtype.val hab)
      exact Nat.add_left_cancel hNat⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def repVertex (d : DirIdx) : V :=
  decodeVertex d (repEmb d)

theorem dirMask_base_repVertex (d : DirIdx) :
    dirMask baseVertex (repVertex d) = N1000000StructureConstants.maskAt d := by
  simpa [repVertex] using decodeVertex_mask (k := d) (g := repEmb d)

-- The overlap-type coefficient induced by a coloring.
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def coeff (f : Coloring n) (d : DirIdx) : Q :=
  corrAvg f baseVertex (repVertex d)

theorem corrAvg_eq_coeff_of_dirMask_eq (f : Coloring n) {u v : V} (d : DirIdx)
    (h : dirMask u v = N1000000StructureConstants.maskAt d) : corrAvg f u v = coeff (f := f) d := by
  classical
  have hrep : dirMask baseVertex (repVertex d) = N1000000StructureConstants.maskAt d :=
    dirMask_base_repVertex d
  have : dirMask u v = dirMask baseVertex (repVertex d) := by simpa [hrep] using h
  -- `corrAvg` depends only on the directed mask.
  simpa [coeff] using (corrAvg_eq_of_dirMask_eq (f := f) (u := u) (v := v) (u' := baseVertex)
    (v' := repVertex d) this)

theorem corrAvg_symmetric (f : Coloring n) (u v : V) : corrAvg f u v = corrAvg f v u := by
  classical
  unfold corrAvg corr
  -- commutativity of multiplication in `ℚ`
  simp [mul_comm]

-- Decompose the orbit-averaged correlation matrix into the directed orbital basis `A`.
theorem corrAvgMatrix_eq_sum_coeff_A (f : Coloring n) :
    corrAvgMatrix (f := f) = ∑ d : DirIdx, (coeff (f := f) d) • A d := by
  classical
  ext u v
  -- Pick the directed type index `d0` of `(v,u)`.
  let d0 : DirIdx := dirIdxOfDirMask (u := v) (v := u)
  have hd0 : dirMask v u = N1000000StructureConstants.maskAt d0 := by
    simpa [d0] using (maskAt_dirIdxOfDirMask (u := v) (v := u)).symm
  have hA0 : A d0 u v = 1 := by
    simp [N1000000OrbitalBasis.A, hd0]
  have hAne : ∀ d : DirIdx, d ≠ d0 → A d u v = 0 := by
    intro d hd
    by_cases hEq : dirMask v u = N1000000StructureConstants.maskAt d
    · -- Injectivity of `maskAt` forces `d = d0`.
      have : N1000000StructureConstants.maskAt d0 = N1000000StructureConstants.maskAt d := by
        simpa [hd0] using hEq
      exact False.elim (hd (maskAt_injective this.symm))
    · simp [N1000000OrbitalBasis.A, hEq]
  -- Reduce the `DirIdx` sum to the single nonzero term `d0`.
  have hSum :
      (∑ d : DirIdx, (coeff (f := f) d) * (A d u v)) = coeff (f := f) d0 := by
    -- Convert to a `Finset.univ.sum` and isolate `d0`.
    classical
    have hSum' :
        (Finset.univ : Finset DirIdx).sum (fun d => (coeff (f := f) d) * (A d u v))
          = (coeff (f := f) d0) * (A d0 u v) := by
      refine Finset.sum_eq_single d0 (f := fun d => (coeff (f := f) d) * (A d u v)) ?_ ?_
      · intro d hdMem hdNe
        -- `A d u v = 0` for `d ≠ d0`
        calc
          (coeff (f := f) d) * (A d u v) = (coeff (f := f) d) * 0 := by
              rw [hAne d hdNe]
          _ = 0 := by simp
      · intro hdNotMem
        exact False.elim (hdNotMem (Finset.mem_univ d0))
    -- back to the `Fintype` sum and use `A d0 u v = 1`.
    have hF : (∑ d : DirIdx, (coeff (f := f) d) * (A d u v))
        = (Finset.univ : Finset DirIdx).sum (fun d => (coeff (f := f) d) * (A d u v)) := by
      rfl
    calc
      (∑ d : DirIdx, (coeff (f := f) d) * (A d u v))
          = (coeff (f := f) d0) * (A d0 u v) := by simpa [hF] using hSum'
      _ = coeff (f := f) d0 := by
            rw [hA0]
            simp
  -- Identify the RHS entrywise and finish.
  have hCoeff : corrAvg f u v = coeff (f := f) d0 := by
    have hSym : corrAvg f u v = corrAvg f v u := corrAvg_symmetric (f := f) u v
    have hDir : dirMask v u = N1000000StructureConstants.maskAt d0 := by simpa using hd0
    -- Apply `corrAvg_eq_coeff_of_dirMask_eq` on `(v,u)`.
    simpa [coeff] using
      hSym.trans (corrAvg_eq_coeff_of_dirMask_eq (f := f) (u := v) (v := u) d0 hDir)
  have hRhs :
      (∑ d : DirIdx, (coeff (f := f) d) • A d) u v
        = ∑ d : DirIdx,
          (if dirMask v u = N1000000StructureConstants.maskAt d then
            (coeff (f := f) d)
          else
            0) := by
    -- Expand the sum entrywise using `Fintype.sum_apply` twice.
    have hu :
        (∑ d : DirIdx, (coeff (f := f) d) • A d) u
          = ∑ d : DirIdx, ((coeff (f := f) d) • A d) u := by
      exact (Fintype.sum_apply (a := u) (g := fun d : DirIdx => (coeff (f := f) d) • A d))
    have huv :
        (∑ d : DirIdx, (coeff (f := f) d) • A d) u v
          = (∑ d : DirIdx, ((coeff (f := f) d) • A d) u) v := by
      simpa using congrArg (fun g : V → Q => g v) hu
    have hv :
        (∑ d : DirIdx, ((coeff (f := f) d) • A d) u) v
          = ∑ d : DirIdx, ((coeff (f := f) d) • A d) u v := by
      exact (Fintype.sum_apply (a := v) (g := fun d : DirIdx => ((coeff (f := f) d) • A d) u))
    -- Now unfold scalar multiplication and `A`.
    calc
      (∑ d : DirIdx, (coeff (f := f) d) • A d) u v
          = ∑ d : DirIdx, ((coeff (f := f) d) • A d) u v := by
              rw [huv]
              exact hv
      _ = ∑ d : DirIdx,
        (if dirMask v u = N1000000StructureConstants.maskAt d then (coeff (f := f) d) else 0) := by
            simp [N1000000OrbitalBasis.A, Matrix.smul_apply, mul_ite, mul_one, mul_zero]
  have hSumIf :
      (∑ d : DirIdx,
        (if dirMask v u = N1000000StructureConstants.maskAt d then (coeff (f := f) d) else 0))
        = coeff (f := f) d0 := by
    -- This is the same sum as `hSum` after unfolding `A`.
    simpa [N1000000OrbitalBasis.A, mul_ite, mul_one, mul_zero] using hSum
  calc
    corrAvgMatrix (f := f) u v = corrAvg f u v := rfl
    _ = coeff (f := f) d0 := hCoeff
    _ = ∑ d : DirIdx,
      (if dirMask v u = N1000000StructureConstants.maskAt d then (coeff (f := f) d) else 0) := by
          simpa using hSumIf.symm
    _ = (∑ d : DirIdx, (coeff (f := f) d) • A d) u v := by
          simp [hRhs]

end N1000000CorrAvgMatrixDecompose

end Distributed2Coloring.LowerBound
