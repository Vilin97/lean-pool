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
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeBase
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0Int
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Z

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000WeakDuality
open Distributed2Coloring.LowerBound.N1000000WedderburnData
open Distributed2Coloring.LowerBound.N1000000Z

-- This file performs large, mostly-automatic simplifications over big rational expressions;
-- increasing `maxHeartbeats` avoids spurious timeouts in the kernel reduction.
theorem compBasis_id_matches_S0 :
    ∀ r : Block, compBasis r idDirIdx = (blockScales[r.1]! : Q) • S0 r := by
  intro r
  classical
  ext p q
  -- Reduce the `S0` entry by cancelling `gcd(|s|, D)` to avoid huge intermediate products.
  let s : Int := N1000000Z.matGet (S0Num r) p.1 q.1
  let g : Nat := Nat.gcd s.natAbs D
  let s' : Int := s / (g : Int)
  let D' : Nat := D / g
  have hs_dvd : (g : Int) ∣ s := by
    -- `g = gcd(|s|, D)` divides `|s|`, hence divides `s`.
    exact (Int.natCast_dvd (n := s)).2 (Nat.gcd_dvd_left s.natAbs D)
  have hs_cast : (s' : Q) = (s : Q) / (g : Q) := by
    -- Cast the exact integer quotient `s' = s / g` into `ℚ`.
    simpa [s'] using (Int.cast_div_charZero (k := Q) (m := s) (n := (g : Int)) hs_dvd)
  have hsRed0 : (s : Q) / (D : Q) = (s : Q) / (g : Q) / (D' : Q) := by
    -- This is the cancellation lemma, unfolded at `g` and `D'`.
    simpa [g, D'] using (div_by_D_eq_div_by_div_gcd (s := s))
  have hsRed : (s : Q) / (D : Q) = (s' : Q) / (D' : Q) := by
    -- Replace the intermediate factor `(s : ℚ) / g` by the cast quotient `s'`.
    calc
      (s : Q) / (D : Q) = (s : Q) / (g : Q) / (D' : Q) := hsRed0
      _ = (s' : Q) / (D' : Q) := by
            -- `hs_cast` gives `(s' : ℚ) = (s : ℚ)/g`; rewrite and simplify.
            simp [hs_cast]
  -- Reduce to an integer cross-multiplication identity (discharged by finite computation).
  have hInt :
      compBasisIntEntry (r := r) (d := idDirIdx) p q *
          Int.ofNat ((blockScales[r.1]! : Q).den * D')
        =
        (blockScales[r.1]! : Q).num * s' * Int.ofNat (basisDen r * basisDen r) := by
    -- Computed once (by `decide`) in small per-block modules to avoid OOM in a single file.
    have hGoal : S0IntGoal r p q := s0IntGoal_all (r := r) (p := p) (q := q)
    simpa [S0IntGoal, s, g, s', D'] using hGoal
  have hden1 : ((basisDen r : Q) * (basisDen r : Q)) ≠ 0 := by
    have : (basisDen r : Q) ≠ 0 := basisDenQ_ne_zero r
    exact mul_ne_zero this this
  have hD'pos : 0 < D' := by
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (by decide : 0 < D)
    have hg_le : g ≤ D := Nat.le_of_dvd (by decide : 0 < D) (Nat.gcd_dvd_right s.natAbs D)
    exact Nat.div_pos hg_le hgpos
  have hden2 : ((blockScales[r.1]! : Q).den * D' : Q) ≠ 0 := by
    have hNat : 0 < (blockScales[r.1]! : Q).den * D' :=
      Nat.mul_pos (Rat.den_pos (blockScales[r.1]! : Q)) hD'pos
    exact_mod_cast (Nat.ne_of_gt hNat)
  have hEqFrac :
      ((compBasisIntEntry (r := r) (d := idDirIdx) p q : Int) : Q) /
            ((basisDen r : Q) * (basisDen r : Q))
        =
        (((blockScales[r.1]! : Q).num * s' : Int) : Q) /
            ((blockScales[r.1]! : Q).den * D' : Q) := by
    apply (div_eq_div_iff hden1 hden2).2
    exact_mod_cast hInt
  have hScale :
      (blockScales[r.1]! : Q) * ((s' : Q) / (D' : Q))
        =
        (((blockScales[r.1]! : Q).num * s' : Int) : Q) /
          ((blockScales[r.1]! : Q).den * D' : Q) := by
    -- Avoid rewriting `q0` into `q0.num / q0.den` (which introduces self-referential projections);
    -- instead rewrite `q0.num / q0.den` back to `q0`.
    let q0 : Q := blockScales[r.1]!
    have hFrac :
        ((q0.num : Q) / (q0.den : Q)) * ((s' : Q) / (D' : Q))
          =
          (((q0.num * s' : Int) : Q) / (q0.den * D' : Q)) := by
      simp [div_mul_div_comm, Int.cast_mul, mul_comm]
    have hToQ0 :
        ((q0.num : Q) / (q0.den : Q)) * ((s' : Q) / (D' : Q)) =
          q0 * ((s' : Q) / (D' : Q)) := by
      simp [Rat.num_div_den q0]
    calc
      q0 * ((s' : Q) / (D' : Q))
          = ((q0.num : Q) / (q0.den : Q)) * ((s' : Q) / (D' : Q)) := by simpa using hToQ0.symm
      _ = (((q0.num * s' : Int) : Q) / (q0.den * D' : Q)) := by simpa using hFrac
      _ = (((blockScales[r.1]! : Q).num * s' : Int) : Q) /
            ((blockScales[r.1]! : Q).den * D' : Q) := by
            rfl
  have hsRed' : (s' : Q) / (D' : Q) = (s : Q) / (D : Q) := by simpa using hsRed.symm
  have hEqFracScaled :
      ((compBasisIntEntry (r := r) (d := idDirIdx) p q : Int) : Q) /
            ((basisDen r : Q) * (basisDen r : Q))
        =
        (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) := by
    calc
      ((compBasisIntEntry (r := r) (d := idDirIdx) p q : Int) : Q) /
            ((basisDen r : Q) * (basisDen r : Q))
          =
          (((blockScales[r.1]! : Q).num * s' : Int) : Q) / ((blockScales[r.1]! : Q).den * D' : Q) :=
            hEqFrac
      _ = (blockScales[r.1]! : Q) * ((s' : Q) / (D' : Q)) := by simpa using hScale.symm
      _ = (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) := by simp [hsRed']
  -- Finish by rewriting `compBasis` and `S0` entrywise into their fraction forms.
  simpa [compBasis_entry_eq_div, N1000000WeakDuality.S0, N1000000WeakDuality.S0Num,
    N1000000Z.toMat3Scaled, N1000000Z.matGet, s, Matrix.smul_apply, mul_assoc, mul_left_comm,
    mul_comm] using hEqFracScaled

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
