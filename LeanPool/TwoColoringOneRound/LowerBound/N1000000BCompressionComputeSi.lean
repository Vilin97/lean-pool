/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeBase
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiInt
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Z

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000WeakDuality
open Distributed2Coloring.LowerBound.N1000000Witness
open Distributed2Coloring.LowerBound.N1000000WedderburnData
open Distributed2Coloring.LowerBound.N1000000Z

private lemma rat_scale_mul_reduced_eq (q0 : Q) (s' : Int) (D' : Nat) :
    q0 * ((s' : Q) / (D' : Q)) =
      (((q0.num * s' : Int) : Q) / (q0.den * D' : Q)) := by
  have hFrac :
      ((q0.num : Q) / (q0.den : Q)) * ((s' : Q) / (D' : Q)) =
        (((q0.num * s' : Int) : Q) / (q0.den * D' : Q)) := by
    simp [div_mul_div_comm, Int.cast_mul, mul_comm]
  have hToQ0 :
      ((q0.num : Q) / (q0.den : Q)) * ((s' : Q) / (D' : Q)) =
        q0 * ((s' : Q) / (D' : Q)) := by
    simp [Rat.num_div_den q0]
  calc
    q0 * ((s' : Q) / (D' : Q)) =
        ((q0.num : Q) / (q0.den : Q)) * ((s' : Q) / (D' : Q)) := by
          simpa using hToQ0.symm
    _ = (((q0.num * s' : Int) : Q) / (q0.den * D' : Q)) := by
          simpa using hFrac

-- This is the Si-analogue of `compBasis_id_matches_S0`, proved entrywise by reducing to
-- finitely-many integer identities (precomputed in `N1000000BCompressionComputeSiInt`).
theorem compBasisSymm_var_matches_Si :
    ∀ r : Block, ∀ i : Var,
      compBasisSymm r (varOrbit i) = (blockScales[r.1]! : Q) • Si r i := by
  intro r i
  classical
  ext p q
  -- Reduce the `Si` entry by cancelling `gcd(|s|, D)` to avoid huge intermediate products.
  let s : Int := N1000000Z.matGet (SiNum r i) p.1 q.1
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
    simpa [g, D'] using (div_by_D_eq_div_by_div_gcd (s := s))
  have hsRed : (s : Q) / (D : Q) = (s' : Q) / (D' : Q) := by
    calc
      (s : Q) / (D : Q) = (s : Q) / (g : Q) / (D' : Q) := hsRed0
      _ = (s' : Q) / (D' : Q) := by
            simp [hs_cast]
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
  -- Reduce to an integer cross-multiplication identity, splitting on fixed-point vs
  -- non-fixed-point.
  by_cases hFix : tTr[(varOrbit i).1]! = (varOrbit i).1
  · have hInt :
        compBasisIntEntry (r := r) (d := varOrbit i) p q *
            Int.ofNat ((blockScales[r.1]! : Q).den * D')
          =
          (blockScales[r.1]! : Q).num * s' * Int.ofNat (basisDen r * basisDen r) := by
      have hGoal : SiIntGoal r i p q := siIntGoal_all (r := r) (i := i) (p := p) (q := q)
      have hGoal' := hGoal
      dsimp [SiIntGoal] at hGoal'
      have hSel := hGoal'
      rw [if_pos hFix] at hSel
      simpa [s, g, s', D'] using hSel
    have hEqFrac :
        ((compBasisIntEntry (r := r) (d := varOrbit i) p q : Int) : Q) /
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
      simpa using
        (rat_scale_mul_reduced_eq (q0 := blockScales[r.1]!) (s' := s') (D' := D'))
    have hsRed' : (s' : Q) / (D' : Q) = (s : Q) / (D : Q) := by
      simpa using hsRed.symm
    have hEqFracScaled :
        ((compBasisIntEntry (r := r) (d := varOrbit i) p q : Int) : Q) /
              ((basisDen r : Q) * (basisDen r : Q))
          =
          (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) := by
      calc
        ((compBasisIntEntry (r := r) (d := varOrbit i) p q : Int) : Q) /
              ((basisDen r : Q) * (basisDen r : Q))
            =
            (((blockScales[r.1]! : Q).num * s' : Int) : Q) /
              ((blockScales[r.1]! : Q).den * D' : Q) :=
              hEqFrac
        _ = (blockScales[r.1]! : Q) * ((s' : Q) / (D' : Q)) := by
              simpa using hScale.symm
        _ = (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) := by
              simp [hsRed']
    -- Convert the `Si` entry into the explicit quotient `s / D` and finish entrywise.
    have hSiEntry :
        (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) =
          ((blockScales[r.1]! : Q) • N1000000WeakDuality.Si r i) p q := by
      simp [N1000000WeakDuality.Si, N1000000WeakDuality.SiNum, N1000000Z.toMat3Scaled,
        N1000000Z.matGet, s, Matrix.smul_apply]
    calc
      compBasisSymm r (varOrbit i) p q
          = (compBasis r (varOrbit i)) p q := by
                dsimp [compBasisSymm]
                rw [if_pos hFix]
      _ = ((compBasisIntEntry (r := r) (d := varOrbit i) p q : Int) : Q) /
            ((basisDen r : Q) * (basisDen r : Q)) := by
            simpa using (compBasis_entry_eq_div (r := r) (d := varOrbit i) (p := p) (q := q))
      _ = (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) := hEqFracScaled
      _ = ((blockScales[r.1]! : Q) • N1000000WeakDuality.Si r i) p q := by
            simpa using hSiEntry
  · have hInt :
        (compBasisIntEntry (r := r) (d := varOrbit i) p q +
              compBasisIntEntry (r := r) (d := invDir (varOrbit i)) p q) *
            Int.ofNat ((blockScales[r.1]! : Q).den * D')
          =
          (blockScales[r.1]! : Q).num * s' * Int.ofNat (basisDen r * basisDen r) := by
      have hGoal : SiIntGoal r i p q := siIntGoal_all (r := r) (i := i) (p := p) (q := q)
      have hGoal' := hGoal
      dsimp [SiIntGoal] at hGoal'
      have hSel := hGoal'
      rw [if_neg hFix] at hSel
      simpa [s, g, s', D'] using hSel
    have hEqFrac :
        (((compBasisIntEntry (r := r) (d := varOrbit i) p q +
                  compBasisIntEntry (r := r) (d := invDir (varOrbit i)) p q) : Int) : Q) /
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
      simpa using
        (rat_scale_mul_reduced_eq (q0 := blockScales[r.1]!) (s' := s') (D' := D'))
    have hsRed' : (s' : Q) / (D' : Q) = (s : Q) / (D : Q) := by
      simpa using hsRed.symm
    have hEqFracScaled :
        (((compBasisIntEntry (r := r) (d := varOrbit i) p q +
                  compBasisIntEntry (r := r) (d := invDir (varOrbit i)) p q) : Int) : Q) /
              ((basisDen r : Q) * (basisDen r : Q))
          =
          (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) := by
      calc
        (((compBasisIntEntry (r := r) (d := varOrbit i) p q +
                    compBasisIntEntry (r := r) (d := invDir (varOrbit i)) p q) : Int) : Q) /
                ((basisDen r : Q) * (basisDen r : Q))
            =
            (((blockScales[r.1]! : Q).num * s' : Int) : Q) /
              ((blockScales[r.1]! : Q).den * D' : Q) :=
              hEqFrac
        _ = (blockScales[r.1]! : Q) * ((s' : Q) / (D' : Q)) := by
              simpa using hScale.symm
        _ = (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) := by
              simp [hsRed']
    have hSiEntry :
        (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) =
          ((blockScales[r.1]! : Q) • N1000000WeakDuality.Si r i) p q := by
      simp [N1000000WeakDuality.Si, N1000000WeakDuality.SiNum, N1000000Z.toMat3Scaled,
        N1000000Z.matGet, s, Matrix.smul_apply]
    calc
      compBasisSymm r (varOrbit i) p q
          = (compBasis r (varOrbit i) + compBasis r (invDir (varOrbit i))) p q := by
                dsimp [compBasisSymm]
                rw [if_neg hFix]
                rfl
      _ = compBasis r (varOrbit i) p q + compBasis r (invDir (varOrbit i)) p q := by
            rfl
      _ = ((compBasisIntEntry (r := r) (d := varOrbit i) p q : Int) : Q) /
              ((basisDen r : Q) * (basisDen r : Q))
            +
            ((compBasisIntEntry (r := r) (d := invDir (varOrbit i)) p q : Int) : Q) /
              ((basisDen r : Q) * (basisDen r : Q)) := by
            simp [compBasis_entry_eq_div]
      _ =
          (((compBasisIntEntry (r := r) (d := varOrbit i) p q +
                  compBasisIntEntry (r := r) (d := invDir (varOrbit i)) p q) : Int) : Q) /
              ((basisDen r : Q) * (basisDen r : Q)) := by
            -- Combine the two fractions and rewrite `(a : ℚ) + (b : ℚ)` as a cast of an `Int`
            -- sum.
            have :
                ((compBasisIntEntry (r := r) (d := varOrbit i) p q : Int) : Q) /
                      ((basisDen r : Q) * (basisDen r : Q))
                  +
                  ((compBasisIntEntry (r := r) (d := invDir (varOrbit i)) p q : Int) : Q) /
                      ((basisDen r : Q) * (basisDen r : Q))
                  =
                  (((compBasisIntEntry (r := r) (d := varOrbit i) p q : Int) : Q) +
                        ((compBasisIntEntry (r := r) (d := invDir (varOrbit i)) p q : Int) : Q)) /
                      ((basisDen r : Q) * (basisDen r : Q)) := by
                simpa using
                  (add_div
                        ((compBasisIntEntry (r := r) (d := varOrbit i) p q : Int) : Q)
                        ((compBasisIntEntry (r := r) (d := invDir (varOrbit i)) p q : Int) : Q)
                        ((basisDen r : Q) * (basisDen r : Q))).symm
            -- Now rewrite the numerator as a cast of an `Int` sum.
            simpa [Int.cast_add, add_assoc, add_comm, add_left_comm] using this
      _ = (blockScales[r.1]! : Q) * ((s : Q) / (D : Q)) := hEqFracScaled
      _ = ((blockScales[r.1]! : Q) • N1000000WeakDuality.Si r i) p q := by
            simpa using hSiEntry

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
