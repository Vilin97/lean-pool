/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.Defs
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000MuLinear
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Objective
import LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000Bound
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000Bound

open scoped BigOperators

open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000MuLinear
open Distributed2Coloring.LowerBound.N1000000Objective
open Distributed2Coloring.LowerBound.N1000000Relaxation
open Distributed2Coloring.LowerBound.N1000000WeakDuality

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ

private theorem edgeCount_ne_zero : edgeCount n ≠ 0 := by
  classical
  -- Provide `Nonempty (Edge n)` explicitly.
  have : Nonempty (Edge n) := ⟨edgeRep⟩
  exact Fintype.card_ne_zero

theorem dualObjective_ge_target :
    ((-26121 : Q) / 50000) ≤ (dualObjective : Q) := by
  -- Rewrite `dualObjective` to the closed-form constant `dualObjectiveD2 / D^2`.
  simp only [N1000000WeakDuality.dualObjective, N1000000.dualObjective_ok,
    N1000000Data.dualObjectiveD2]
  -- Clear denominators using `div_le_div_iff` with positive denominators.
  have hb : (0 : Q) < 50000 := by norm_num
  have hD : (0 : Q) < (D : Q) := by
    -- `D` is a positive natural number (it is a power of two in the exporter).
    exact_mod_cast (show 0 < D by decide)
  have hd : (0 : Q) < (D : Q) * (D : Q) := mul_pos hD hD
  -- `a/b ≤ c/d` iff `a*d ≤ c*b` when `b,d > 0`.
  have hCross :
      ((-26121 : Q) * ((D : Q) * (D : Q)))
        ≤ ((N1000000Data.dualObjectiveD2 : Int) : Q) * (50000 : Q) := by
    -- Both sides are integers (viewed in `ℚ`), so this reduces to an integer inequality.
    have hCrossInt :
        (-(26121 * (D * D) : Int)) ≤ N1000000Data.dualObjectiveD2 * (50000 : Int) := by
      -- A direct computation on integers.
      decide
    -- Cast the integer inequality into `ℚ`.
    exact_mod_cast hCrossInt
  have h :=
    (div_le_div_iff₀ (a := (-26121 : Q)) (b := (50000 : Q))
        (c := ((N1000000Data.dualObjectiveD2 : Int) : Q)) (d := ((D : Q) * (D : Q))) hb hd).2 hCross
  simpa [N1000000Data.dualObjectiveD2, mul_assoc, mul_comm, mul_left_comm] using h

theorem monoFraction_ge_23879_of_psd (f : Coloring n)
    (hpsd : ∀ r : Block, (S (xFromColoring f) r).PosSemidef) :
    (23879 : Q) / 100000 ≤ monoFraction f := by
  -- Package the primal feasibility needed by weak duality.
  have hfeas : PrimalFeasibleForCertificate (xFromColoring f) := by
    refine ⟨xFromColoring_muLinear (f := f), hpsd⟩
  -- Weak duality gives a lower bound on `xEdge`, hence on `edgeCorrelation f`.
  have hedgeCorr : (dualObjective : Q) ≤ edgeCorrelation f := by
    have hxEdge : (dualObjective : Q) ≤ xEdge (xFromColoring f) :=
      weakDuality (x := xFromColoring f) hfeas
    simpa [xEdge_xFromColoring_eq_edgeCorrelation (f := f)] using hxEdge
  have hedgeCorr' : ((-26121 : Q) / 50000) ≤ edgeCorrelation f := by
    exact le_trans dualObjective_ge_target hedgeCorr
  -- Convert correlation to monochromatic-edge fraction: `mono = (1 + corr)/2`.
  have hmono :
      ((1 : Q) + ((-26121 : Q) / 50000)) / 2 ≤ ((1 : Q) + edgeCorrelation f) / 2 := by
    have : (1 : Q) + ((-26121 : Q) / 50000) ≤ (1 : Q) + edgeCorrelation f := by
      simpa [add_le_add_iff_left] using hedgeCorr'
    exact (div_le_div_of_nonneg_right this (by norm_num))
  -- Finish by rewriting `monoFraction`.
  have hmonoEq := monoFraction_eq_one_add_edgeCorrelation_div_two (f := f) (hE := edgeCount_ne_zero)
  -- Arithmetic: `(1 + (-26121/50000))/2 = 23879/100000`.
  have htarget : ((1 : Q) + ((-26121 : Q) / 50000)) / 2 = (23879 : Q) / 100000 := by norm_num
  -- Combine.
  calc
    (23879 : Q) / 100000
        = ((1 : Q) + ((-26121 : Q) / 50000)) / 2 := by simp [htarget]
    _ ≤ ((1 : Q) + edgeCorrelation f) / 2 := hmono
    _ = monoFraction f := by simp [hmonoEq]

end N1000000Bound

end Distributed2Coloring.LowerBound
