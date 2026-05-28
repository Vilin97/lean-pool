/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.Defs
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data

namespace Distributed2Coloring.LowerBound

/-!
This file will host the Lean-level encoding of the exact rational certificate and the
main theorem for `n = 10^6`.

Planned approach (to be implemented):
* encode the reduced SDP data over `ℚ` (constraints and seven small PSD blocks),
* import the exact rational dual certificate,
* prove dual feasibility and evaluate the dual objective exactly,
* translate the resulting edge-correlation bound into a monochromatic-edge bound.
-/

namespace N1000000

open Distributed2Coloring.LowerBound.N1000000Data

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def coeffAt (a : Array Int) (i : Nat) : Int :=
  a.getD i 0

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def innerD2 (A B : Array (Array Int)) : Int :=
  let rows := A.size
  let cols := if rows = 0 then 0 else (A.getD 0 #[]).size
  (Finset.range rows).sum fun i =>
    (Finset.range cols).sum fun j =>
      (A.getD i #[]).getD j 0 * (B.getD i #[]).getD j 0

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def linNumD (i : Nat) : Int :=
  muSupport.foldl (fun acc t => acc + coeffAt t.2.1 i * t.2.2) 0

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def psdNumD2 (i : Nat) : Int :=
  (Finset.range SiBlocks.size).sum fun r =>
    innerD2 (SiBlocks.getD r #[] |>.getD i #[]) (ZBlocks.getD r #[])

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def c (i : Nat) : Int :=
  if i = edgeVar then 1 else 0

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def stationarityLHS_D2 (i : Nat) : Int :=
  -- `linNumD i` represents the numerator over `D`; multiply by `D` to put it over `D^2`.
  (linNumD i) * (D : Int) - psdNumD2 i

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def dualObjectiveComputedD2 : Int :=
  let muSumD : Int := muSupport.foldl (fun acc t => acc + t.2.2) 0
  let psdSumD2 : Int :=
    (Finset.range S0Blocks.size).sum fun r =>
      innerD2 (S0Blocks.getD r #[]) (ZBlocks.getD r #[])
  -- Multiply by `D^2` to clear denominators:
  --   obj = - (muSumD / D) - (psdSumD2 / D^2),
  -- so obj * D^2 = -muSumD * D - psdSumD2.
  (-muSumD) * (D : Int) - psdSumD2

theorem dualObjective_ok : dualObjectiveComputedD2 = dualObjectiveD2 := by
  decide

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def stationarityOK : Bool :=
  let D2 : Int := (D : Int) * (D : Int)
  (List.range numVars).all fun i =>
    decide (stationarityLHS_D2 i = -(c i) * D2)

theorem stationarityOK_true : stationarityOK = true := by
  decide

end N1000000

end Distributed2Coloring.LowerBound
