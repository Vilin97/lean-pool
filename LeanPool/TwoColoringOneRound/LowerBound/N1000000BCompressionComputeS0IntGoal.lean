/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeBase
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Z

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000WeakDuality
open Distributed2Coloring.LowerBound.N1000000WedderburnData
open Distributed2Coloring.LowerBound.N1000000Z

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev S0IntGoal (r : Block) (p q : Fin 3) : Prop :=
  let s : Int := N1000000Z.matGet (S0Num r) p.1 q.1
  let g : Nat := Nat.gcd s.natAbs D
  let s' : Int := s / (g : Int)
  let D' : Nat := D / g
  compBasisIntEntry (r := r) (d := idDirIdx) p q * Int.ofNat ((blockScales[r.1]! : Q).den * D') =
    (blockScales[r.1]! : Q).num * s' * Int.ofNat (basisDen r * basisDen r)

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound

