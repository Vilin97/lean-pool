/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Polyrith
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeBase
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000Z

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000WeakDuality
open Distributed2Coloring.LowerBound.N1000000StructureConstants
open Distributed2Coloring.LowerBound.N1000000Witness
open Distributed2Coloring.LowerBound.N1000000WedderburnData
open Distributed2Coloring.LowerBound.N1000000Z

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SiIntGoal (r : Block) (i : Var) (p q : Fin 3) : Prop :=
  let d : DirIdx := varOrbit i
  let s : Int := N1000000Z.matGet (SiNum r i) p.1 q.1
  let g : Nat := Nat.gcd s.natAbs D
  let s' : Int := s / (g : Int)
  let D' : Nat := D / g
  if tTr[d.1]! = d.1 then
    compBasisIntEntry (r := r) (d := d) p q * Int.ofNat ((blockScales[r.1]! : Q).den * D') =
      (blockScales[r.1]! : Q).num * s' * Int.ofNat (basisDen r * basisDen r)
  else
    (compBasisIntEntry (r := r) (d := d) p q +
          compBasisIntEntry (r := r) (d := invDir d) p q) *
        Int.ofNat ((blockScales[r.1]! : Q).den * D') =
      (blockScales[r.1]! : Q).num * s' * Int.ofNat (basisDen r * basisDen r)

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
