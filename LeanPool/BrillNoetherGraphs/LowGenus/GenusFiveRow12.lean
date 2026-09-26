/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow12Tripod

/-!
# The Atanasov--Ranganathan construction on row 12

Put one chip on each of `3,4,5,6`.  The remaining vertices `0` and `1` are
centres of configuration-2 tripods, while `2--7` and its four incident arms
form configuration 3 of Atanasov--Ranganathan, Proposition 5.1.

Both local pictures are core generic and live in
`LowGenus/ConfigurationTwo.lean` and
`LowGenus/ConfigurationThree.lean`.  Because each of
those structures names its centres by an explicit `isCenter` table rather
than "every chip-free vertex", row 12 can declare `{0,1}` to be tripod
centres and `{2,7}` to be a configuration-3 pair, and this file only has to
name the row's lookup tables, check the incidence facts, and observe that the
two tables between them cover every chip-free vertex.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow12

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open GenusFiveCoreAtlas
open ConfigurationThree

/-! ## The row-12 configuration-3 lookup tables -/

/-- The two centres belonging to the configuration-3 component. -/
def isPairCenter : Fin 8 → Bool
  | 2 | 7 => true
  | _ => false

/-- The other chip-free centre in the same configuration-3 component. -/
def partner : Fin 8 → Fin 8
  | 2 => 7
  | 7 => 2
  | v => v

/-- The two arms from a pair centre to chip vertices. -/
def firstArm : Fin 8 → Fin 12
  | 2 => 1
  | 7 => 7
  | _ => 0

/-- Second arm of the row-12 configuration, using slot 2 at centre 2 and slot 8 at centre 7,
with zero as the unused default. -/
def secondArm : Fin 8 → Fin 12
  | 2 => 2
  | 7 => 8
  | _ => 0

/-- The chip at the far end of the first arm. -/
def firstChip : Fin 8 → Fin 8
  | 2 => 4
  | 7 => 6
  | _ => 0

/-- The chip at the far end of the second arm. -/
def secondChip : Fin 8 → Fin 8
  | 2 => 3
  | 7 => 5
  | _ => 0

/-- The edge joining the two chip-free centres. -/
def middleEdge : Fin 8 → Fin 12
  | 2 | 7 => 11
  | _ => 11

/-- The pair `2--7` of row 12, read as an AR configuration-3 picture. -/
def row12PairConfig : ConfigThree 8 12 where
  core := row12Core
  chipOne := 3
  chipTwo := 4
  chipThree := 5
  chipFour := 6
  isCenter := isPairCenter
  partner := partner
  firstArm := firstArm
  secondArm := secondArm
  middleSlot := middleEdge
  firstChip := firstChip
  secondChip := secondChip
  center_not_chip := by decide
  partner_isCenter := by decide
  partner_ne := by decide
  partner_partner := by decide
  middleSlot_partner := by decide
  firstChip_isChip := by decide
  secondChip_isChip := by decide
  firstArm_ends := by decide
  secondArm_ends := by decide
  middleSlot_ends := by decide
  firstArm_ne_secondArm := by decide
  incident_slots := by decide
  chipSum := by
    intro v hv f
    fin_cases v <;>
      simp only [isPairCenter, Fin.zero_eta, Fin.isValue, Bool.false_eq_true, Fin.mk_one,
        Fin.reduceFinMk, firstChip, secondChip, partner] at hv ⊢<;> ring

/-! ## Combining the two local pictures

The row's closing step lives in `GenusFiveRow12Guarding`, which feeds
`centers_cover` straight into a `Guarding.GuardingSet` and lets
`GuardingSet.closedConstruction` do the rest.  The hand-written composition
that used to stand here -- a `rowDivisor`, two `rfl` bridges to the two
configuration divisors, a chip/centre dispatch, and a call to
`ofReachesCoreClasses` -- was exactly the generic argument, and is retired. -/

/-- The two `isCenter` tables between them name every chip-free vertex. -/
theorem centers_cover : ∀ v : Fin 8, ¬ row12PairConfig.IsChip v →
    isPairCenter v = true ∨ GenusFiveRow12Tripod.isCenter v = true := by
  decide

end AtanasovRanganathan.GenusFiveRow12
