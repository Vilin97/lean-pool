/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThree

/-!
# The Atanasov--Ranganathan construction on row 16

Put one chip on each of `3,4,5,6`.  The chip-free core vertices form the two
edges `0--1` and `2--7`; together with their four incident chip vertices,
each is configuration 3 of Atanasov--Ranganathan, Proposition 5.1.

The calculation itself is core generic and lives in
`LowGenus/ConfigurationThree.lean`.  All this file does
is name the row's lookup tables and check the incidence facts that file asks
for.
-/

namespace AtanasovRanganathan.GenusFiveRow16

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Configurations
open GenusFiveCoreAtlas
open ConfigurationThree

/-- The other chip-free centre in the same configuration-3 component. -/
def partner : Fin 8 → Fin 8
  | 0 => 1
  | 1 => 0
  | 2 => 7
  | 7 => 2
  | v => v

/-- The first arm from each chip-free centre to a chip vertex. -/
def firstArm : Fin 8 → Fin 12
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 7 => 7
  | _ => 0

/-- The second arm from each chip-free centre to a chip vertex. -/
def secondArm : Fin 8 → Fin 12
  | 0 => 9
  | 1 => 10
  | 2 => 2
  | 7 => 8
  | _ => 0

/-- The chip at the far end of the first arm. -/
def firstChip : Fin 8 → Fin 8
  | 0 => 4
  | 1 => 3
  | 2 => 4
  | 7 => 6
  | _ => 0

/-- The chip at the far end of the second arm. -/
def secondChip : Fin 8 → Fin 8
  | 0 => 5
  | 1 => 6
  | 2 => 3
  | 7 => 5
  | _ => 0

/-- The edge joining the two chip-free centres. -/
def middleEdge : Fin 8 → Fin 12
  | 0 | 1 => 4
  | 2 | 7 => 11
  | _ => 4

/-- The chip-free core vertices, as a decidable table. -/
def isCenter : Fin 8 → Bool
  | 0 | 1 | 2 | 7 => true
  | _ => false

/-- Row 16 read as a pair of AR configuration-3 pictures. -/
def row16Config : ConfigThree 8 12 where
  core := row16Core
  chipOne := 3
  chipTwo := 4
  chipThree := 5
  chipFour := 6
  isCenter := isCenter
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
      simp only [isCenter, Fin.zero_eta, Fin.isValue, firstChip, secondChip, partner, add_left_inj,
        Fin.mk_one, Fin.reduceFinMk, Bool.false_eq_true] at hv ⊢<;> ring

/-- AR configuration 3 on row 16, valid simultaneously on the open cell and
every nonloopy forest face. -/
theorem row16_closedConstruction :
    ClosedSubdivisionDharConstruction row16Core (by norm_num) :=
  row16Config.closedConstruction (by norm_num) row16_connected (by decide)

end AtanasovRanganathan.GenusFiveRow16
