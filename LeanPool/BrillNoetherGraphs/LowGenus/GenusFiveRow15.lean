/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThree

/-!
# The Atanasov--Ranganathan construction on row 15

Row 15 is the eight-cycle with opposite chords.  Put one chip on each even
vertex `0,2,4,6`.  The chip-free core vertices form the two edges `1--5` and
`3--7`; together with their four incident chip vertices, each is
configuration 3 of Atanasov--Ranganathan, Proposition 5.1.

The calculation itself is core generic and lives in
`LowGenus/ConfigurationThree.lean`.  All this file does
is name the row's lookup tables and check the incidence facts that file asks
for.
-/

namespace AtanasovRanganathan.GenusFiveRow15

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Configurations
open GenusFiveCoreAtlas
open ConfigurationThree

/-- The other chip-free centre in the same configuration-3 component. -/
def partner : Fin 8 → Fin 8
  | 1 => 5
  | 5 => 1
  | 3 => 7
  | 7 => 3
  | v => v

/-- The first arm from each chip-free centre to a chip vertex. -/
def firstArm : Fin 8 → Fin 12
  | 1 => 0
  | 5 => 4
  | 3 => 2
  | 7 => 6
  | _ => 0

/-- The second arm from each chip-free centre to a chip vertex. -/
def secondArm : Fin 8 → Fin 12
  | 1 => 1
  | 5 => 5
  | 3 => 3
  | 7 => 7
  | _ => 0

/-- The chip at the far end of the first arm. -/
def firstChip : Fin 8 → Fin 8
  | 1 => 0
  | 5 => 4
  | 3 => 2
  | 7 => 6
  | _ => 0

/-- The chip at the far end of the second arm. -/
def secondChip : Fin 8 → Fin 8
  | 1 => 2
  | 5 => 6
  | 3 => 4
  | 7 => 0
  | _ => 0

/-- The edge joining the two chip-free centres. -/
def middleEdge : Fin 8 → Fin 12
  | 1 | 5 => 9
  | 3 | 7 => 11
  | _ => 9

/-- The chip-free core vertices, as a decidable table. -/
def isCenter : Fin 8 → Bool
  | 1 | 3 | 5 | 7 => true
  | _ => false

/-- Row 15 read as a pair of AR configuration-3 pictures. -/
def row15Config : ConfigThree 8 12 where
  core := row15Core
  chipOne := 0
  chipTwo := 2
  chipThree := 4
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
      simp only [isCenter, Fin.zero_eta, Fin.isValue, Bool.false_eq_true, Fin.mk_one, firstChip,
        secondChip, partner, Fin.reduceFinMk] at hv ⊢<;> ring

/-- AR configuration 3 on row 15, valid simultaneously on the open cell and
every nonloopy forest face. -/
theorem row15_closedConstruction :
    ClosedSubdivisionDharConstruction row15Core (by norm_num) :=
  row15Config.closedConstruction (by norm_num) row15_connected (by decide)

end AtanasovRanganathan.GenusFiveRow15
