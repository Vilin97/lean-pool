/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationTwo

/-!
# The Atanasov--Ranganathan construction on row 11

Row 11 is the cube.  Put one chip on the bipartition class `{0, 3, 5, 6}`.
At a chip-free vertex of the other class, interpolate the same negative
height along its three incident arms, choosing that height to be the shortest
arm length.  Every arm consumes at most its endpoint chip and a shortest arm
delivers a chip to the centre.  This is configuration 2 of
Atanasov--Ranganathan, Proposition 5.1.

All four chip-free cube vertices are tripod centres, so the whole
closed-orthant construction comes from `ConfigTwo.closedConstruction`.  The
calculation itself is core generic and lives in
`LowGenus/ConfigurationTwo.lean`, over the base layer in
`LowGenus/ConfigurationCommon.lean` (which is where the
ramp and endpoint lemmas this file used to carry now live).  All this file
does is name the row's lookup tables and check the incidence facts.
-/

namespace AtanasovRanganathan.GenusFiveRow11

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open GenusFiveCoreAtlas
open ConfigurationTwo

/-- The chip-free bipartition class of the cube, as a decidable table.  Every
one of its vertices is a configuration-2 tripod centre. -/
def isCenter : Fin 8 → Bool
  | 1 | 2 | 4 | 7 => true
  | _ => false

/-- The three displayed arms at each chip-free cube vertex. -/
def firstArm : Fin 8 → Fin 12
  | 1 => 0
  | 2 => 2
  | 4 => 4
  | 7 => 5
  | _ => 0

def secondArm : Fin 8 → Fin 12
  | 1 => 1
  | 2 => 3
  | 4 => 7
  | 7 => 6
  | _ => 0

def thirdArm : Fin 8 → Fin 12
  | 1 => 9
  | 2 => 11
  | 4 => 8
  | 7 => 10
  | _ => 0

/-- The chip vertex at the far end of each displayed arm. -/
def firstChip : Fin 8 → Fin 8
  | 1 => 0
  | 2 => 3
  | 4 => 5
  | 7 => 5
  | _ => 0

def secondChip : Fin 8 → Fin 8
  | 1 => 3
  | 2 => 0
  | 4 => 6
  | 7 => 6
  | _ => 0

def thirdChip : Fin 8 → Fin 8
  | 1 => 5
  | 2 => 6
  | 4 => 0
  | 7 => 3
  | _ => 0

/-- The one chip a tripod centre does not touch: the cube vertex antipodal to
it. -/
def spareChip : Fin 8 → Fin 8
  | 1 => 6
  | 2 => 5
  | 4 => 3
  | 7 => 0
  | _ => 0

/-- The cube read as four AR configuration-2 pictures. -/
def row11Config : ConfigTwo where
  core := row11Core
  chipOne := 0
  chipTwo := 3
  chipThree := 5
  chipFour := 6
  isCenter := isCenter
  firstArm := firstArm
  secondArm := secondArm
  thirdArm := thirdArm
  firstChip := firstChip
  secondChip := secondChip
  thirdChip := thirdChip
  spareChip := spareChip
  center_not_chip := by decide
  firstChip_isChip := by decide
  secondChip_isChip := by decide
  thirdChip_isChip := by decide
  firstArm_ends := by decide
  secondArm_ends := by decide
  thirdArm_ends := by decide
  firstArm_ne_secondArm := by decide
  firstArm_ne_thirdArm := by decide
  secondArm_ne_thirdArm := by decide
  incident_slots := by decide
  chipSum := by
    intro v hv f
    fin_cases v <;>
      simp only [isCenter, Fin.zero_eta, Fin.isValue, Bool.false_eq_true, Fin.mk_one, firstChip,
        secondChip, thirdChip, spareChip, Fin.reduceFinMk] at hv ⊢<;>
      ring

/-- One chip on the selected bipartition class. -/
def cubeDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  fourChipDivisor (d.coreVertex 0) (d.coreVertex 3)
    (d.coreVertex 5) (d.coreVertex 6)

theorem cubeDivisor_eq_config (d : DegSpec 8 12) :
    cubeDivisor d = row11Config.divisor d := rfl

/-- AR configuration 2 on the cube, valid simultaneously on the open cell and
every nonloopy forest face. -/
theorem row11_closedConstruction :
    ClosedSubdivisionDharConstruction row11Core (by norm_num) :=
  row11Config.closedConstruction row11_connected (by decide)

end AtanasovRanganathan.GenusFiveRow11
