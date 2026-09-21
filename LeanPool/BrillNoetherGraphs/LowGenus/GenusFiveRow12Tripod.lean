/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationTwo

/-!
# The tripod part of the Atanasov--Ranganathan construction on row 12

Put one chip on each of `{3, 4, 5, 6}`.  At either tripod center `0` or `1`,
interpolate the same negative height along its three incident arms, choosing
that height to be the shortest arm length.  Every arm consumes at most its
endpoint chip and a shortest arm delivers a chip to the centre.  This is
configuration 2 of Atanasov--Ranganathan, Proposition 5.1.

The calculation itself is core generic and lives in
`LowGenus/ConfigurationTwo.lean`.  All this file does is
name the row's lookup tables, check the incidence facts that file asks for,
and re-export the reach statement in the shape row 12 consumes.
-/

namespace AtanasovRanganathan.GenusFiveRow12Tripod

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

/-- The two configuration-2 centers, as a decidable table. -/
def isCenter : Fin 8 → Bool
  | 0 | 1 => true
  | _ => false

/-- The three displayed arms at each tripod center. -/
def firstArm : Fin 8 → Fin 12
  | 0 => 0
  | 1 => 3
  | _ => 0

def secondArm : Fin 8 → Fin 12
  | 0 => 4
  | 1 => 5
  | _ => 0

def thirdArm : Fin 8 → Fin 12
  | 0 => 9
  | 1 => 10
  | _ => 0

/-- The chip vertex at the far end of each displayed arm. -/
def firstChip : Fin 8 → Fin 8
  | 0 => 4
  | 1 => 3
  | _ => 0

def secondChip : Fin 8 → Fin 8
  | 0 => 3
  | 1 => 4
  | _ => 0

def thirdChip : Fin 8 → Fin 8
  | 0 => 5
  | 1 => 6
  | _ => 0

/-- The one chip a tripod center does not touch. -/
def spareChip : Fin 8 → Fin 8
  | 0 => 6
  | 1 => 5
  | _ => 0

/-- The two tripod centres of row 12, read as AR configuration-2 pictures. -/
def row12TripodConfig : ConfigTwo where
  core := row12Core
  chipOne := 3
  chipTwo := 4
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
      simp only [isCenter, Fin.zero_eta, Fin.isValue, firstChip, secondChip, thirdChip, spareChip,
        add_left_inj, Fin.mk_one, Fin.reduceFinMk, Bool.false_eq_true] at hv ⊢<;>
      ring

/-! ## The shape row 12 consumes -/

/-- The two configuration-2 centers. -/
def IsTripodCenter (v : Fin 8) : Prop := v = 0 ∨ v = 1

instance (v : Fin 8) : Decidable (IsTripodCenter v) := by
  unfold IsTripodCenter
  infer_instance

theorem isCenter_of_isTripodCenter {v : Fin 8} (h : IsTripodCenter v) :
    isCenter v = true := by
  rcases h with rfl | rfl <;> rfl

/-- One chip on the selected bipartition class. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  fourChipDivisor (d.coreVertex 3) (d.coreVertex 4)
    (d.coreVertex 5) (d.coreVertex 6)

theorem rowDivisor_eq_config (d : DegSpec 8 12) :
    rowDivisor d = row12TripodConfig.divisor d := rfl

/-- **Configuration 2 at either tripod centre of row 12.** -/
theorem rowDivisor_reaches_tripodCenter
    (d : DegSpec 8 12) (hCore : d.core = row12Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row12Core F x y)
    (center : Fin 8) (hCenter : IsTripodCenter center) :
    Reaches d.graph (rowDivisor d) (d.coreVertex center) :=
  row12TripodConfig.reaches_center d hCore F hRepReach
    (isCenter_of_isTripodCenter hCenter)

end AtanasovRanganathan.GenusFiveRow12Tripod
