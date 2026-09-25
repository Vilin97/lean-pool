/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationBananaTail
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationTwo
public import LeanPool.BrillNoetherGraphs.LowGenus.GuardingSet

/-!
# The Atanasov--Ranganathan construction on row 06, as a guarding set

Row 06 is the *theta with three bananas*: two hub vertices `2` and `3`, joined
by three disjoint handles, each handle a path

```
   2 -- x == y -- 3        (x == y a banana pair of slots)
```

with `(x, y) = (0, 1)`, `(4, 5)` and `(7, 6)`.  The twelve slots are

```
  0, 1 : 0 == 1     2 : 2 -- 0    3 : 1 -- 3
  5, 6 : 7 == 6     4 : 2 -- 7    7 : 6 -- 3
 10,11 : 4 == 5     9 : 2 -- 4    8 : 3 -- 5
```

**The guarding set is `{0, 3, 4, 7}`** -- the hub `3` together with the near
end of each banana.  It leaves chip free the other hub `2` and the far end of
each banana, and each of those four vertices is the centre of a picture that is
already in the configuration library:

* `2` is a **configuration-2 tripod**: its three slots `2, 4, 9` end on the
  three distinct chips `0, 7, 4`;
* `1`, `5` and `6` are each the centre of **AR's sixth picture**, the banana
  tail of `LowGenus/ConfigurationBananaTail.lean`: for the centre `1` the arm
  vertex is `c = 2`, the arm chips are `a = 7` and `b = 4`, the middle slot is
  `2 -- 0`, the banana chip is `d = 0`, and the tail slot `1 -- 3` lands on the
  chip `f = 3`.

This is exactly the decomposition of `GenusFiveRow14`, with the multiplicities
exchanged: row 14 is three tripods and one banana tail, row 06 is one tripod
and three banana tails.  The three banana tails are images of one another under
the handle-permuting symmetry of the core, so the banana argument is written
**once**, parameterized by the centre `1`, `5` or `6`; every lookup table below
is a `Fin 8`-indexed function of that centre and every proof splits on it.

The closing step is not written by hand at all: the four pictures are packaged
as an `AtanasovRanganathan.Guarding.GuardingSet` and
`GuardingSet.closedConstruction` supplies the row's
`ClosedSubdivisionDharConstruction`.

**This replaces the generated fixed cover.**  The eight modules
`GenusFiveRow06Symmetry`, `GenusFiveRow06CoverBase`,
`GenusFiveRow06CoverCells0`--`4` and `GenusFiveRow06FixedCover` give an
independent machine-generated chamber-cover proof of the same theorem.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open GenusFiveCoreAtlas
open ConfigurationFive
open ConfigurationBananaTail
open Guarding

/-! ## The divisor -/

/-- The hub `3` together with the near end of each of the three bananas. -/
def IsChipVertex (v : Fin 8) : Prop :=
  v = 0 ∨ v = 3 ∨ v = 4 ∨ v = 7

instance (v : Fin 8) : Decidable (IsChipVertex v) := by
  unfold IsChipVertex
  infer_instance

/-- Indicator weight of the four guarding-set vertices 0, 3, 4, and 7. -/
def chipWeight (v : Fin 8) : ℤ := if IsChipVertex v then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  by_cases hv : IsChipVertex v <;> simp [chipWeight, hv]

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 4 := by decide

/-- The row's weight is the four-chip indicator of the guarding-set glue. -/
theorem chipWeight_eq_fourChipWeight :
    chipWeight = Guarding.fourChipWeight 0 3 4 7 := by
  funext v
  fin_cases v <;> decide

/-- The graph divisor obtained by pushing the four guarding-set chips to their core equivalence
classes. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  d.coreClassDivisor chipWeight

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  d.coreClassDivisor_effective chipWeight chipWeight_nonneg

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, d.deg_coreClassDivisor, sum_chipWeight]

/-! ## The configuration-2 tripod at the hub `2` -/

/-- The predicate selecting vertex 2 as the tripod centre. -/
def isCenter : Fin 8 → Bool
  | 2 => true
  | _ => false

/-- The first tripod arm at centre 2 is slot 2; the value at any other vertex is the unused
default zero. -/
def firstArm : Fin 8 → Fin 12
  | 2 => 2
  | _ => 0

/-- The second tripod arm at centre 2 is slot 4; the value at any other vertex is the unused
default zero. -/
def secondArm : Fin 8 → Fin 12
  | 2 => 4
  | _ => 0

/-- The third tripod arm at centre 2 is slot 9; the value at any other vertex is the unused
default zero. -/
def thirdArm : Fin 8 → Fin 12
  | 2 => 9
  | _ => 0

/-- The chip at the far end of the first tripod arm is vertex 0; other inputs use the same
default. -/
def firstChip : Fin 8 → Fin 8
  | 2 => 0
  | _ => 0

/-- The chip at the far end of the second tripod arm is vertex 7; inputs other than centre 2 use
default zero. -/
def secondChip : Fin 8 → Fin 8
  | 2 => 7
  | _ => 0

/-- The chip at the far end of the third tripod arm is vertex 4; inputs other than centre 2 use
default zero. -/
def thirdChip : Fin 8 → Fin 8
  | 2 => 4
  | _ => 0

/-- The one chip the tripod centre does not touch: the far hub `3`. -/
def spareChip : Fin 8 → Fin 8
  | 2 => 3
  | _ => 0

/-- The hub `2` read as an AR configuration-2 picture. -/
def row06TripodConfig : ConfigurationTwo.ConfigTwo where
  core := row06Core
  chipOne := 0
  chipTwo := 3
  chipThree := 4
  chipFour := 7
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
    have honly : ∀ w : Fin 8, isCenter w = true → w = 2 := by decide
    obtain rfl := honly v hv
    simp only [firstChip, secondChip, thirdChip, spareChip]
    ring

/-- The class-sum form of the displayed divisor agrees with the four-chip form
the configuration-2 family uses. -/
theorem rowDivisor_eq_tripodConfig (d : DegSpec 8 12) :
    rowDivisor d = row06TripodConfig.divisor d := by
  rw [rowDivisor, chipWeight_eq_fourChipWeight,
    Guarding.coreClassDivisor_eq_fourChipDivisor d (a := 0) (b := 3) (c := 4)
      (e := 7) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  rfl

/-! ## The three banana tails

The three handles are interchangeable, so the banana argument is written once
with the centre as a parameter.  For a centre `c ∈ {1, 5, 6}` the tables below
name the six slots and the four other vertices of AR's sixth picture:

| centre `c` | arms `a`, `b` | middle `2 -- d` | banana `d == c` | tail `c -- 3` |
|---|---|---|---|---|
| `1` | `4` to `7`, `9` to `4` | `2` | `0`, `1` | `3` |
| `5` | `2` to `0`, `4` to `7` | `9` | `10`, `11` | `8` |
| `6` | `2` to `0`, `9` to `4` | `4` | `5`, `6` | `7` |

The arm vertex is the hub `2` and the tail chip is the hub `3` in all three. -/

/-- The predicate selecting vertices 1, 5, and 6 as the three banana-tail centres. -/
def isBananaCenter : Fin 8 → Bool
  | 1 | 5 | 6 => true
  | _ => false

theorem isBananaCenter_iff (c : Fin 8) :
    isBananaCenter c = true ↔ c = 1 ∨ c = 5 ∨ c = 6 := by
  revert c
  decide

/-- First external arm slot for centres 1, 5, and 6, respectively 4, 2, and 2; all other inputs
use zero. -/
def armSlotA : Fin 8 → Fin 12
  | 1 => 4
  | 5 => 2
  | 6 => 2
  | _ => 0

/-- Second external arm slot for centres 1, 5, and 6, respectively 9, 4, and 9; all other inputs
use zero. -/
def armSlotB : Fin 8 → Fin 12
  | 1 => 9
  | 5 => 4
  | 6 => 9
  | _ => 0

/-- Middle slot joining hub 2 to the near banana chip, respectively 2, 9, and 4 for centres 1,
5, and 6. -/
def midSlot : Fin 8 → Fin 12
  | 1 => 2
  | 5 => 9
  | 6 => 4
  | _ => 0

/-- First parallel banana slot, respectively 0, 10, and 5 for centres 1, 5, and 6; other inputs
use zero. -/
def banSlotP : Fin 8 → Fin 12
  | 1 => 0
  | 5 => 10
  | 6 => 5
  | _ => 0

/-- Second parallel banana slot, respectively 1, 11, and 6 for centres 1, 5, and 6; other inputs
use zero. -/
def banSlotQ : Fin 8 → Fin 12
  | 1 => 1
  | 5 => 11
  | 6 => 6
  | _ => 0

/-- Tail slot joining the banana centre to the far chip at vertex 3, respectively 3, 8, and 7
for centres 1, 5, and 6. -/
def tailSlot : Fin 8 → Fin 12
  | 1 => 3
  | 5 => 8
  | 6 => 7
  | _ => 0

/-- Chip at the end of the first external arm, respectively vertex 7, 0, or 0 for centres 1, 5,
or 6. -/
def armChipA : Fin 8 → Fin 8
  | 1 => 7
  | 5 => 0
  | 6 => 0
  | _ => 0

/-- Chip at the end of the second external arm, respectively vertex 4, 7, or 4 for centres 1, 5,
or 6. -/
def armChipB : Fin 8 → Fin 8
  | 1 => 4
  | 5 => 7
  | 6 => 4
  | _ => 0

/-- The chip at the near end of the banana. -/
def banChip : Fin 8 → Fin 8
  | 1 => 0
  | 5 => 4
  | 6 => 7
  | _ => 0

/-- The tail slot of the centre `5` is the only one of the eighteen displayed
slots whose core orientation points *into* the vertex carrying the higher
height; every other slot of every handle points away from it. -/
def tailLedger : Fin 8 → BananaLedger
  | 1 => fwd
  | 5 => rev
  | 6 => fwd
  | _ => fwd

/-! ### The nested-min heights

`armMin` is the shorter arm at the hub `2`, `parMin` the shorter banana slot. -/

/-- The shorter of the two external arms of a banana-tail configuration. -/
def armMin (c : Fin 8) (d : DegSpec 8 12) : ℕ :=
  min (d.length (armSlotA c)) (d.length (armSlotB c))

/-- The shorter of the two parallel slots in the selected banana. -/
def parMin (c : Fin 8) (d : DegSpec 8 12) : ℕ :=
  min (d.length (banSlotP c)) (d.length (banSlotQ c))

/-- The height at the centre. -/
def endHeight (c : Fin 8) (d : DegSpec 8 12) : ℕ :=
  min (d.length (tailSlot c)) (armMin c d + d.length (midSlot c) + parMin c d)

/-- The height at the chip at the near end of the banana. -/
def midHeight (c : Fin 8) (d : DegSpec 8 12) : ℕ :=
  min (endHeight c d) (armMin c d + d.length (midSlot c))

/-- The height at the chip-free hub `2`. -/
def armHeight (c : Fin 8) (d : DegSpec 8 12) : ℕ :=
  min (midHeight c d) (armMin c d)

/-- The unquotiented height profile: use the arm height at hub 2, the middle height at the near
banana chip, the end height at the centre, and zero elsewhere. -/
def rawHeight (c : Fin 8) (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 2 then armHeight c d
  else if v = banChip c then midHeight c d
  else if v = c then endHeight c d
  else 0

/-- Integer-valued firing potential given by the negative of the unquotiented height profile. -/
def rawPotential (c : Fin 8) (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  -(rawHeight c d v : ℤ)

/-- Reading the raw profile at the canonical representative makes class
invariance definitional. -/
def firingPotential (c : Fin 8) (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  rawPotential c d (d.rep v)

theorem firingPotential_repInvariant (c : Fin 8) (d : DegSpec 8 12) :
    d.RepInvariant (firingPotential c d) := by
  intro v
  simp [firingPotential, d.rep_idem]

theorem rawHeight_eq_of_zero_edge (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (e : Fin 12) :
    d.length e = 0 →
      rawHeight c d (row06Core.tail e) = rawHeight c d (row06Core.head e) := by
  rcases (isBananaCenter_iff c).mp hc with rfl | rfl | rfl
  all_goals fin_cases e
  all_goals
    simp [rawHeight, armHeight, midHeight, endHeight, armMin, parMin, banChip,
      armSlotA, armSlotB, midSlot, banSlotP, banSlotQ, tailSlot, row06Core]
  all_goals omega

theorem rawPotential_eq_of_zero_edge (c : Fin 8)
    (hc : isBananaCenter c = true) (d : DegSpec 8 12) {e : Fin 12}
    (hZero : d.length e = 0) :
    rawPotential c d (row06Core.tail e) =
      rawPotential c d (row06Core.head e) := by
  rw [rawPotential, rawPotential, rawHeight_eq_of_zero_edge c hc d e hZero]

theorem rawPotential_eq_of_reach (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (F : Finset (Fin 12))
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {u v : Fin 8} (hReach : ReachIn row06Core F u v) :
    rawPotential c d u = rawPotential c d v := by
  induction hReach with
  | refl => rfl
  | @tail a b hPrefix hLast ih =>
      rw [ih]
      obtain ⟨e, he, hab | hab⟩ := hLast
      · rw [← hab.1, ← hab.2]
        exact rawPotential_eq_of_zero_edge c hc d
          ((hFZero e).mp ((mem_edgeList F e).mp he))
      · rw [← hab.1, ← hab.2]
        exact (rawPotential_eq_of_zero_edge c hc d
          ((hFZero e).mp ((mem_edgeList F e).mp he))).symm

theorem firingPotential_eq_raw (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row06Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (v : Fin 8) :
    firingPotential c d v = rawPotential c d v := by
  apply rawPotential_eq_of_reach c hc d F hFZero
  exact (hRepReach (d.rep v) v).mp (d.rep_idem v)

/-! ### Redistributing chips inside contracted classes -/

export ConfigurationCommon (indicatorWeight transferWeight
  sum_transferWeight_eq_zero sum_indicatorWeight_class
  positiveEndpointContribution positiveEndpointContribution_classSum_eq)

/-- The conditional transfer that pays for the two banana chips when the middle
slot has collapsed. -/
def shiftWeight (c : Fin 8) (d : DegSpec 8 12) : ℤ :=
  if d.length (midSlot c) = 0 ∧ midHeight c d < endHeight c d then 1 else 0

/-- The guarding-set weight redistributed across contracted arms and tail, with a further
transfer across a contracted middle slot when the end height exceeds the middle height. -/
def allocatedWeight (c : Fin 8) (d : DegSpec 8 12) (vertex : Fin 8) : ℤ :=
  chipWeight vertex +
    (if d.length (armSlotA c) = 0 then
      transferWeight (armChipA c) 2 vertex else 0) +
    (if d.length (armSlotB c) = 0 then
      transferWeight (armChipB c) 2 vertex else 0) +
    (if d.length (tailSlot c) = 0 then transferWeight 3 c vertex else 0) +
    (if d.length (midSlot c) = 0 ∧ midHeight c d < endHeight c d then
      transferWeight 2 (banChip c) vertex else 0)

theorem allocated_class_sum_eq (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (hCore : d.core = row06Core) (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocatedWeight c d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  have hCases := (isBananaCenter_iff c).mp hc
  have hArmA : d.length (armSlotA c) = 0 → d.rep (armChipA c) = d.rep 2 := by
    intro hZero
    have h := d.rep_zero (armSlotA c) hZero
    revert h
    rcases hCases with rfl | rfl | rfl <;>
      (intro h;
        first
          | (simpa [hCore, row06Core, armSlotA, armChipA] using h)
          | (simpa [hCore, row06Core, armSlotA, armChipA] using h.symm))
  have hArmB : d.length (armSlotB c) = 0 → d.rep (armChipB c) = d.rep 2 := by
    intro hZero
    have h := d.rep_zero (armSlotB c) hZero
    revert h
    rcases hCases with rfl | rfl | rfl <;>
      (intro h;
        first
          | (simpa [hCore, row06Core, armSlotB, armChipB] using h)
          | (simpa [hCore, row06Core, armSlotB, armChipB] using h.symm))
  have hTail : d.length (tailSlot c) = 0 → d.rep 3 = d.rep c := by
    intro hZero
    have h := d.rep_zero (tailSlot c) hZero
    revert h
    rcases hCases with rfl | rfl | rfl <;>
      (intro h;
        first
          | (simpa [hCore, row06Core, tailSlot] using h)
          | (simpa [hCore, row06Core, tailSlot] using h.symm))
  have hShift : (d.length (midSlot c) = 0 ∧ midHeight c d < endHeight c d) →
      d.rep 2 = d.rep (banChip c) := by
    intro hZero
    have h := d.rep_zero (midSlot c) hZero.1
    revert h
    rcases hCases with rfl | rfl | rfl <;>
      (intro h; simpa [hCore, row06Core, midSlot, banChip] using h)
  have hConditional (P : Prop) [Decidable P] (source target : Fin 8)
      (hRep : P → d.rep source = d.rep target) :
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
          (if P then transferWeight source target v else 0) = 0 := by
    by_cases hP : P
    · simp only [if_pos hP]
      exact sum_transferWeight_eq_zero d (hRep hP) r
    · simp [hP]
  simp only [allocatedWeight, Finset.sum_add_distrib]
  rw [hConditional _ _ _ hArmA, hConditional _ _ _ hArmB,
    hConditional _ _ _ hTail, hConditional _ _ _ hShift]
  simp

/-! ### Which vertex of the centre's class carries the delivered chip -/

/-- Target representative after contraction: use the near banana chip when a parallel slot has
zero length and the tail is longer than the shorter arm plus the middle slot; use the centre
otherwise. -/
def targetOwner (c : Fin 8) (d : DegSpec 8 12) : Fin 8 :=
  if parMin c d = 0 ∧ armMin c d + d.length (midSlot c) < d.length (tailSlot c)
    then banChip c else c

theorem targetOwner_rep_eq_center (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (hCore : d.core = row06Core) :
    d.rep (targetOwner c d) = d.rep c := by
  have hCases := (isBananaCenter_iff c).mp hc
  unfold targetOwner
  split_ifs with hP
  · have hEither : d.length (banSlotP c) = 0 ∨ d.length (banSlotQ c) = 0 := by
      have := hP.1
      simp only [parMin, Nat.min_eq_zero_iff] at this
      exact this
    rcases hEither with hZero | hZero
    · have h := d.rep_zero (banSlotP c) hZero
      revert h
      rcases hCases with rfl | rfl | rfl <;>
        (intro h; simpa [hCore, row06Core, banSlotP, banChip] using h)
    · have h := d.rep_zero (banSlotQ c) hZero
      revert h
      rcases hCases with rfl | rfl | rfl <;>
        (intro h; simpa [hCore, row06Core, banSlotQ, banChip] using h)
  · rfl

/-! ### Endpoint accounting on the contracted face -/

/-- The same sum read off a height profile rather than a potential. -/
def heightEndpointSum (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  ∑ e : Fin 12,
    ((if d.core.tail e = v then
        tailContribution (d.length e) (h (d.core.tail e)) (h (d.core.head e))
      else 0) +
    (if d.core.head e = v then
        headContribution (d.length e) (h (d.core.tail e)) (h (d.core.head e))
      else 0))

theorem positiveEndpointContribution_eq_heightForm
    (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row06Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (v : Fin 8) :
    positiveEndpointContribution d (firingPotential c d) v =
      heightEndpointSum d (rawHeight c d) v := by
  have hp : firingPotential c d = rawPotential c d := by
    funext w
    exact firingPotential_eq_raw c hc d F hRepReach hFZero w
  rw [hp]
  unfold positiveEndpointContribution heightEndpointSum tailContribution
    headContribution
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hZero : d.length e = 0
  · simp [hZero]
  · have hRise : d.coreRise (rawPotential c d) e =
        (rawHeight c d (d.core.tail e) : ℤ) -
          (rawHeight c d (d.core.head e) : ℤ) := by
      unfold DegSpec.coreRise rawPotential
      ring
    simp [hZero, hRise]

/-! ### The per-vertex coefficient of the local residual

The six vertices of the picture are `armChipA c`, `armChipB c`, the hub `2`,
`banChip c`, the centre `c` and the hub `3`; on each handle these are six
distinct vertices, and every other vertex sits at height zero with no displaced
chip. -/

/-- Expanded coefficients after adding the banana-tail height endpoint sum to the allocated
weight, separated by the six distinguished vertices of the configuration. -/
def bananaCoefficient (c : Fin 8) (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = armChipA c then
    positiveChip (d.length (armSlotA c)) +
      fwd.head (d.length (armSlotA c)) (armHeight c d) 0
  else if v = armChipB c then
    positiveChip (d.length (armSlotB c)) +
      fwd.head (d.length (armSlotB c)) (armHeight c d) 0
  else if v = 2 then
    zeroChip (d.length (armSlotA c)) + zeroChip (d.length (armSlotB c)) -
      shiftWeight c d +
      (fwd.tail (d.length (armSlotA c)) (armHeight c d) 0 +
        fwd.tail (d.length (armSlotB c)) (armHeight c d) 0 +
        fwd.tail (d.length (midSlot c)) (armHeight c d) (midHeight c d))
  else if v = banChip c then
    1 + shiftWeight c d +
      (fwd.head (d.length (midSlot c)) (armHeight c d) (midHeight c d) +
        fwd.tail (d.length (banSlotP c)) (midHeight c d) (endHeight c d) +
        fwd.tail (d.length (banSlotQ c)) (midHeight c d) (endHeight c d))
  else if v = c then
    zeroChip (d.length (tailSlot c)) +
      (fwd.head (d.length (banSlotP c)) (midHeight c d) (endHeight c d) +
        fwd.head (d.length (banSlotQ c)) (midHeight c d) (endHeight c d) +
        (tailLedger c).tail (d.length (tailSlot c)) (endHeight c d) 0)
  else if v = 3 then
    positiveChip (d.length (tailSlot c)) +
      (tailLedger c).head (d.length (tailSlot c)) (endHeight c d) 0
  else 0

/-! The endpoint bookkeeping is a single kernel-level computation on each
handle.  It is stated three times, once per centre, only so that each of the
three `fin_cases` sweeps gets its own elaboration budget. -/

theorem bananaCoefficient_eq_one (d : DegSpec 8 12)
    (hCore : d.core = row06Core) (v : Fin 8) :
    allocatedWeight 1 d v + heightEndpointSum d (rawHeight 1 d) v =
      bananaCoefficient 1 d v := by
  fin_cases v
  all_goals
    simp +decide [heightEndpointSum, bananaCoefficient, allocatedWeight,
      transferWeight, indicatorWeight, chipWeight, shiftWeight, rawHeight,
      armSlotA, armSlotB, midSlot, banSlotP, banSlotQ, tailSlot, banChip,
      tailLedger, armMin, parMin, armHeight, midHeight, endHeight,
      ConfigurationThreeChain.forward, fwd, positiveChip, zeroChip, hCore,
      row06Core, Fin.sum_univ_succ, reduceIte]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals ring

theorem bananaCoefficient_eq_five (d : DegSpec 8 12)
    (hCore : d.core = row06Core) (v : Fin 8) :
    allocatedWeight 5 d v + heightEndpointSum d (rawHeight 5 d) v =
      bananaCoefficient 5 d v := by
  fin_cases v
  all_goals
    simp +decide [heightEndpointSum, bananaCoefficient, allocatedWeight,
      transferWeight, indicatorWeight, chipWeight, shiftWeight, rawHeight,
      armSlotA, armSlotB, midSlot, banSlotP, banSlotQ, tailSlot, banChip,
      tailLedger, armMin, parMin, armHeight, midHeight, endHeight,
      ConfigurationThreeChain.forward, ConfigurationThreeChain.reverse, fwd,
      rev, positiveChip, zeroChip, hCore, row06Core, Fin.sum_univ_succ,
      reduceIte]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals ring

theorem bananaCoefficient_eq_six (d : DegSpec 8 12)
    (hCore : d.core = row06Core) (v : Fin 8) :
    allocatedWeight 6 d v + heightEndpointSum d (rawHeight 6 d) v =
      bananaCoefficient 6 d v := by
  fin_cases v
  all_goals
    simp +decide [heightEndpointSum, bananaCoefficient, allocatedWeight,
      transferWeight, indicatorWeight, chipWeight, shiftWeight, rawHeight,
      armSlotA, armSlotB, midSlot, banSlotP, banSlotQ, tailSlot, banChip,
      tailLedger, armMin, parMin, armHeight, midHeight, endHeight,
      ConfigurationThreeChain.forward, fwd, positiveChip, zeroChip, hCore,
      row06Core, Fin.sum_univ_succ, reduceIte]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals ring

theorem bananaCoefficient_eq (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (hCore : d.core = row06Core) (v : Fin 8) :
    allocatedWeight c d v + heightEndpointSum d (rawHeight c d) v =
      bananaCoefficient c d v := by
  rcases (isBananaCenter_iff c).mp hc with rfl | rfl | rfl
  · exact bananaCoefficient_eq_one d hCore v
  · exact bananaCoefficient_eq_five d hCore v
  · exact bananaCoefficient_eq_six d hCore v

/-! ### The local residual at the centre -/

/-- On each handle the six displayed vertices are distinct, so the branches of
`bananaCoefficient` do not interfere. -/
theorem picture_vertices_distinct (c : Fin 8) (hc : isBananaCenter c = true) :
    armChipA c ≠ armChipB c ∧ armChipA c ≠ 2 ∧ armChipA c ≠ banChip c ∧
      armChipA c ≠ c ∧ armChipA c ≠ 3 ∧
    armChipB c ≠ 2 ∧ armChipB c ≠ banChip c ∧ armChipB c ≠ c ∧
      armChipB c ≠ 3 ∧
    (2 : Fin 8) ≠ banChip c ∧ (2 : Fin 8) ≠ c ∧ (2 : Fin 8) ≠ 3 ∧
    banChip c ≠ c ∧ banChip c ≠ 3 ∧ c ≠ (3 : Fin 8) := by
  rcases (isBananaCenter_iff c).mp hc with rfl | rfl | rfl <;> decide

theorem bananaResidual_nonneg (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (v : Fin 8) :
    0 ≤ bananaCoefficient c d v - indicatorWeight v (targetOwner c d) := by
  obtain ⟨hAB, hA2, hAd, hAc, hA3, hB2, hBd, hBc, hB3, h2d, h2c, h23,
    hdc, hd3, hc3⟩ := picture_vertices_distinct c hc
  have hm : armMin c d =
    min (d.length (armSlotA c)) (d.length (armSlotB c)) := rfl
  have hpq : parMin c d =
    min (d.length (banSlotP c)) (d.length (banSlotQ c)) := rfl
  have hE : endHeight c d =
      min (d.length (tailSlot c))
        (armMin c d + d.length (midSlot c) + parMin c d) := rfl
  have hD : midHeight c d =
      min (endHeight c d) (armMin c d + d.length (midSlot c)) := rfl
  have hC : armHeight c d = min (midHeight c d) (armMin c d) := rfl
  have hshift : shiftWeight c d =
      if d.length (midSlot c) = 0 ∧ midHeight c d < endHeight c d then 1
        else 0 := rfl
  have hCla : armHeight c d ≤ 0 + d.length (armSlotA c) := by omega
  have hClb : armHeight c d ≤ 0 + d.length (armSlotB c) := by omega
  have hEu : endHeight c d ≤ 0 + d.length (tailSlot c) := by omega
  have hOwner : targetOwner c d =
      if parMin c d = 0 ∧
        armMin c d + d.length (midSlot c) < d.length (tailSlot c)
      then banChip c else c := rfl
  have hkBan : indicatorWeight (banChip c) (targetOwner c d) =
      if parMin c d = 0 ∧
        armMin c d + d.length (midSlot c) < d.length (tailSlot c) then 1
      else 0 := by
    by_cases hP : parMin c d = 0 ∧
      armMin c d + d.length (midSlot c) < d.length (tailSlot c) <;>
      simp [indicatorWeight, hOwner, hP, hdc]
  have hkCen : indicatorWeight c (targetOwner c d) =
      if parMin c d = 0 ∧
        armMin c d + d.length (midSlot c) < d.length (tailSlot c) then 0
      else 1 := by
    by_cases hP : parMin c d = 0 ∧
      armMin c d + d.length (midSlot c) < d.length (tailSlot c) <;>
      simp [indicatorWeight, hOwner, hP, Ne.symm hdc]
  have hkOff : ∀ w : Fin 8, w ≠ banChip c → w ≠ c →
      indicatorWeight w (targetOwner c d) = 0 := by
    intro w h1 h2
    by_cases hP : parMin c d = 0 ∧
      armMin c d + d.length (midSlot c) < d.length (tailSlot c) <;>
      simp [indicatorWeight, hOwner, hP, h1, h2]
  by_cases hvA : v = armChipA c
  · have hcoef : bananaCoefficient c d v =
        positiveChip (d.length (armSlotA c)) +
          fwd.head (d.length (armSlotA c)) (armHeight c d) 0 := by
      unfold bananaCoefficient
      rw [if_pos hvA]
    rw [hcoef, hvA, hkOff _ hAd hAc]
    have h := leaf_nonneg fwd (L := d.length (armSlotA c))
      (hu := armHeight c d) (hv := 0) (Nat.zero_le _) hCla
    omega
  by_cases hvB : v = armChipB c
  · have hcoef : bananaCoefficient c d v =
        positiveChip (d.length (armSlotB c)) +
          fwd.head (d.length (armSlotB c)) (armHeight c d) 0 := by
      unfold bananaCoefficient
      rw [if_neg hvA, if_pos hvB]
    rw [hcoef, hvB, hkOff _ hBd hBc]
    have h := leaf_nonneg fwd (L := d.length (armSlotB c))
      (hu := armHeight c d) (hv := 0) (Nat.zero_le _) hClb
    omega
  by_cases hv2 : v = 2
  · have hcoef : bananaCoefficient c d v =
        zeroChip (d.length (armSlotA c)) + zeroChip (d.length (armSlotB c)) -
          shiftWeight c d +
          (fwd.tail (d.length (armSlotA c)) (armHeight c d) 0 +
            fwd.tail (d.length (armSlotB c)) (armHeight c d) 0 +
            fwd.tail (d.length (midSlot c)) (armHeight c d)
              (midHeight c d)) := by
      unfold bananaCoefficient
      rw [if_neg hvA, if_neg hvB, if_pos hv2]
    rw [hcoef, hv2, hkOff _ h2d h2c]
    have h := armCenter_nonneg fwd fwd fwd
      (la := d.length (armSlotA c)) (lb := d.length (armSlotB c))
      (w := d.length (midSlot c)) (p := d.length (banSlotP c))
      (q := d.length (banSlotQ c)) (u := d.length (tailSlot c))
      (m := armMin c d) (pq := parMin c d) (C := armHeight c d)
      (D := midHeight c d) (E := endHeight c d)
      (shiftWeight c d) hm hpq hE hD hC hshift
    omega
  by_cases hvd : v = banChip c
  · have hcoef : bananaCoefficient c d v =
        1 + shiftWeight c d +
          (fwd.head (d.length (midSlot c)) (armHeight c d) (midHeight c d) +
            fwd.tail (d.length (banSlotP c)) (midHeight c d) (endHeight c d) +
            fwd.tail (d.length (banSlotQ c)) (midHeight c d)
              (endHeight c d)) := by
      unfold bananaCoefficient
      rw [if_neg hvA, if_neg hvB, if_neg hv2, if_pos hvd]
    rw [hcoef, hvd, hkBan]
    have h := bananaChip_nonneg fwd fwd fwd
      (la := d.length (armSlotA c)) (lb := d.length (armSlotB c))
      (w := d.length (midSlot c)) (p := d.length (banSlotP c))
      (q := d.length (banSlotQ c)) (u := d.length (tailSlot c))
      (m := armMin c d) (pq := parMin c d) (C := armHeight c d)
      (D := midHeight c d) (E := endHeight c d)
      (shiftWeight c d)
      (if parMin c d = 0 ∧
        armMin c d + d.length (midSlot c) < d.length (tailSlot c) then 1
        else 0)
      hm hpq hE hD hC hshift
      (by split_ifs <;> norm_num)
      (by
        intro hk
        by_cases hP : parMin c d = 0 ∧
          armMin c d + d.length (midSlot c) < d.length (tailSlot c)
        · exact hP.1
        · rw [if_neg hP] at hk; norm_num at hk)
    omega
  by_cases hvc : v = c
  · have hcoef : bananaCoefficient c d v =
        zeroChip (d.length (tailSlot c)) +
          (fwd.head (d.length (banSlotP c)) (midHeight c d) (endHeight c d) +
            fwd.head (d.length (banSlotQ c)) (midHeight c d) (endHeight c d) +
            (tailLedger c).tail (d.length (tailSlot c)) (endHeight c d) 0) := by
      unfold bananaCoefficient
      rw [if_neg hvA, if_neg hvB, if_neg hv2, if_neg hvd, if_pos hvc]
    rw [hcoef, hvc, hkCen]
    have h := center_nonneg fwd fwd (tailLedger c)
      (la := d.length (armSlotA c)) (lb := d.length (armSlotB c))
      (w := d.length (midSlot c)) (p := d.length (banSlotP c))
      (q := d.length (banSlotQ c)) (u := d.length (tailSlot c))
      (m := armMin c d) (pq := parMin c d) (C := armHeight c d)
      (D := midHeight c d) (E := endHeight c d)
      (if parMin c d = 0 ∧
        armMin c d + d.length (midSlot c) < d.length (tailSlot c) then 0
        else 1)
      hm hpq hE hD hC
      (by split_ifs <;> norm_num)
      (by
        intro hk
        by_cases hP : parMin c d = 0 ∧
          armMin c d + d.length (midSlot c) < d.length (tailSlot c)
        · rw [if_pos hP] at hk; norm_num at hk
        · exact hP)
    omega
  by_cases hv3 : v = 3
  · have hcoef : bananaCoefficient c d v =
        positiveChip (d.length (tailSlot c)) +
          (tailLedger c).head (d.length (tailSlot c)) (endHeight c d) 0 := by
      unfold bananaCoefficient
      rw [if_neg hvA, if_neg hvB, if_neg hv2, if_neg hvd, if_neg hvc,
        if_pos hv3]
    rw [hcoef, hv3, hkOff _ (Ne.symm hd3) (Ne.symm hc3)]
    have h := leaf_nonneg (tailLedger c) (L := d.length (tailSlot c))
      (hu := endHeight c d) (hv := 0) (Nat.zero_le _) hEu
    omega
  · have hcoef : bananaCoefficient c d v = 0 := by
      unfold bananaCoefficient
      rw [if_neg hvA, if_neg hvB, if_neg hv2, if_neg hvd, if_neg hvc,
        if_neg hv3]
    rw [hcoef, hkOff v hvd hvc]
    norm_num

theorem localResidual_nonneg (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (hCore : d.core = row06Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row06Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (v : Fin 8) :
    0 ≤ allocatedWeight c d v - indicatorWeight v (targetOwner c d) +
      positiveEndpointContribution d (firingPotential c d) v := by
  rw [positiveEndpointContribution_eq_heightForm c hc d F hRepReach hFZero v]
  have hEq := bananaCoefficient_eq c hc d hCore v
  have hRes := bananaResidual_nonneg c hc d v
  omega

theorem residual_effective (c : Fin 8) (hc : isBananaCenter c = true)
    (d : DegSpec 8 12) (hCore : d.core = row06Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row06Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) :
    effective (rowDivisor d - oneChip (d.coreVertex c) +
      prin d.graph (d.interpolatedScript (firingPotential c d))) := by
  have hInv : d.RepInvariant (firingPotential c d) :=
    firingPotential_repInvariant c d
  intro vertex
  rcases vertex with coreClass | interior
  · obtain ⟨r, hr⟩ := coreClass
    have hVertex : (Sum.inl ⟨r, hr⟩ : d.Vertex) = d.coreVertex r := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hr.symm
    rw [hVertex]
    change 0 ≤ rowDivisor d (d.coreVertex r) -
      oneChip (G := d.graph) (d.coreVertex c) (d.coreVertex r) +
      prin d.graph (d.interpolatedScript (firingPotential c d)) (d.coreVertex r)
    rw [rowDivisor, d.coreClassDivisor_coreVertex]
    rw [← allocated_class_sum_eq c hc d hCore r]
    rw [← positiveEndpointContribution_classSum_eq d (firingPotential c d)
      hInv r]
    have hOwner := targetOwner_rep_eq_center c hc d hCore
    have hIndicator := sum_indicatorWeight_class d (targetOwner c d) r
    have hOneChip :
        oneChip (G := d.graph) (d.coreVertex c) (d.coreVertex r) =
          ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
            indicatorWeight v (targetOwner c d) := by
      rw [hIndicator]
      simp only [oneChip, d.coreVertex_eq_iff]
      rw [hOwner]
      simp only [eq_comm]
    rw [hOneChip]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro v _hv
    simpa [sub_eq_add_neg, add_assoc] using
      localResidual_nonneg c hc d hCore F hRepReach hFZero v
  · obtain ⟨edge, offset⟩ := interior
    change 0 ≤ rowDivisor d (d.interiorVertex edge offset) -
      oneChip (G := d.graph) (d.coreVertex c)
        (d.interiorVertex edge offset) +
      prin d.graph (d.interpolatedScript (firingPotential c d))
        (d.interiorVertex edge offset)
    rw [rowDivisor, d.coreClassDivisor_interiorVertex]
    have hNe : d.coreVertex c ≠ d.interiorVertex edge offset := by
      simp [DegSpec.coreVertex, DegSpec.interiorVertex]
    simp only [oneChip, if_neg hNe.symm, zero_sub, neg_zero, zero_add]
    exact d.prin_interpolatedScript_interiorVertex_nonneg hInv edge offset

/-! ## The guarding set -/

/-- The tripod table and the three banana centres between them name every
chip-free vertex. -/
theorem centers_cover : ∀ v : Fin 8, ¬ IsChipVertex v →
    isCenter v = true ∨ isBananaCenter v = true := by decide

/-- **Row 06 as a guarding set.**  Chips on `0, 3, 4, 7`; the hub `2` guarded by
AR's second picture and the three banana far ends by AR's sixth. -/
def row06Guard : GuardingSet row06Core where
  chips := chipWeight
  chips_nonneg := chipWeight_nonneg
  chips_deg := sum_chipWeight
  guard := by
    intro v hv d hCore hRepReach
    have hNotChip : ¬ IsChipVertex v := by
      by_cases h : IsChipVertex v
      · simp [chipWeight, h] at hv
      · exact h
    show Reaches d.graph (rowDivisor d) (d.coreVertex v)
    rcases centers_cover v hNotChip with hTripod | hBanana
    · have h := row06TripodConfig.reaches_center d hCore (zeroSlots d.length)
        hRepReach hTripod
      rw [← rowDivisor_eq_tripodConfig] at h
      exact h
    · exact (DharMove.ofScript (d.interpolatedScript (firingPotential v d))
        (residual_effective v hBanana d hCore (zeroSlots d.length) hRepReach
          (mem_zeroSlots d.length))).reaches

/-- **AR configurations 2 and 6 on row 06**, valid simultaneously on the open
cell and every nonloopy forest face.  The closing step is
`GuardingSet.closedConstruction`; nothing row-specific happens after the four
pictures are named. -/
theorem row06_closedConstruction :
    ClosedSubdivisionDharConstruction row06Core (by norm_num) :=
  row06Guard.closedConstruction (by norm_num) row06_connected

end AtanasovRanganathan.GenusFiveRow06
