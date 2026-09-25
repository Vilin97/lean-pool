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
# The Atanasov--Ranganathan construction on row 14

Row 14 is `K₃,₃` with the edge `0--1` deleted and replaced by the path
`0 -- 6 == 7 -- 1`, whose middle step is a banana.  The bipartition of the
`K₃,₃` part is `{0,3,5}` against `{2,1,4}`.

Put one chip on each of `0, 3, 5, 7`.  This is exactly the divisor
Atanasov--Ranganathan display for this family (Figure 8 scope 14; the
straightforward-cases figure marks `a = 0`, `d = 3`, `f = 5`, `h = 7` as the
chip vertices), and exactly the divisor of the generated fixed cover.  The
chip-free vertices are `1, 2, 4, 6`, and the paper's own edge patterns split
them as:

* dashed -- vertex `2`, whose three slots end on the chips `0, 3, 5`;
* dotted -- vertex `4`, whose three slots end on the chips `5, 0, 3`;
* plain  -- vertices `1` and `6`, forming AR's *sixth* local picture:
  `3 -- 1 -- 5`, then `1 -- 7`, then the banana `7 == 6`, then `6 -- 0`.

Vertex `1` is read here as a third configuration-2 tripod rather than as the
arm vertex of that sixth picture -- its three slots also end on chips
(`7, 3, 5`) -- which leaves only the far end `6` of the banana to be done by
hand.  So three of the four centres come straight from
`LowGenus/ConfigurationTwo.lean`, and the fourth from
`LowGenus/ConfigurationBananaTail.lean`, which carries
AR's sixth picture generically in the core.

The two families are combined exactly as in `GenusFiveRow12`: each names its
own centres, and between them they cover every chip-free vertex.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow14

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open Guarding
open GenusFiveCoreAtlas
open ConfigurationFive
open ConfigurationBananaTail

/-! ## The divisor -/

/-- The four guarding-set chip vertices 0, 3, 5, and 7 of row 14. -/
def IsChipVertex (v : Fin 8) : Prop :=
  v = 0 ∨ v = 3 ∨ v = 5 ∨ v = 7

instance (v : Fin 8) : Decidable (IsChipVertex v) := by
  unfold IsChipVertex
  infer_instance

/-- Indicator weight placing one chip at each guarding-set vertex. -/
def chipWeight (v : Fin 8) : ℤ := if IsChipVertex v then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  by_cases hv : IsChipVertex v <;> simp [chipWeight, hv]

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 4 := by decide

/-- The row-14 graph divisor obtained by pushing the four guarding-set chips to their core
equivalence classes. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  d.coreClassDivisor chipWeight

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  d.coreClassDivisor_effective chipWeight chipWeight_nonneg

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, d.deg_coreClassDivisor, sum_chipWeight]

/-! ## The three configuration-2 tripods -/

/-- The chip-free vertices all of whose slots end on a chip. -/
def isCenter : Fin 8 → Bool
  | 1 | 2 | 4 => true
  | _ => false

/-- First tripod arm at centres 1, 2, and 4, respectively slots 1, 4, and 8; other inputs use
zero. -/
def firstArm : Fin 8 → Fin 12
  | 1 => 1
  | 2 => 4
  | 4 => 8
  | _ => 0

/-- Second tripod arm at centres 1, 2, and 4, respectively slots 6, 5, and 9; other inputs use
zero. -/
def secondArm : Fin 8 → Fin 12
  | 1 => 6
  | 2 => 5
  | 4 => 9
  | _ => 0

/-- Third tripod arm at centres 1, 2, and 4, respectively slots 7, 10, and 11; other inputs use
zero. -/
def thirdArm : Fin 8 → Fin 12
  | 1 => 7
  | 2 => 10
  | 4 => 11
  | _ => 0

/-- Chip at the end of the first tripod arm for centres 1, 2, and 4, respectively vertices 7, 0,
and 5. -/
def firstChip : Fin 8 → Fin 8
  | 1 => 7
  | 2 => 0
  | 4 => 5
  | _ => 0

/-- Chip at the end of the second tripod arm for centres 1, 2, and 4, respectively vertices 3,
3, and 0. -/
def secondChip : Fin 8 → Fin 8
  | 1 => 3
  | 2 => 3
  | 4 => 0
  | _ => 0

/-- Chip at the end of the third tripod arm for centres 1, 2, and 4, respectively vertices 5, 5,
and 3. -/
def thirdChip : Fin 8 → Fin 8
  | 1 => 5
  | 2 => 5
  | 4 => 3
  | _ => 0

/-- The one chip each tripod centre does not touch. -/
def spareChip : Fin 8 → Fin 8
  | 1 => 0
  | 2 => 7
  | 4 => 7
  | _ => 0

/-- Row 14 read as three AR configuration-2 pictures. -/
def row14TripodConfig : ConfigurationTwo.ConfigTwo where
  core := row14Core
  chipOne := 0
  chipTwo := 3
  chipThree := 5
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
    fin_cases v <;>
      simp only [isCenter, Fin.zero_eta, Fin.isValue, Bool.false_eq_true, Fin.mk_one, firstChip,
        secondChip, thirdChip, spareChip, Fin.reduceFinMk, add_left_inj] at hv ⊢<;>
      ring

/-- The class-sum form of the displayed divisor agrees with the four-chip
form the configuration-2 family uses. -/
theorem rowDivisor_eq_tripodConfig (d : DegSpec 8 12) :
    rowDivisor d = row14TripodConfig.divisor d := by
  classical
  funext vertex
  rcases vertex with coreClass | interior
  · obtain ⟨r, hr⟩ := coreClass
    have hVertex : (Sum.inl ⟨r, hr⟩ : d.Vertex) = d.coreVertex r := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hr.symm
    rw [hVertex, rowDivisor, d.coreClassDivisor_coreVertex,
      row14TripodConfig.divisor_coreVertex_eq d r]
    rw [Finset.sum_filter]
    simp only [show row14TripodConfig.chipOne = 0 from rfl,
      show row14TripodConfig.chipTwo = 3 from rfl,
      show row14TripodConfig.chipThree = 5 from rfl,
      show row14TripodConfig.chipFour = 7 from rfl]
    simp only [chipWeight, IsChipVertex, Fin.isValue, Fin.sum_univ_succ, Fin.reduceEq, or_self,
      or_false, ↓reduceIte, Fin.succ_ne_zero, false_or, Fin.succ_zero_eq_one, ite_self,
      Fin.succ_one_eq_two, Fin.reduceSucc, or_true, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, zero_add, ConfigurationTwo.chipInd]
    ring
  · obtain ⟨edge, offset⟩ := interior
    have hVertex : (Sum.inr ⟨edge, offset⟩ : d.Vertex) =
        d.interiorVertex edge offset := rfl
    rw [hVertex, rowDivisor, d.coreClassDivisor_interiorVertex,
      row14TripodConfig.divisor_interiorVertex_eq_zero d edge offset]

/-! ## The nested-min heights of AR's sixth picture at vertex `6`

`la = |3--1|` and `lb = |1--5|` are the two arms, `w = |7--1|` the middle
slot, `p, q = |7--6|` the banana, and `u = |0--6|` the tail slot. -/

/-- The shorter external arm of the banana-tail configuration, the minimum of lengths 6 and 7. -/
def armMin (d : DegSpec 8 12) : ℕ := min (d.length 6) (d.length 7)

/-- The shorter parallel banana slot, the minimum of lengths 2 and 3. -/
def parMin (d : DegSpec 8 12) : ℕ := min (d.length 2) (d.length 3)

/-- The height at the centre `6`. -/
def endHeight (d : DegSpec 8 12) : ℕ :=
  min (d.length 0) (armMin d + d.length 1 + parMin d)

/-- The height at the chip `7` at the near end of the banana. -/
def midHeight (d : DegSpec 8 12) : ℕ :=
  min (endHeight d) (armMin d + d.length 1)

/-- The height at the chip-free arm vertex `1`. -/
def armHeight (d : DegSpec 8 12) : ℕ := min (midHeight d) (armMin d)

/-- Unquotiented banana-tail height: arm height at vertex 1, middle height at vertex 7, end
height at vertex 6, and zero elsewhere. -/
def rawHeight (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 1 then armHeight d
  else if v = 7 then midHeight d
  else if v = 6 then endHeight d
  else 0

/-- Integer-valued firing potential given by the negative of the unquotiented banana-tail
height. -/
def rawPotential (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  -(rawHeight d v : ℤ)

/-- Reading the raw profile at the canonical representative makes class
invariance definitional. -/
def firingPotential (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  rawPotential d (d.rep v)

theorem firingPotential_repInvariant (d : DegSpec 8 12) :
    d.RepInvariant (firingPotential d) := by
  intro v
  simp [firingPotential, d.rep_idem]

theorem rawHeight_eq_of_zero_edge (d : DegSpec 8 12) (e : Fin 12) :
    d.length e = 0 →
      rawHeight d (row14Core.tail e) = rawHeight d (row14Core.head e) := by
  fin_cases e
  all_goals
    simp [rawHeight, armHeight, midHeight, endHeight, armMin, parMin,
      row14Core]
  all_goals omega

theorem rawPotential_eq_of_zero_edge (d : DegSpec 8 12) {e : Fin 12}
    (hZero : d.length e = 0) :
    rawPotential d (row14Core.tail e) = rawPotential d (row14Core.head e) := by
  rw [rawPotential, rawPotential, rawHeight_eq_of_zero_edge d e hZero]

theorem rawPotential_eq_of_reach
    (d : DegSpec 8 12) (F : Finset (Fin 12))
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0)
    {u v : Fin 8} (hReach : ReachIn row14Core F u v) :
    rawPotential d u = rawPotential d v := by
  induction hReach with
  | refl => rfl
  | @tail a b hPrefix hLast ih =>
      rw [ih]
      obtain ⟨e, he, hab | hab⟩ := hLast
      · rw [← hab.1, ← hab.2]
        exact rawPotential_eq_of_zero_edge d
          ((hFZero e).mp ((mem_edgeList F e).mp he))
      · rw [← hab.1, ← hab.2]
        exact (rawPotential_eq_of_zero_edge d
          ((hFZero e).mp ((mem_edgeList F e).mp he))).symm

theorem firingPotential_eq_raw
    (d : DegSpec 8 12) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row14Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (v : Fin 8) :
    firingPotential d v = rawPotential d v := by
  apply rawPotential_eq_of_reach d F hFZero
  exact (hRepReach (d.rep v) v).mp (d.rep_idem v)

/-! ## Redistributing chips inside contracted classes -/

export ConfigurationCommon (indicatorWeight transferWeight
  sum_transferWeight_eq_zero sum_indicatorWeight_class
  positiveEndpointContribution positiveEndpointContribution_classSum_eq)

/-- The conditional transfer that pays for the two banana chips when the
middle slot has collapsed. -/
def shiftWeight (d : DegSpec 8 12) : ℤ :=
  if d.length 1 = 0 ∧ midHeight d < endHeight d then 1 else 0

/-- The four-chip weight redistributed across contracted arms 6 and 7 and tail 0, with a further
transfer from 1 to 7 across contracted slot 1 when the height comparison requires it. -/
def allocatedWeight (d : DegSpec 8 12) (vertex : Fin 8) : ℤ :=
  chipWeight vertex +
    (if d.length 6 = 0 then transferWeight 3 1 vertex else 0) +
    (if d.length 7 = 0 then transferWeight 5 1 vertex else 0) +
    (if d.length 0 = 0 then transferWeight 0 6 vertex else 0) +
    (if d.length 1 = 0 ∧ midHeight d < endHeight d then
      transferWeight 1 7 vertex else 0)

theorem allocated_class_sum_eq
    (d : DegSpec 8 12) (hCore : d.core = row14Core) (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocatedWeight d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  have hArmOne : d.length 6 = 0 → d.rep 3 = d.rep 1 := by
    intro hZero
    have h := d.rep_zero 6 hZero
    simpa [hCore, row14Core] using h
  have hArmTwo : d.length 7 = 0 → d.rep 5 = d.rep 1 := by
    intro hZero
    have h := d.rep_zero 7 hZero
    simpa [hCore, row14Core] using h.symm
  have hTail : d.length 0 = 0 → d.rep 0 = d.rep 6 := by
    intro hZero
    have h := d.rep_zero 0 hZero
    simpa [hCore, row14Core] using h
  have hShift : (d.length 1 = 0 ∧ midHeight d < endHeight d) →
      d.rep 1 = d.rep 7 := by
    intro hZero
    have h := d.rep_zero 1 hZero.1
    simpa [hCore, row14Core] using h.symm
  have hConditional (P : Prop) [Decidable P] (source target : Fin 8)
      (hRep : P → d.rep source = d.rep target) :
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
          (if P then transferWeight source target v else 0) = 0 := by
    by_cases hP : P
    · simp only [ite_eq_left hP]
      exact sum_transferWeight_eq_zero d (hRep hP) r
    · simp [hP]
  simp only [allocatedWeight, Finset.sum_add_distrib]
  rw [hConditional _ _ _ hArmOne, hConditional _ _ _ hArmTwo,
    hConditional _ _ _ hTail, hConditional _ _ _ hShift]
  simp

/-! ## Which vertex of the centre's class carries the delivered chip -/

/-- Target representative for centre 6: choose vertex 7 when a parallel slot contracts and the
tail is longer than the shorter arm plus middle slot 1; choose vertex 6 otherwise. -/
def targetOwner (d : DegSpec 8 12) : Fin 8 :=
  if parMin d = 0 ∧ armMin d + d.length 1 < d.length 0 then 7 else 6

theorem targetOwner_rep_eq_center
    (d : DegSpec 8 12) (hCore : d.core = row14Core) :
    d.rep (targetOwner d) = d.rep 6 := by
  unfold targetOwner
  split_ifs with hP
  · have hEither : d.length 2 = 0 ∨ d.length 3 = 0 := by
      have := hP.1
      simp only [parMin, Nat.min_eq_zero_iff] at this
      exact this
    rcases hEither with hZero | hZero
    · have h := d.rep_zero 2 hZero
      simpa [hCore, row14Core] using h
    · have h := d.rep_zero 3 hZero
      simpa [hCore, row14Core] using h
  · rfl

/-! ## Endpoint accounting on the contracted face -/

theorem positiveEndpointContribution_eq_heightForm
    (d : DegSpec 8 12) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row14Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (v : Fin 8) :
    positiveEndpointContribution d (firingPotential d) v =
      ∑ e : Fin 12,
        ((if d.core.tail e = v then
            tailContribution (d.length e) (rawHeight d (d.core.tail e))
              (rawHeight d (d.core.head e)) else 0) +
        (if d.core.head e = v then
            headContribution (d.length e) (rawHeight d (d.core.tail e))
              (rawHeight d (d.core.head e)) else 0)) := by
  have hp : firingPotential d = rawPotential d := by
    funext w
    exact firingPotential_eq_raw d F hRepReach hFZero w
  rw [hp]
  unfold positiveEndpointContribution tailContribution headContribution
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hZero : d.length e = 0
  · simp [hZero]
  · have hRise : d.coreRise (rawPotential d) e =
        (rawHeight d (d.core.tail e) : ℤ) -
          (rawHeight d (d.core.head e) : ℤ) := by
      unfold DegSpec.coreRise rawPotential
      ring
    simp [hZero, hRise]

/-! ## The per-vertex coefficient of the local residual -/

/-- Expanded coefficients of the allocated divisor after the banana-tail height script, with
each incident slot read in its prescribed orientation. -/
def bananaCoefficient (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    positiveChip (d.length 0) + rev.head (d.length 0) (endHeight d) 0
  else if v = 1 then
    zeroChip (d.length 6) + zeroChip (d.length 7) - shiftWeight d +
      (rev.tail (d.length 6) (armHeight d) 0 +
        fwd.tail (d.length 7) (armHeight d) 0 +
        rev.tail (d.length 1) (armHeight d) (midHeight d))
  else if v = 3 then
    positiveChip (d.length 6) + rev.head (d.length 6) (armHeight d) 0
  else if v = 5 then
    positiveChip (d.length 7) + fwd.head (d.length 7) (armHeight d) 0
  else if v = 6 then
    zeroChip (d.length 0) +
      (fwd.head (d.length 2) (midHeight d) (endHeight d) +
        fwd.head (d.length 3) (midHeight d) (endHeight d) +
        rev.tail (d.length 0) (endHeight d) 0)
  else if v = 7 then
    1 + shiftWeight d +
      (rev.head (d.length 1) (armHeight d) (midHeight d) +
        fwd.tail (d.length 2) (midHeight d) (endHeight d) +
        fwd.tail (d.length 3) (midHeight d) (endHeight d))
  else 0

theorem bananaCoefficient_eq
    (d : DegSpec 8 12) (hCore : d.core = row14Core) (v : Fin 8) :
    allocatedWeight d v +
        ∑ edge : Fin 12,
          ((if d.core.tail edge = v then
              tailContribution (d.length edge)
                (rawHeight d (d.core.tail edge))
                (rawHeight d (d.core.head edge)) else 0) +
          (if d.core.head edge = v then
              headContribution (d.length edge)
                (rawHeight d (d.core.tail edge))
                (rawHeight d (d.core.head edge)) else 0)) =
      bananaCoefficient d v := by
  fin_cases v
  all_goals
    simp +decide [bananaCoefficient, allocatedWeight, transferWeight,
      indicatorWeight, chipWeight, shiftWeight, rawHeight,
      ConfigurationThreeChain.forward, ConfigurationThreeChain.reverse, fwd, rev,
      positiveChip, zeroChip, hCore, row14Core, Fin.sum_univ_succ, reduceIte]
  all_goals (try (first | ring1 | ring_nf))
  all_goals (try split_ifs)
  all_goals ring


/-! ## The local residual at the centre `6` -/

theorem bananaResidual_nonneg (d : DegSpec 8 12) (v : Fin 8) :
    0 ≤ bananaCoefficient d v - indicatorWeight v (targetOwner d) := by
  have hm : armMin d = min (d.length 6) (d.length 7) := rfl
  have hpq : parMin d = min (d.length 2) (d.length 3) := rfl
  have hE : endHeight d =
      min (d.length 0) (armMin d + d.length 1 + parMin d) := rfl
  have hD : midHeight d = min (endHeight d) (armMin d + d.length 1) := rfl
  have hC : armHeight d = min (midHeight d) (armMin d) := rfl
  have hshift : shiftWeight d =
      if d.length 1 = 0 ∧ midHeight d < endHeight d then 1 else 0 := rfl
  have hCla : armHeight d ≤ 0 + d.length 6 := by omega
  have hClb : armHeight d ≤ 0 + d.length 7 := by omega
  have hEu : endHeight d ≤ 0 + d.length 0 := by omega
  have hOwner : targetOwner d =
      if parMin d = 0 ∧ armMin d + d.length 1 < d.length 0 then 7 else 6 := rfl
  have hkSix : indicatorWeight (6 : Fin 8) (targetOwner d) =
      if parMin d = 0 ∧ armMin d + d.length 1 < d.length 0 then 0 else 1 := by
    by_cases hP : parMin d = 0 ∧ armMin d + d.length 1 < d.length 0 <;>
      simp [indicatorWeight, hOwner, hP]
  have hkSeven : indicatorWeight (7 : Fin 8) (targetOwner d) =
      if parMin d = 0 ∧ armMin d + d.length 1 < d.length 0 then 1 else 0 := by
    by_cases hP : parMin d = 0 ∧ armMin d + d.length 1 < d.length 0 <;>
      simp [indicatorWeight, hOwner, hP]
  have hkOff : ∀ w : Fin 8, w ≠ 6 → w ≠ 7 →
      indicatorWeight w (targetOwner d) = 0 := by
    intro w h1 h2
    by_cases hP : parMin d = 0 ∧ armMin d + d.length 1 < d.length 0 <;>
      simp [indicatorWeight, hOwner, hP, h1, h2]
  clear hOwner
  fin_cases v
  · show (0:ℤ) ≤ bananaCoefficient d 0 -
        indicatorWeight (0 : Fin 8) (targetOwner d)
    have hc : bananaCoefficient d 0 = positiveChip (d.length 0) +
        rev.head (d.length 0) (endHeight d) 0 := rfl
    rw [hc, hkOff 0 (by decide) (by decide)]
    have h := leaf_nonneg rev (L := d.length 0) (hu := endHeight d) (hv := 0)
      (Nat.zero_le _) hEu
    omega
  · show (0:ℤ) ≤ bananaCoefficient d 1 -
        indicatorWeight (1 : Fin 8) (targetOwner d)
    have hc : bananaCoefficient d 1 =
        zeroChip (d.length 6) + zeroChip (d.length 7) - shiftWeight d +
          (rev.tail (d.length 6) (armHeight d) 0 +
            fwd.tail (d.length 7) (armHeight d) 0 +
            rev.tail (d.length 1) (armHeight d) (midHeight d)) := rfl
    rw [hc, hkOff 1 (by decide) (by decide)]
    have h := armCenter_nonneg rev fwd rev
      (la := d.length 6) (lb := d.length 7) (w := d.length 1)
      (p := d.length 2) (q := d.length 3) (u := d.length 0)
      (m := armMin d) (pq := parMin d) (C := armHeight d)
      (D := midHeight d) (E := endHeight d)
      (shiftWeight d) hm hpq hE hD hC hshift
    omega
  · show (0:ℤ) ≤ bananaCoefficient d 2 -
        indicatorWeight (2 : Fin 8) (targetOwner d)
    have hc : bananaCoefficient d 2 = 0 := rfl
    rw [hc, hkOff 2 (by decide) (by decide)]
    norm_num
  · show (0:ℤ) ≤ bananaCoefficient d 3 -
        indicatorWeight (3 : Fin 8) (targetOwner d)
    have hc : bananaCoefficient d 3 = positiveChip (d.length 6) +
        rev.head (d.length 6) (armHeight d) 0 := rfl
    rw [hc, hkOff 3 (by decide) (by decide)]
    have h := leaf_nonneg rev (L := d.length 6) (hu := armHeight d) (hv := 0)
      (Nat.zero_le _) hCla
    omega
  · show (0:ℤ) ≤ bananaCoefficient d 4 -
        indicatorWeight (4 : Fin 8) (targetOwner d)
    have hc : bananaCoefficient d 4 = 0 := rfl
    rw [hc, hkOff 4 (by decide) (by decide)]
    norm_num
  · show (0:ℤ) ≤ bananaCoefficient d 5 -
        indicatorWeight (5 : Fin 8) (targetOwner d)
    have hc : bananaCoefficient d 5 = positiveChip (d.length 7) +
        fwd.head (d.length 7) (armHeight d) 0 := rfl
    rw [hc, hkOff 5 (by decide) (by decide)]
    have h := leaf_nonneg fwd (L := d.length 7) (hu := armHeight d) (hv := 0)
      (Nat.zero_le _) hClb
    omega
  · show (0:ℤ) ≤ bananaCoefficient d 6 -
        indicatorWeight (6 : Fin 8) (targetOwner d)
    have hc : bananaCoefficient d 6 =
        zeroChip (d.length 0) +
          (fwd.head (d.length 2) (midHeight d) (endHeight d) +
            fwd.head (d.length 3) (midHeight d) (endHeight d) +
            rev.tail (d.length 0) (endHeight d) 0) := rfl
    rw [hc, hkSix]
    have h := center_nonneg fwd fwd rev
      (la := d.length 6) (lb := d.length 7) (w := d.length 1)
      (p := d.length 2) (q := d.length 3) (u := d.length 0)
      (m := armMin d) (pq := parMin d) (C := armHeight d)
      (D := midHeight d) (E := endHeight d)
      (if parMin d = 0 ∧ armMin d + d.length 1 < d.length 0 then 0 else 1)
      hm hpq hE hD hC
      (by split_ifs <;> norm_num)
      (by
        intro hk
        by_cases hP : parMin d = 0 ∧ armMin d + d.length 1 < d.length 0
        · rw [ite_eq_left hP] at hk; norm_num at hk
        · exact hP)
    omega
  · show (0:ℤ) ≤ bananaCoefficient d 7 -
        indicatorWeight (7 : Fin 8) (targetOwner d)
    have hc : bananaCoefficient d 7 =
        1 + shiftWeight d +
          (rev.head (d.length 1) (armHeight d) (midHeight d) +
            fwd.tail (d.length 2) (midHeight d) (endHeight d) +
            fwd.tail (d.length 3) (midHeight d) (endHeight d)) := rfl
    rw [hc, hkSeven]
    have h := bananaChip_nonneg rev fwd fwd
      (la := d.length 6) (lb := d.length 7) (w := d.length 1)
      (p := d.length 2) (q := d.length 3) (u := d.length 0)
      (m := armMin d) (pq := parMin d) (C := armHeight d)
      (D := midHeight d) (E := endHeight d)
      (shiftWeight d)
      (if parMin d = 0 ∧ armMin d + d.length 1 < d.length 0 then 1 else 0)
      hm hpq hE hD hC hshift
      (by split_ifs <;> norm_num)
      (by
        intro hk
        by_cases hP : parMin d = 0 ∧ armMin d + d.length 1 < d.length 0
        · exact hP.1
        · rw [ite_eq_right hP] at hk; norm_num at hk)
    omega

theorem localResidual_nonneg
    (d : DegSpec 8 12) (hCore : d.core = row14Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row14Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) (v : Fin 8) :
    0 ≤ allocatedWeight d v - indicatorWeight v (targetOwner d) +
      positiveEndpointContribution d (firingPotential d) v := by
  rw [positiveEndpointContribution_eq_heightForm d F hRepReach hFZero v]
  have hEq := bananaCoefficient_eq d hCore v
  have hRes := bananaResidual_nonneg d v
  omega

theorem residual_effective
    (d : DegSpec 8 12) (hCore : d.core = row14Core)
    (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn row14Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) :
    effective (rowDivisor d - oneChip (d.coreVertex 6) +
      prin d.graph (d.interpolatedScript (firingPotential d))) := by
  have hInv : d.RepInvariant (firingPotential d) :=
    firingPotential_repInvariant d
  intro vertex
  rcases vertex with coreClass | interior
  · obtain ⟨r, hr⟩ := coreClass
    have hVertex : (Sum.inl ⟨r, hr⟩ : d.Vertex) = d.coreVertex r := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hr.symm
    rw [hVertex]
    change 0 ≤ rowDivisor d (d.coreVertex r) -
      oneChip (G := d.graph) (d.coreVertex 6) (d.coreVertex r) +
      prin d.graph (d.interpolatedScript (firingPotential d)) (d.coreVertex r)
    rw [rowDivisor, d.coreClassDivisor_coreVertex]
    rw [← allocated_class_sum_eq d hCore r]
    rw [← positiveEndpointContribution_classSum_eq d (firingPotential d) hInv r]
    have hOwner := targetOwner_rep_eq_center d hCore
    have hIndicator := sum_indicatorWeight_class d (targetOwner d) r
    have hOneChip :
        oneChip (G := d.graph) (d.coreVertex 6) (d.coreVertex r) =
          ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
            indicatorWeight v (targetOwner d) := by
      rw [hIndicator]
      simp only [oneChip, d.coreVertex_eq_iff]
      rw [hOwner]
      simp only [eq_comm]
    rw [hOneChip]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro v _hv
    simpa [sub_eq_add_neg, add_assoc] using
      localResidual_nonneg d hCore F hRepReach hFZero v
  · obtain ⟨edge, offset⟩ := interior
    change 0 ≤ rowDivisor d (d.interiorVertex edge offset) -
      oneChip (G := d.graph) (d.coreVertex 6)
        (d.interiorVertex edge offset) +
      prin d.graph (d.interpolatedScript (firingPotential d))
        (d.interiorVertex edge offset)
    rw [rowDivisor, d.coreClassDivisor_interiorVertex]
    have hNe : d.coreVertex 6 ≠ d.interiorVertex edge offset := by
      simp [DegSpec.coreVertex, DegSpec.interiorVertex]
    simp only [oneChip, ite_eq_right hNe.symm, zero_sub, neg_zero, zero_add]
    exact d.prin_interpolatedScript_interiorVertex_nonneg hInv edge offset

/-! ## Combining the two families -/

/-- The tripod table and the banana centre between them name every chip-free
vertex. -/
theorem centers_cover : ∀ v : Fin 8, ¬ IsChipVertex v →
    isCenter v = true ∨ v = 6 := by decide

/-- **Row 14 as a guarding set.**  Chips on `0, 3, 5, 7`; the tripod table
covers `1, 2, 4` and the banana tail covers `6`.  The closing step is the
generic `Guarding.GuardingSet.closedConstruction`, exactly as on row 06, whose
decomposition is this one with the multiplicities exchanged. -/
def row14Guard : GuardingSet row14Core where
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
    rcases centers_cover v hNotChip with hTripod | hSix
    · have h := row14TripodConfig.reaches_center d hCore (zeroSlots d.length)
        hRepReach hTripod
      rw [← rowDivisor_eq_tripodConfig] at h
      exact h
    · subst hSix
      exact (DharMove.ofScript (d.interpolatedScript (firingPotential d))
        (residual_effective d hCore (zeroSlots d.length) hRepReach
          (mem_zeroSlots d.length))).reaches

/-- AR configurations 2 and 6 on row 14, valid simultaneously on the open
cell and every nonloopy forest face. -/
theorem row14_closedConstruction :
    ClosedSubdivisionDharConstruction row14Core (by norm_num) :=
  row14Guard.closedConstruction (by norm_num) row14_connected

end AtanasovRanganathan.GenusFiveRow14
