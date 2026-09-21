/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ClosedConstructionTail
import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationCommon
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSeparator

/-!
# Atanasov--Ranganathan configuration 3, generic in the core

Configuration 3 of Atanasov--Ranganathan, Proposition 5.1, is the local
picture at a chip-free *pair* of adjacent core vertices, each of whose two
remaining slots ends on a chip vertex.  Several genus-five rows are covered by
this one picture, and until now each row carried its own verbatim copy of the
calculation against its own lookup tables.

This file states the picture once, as a `ConfigThree` bundle of the lookup
data together with the incidence facts a row must check, and proves the whole
closed-face calculation from those facts alone.  A row supplies the tables and
discharges the `Prop` fields; nothing else.

For a target centre, let `a` and `b` be the shorter arm lengths on the target
and partner sides, and let `m` be the middle-slot length.  We interpolate the
core potentials `-h₁, -h₂`, where

* `h₂ = min a b`, and
* `h₁ = min a (h₂ + m)`.

If `h₁ = a`, a target arm supplies the requested chip.  Otherwise the middle
slot is full and supplies it.  Whenever the partner loses a chip through the
middle slot, `h₂ = b`, so one of its arms replenishes that chip.  This formula
also has `h₁ = h₂` when `m = 0`, which is exactly what is needed on a closed
face where the two centres contract.

## Core size

`ConfigThree n p` is generic in the core size: `n` vertices and `p` slots.
The genus-five atlas instantiates it at `ConfigThree 8 12`; it also supports
the instance `ConfigThree 10 15`. The
whole file is size-free except for `closedConstruction`, which needs `0 < n`
and takes it as a hypothesis, the same one
`Guarding.GuardingSet.closedConstruction` carries.
-/

namespace AtanasovRanganathan.ConfigurationThree

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open ConfigurationCommon

variable {n p : ℕ}

/-! ## Unordered incidence -/

/-- The slot `e` joins `u` and `v`, in either orientation. -/
def Ends (core : Core n p) (e : Fin p) (u v : Fin n) : Prop :=
  (core.tail e = u ∧ core.head e = v) ∨ (core.tail e = v ∧ core.head e = u)

instance (core : Core n p) (e : Fin p) (u v : Fin n) :
    Decidable (Ends core e u v) := by
  unfold Ends
  infer_instance

/-- A slot has one pair of endpoints: two `Ends` readings of the same slot
agree as unordered pairs. -/
theorem Ends.pair_eq {core : Core n p} {e : Fin p} {u v u' v' : Fin n}
    (h : Ends core e u v) (h' : Ends core e u' v') :
    (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  rcases h with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases h' with ⟨ht', hh'⟩ | ⟨ht', hh'⟩
  · exact Or.inl ⟨ht.symm.trans ht', hh.symm.trans hh'⟩
  · exact Or.inr ⟨ht.symm.trans ht', hh.symm.trans hh'⟩
  · exact Or.inr ⟨hh.symm.trans hh', ht.symm.trans ht'⟩
  · exact Or.inl ⟨hh.symm.trans hh', ht.symm.trans ht'⟩

/-- Two slots with different first endpoints are different slots. -/
theorem ne_of_ends_of_ne {core : Core n p} {e f : Fin p} {u a v b : Fin n}
    (he : Ends core e u a) (hf : Ends core f v b) (huv : u ≠ v) (hub : u ≠ b) :
    e ≠ f := by
  rintro rfl
  rcases he.pair_eq hf with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact huv h1
  · exact hub h1

/-- Two slots at the same vertex with different far endpoints are different
slots. -/
theorem ne_of_ends_same {core : Core n p} {e f : Fin p} {u a b : Fin n}
    (he : Ends core e u a) (hf : Ends core f u b) (hab : a ≠ b) (hub : u ≠ b) :
    e ≠ f := by
  rintro rfl
  rcases he.pair_eq hf with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact hab h2
  · exact hub h1

/-! ## Small arithmetic reused from the row-11 step lemmas -/

theorem step_zero {L i : ℕ} (hi : i < L) :
    SubdivisionArithmetic.step L 0 i = 0 :=
  SubdivisionArithmetic.step_zero_of_lt hi

/-- One chip leaves an arm exactly when its ramp has positive height. -/
def drain (height : ℕ) : ℤ := if 0 < height then 1 else 0

theorem drain_bounds (height : ℕ) :
    0 ≤ drain height ∧ drain height ≤ 1 := by
  unfold drain
  split_ifs <;> omega

theorem drain_eq_one {height : ℕ} (h : 0 < height) : drain height = 1 := by
  simp [drain, h]

theorem drain_eq_zero : drain 0 = 0 := by simp [drain]

theorem indicator_bounds (p : Prop) [Decidable p] :
    0 ≤ (if p then (1 : ℤ) else 0) ∧ (if p then (1 : ℤ) else 0) ≤ 1 := by
  split_ifs <;> omega

theorem firstStep_neg_eq_neg_drain {L height : ℕ}
    (hLength : 0 < L) (hLe : height ≤ L) :
    SubdivisionArithmetic.step L (-(height : ℤ)) 0 = -drain height := by
  rcases Nat.eq_zero_or_pos height with rfl | hHeight
  · simp [drain, step_zero hLength]
  · rw [ConfigurationCommon.firstStep_neg_eq_neg_one hHeight hLe]
    simp [drain, hHeight]

theorem lastStep_pos_eq_drain {L height : ℕ}
    (hLength : 0 < L) (hLe : height ≤ L) :
    SubdivisionArithmetic.step L (height : ℤ) (L - 1) = drain height := by
  rcases Nat.eq_zero_or_pos height with rfl | hHeight
  · simp only [Nat.cast_zero, drain, lt_self_iff_false, ↓reduceIte]
    rw [step_zero (by omega)]
  · rw [ConfigurationCommon.lastStep_pos_eq_one hHeight hLe]
    simp [drain, hHeight]

/-! ## Splitting a slot sum over the finitely many active slots -/

theorem sum_three (g : Fin p → ℤ) {a b c : Fin p}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hzero : ∀ x : Fin p, x ≠ a → x ≠ b → x ≠ c → g x = 0) :
    ∑ x : Fin p, g x = g a + g b + g c := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b, c} : Finset (Fin p)))
    (by
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact hzero x hx.1 hx.2.1 hx.2.2)]
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]
  ring

theorem sum_five (g : Fin p → ℤ) {a b c u v : Fin p}
    (hab : a ≠ b) (hac : a ≠ c) (hau : a ≠ u) (hav : a ≠ v)
    (hbc : b ≠ c) (hbu : b ≠ u) (hbv : b ≠ v)
    (hcu : c ≠ u) (hcv : c ≠ v) (huv : u ≠ v)
    (hzero : ∀ x : Fin p, x ≠ a → x ≠ b → x ≠ c → x ≠ u → x ≠ v → g x = 0) :
    ∑ x : Fin p, g x = g a + g b + g c + g u + g v := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b, c, u, v} : Finset (Fin p)))
    (by
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact hzero x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2)]
  rw [Finset.sum_insert (by simp [hab, hac, hau, hav]),
    Finset.sum_insert (by simp [hbc, hbu, hbv]),
    Finset.sum_insert (by simp [hcu, hcv]),
    Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
  ring

/-! ## One slot's endpoint terms -/

/-- The two endpoint terms one core slot contributes at one core vertex.
This is literally the summand of `ConfigurationCommon.endpointContribution`. -/
def slotTerm (d : DegSpec n p) (potential : Fin n → ℤ) (e : Fin p)
    (v : Fin n) : ℤ :=
  (if d.core.tail e = v then
      SubdivisionArithmetic.step (d.length e) (d.coreRise potential e) 0
    else 0) +
  (if d.core.head e = v then
      -SubdivisionArithmetic.step (d.length e) (d.coreRise potential e)
        (d.length e - 1)
    else 0)

theorem endpointContribution_eq_sum (d : DegSpec n p)
    (potential : Fin n → ℤ) (v : Fin n) :
    ConfigurationCommon.endpointContribution d potential v =
      ∑ e : Fin p, slotTerm d potential e v := rfl

/-- The value of one slot's endpoint terms at a vertex where the potential is
`a` and whose far end carries potential `b`. -/
def slotValue (d : DegSpec n p) (center : Fin n) (e : Fin p) (a b : ℤ) : ℤ :=
  if d.core.tail e = center then
    SubdivisionArithmetic.step (d.length e) (b - a) 0
  else
    -SubdivisionArithmetic.step (d.length e) (a - b) (d.length e - 1)

theorem slotTerm_eq_slotValue (d : DegSpec n p) (potential : Fin n → ℤ)
    {e : Fin p} {center other : Fin n}
    (hEnds : Ends d.core e center other) (hne : other ≠ center) :
    slotTerm d potential e center =
      slotValue d center e (potential center) (potential other) := by
  rcases hEnds with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · simp [slotTerm, slotValue, DegSpec.coreRise, ht, hh, hne]
  · simp [slotTerm, slotValue, DegSpec.coreRise, ht, hh, hne]

/-- Contribution at a centre from one of its arms, whose far endpoint carries
potential zero. -/
def armContribution (d : DegSpec n p) (center : Fin n) (edge : Fin p)
    (height : ℕ) : ℤ :=
  if d.core.tail edge = center then
    SubdivisionArithmetic.step (d.length edge) (height : ℤ) 0
  else
    -SubdivisionArithmetic.step (d.length edge) (-(height : ℤ))
      (d.length edge - 1)

theorem armContribution_eq_slotValue (d : DegSpec n p) (center : Fin n)
    (edge : Fin p) (height : ℕ) :
    armContribution d center edge height =
      slotValue d center edge (-(height : ℤ)) 0 := by
  simp [armContribution, slotValue]

/-- A ramp that goes *down* from the centre never removes a chip there. -/
theorem slotValue_nonneg (d : DegSpec n p) (center : Fin n) (e : Fin p)
    {a b : ℤ} {k : ℕ} (hk : b - a = (k : ℤ))
    (hLength : 0 < d.length e) (hLe : k ≤ d.length e) :
    0 ≤ slotValue d center e a b := by
  rcases Nat.eq_zero_or_pos k with rfl | hPos
  · have h0 : b - a = 0 := by simpa using hk
    have h0' : a - b = 0 := by omega
    unfold slotValue
    split
    · rw [h0, step_zero hLength]
    · rw [h0', step_zero (show d.length e - 1 < d.length e by omega)]
      omega
  · unfold slotValue
    split
    · rw [hk]
      exact ConfigurationCommon.firstStep_pos_nonneg hLength
    · have hneg : a - b = -(k : ℤ) := by omega
      rw [hneg]
      have hSlope := ConfigurationCommon.lastStep_neg_nonpos hPos hLe
      omega

/-- A full-length ramp delivers exactly one chip to the centre. -/
theorem slotValue_eq_one_of_full (d : DegSpec n p) (center : Fin n)
    (e : Fin p) {a b : ℤ} (hFull : b - a = (d.length e : ℤ))
    (hLength : 0 < d.length e) :
    slotValue d center e a b = 1 := by
  have hneg : a - b = -(d.length e : ℤ) := by omega
  unfold slotValue
  split
  · rw [hFull]
    exact ConfigurationCommon.firstStep_full_eq_one hLength
  · rw [hneg]
    have hSlope := ConfigurationCommon.lastStep_neg_full_eq_neg_one hLength
    omega

/-- A ramp that goes *up* from the centre removes exactly one chip there when
its height is positive, and nothing when it is flat. -/
theorem slotValue_eq_neg_drain (d : DegSpec n p) (center : Fin n) (e : Fin p)
    {a b : ℤ} {k : ℕ} (hk : a - b = (k : ℤ))
    (hLength : 0 < d.length e) (hLe : k ≤ d.length e) :
    slotValue d center e a b = -drain k := by
  rcases Nat.eq_zero_or_pos k with rfl | hPos
  · rw [drain_eq_zero, neg_zero]
    have h0 : a - b = 0 := by simpa using hk
    have h0' : b - a = 0 := by omega
    unfold slotValue
    split
    · rw [h0', step_zero hLength]
    · rw [h0, step_zero (show d.length e - 1 < d.length e by omega)]
      simp
  · rw [drain_eq_one hPos]
    have hb : b - a = -(k : ℤ) := by omega
    unfold slotValue
    split
    · rw [hb]
      exact ConfigurationCommon.firstStep_neg_eq_neg_one hPos hLe
    · rw [hk, ConfigurationCommon.lastStep_pos_eq_one hPos hLe]

theorem armContribution_nonneg (d : DegSpec n p) (center : Fin n)
    (e : Fin p) {height : ℕ} (hLe : height ≤ d.length e)
    (hLength : 0 < d.length e) :
    0 ≤ armContribution d center e height := by
  rw [armContribution_eq_slotValue]
  exact slotValue_nonneg d center e (k := height) (by omega) hLength hLe

theorem armContribution_eq_one_of_full (d : DegSpec n p) (center : Fin n)
    (e : Fin p) {height : ℕ} (hFull : height = d.length e)
    (hLength : 0 < d.length e) :
    armContribution d center e height = 1 := by
  rw [armContribution_eq_slotValue]
  exact slotValue_eq_one_of_full d center e (by omega) hLength

/-! ## One slot's contribution to a *different* contracted class -/

theorem endpointPair_eq_zero_of_reps (d : DegSpec n p)
    (potential : Fin n → ℤ) (e : Fin p) (r : Fin n)
    (hTail : d.rep (d.core.tail e) ≠ d.rep r)
    (hHead : d.rep (d.core.head e) ≠ d.rep r) :
    ConfigurationCommon.endpointPair d potential e r = 0 := by
  simp [ConfigurationCommon.endpointPair, hTail, hHead]

/-- An arm of height `h` from a centre off the class of `r` removes
`drain h` chips from the class of its far endpoint. -/
theorem endpointPair_arm (d : DegSpec n p) (potential : Fin n → ℤ)
    {e : Fin p} {center chip r : Fin n} {h : ℕ}
    (hEnds : Ends d.core e center chip)
    (hCentre : potential center = -(h : ℤ)) (hFar : potential chip = 0)
    (hLength : 0 < d.length e) (hLe : h ≤ d.length e)
    (hNot : d.rep center ≠ d.rep r) :
    ConfigurationCommon.endpointPair d potential e r =
      -drain h * (if d.rep chip = d.rep r then 1 else 0) := by
  rcases hEnds with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have hrise : d.coreRise potential e = (h : ℤ) := by
      simp [DegSpec.coreRise, ht, hh, hCentre, hFar]
    simp only [ConfigurationCommon.endpointPair, ht, hh, hrise, if_neg hNot,
      zero_add]
    rw [lastStep_pos_eq_drain hLength hLe]
    split_ifs <;> ring
  · have hrise : d.coreRise potential e = -(h : ℤ) := by
      simp [DegSpec.coreRise, ht, hh, hCentre, hFar]
    simp only [ConfigurationCommon.endpointPair, ht, hh, hrise, if_neg hNot,
      add_zero]
    rw [firstStep_neg_eq_neg_drain hLength hLe]
    split_ifs <;> ring

/-! ## The configuration data -/

/-- Membership in a displayed four-chip set.  Spelled out so that the fields
of `ConfigThree` can refer to it. -/
def IsChipOf (a b c e v : Fin n) : Prop := v = a ∨ v = b ∨ v = c ∨ v = e

instance (a b c e v : Fin n) : Decidable (IsChipOf a b c e v) := by
  unfold IsChipOf
  infer_instance

/-- The lookup data of one AR configuration-3 row, together with exactly the
incidence facts the calculation uses.

The four chips carry the divisor.  Each declared centre `v` is chip free and
paired with `partner v`, joined to it by `middleSlot v`, and its two other
slots `firstArm v`, `secondArm v` end on the chips `firstChip v`,
`secondChip v`.

As in `ConfigTwo`, the centres are named by an explicit predicate `isCenter`
rather than "every chip-free vertex", so that a row combining several local
pictures can declare only some of its chip-free vertices to be
configuration-3 centres.  A row all of whose chip-free vertices are centres
gets the whole closed-orthant construction from `closedConstruction`. -/
structure ConfigThree (n p : ℕ) where
  core : Core n p
  chipOne : Fin n
  chipTwo : Fin n
  chipThree : Fin n
  chipFour : Fin n
  isCenter : Fin n → Bool
  partner : Fin n → Fin n
  firstArm : Fin n → Fin p
  secondArm : Fin n → Fin p
  middleSlot : Fin n → Fin p
  firstChip : Fin n → Fin n
  secondChip : Fin n → Fin n
  center_not_chip : ∀ v : Fin n, isCenter v = true →
    ¬ IsChipOf chipOne chipTwo chipThree chipFour v
  partner_isCenter : ∀ v : Fin n, isCenter v = true →
    isCenter (partner v) = true
  partner_ne : ∀ v : Fin n, isCenter v = true → partner v ≠ v
  partner_partner : ∀ v : Fin n, isCenter v = true → partner (partner v) = v
  middleSlot_partner : ∀ v : Fin n, isCenter v = true →
    middleSlot (partner v) = middleSlot v
  firstChip_isChip : ∀ v : Fin n, isCenter v = true →
    IsChipOf chipOne chipTwo chipThree chipFour (firstChip v)
  secondChip_isChip : ∀ v : Fin n, isCenter v = true →
    IsChipOf chipOne chipTwo chipThree chipFour (secondChip v)
  firstArm_ends : ∀ v : Fin n, isCenter v = true →
    Ends core (firstArm v) v (firstChip v)
  secondArm_ends : ∀ v : Fin n, isCenter v = true →
    Ends core (secondArm v) v (secondChip v)
  middleSlot_ends : ∀ v : Fin n, isCenter v = true →
    Ends core (middleSlot v) v (partner v)
  firstArm_ne_secondArm : ∀ v : Fin n, isCenter v = true →
    firstArm v ≠ secondArm v
  incident_slots : ∀ v : Fin n, isCenter v = true → ∀ e : Fin p,
    core.tail e = v ∨ core.head e = v →
      e = firstArm v ∨ e = secondArm v ∨ e = middleSlot v
  chipSum : ∀ v : Fin n, isCenter v = true → ∀ f : Fin n → ℤ,
    f chipOne + f chipTwo + f chipThree + f chipFour =
      f (firstChip v) + f (secondChip v) +
        f (firstChip (partner v)) + f (secondChip (partner v))

namespace ConfigThree

variable (cfg : ConfigThree n p)

/-- The four displayed chip vertices. -/
abbrev IsChip (v : Fin n) : Prop :=
  IsChipOf cfg.chipOne cfg.chipTwo cfg.chipThree cfg.chipFour v

theorem chip_ne_of_not_chip {u v : Fin n} (hu : cfg.IsChip u)
    (hv : ¬cfg.IsChip v) : u ≠ v := by
  rintro rfl
  exact hv hu

/-- A declared centre carries no chip. -/
theorem notChip (v : Fin n) (h : cfg.isCenter v = true) : ¬cfg.IsChip v :=
  cfg.center_not_chip v h

/-- The partner of a declared centre carries no chip. -/
theorem partner_not_chip (v : Fin n) (h : cfg.isCenter v = true) :
    ¬cfg.IsChip (cfg.partner v) :=
  cfg.center_not_chip _ (cfg.partner_isCenter v h)

theorem center_ne_partner {center : Fin n} (hCenter : cfg.isCenter center = true) :
    center ≠ cfg.partner center := (cfg.partner_ne center hCenter).symm

/-! ### Incidence facts transported to a degenerate spec -/

variable (d : DegSpec n p)

theorem ends_firstArm (hCore : d.core = cfg.core) {center : Fin n}
    (hCenter : cfg.isCenter center = true) :
    Ends d.core (cfg.firstArm center) center (cfg.firstChip center) := by
  rw [hCore]
  exact cfg.firstArm_ends center hCenter

theorem ends_secondArm (hCore : d.core = cfg.core) {center : Fin n}
    (hCenter : cfg.isCenter center = true) :
    Ends d.core (cfg.secondArm center) center (cfg.secondChip center) := by
  rw [hCore]
  exact cfg.secondArm_ends center hCenter

theorem ends_middleSlot (hCore : d.core = cfg.core) {center : Fin n}
    (hCenter : cfg.isCenter center = true) :
    Ends d.core (cfg.middleSlot center) center (cfg.partner center) := by
  rw [hCore]
  exact cfg.middleSlot_ends center hCenter

/-- The middle slot read from the partner side. -/
theorem ends_middleSlot_partner (hCore : d.core = cfg.core) {center : Fin n}
    (hCenter : cfg.isCenter center = true) :
    Ends d.core (cfg.middleSlot center) (cfg.partner center) center := by
  have h := cfg.ends_middleSlot d hCore (cfg.partner_isCenter center hCenter)
  rw [cfg.middleSlot_partner center hCenter,
    cfg.partner_partner center hCenter] at h
  exact h

theorem not_incident_of_ne {center : Fin n} (hCenter : cfg.isCenter center = true)
    {e : Fin p} (h1 : e ≠ cfg.firstArm center) (h2 : e ≠ cfg.secondArm center)
    (h3 : e ≠ cfg.middleSlot center) :
    cfg.core.tail e ≠ center ∧ cfg.core.head e ≠ center := by
  constructor <;> intro h
  · rcases cfg.incident_slots center hCenter e (Or.inl h) with h' | h' | h'
    exacts [h1 h', h2 h', h3 h']
  · rcases cfg.incident_slots center hCenter e (Or.inr h) with h' | h' | h'
    exacts [h1 h', h2 h', h3 h']

/-! ### The displayed divisor -/

/-- The indicator of "the chip at `v` sits in the contracted class of `r`". -/
def chipInd (r v : Fin n) : ℤ := if d.rep v = d.rep r then 1 else 0

theorem chipInd_nonneg (r v : Fin n) : 0 ≤ chipInd d r v := by
  unfold chipInd
  split_ifs <;> omega

/-- One chip on each of the four displayed vertices. -/
def divisor : CFDiv d.graph :=
  fourChipDivisor (d.coreVertex cfg.chipOne) (d.coreVertex cfg.chipTwo)
    (d.coreVertex cfg.chipThree) (d.coreVertex cfg.chipFour)

theorem divisor_effective : effective (cfg.divisor d) :=
  fourChipDivisor_effective _ _ _ _

theorem deg_divisor : deg (cfg.divisor d) = 4 :=
  deg_fourChipDivisor _ _ _ _

theorem one_le_divisor_at_chip {chip : Fin n} (hChip : cfg.IsChip chip) :
    1 ≤ cfg.divisor d (d.coreVertex chip) := by
  rcases hChip with rfl | rfl | rfl | rfl
  · exact fourChipDivisor_has_chip_first _ _ _ _
  · exact fourChipDivisor_has_chip_second _ _ _ _
  · exact fourChipDivisor_has_chip_third _ _ _ _
  · exact fourChipDivisor_has_chip_fourth _ _ _ _

theorem one_le_divisor_of_chip_rep_eq {chip center : Fin n}
    (hChip : cfg.IsChip chip) (hEq : d.rep chip = d.rep center) :
    1 ≤ cfg.divisor d (d.coreVertex center) := by
  have hVertex : d.coreVertex chip = d.coreVertex center :=
    (d.coreVertex_eq_iff chip center).mpr hEq
  rw [← hVertex]
  exact cfg.one_le_divisor_at_chip d hChip

theorem divisor_coreVertex_eq (r : Fin n) :
    cfg.divisor d (d.coreVertex r) =
      chipInd d r cfg.chipOne + chipInd d r cfg.chipTwo +
        chipInd d r cfg.chipThree + chipInd d r cfg.chipFour := by
  simp [divisor, chipInd, fourChipDivisor, one_chip, d.coreVertex_eq_iff,
    eq_comm]

theorem divisor_interiorVertex_eq_zero (e : Fin p) (o : Fin (d.length e - 1)) :
    cfg.divisor d (d.interiorVertex e o) = 0 := by
  simp [divisor, fourChipDivisor, one_chip, DegSpec.coreVertex,
    DegSpec.interiorVertex]

/-- A slot from a chip-free class to a chip cannot have collapsed. -/
theorem length_pos_of_incident_chip {center chip : Fin n} {edge : Fin p}
    (hChip : cfg.IsChip chip) (hEnds : Ends d.core edge center chip)
    (hZero : cfg.divisor d (d.coreVertex center) = 0) :
    0 < d.length edge := by
  rcases Nat.eq_zero_or_pos (d.length edge) with hLength | hLength
  · have hRepEnds := d.rep_zero edge hLength
    have hRepChip : d.rep chip = d.rep center := by
      rcases hEnds with ⟨hTail, hHead⟩ | ⟨hTail, hHead⟩
      · simpa [hTail, hHead] using hRepEnds.symm
      · simpa [hTail, hHead] using hRepEnds
    have hOne := cfg.one_le_divisor_of_chip_rep_eq d hChip hRepChip
    omega
  · exact hLength

/-! ### The two interpolation heights -/

def armMin (v : Fin n) : ℕ :=
  min (d.length (cfg.firstArm v)) (d.length (cfg.secondArm v))

/-- Height at the partner centre. -/
def partnerHeight (center : Fin n) : ℕ :=
  min (cfg.armMin d center) (cfg.armMin d (cfg.partner center))

/-- Height at the requested centre. -/
def targetHeight (center : Fin n) : ℕ :=
  min (cfg.armMin d center)
    (cfg.partnerHeight d center + d.length (cfg.middleSlot center))

theorem armMin_le_first (v : Fin n) :
    cfg.armMin d v ≤ d.length (cfg.firstArm v) := by simp [armMin]

theorem armMin_le_second (v : Fin n) :
    cfg.armMin d v ≤ d.length (cfg.secondArm v) := by simp [armMin]

theorem armMin_eq_first_or_second (v : Fin n) :
    cfg.armMin d v = d.length (cfg.firstArm v) ∨
      cfg.armMin d v = d.length (cfg.secondArm v) := min_choice _ _

theorem partnerHeight_le_targetArmMin (center : Fin n) :
    cfg.partnerHeight d center ≤ cfg.armMin d center := by simp [partnerHeight]

theorem partnerHeight_le_partnerArmMin (center : Fin n) :
    cfg.partnerHeight d center ≤ cfg.armMin d (cfg.partner center) := by
  simp [partnerHeight]

theorem targetHeight_le_armMin (center : Fin n) :
    cfg.targetHeight d center ≤ cfg.armMin d center := by simp [targetHeight]

theorem partnerHeight_le_targetHeight (center : Fin n) :
    cfg.partnerHeight d center ≤ cfg.targetHeight d center := by
  simp only [targetHeight]
  exact (Nat.le_min).2 ⟨cfg.partnerHeight_le_targetArmMin d center, by omega⟩

theorem targetHeight_sub_partnerHeight_le_middle (center : Fin n) :
    cfg.targetHeight d center - cfg.partnerHeight d center ≤
      d.length (cfg.middleSlot center) := by
  have h : cfg.targetHeight d center ≤
      cfg.partnerHeight d center + d.length (cfg.middleSlot center) :=
    Nat.min_le_right _ _
  omega

theorem targetHeight_eq_armMin_or_full_middle (center : Fin n) :
    cfg.targetHeight d center = cfg.armMin d center ∨
      cfg.targetHeight d center =
        cfg.partnerHeight d center + d.length (cfg.middleSlot center) :=
  min_choice _ _

theorem partnerHeight_eq_partnerArmMin_of_lt (center : Fin n)
    (hLt : cfg.partnerHeight d center < cfg.targetHeight d center) :
    cfg.partnerHeight d center = cfg.armMin d (cfg.partner center) := by
  change min (cfg.armMin d center) (cfg.armMin d (cfg.partner center)) = _
  by_cases h : cfg.armMin d center ≤ cfg.armMin d (cfg.partner center)
  · have hPartner : cfg.partnerHeight d center = cfg.armMin d center :=
      Nat.min_eq_left h
    have hLe := cfg.targetHeight_le_armMin d center
    omega
  · exact Nat.min_eq_right (by omega)

theorem targetHeight_eq_partnerHeight_of_middle_zero (center : Fin n)
    (hZero : d.length (cfg.middleSlot center) = 0) :
    cfg.targetHeight d center = cfg.partnerHeight d center := by
  have hLe : cfg.targetHeight d center ≤ cfg.partnerHeight d center := by
    unfold targetHeight
    rw [hZero]
    simp
  have hGe := cfg.partnerHeight_le_targetHeight d center
  omega

theorem targetHeight_eq_min_armMins_of_middle_zero (center : Fin n)
    (hMiddleZero : d.length (cfg.middleSlot center) = 0) :
    cfg.targetHeight d center =
      min (cfg.armMin d center) (cfg.armMin d (cfg.partner center)) := by
  simp [targetHeight, partnerHeight, hMiddleZero]

theorem targetHeight_le_middle_of_partnerHeight_zero (center : Fin n)
    (hPartnerHeight : cfg.partnerHeight d center = 0) :
    cfg.targetHeight d center ≤ d.length (cfg.middleSlot center) := by
  simp [targetHeight, hPartnerHeight]

theorem partnerHeight_eq_zero_of_firstPartnerArm_zero (center : Fin n)
    (hZero : d.length (cfg.firstArm (cfg.partner center)) = 0) :
    cfg.partnerHeight d center = 0 := by
  simp [partnerHeight, armMin, hZero]

theorem partnerHeight_eq_zero_of_secondPartnerArm_zero (center : Fin n)
    (hZero : d.length (cfg.secondArm (cfg.partner center)) = 0) :
    cfg.partnerHeight d center = 0 := by
  simp [partnerHeight, armMin, hZero]

theorem armMin_pos (hCore : d.core = cfg.core) {center : Fin n}
    (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0) :
    0 < cfg.armMin d center := by
  have hFirst := cfg.length_pos_of_incident_chip d
    (cfg.firstChip_isChip center hCenter)
    (cfg.ends_firstArm d hCore hCenter) hZero
  have hSecond := cfg.length_pos_of_incident_chip d
    (cfg.secondChip_isChip center hCenter)
    (cfg.ends_secondArm d hCore hCenter) hZero
  simp only [armMin]
  omega

theorem targetHeight_pos (hCore : d.core = cfg.core) {center : Fin n}
    (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0) :
    0 < cfg.targetHeight d center := by
  have hTargetMin := cfg.armMin_pos d hCore hCenter hZero
  rcases Nat.eq_zero_or_pos (d.length (cfg.middleSlot center)) with
      hMiddle | hMiddle
  · have hRepEnds := d.rep_zero (cfg.middleSlot center) hMiddle
    have hRepPartner : d.rep (cfg.partner center) = d.rep center := by
      rcases cfg.ends_middleSlot d hCore hCenter with ⟨hTail, hHead⟩ | ⟨hTail, hHead⟩
      · simpa [hTail, hHead] using hRepEnds.symm
      · simpa [hTail, hHead] using hRepEnds
    have hVertex : d.coreVertex (cfg.partner center) = d.coreVertex center :=
      (d.coreVertex_eq_iff (cfg.partner center) center).mpr hRepPartner
    have hPartnerZero :
        cfg.divisor d (d.coreVertex (cfg.partner center)) = 0 := by
      rw [hVertex]
      exact hZero
    have hPartnerMin := cfg.armMin_pos d hCore
      (cfg.partner_isCenter center hCenter) hPartnerZero
    unfold targetHeight partnerHeight
    omega
  · unfold targetHeight partnerHeight
    omega

/-! ### Which core classes a chip-free centre can meet -/

/-- From one of the two chip-free centres, every step either lands on a chip
or stays in that two-vertex pair. -/
theorem adjacent_pair_or_chip {l : List (Fin p)} {center u v : Fin n}
    (hCenter : cfg.isCenter center = true)
    (hPair : u = center ∨ u = cfg.partner center)
    (hAdjacent : AdjInList cfg.core l u v) :
    cfg.IsChip v ∨ v = center ∨ v = cfg.partner center := by
  have hu : cfg.isCenter u = true := by
    rcases hPair with rfl | rfl
    · exact hCenter
    · exact cfg.partner_isCenter center hCenter
  have hu' : ¬cfg.IsChip u := cfg.center_not_chip u hu
  obtain ⟨e, _he, huv⟩ := hAdjacent
  have hEnds : Ends cfg.core e u v := by
    rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
  have hInc : cfg.core.tail e = u ∨ cfg.core.head e = u := by
    rcases hEnds with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2
  rcases cfg.incident_slots u hu e hInc with rfl | rfl | rfl
  · rcases hEnds.pair_eq (cfg.firstArm_ends u hu) with ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inl (by rw [h]; exact cfg.firstChip_isChip u hu)
    · exact absurd (by rw [h]; exact cfg.firstChip_isChip u hu) hu'
  · rcases hEnds.pair_eq (cfg.secondArm_ends u hu) with ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inl (by rw [h]; exact cfg.secondChip_isChip u hu)
    · exact absurd (by rw [h]; exact cfg.secondChip_isChip u hu) hu'
  · rcases hEnds.pair_eq (cfg.middleSlot_ends u hu) with ⟨_, h⟩ | ⟨h, _⟩
    · rcases hPair with rfl | rfl
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (by rw [h, cfg.partner_partner center hCenter]))
    · exact absurd h.symm (cfg.partner_ne u hu)

/-- A zero-edge class with no chip consists only of the two centres in one
configuration-3 component. -/
theorem reach_mem_pair_of_no_chip {F : Finset (Fin p)} {center v : Fin n}
    (hCenter : cfg.isCenter center = true)
    (hNoChip : ∀ s : Fin n, cfg.IsChip s → ¬ReachIn cfg.core F center s)
    (hReach : ReachIn cfg.core F center v) :
    v = center ∨ v = cfg.partner center := by
  induction hReach with
  | refl => exact Or.inl rfl
  | @tail b c hPrefix hLast ih =>
      rcases cfg.adjacent_pair_or_chip hCenter ih hLast with hChip | hPair
      · exact (hNoChip c hChip (hPrefix.tail hLast)).elim
      · exact hPair

/-- A zero-divisor core class is contained in its displayed centre pair. -/
theorem rep_eq_center_or_partner_of_divisor_zero (F : Finset (Fin p))
    (hRepReach : ∀ x y : Fin n,
      d.rep x = d.rep y ↔ ReachIn cfg.core F x y)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    {v : Fin n} (hEq : d.rep v = d.rep center) :
    v = center ∨ v = cfg.partner center := by
  have hNoChip : ∀ s : Fin n, cfg.IsChip s →
      ¬ReachIn cfg.core F center s := by
    intro s hs hReach
    have hRep : d.rep s = d.rep center :=
      (hRepReach s center).mpr
        (reachInList_symmetric cfg.core (edgeList F) hReach)
    have hOne := cfg.one_le_divisor_of_chip_rep_eq d hs hRep
    omega
  exact cfg.reach_mem_pair_of_no_chip hCenter hNoChip
    ((hRepReach center v).mp hEq.symm)

theorem reach_eq_center_of_slots_positive (F : Finset (Fin p))
    (hFZero : ∀ e : Fin p, e ∈ F ↔ d.length e = 0)
    {center v : Fin n} (hCenter : cfg.isCenter center = true)
    (hFirst : 0 < d.length (cfg.firstArm center))
    (hSecond : 0 < d.length (cfg.secondArm center))
    (hMiddle : 0 < d.length (cfg.middleSlot center))
    (hReach : ReachIn cfg.core F center v) : v = center := by
  induction hReach with
  | refl => rfl
  | @tail b c hPrefix hLast ih =>
      subst b
      obtain ⟨e, he, huv⟩ := hLast
      have heZero : d.length e = 0 :=
        (hFZero e).mp ((mem_edgeList F e).mp he)
      have hInc : cfg.core.tail e = center ∨ cfg.core.head e = center := by
        rcases huv with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inl h1
        · exact Or.inr h1
      rcases cfg.incident_slots center hCenter e hInc with rfl | rfl | rfl <;>
        omega

theorem singleton_class_of_slots_positive (F : Finset (Fin p))
    (hRepReach : ∀ x y : Fin n,
      d.rep x = d.rep y ↔ ReachIn cfg.core F x y)
    (hFZero : ∀ e : Fin p, e ∈ F ↔ d.length e = 0)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hFirst : 0 < d.length (cfg.firstArm center))
    (hSecond : 0 < d.length (cfg.secondArm center))
    (hMiddle : 0 < d.length (cfg.middleSlot center)) :
    ∀ v : Fin n, d.rep v = d.rep center ↔ v = center := by
  intro v
  constructor
  · intro hEq
    exact cfg.reach_eq_center_of_slots_positive d F hFZero hCenter hFirst
      hSecond hMiddle ((hRepReach center v).mp hEq.symm)
  · rintro rfl
    rfl

theorem firstPartnerChip_rep_eq_of_length_zero (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hZero : d.length (cfg.firstArm (cfg.partner center)) = 0) :
    d.rep (cfg.firstChip (cfg.partner center)) =
      d.rep (cfg.partner center) := by
  have hRep := d.rep_zero (cfg.firstArm (cfg.partner center)) hZero
  rcases cfg.ends_firstArm d hCore (cfg.partner_isCenter center hCenter) with
      ⟨ht, hh⟩ | ⟨ht, hh⟩
  · simpa [ht, hh] using hRep.symm
  · simpa [ht, hh] using hRep

theorem secondPartnerChip_rep_eq_of_length_zero (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hZero : d.length (cfg.secondArm (cfg.partner center)) = 0) :
    d.rep (cfg.secondChip (cfg.partner center)) =
      d.rep (cfg.partner center) := by
  have hRep := d.rep_zero (cfg.secondArm (cfg.partner center)) hZero
  rcases cfg.ends_secondArm d hCore (cfg.partner_isCenter center hCenter) with
      ⟨ht, hh⟩ | ⟨ht, hh⟩
  · simpa [ht, hh] using hRep.symm
  · simpa [ht, hh] using hRep

/-! ### The five active slots of a configuration-3 component -/

section Slots

variable {center : Fin n}

theorem firstArm_ne_middleSlot (hCenter : cfg.isCenter center = true) :
    cfg.firstArm center ≠ cfg.middleSlot center :=
  ne_of_ends_same (cfg.firstArm_ends center hCenter)
    (cfg.middleSlot_ends center hCenter)
    (cfg.chip_ne_of_not_chip (cfg.firstChip_isChip center hCenter)
      (cfg.partner_not_chip center hCenter))
    (cfg.center_ne_partner hCenter)

theorem secondArm_ne_middleSlot (hCenter : cfg.isCenter center = true) :
    cfg.secondArm center ≠ cfg.middleSlot center :=
  ne_of_ends_same (cfg.secondArm_ends center hCenter)
    (cfg.middleSlot_ends center hCenter)
    (cfg.chip_ne_of_not_chip (cfg.secondChip_isChip center hCenter)
      (cfg.partner_not_chip center hCenter))
    (cfg.center_ne_partner hCenter)

theorem center_ne_partnerFirstChip (hCenter : cfg.isCenter center = true) :
    center ≠ cfg.firstChip (cfg.partner center) :=
  (cfg.chip_ne_of_not_chip
    (cfg.firstChip_isChip _ (cfg.partner_isCenter center hCenter))
    (cfg.center_not_chip center hCenter)).symm

theorem center_ne_partnerSecondChip (hCenter : cfg.isCenter center = true) :
    center ≠ cfg.secondChip (cfg.partner center) :=
  (cfg.chip_ne_of_not_chip
    (cfg.secondChip_isChip _ (cfg.partner_isCenter center hCenter))
    (cfg.center_not_chip center hCenter)).symm

theorem firstArm_ne_partnerFirstArm (hCenter : cfg.isCenter center = true) :
    cfg.firstArm center ≠ cfg.firstArm (cfg.partner center) :=
  ne_of_ends_of_ne (cfg.firstArm_ends center hCenter)
    (cfg.firstArm_ends _ (cfg.partner_isCenter center hCenter))
    (cfg.center_ne_partner hCenter) (cfg.center_ne_partnerFirstChip hCenter)

theorem firstArm_ne_partnerSecondArm (hCenter : cfg.isCenter center = true) :
    cfg.firstArm center ≠ cfg.secondArm (cfg.partner center) :=
  ne_of_ends_of_ne (cfg.firstArm_ends center hCenter)
    (cfg.secondArm_ends _ (cfg.partner_isCenter center hCenter))
    (cfg.center_ne_partner hCenter) (cfg.center_ne_partnerSecondChip hCenter)

theorem secondArm_ne_partnerFirstArm (hCenter : cfg.isCenter center = true) :
    cfg.secondArm center ≠ cfg.firstArm (cfg.partner center) :=
  ne_of_ends_of_ne (cfg.secondArm_ends center hCenter)
    (cfg.firstArm_ends _ (cfg.partner_isCenter center hCenter))
    (cfg.center_ne_partner hCenter) (cfg.center_ne_partnerFirstChip hCenter)

theorem secondArm_ne_partnerSecondArm (hCenter : cfg.isCenter center = true) :
    cfg.secondArm center ≠ cfg.secondArm (cfg.partner center) :=
  ne_of_ends_of_ne (cfg.secondArm_ends center hCenter)
    (cfg.secondArm_ends _ (cfg.partner_isCenter center hCenter))
    (cfg.center_ne_partner hCenter) (cfg.center_ne_partnerSecondChip hCenter)

theorem middleSlot_ne_partnerFirstArm (hCenter : cfg.isCenter center = true) :
    cfg.middleSlot center ≠ cfg.firstArm (cfg.partner center) :=
  ne_of_ends_of_ne (cfg.middleSlot_ends center hCenter)
    (cfg.firstArm_ends _ (cfg.partner_isCenter center hCenter))
    (cfg.center_ne_partner hCenter) (cfg.center_ne_partnerFirstChip hCenter)

theorem middleSlot_ne_partnerSecondArm (hCenter : cfg.isCenter center = true) :
    cfg.middleSlot center ≠ cfg.secondArm (cfg.partner center) :=
  ne_of_ends_of_ne (cfg.middleSlot_ends center hCenter)
    (cfg.secondArm_ends _ (cfg.partner_isCenter center hCenter))
    (cfg.center_ne_partner hCenter) (cfg.center_ne_partnerSecondChip hCenter)

end Slots

/-! ### Splitting the endpoint sum -/

theorem endpointContribution_eq_center_slots (hCore : d.core = cfg.core)
    (potential : Fin n → ℤ) {center : Fin n} (hCenter : cfg.isCenter center = true) :
    ConfigurationCommon.endpointContribution d potential center =
      slotTerm d potential (cfg.firstArm center) center +
      slotTerm d potential (cfg.secondArm center) center +
      slotTerm d potential (cfg.middleSlot center) center := by
  rw [endpointContribution_eq_sum]
  refine sum_three _ (cfg.firstArm_ne_secondArm center hCenter)
    (cfg.firstArm_ne_middleSlot hCenter) (cfg.secondArm_ne_middleSlot hCenter)
    ?_
  intro x h1 h2 h3
  obtain ⟨hT, hH⟩ := cfg.not_incident_of_ne hCenter h1 h2 h3
  simp only [slotTerm, hCore, if_neg hT, if_neg hH, add_zero]

theorem endpointContribution_eq_partner_slots (hCore : d.core = cfg.core)
    (potential : Fin n → ℤ) {center : Fin n} (hCenter : cfg.isCenter center = true) :
    ConfigurationCommon.endpointContribution d potential (cfg.partner center) =
      slotTerm d potential (cfg.firstArm (cfg.partner center))
          (cfg.partner center) +
      slotTerm d potential (cfg.secondArm (cfg.partner center))
          (cfg.partner center) +
      slotTerm d potential (cfg.middleSlot center) (cfg.partner center) := by
  have h := cfg.endpointContribution_eq_center_slots d hCore potential
    (cfg.partner_isCenter center hCenter)
  rwa [cfg.middleSlot_partner center hCenter] at h

/-- Both endpoint terms of a collapsed middle slot cancel. -/
theorem middleSlot_terms_cancel (hCore : d.core = cfg.core)
    (potential : Fin n → ℤ) {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hMiddleZero : d.length (cfg.middleSlot center) = 0) :
    slotTerm d potential (cfg.middleSlot center) center +
      slotTerm d potential (cfg.middleSlot center) (cfg.partner center) = 0 := by
  have hne := cfg.partner_ne center hCenter
  have hne' := cfg.center_ne_partner hCenter
  rcases cfg.ends_middleSlot d hCore hCenter with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;>
    simp [slotTerm, ht, hh, hne, hne', hMiddleZero]

/-! ### The interpolated potentials -/

/-- The closed-face core potential for configuration 3. -/
def pairPotential (center : Fin n) (v : Fin n) : ℤ :=
  if d.rep v = d.rep center then -(cfg.targetHeight d center : ℤ)
  else if d.rep v = d.rep (cfg.partner center) then
    -(cfg.partnerHeight d center : ℤ)
  else 0

theorem pairPotential_repInvariant (center : Fin n) :
    d.RepInvariant (cfg.pairPotential d center) := by
  intro v
  simp only [pairPotential, d.rep_idem]

/-- The potential used when only the target class fires. -/
abbrev targetOnlyPotential (center : Fin n) : Fin n → ℤ :=
  ConfigurationCommon.centerPotential d center (cfg.targetHeight d center)

theorem pairPotential_center (center : Fin n) :
    cfg.pairPotential d center center = -(cfg.targetHeight d center : ℤ) := by
  simp [pairPotential]

theorem pairPotential_partner (center : Fin n)
    (hne : d.rep (cfg.partner center) ≠ d.rep center) :
    cfg.pairPotential d center (cfg.partner center) =
      -(cfg.partnerHeight d center : ℤ) := by
  simp [pairPotential, hne]

theorem pairPotential_partner_merged (center : Fin n)
    (hMerged : d.rep (cfg.partner center) = d.rep center) :
    cfg.pairPotential d center (cfg.partner center) =
      -(cfg.targetHeight d center : ℤ) := by
  simp [pairPotential, hMerged]

theorem pairPotential_eq_zero (center : Fin n) {v : Fin n}
    (h1 : d.rep v ≠ d.rep center)
    (h2 : d.rep v ≠ d.rep (cfg.partner center)) :
    cfg.pairPotential d center v = 0 := by
  simp [pairPotential, h1, h2]

theorem rep_partner_ne (center : Fin n) (hCenter : cfg.isCenter center = true)
    (hTarget : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center) :
    d.rep (cfg.partner center) ≠ d.rep center := fun h =>
  cfg.partner_ne center hCenter ((hTarget _).mp h)

theorem rep_chip_ne_center (center : Fin n) {chip : Fin n}
    (hChip : cfg.IsChip chip) (hCenter : cfg.isCenter center = true)
    (hTarget : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center) :
    d.rep chip ≠ d.rep center := fun h =>
  cfg.center_not_chip center hCenter ((hTarget chip).mp h ▸ hChip)

theorem pairPotential_chip_eq_zero (center : Fin n) {chip : Fin n}
    (hChip : cfg.IsChip chip) (hCenter : cfg.isCenter center = true)
    (hTarget : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (hPartner : ∀ v : Fin n,
      d.rep v = d.rep (cfg.partner center) ↔ v = cfg.partner center) :
    cfg.pairPotential d center chip = 0 :=
  cfg.pairPotential_eq_zero d center
    (cfg.rep_chip_ne_center d center hChip hCenter hTarget)
    (cfg.rep_chip_ne_center d (cfg.partner center) hChip
      (cfg.partner_isCenter center hCenter) hPartner)

theorem pairPotential_chip_eq_zero_merged (center : Fin n) {chip : Fin n}
    (hChip : cfg.IsChip chip) (hCenter : cfg.isCenter center = true)
    (hMerged : d.rep (cfg.partner center) = d.rep center)
    (hClass : ∀ v : Fin n,
      d.rep v = d.rep center ↔ v = center ∨ v = cfg.partner center) :
    cfg.pairPotential d center chip = 0 := by
  have h1 : d.rep chip ≠ d.rep center := by
    intro h
    rcases (hClass chip).mp h with rfl | rfl
    · exact cfg.center_not_chip _ hCenter hChip
    · exact cfg.partner_not_chip _ hCenter hChip
  exact cfg.pairPotential_eq_zero d center h1 (by rw [hMerged]; exact h1)

/-! ### The three arm contributions at each centre -/

/-- Contribution at the requested centre from the middle slot. -/
def middleTargetContribution (center : Fin n) : ℤ :=
  slotValue d center (cfg.middleSlot center)
    (-(cfg.targetHeight d center : ℤ)) (-(cfg.partnerHeight d center : ℤ))

/-- Contribution at the partner from the same interpolated middle slot. -/
def middlePartnerContribution (center : Fin n) : ℤ :=
  slotValue d (cfg.partner center) (cfg.middleSlot center)
    (-(cfg.partnerHeight d center : ℤ)) (-(cfg.targetHeight d center : ℤ))

theorem middleTargetContribution_nonneg {center : Fin n}
    (hMiddlePos : 0 < d.length (cfg.middleSlot center)) :
    0 ≤ cfg.middleTargetContribution d center := by
  have hLe := cfg.partnerHeight_le_targetHeight d center
  exact slotValue_nonneg d center _
    (k := cfg.targetHeight d center - cfg.partnerHeight d center) (by omega)
    hMiddlePos (cfg.targetHeight_sub_partnerHeight_le_middle d center)

theorem middleTargetContribution_eq_one_of_full {center : Fin n}
    (hFull : cfg.targetHeight d center =
      cfg.partnerHeight d center + d.length (cfg.middleSlot center))
    (hLength : 0 < d.length (cfg.middleSlot center)) :
    cfg.middleTargetContribution d center = 1 :=
  slotValue_eq_one_of_full d center _ (by omega) hLength

theorem middlePartnerContribution_eq {center : Fin n}
    (hMiddlePos : 0 < d.length (cfg.middleSlot center)) :
    cfg.middlePartnerContribution d center =
      -drain (cfg.targetHeight d center - cfg.partnerHeight d center) := by
  have hLe := cfg.partnerHeight_le_targetHeight d center
  exact slotValue_eq_neg_drain d _ _ (by omega) hMiddlePos
    (cfg.targetHeight_sub_partnerHeight_le_middle d center)

theorem targetOnlyPotential_center (center : Fin n) :
    cfg.targetOnlyPotential d center center =
      -(cfg.targetHeight d center : ℤ) := by
  simp [targetOnlyPotential, ConfigurationCommon.centerPotential]

theorem targetOnlyPotential_eq_zero (center : Fin n) {v : Fin n}
    (h : d.rep v ≠ d.rep center) :
    cfg.targetOnlyPotential d center v = 0 := by
  simp [targetOnlyPotential, ConfigurationCommon.centerPotential, h]

/-! ### The endpoint contribution at each of the two centres -/

theorem endpointContribution_target_eq (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hTarget : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (hPartner : ∀ v : Fin n,
      d.rep v = d.rep (cfg.partner center) ↔ v = cfg.partner center) :
    ConfigurationCommon.endpointContribution d (cfg.pairPotential d center) center =
      armContribution d center (cfg.firstArm center)
          (cfg.targetHeight d center) +
      armContribution d center (cfg.secondArm center)
          (cfg.targetHeight d center) +
      cfg.middleTargetContribution d center := by
  rw [cfg.endpointContribution_eq_center_slots d hCore _ hCenter,
    slotTerm_eq_slotValue d _ (cfg.ends_firstArm d hCore hCenter)
      (cfg.chip_ne_of_not_chip (cfg.firstChip_isChip center hCenter)
        (cfg.center_not_chip center hCenter)),
    slotTerm_eq_slotValue d _ (cfg.ends_secondArm d hCore hCenter)
      (cfg.chip_ne_of_not_chip (cfg.secondChip_isChip center hCenter)
        (cfg.center_not_chip center hCenter)),
    slotTerm_eq_slotValue d _ (cfg.ends_middleSlot d hCore hCenter)
      (cfg.partner_ne center hCenter),
    cfg.pairPotential_center d center,
    cfg.pairPotential_chip_eq_zero d center
      (cfg.firstChip_isChip center hCenter) hCenter hTarget hPartner,
    cfg.pairPotential_chip_eq_zero d center
      (cfg.secondChip_isChip center hCenter) hCenter hTarget hPartner,
    cfg.pairPotential_partner d center
      (cfg.rep_partner_ne d center hCenter hTarget)]
  simp only [armContribution_eq_slotValue]
  rfl

theorem endpointContribution_partner_eq (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hTarget : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (hPartner : ∀ v : Fin n,
      d.rep v = d.rep (cfg.partner center) ↔ v = cfg.partner center) :
    ConfigurationCommon.endpointContribution d (cfg.pairPotential d center)
        (cfg.partner center) =
      armContribution d (cfg.partner center) (cfg.firstArm (cfg.partner center))
          (cfg.partnerHeight d center) +
      armContribution d (cfg.partner center)
          (cfg.secondArm (cfg.partner center)) (cfg.partnerHeight d center) +
      cfg.middlePartnerContribution d center := by
  have hp := cfg.partner_isCenter center hCenter
  rw [cfg.endpointContribution_eq_partner_slots d hCore _ hCenter,
    slotTerm_eq_slotValue d _ (cfg.ends_firstArm d hCore hp)
      (cfg.chip_ne_of_not_chip (cfg.firstChip_isChip _ hp)
        (cfg.center_not_chip _ hp)),
    slotTerm_eq_slotValue d _ (cfg.ends_secondArm d hCore hp)
      (cfg.chip_ne_of_not_chip (cfg.secondChip_isChip _ hp)
        (cfg.center_not_chip _ hp)),
    slotTerm_eq_slotValue d _ (cfg.ends_middleSlot_partner d hCore hCenter)
      (cfg.center_ne_partner hCenter),
    cfg.pairPotential_center d center,
    cfg.pairPotential_chip_eq_zero d center (cfg.firstChip_isChip _ hp)
      hCenter hTarget hPartner,
    cfg.pairPotential_chip_eq_zero d center (cfg.secondChip_isChip _ hp)
      hCenter hTarget hPartner,
    cfg.pairPotential_partner d center
      (cfg.rep_partner_ne d center hCenter hTarget)]
  simp only [armContribution_eq_slotValue]
  rfl

theorem endpointContribution_merged_eq_arms (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hMerged : d.rep (cfg.partner center) = d.rep center)
    (hClass : ∀ v : Fin n,
      d.rep v = d.rep center ↔ v = center ∨ v = cfg.partner center)
    (hMiddleZero : d.length (cfg.middleSlot center) = 0) :
    ConfigurationCommon.endpointContribution d (cfg.pairPotential d center) center +
        ConfigurationCommon.endpointContribution d (cfg.pairPotential d center)
          (cfg.partner center) =
      armContribution d center (cfg.firstArm center)
          (cfg.targetHeight d center) +
      armContribution d center (cfg.secondArm center)
          (cfg.targetHeight d center) +
      armContribution d (cfg.partner center) (cfg.firstArm (cfg.partner center))
          (cfg.targetHeight d center) +
      armContribution d (cfg.partner center)
          (cfg.secondArm (cfg.partner center)) (cfg.targetHeight d center) := by
  have hp := cfg.partner_isCenter center hCenter
  have hCancel := cfg.middleSlot_terms_cancel d hCore (cfg.pairPotential d center)
    hCenter hMiddleZero
  rw [cfg.endpointContribution_eq_center_slots d hCore _ hCenter,
    cfg.endpointContribution_eq_partner_slots d hCore _ hCenter,
    slotTerm_eq_slotValue d _ (cfg.ends_firstArm d hCore hCenter)
      (cfg.chip_ne_of_not_chip (cfg.firstChip_isChip center hCenter)
        (cfg.center_not_chip center hCenter)),
    slotTerm_eq_slotValue d _ (cfg.ends_secondArm d hCore hCenter)
      (cfg.chip_ne_of_not_chip (cfg.secondChip_isChip center hCenter)
        (cfg.center_not_chip center hCenter)),
    slotTerm_eq_slotValue d _ (cfg.ends_firstArm d hCore hp)
      (cfg.chip_ne_of_not_chip (cfg.firstChip_isChip _ hp)
        (cfg.center_not_chip _ hp)),
    slotTerm_eq_slotValue d _ (cfg.ends_secondArm d hCore hp)
      (cfg.chip_ne_of_not_chip (cfg.secondChip_isChip _ hp)
        (cfg.center_not_chip _ hp)),
    slotTerm_eq_slotValue d _ (cfg.ends_middleSlot d hCore hCenter)
      (cfg.partner_ne center hCenter),
    slotTerm_eq_slotValue d _ (cfg.ends_middleSlot_partner d hCore hCenter)
      (cfg.center_ne_partner hCenter),
    cfg.pairPotential_center d center,
    cfg.pairPotential_chip_eq_zero_merged d center
      (cfg.firstChip_isChip center hCenter) hCenter hMerged hClass,
    cfg.pairPotential_chip_eq_zero_merged d center
      (cfg.secondChip_isChip center hCenter) hCenter hMerged hClass,
    cfg.pairPotential_chip_eq_zero_merged d center
      (cfg.firstChip_isChip _ hp) hCenter hMerged hClass,
    cfg.pairPotential_chip_eq_zero_merged d center
      (cfg.secondChip_isChip _ hp) hCenter hMerged hClass,
    cfg.pairPotential_partner_merged d center hMerged]
  simp only [armContribution_eq_slotValue]
  rw [slotTerm_eq_slotValue d _ (cfg.ends_middleSlot d hCore hCenter)
      (cfg.partner_ne center hCenter),
    slotTerm_eq_slotValue d _ (cfg.ends_middleSlot_partner d hCore hCenter)
      (cfg.center_ne_partner hCenter),
    cfg.pairPotential_center d center,
    cfg.pairPotential_partner_merged d center hMerged] at hCancel
  linarith [hCancel]

theorem endpointContribution_targetOnly_eq (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hSingleton : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center) :
    ConfigurationCommon.endpointContribution d (cfg.targetOnlyPotential d center)
        center =
      armContribution d center (cfg.firstArm center)
          (cfg.targetHeight d center) +
      armContribution d center (cfg.secondArm center)
          (cfg.targetHeight d center) +
      armContribution d center (cfg.middleSlot center)
          (cfg.targetHeight d center) := by
  rw [cfg.endpointContribution_eq_center_slots d hCore _ hCenter,
    slotTerm_eq_slotValue d _ (cfg.ends_firstArm d hCore hCenter)
      (cfg.chip_ne_of_not_chip (cfg.firstChip_isChip center hCenter)
        (cfg.center_not_chip center hCenter)),
    slotTerm_eq_slotValue d _ (cfg.ends_secondArm d hCore hCenter)
      (cfg.chip_ne_of_not_chip (cfg.secondChip_isChip center hCenter)
        (cfg.center_not_chip center hCenter)),
    slotTerm_eq_slotValue d _ (cfg.ends_middleSlot d hCore hCenter)
      (cfg.partner_ne center hCenter),
    cfg.targetOnlyPotential_center d center,
    cfg.targetOnlyPotential_eq_zero d center
      (cfg.rep_chip_ne_center d center (cfg.firstChip_isChip center hCenter)
        hCenter hSingleton),
    cfg.targetOnlyPotential_eq_zero d center
      (cfg.rep_chip_ne_center d center (cfg.secondChip_isChip center hCenter)
        hCenter hSingleton),
    cfg.targetOnlyPotential_eq_zero d center
      (cfg.rep_partner_ne d center hCenter hSingleton)]
  simp only [armContribution_eq_slotValue]

/-! ### The chip actually delivered to each centre -/

theorem endpointContribution_target_ge_one (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    (hMiddlePos : 0 < d.length (cfg.middleSlot center))
    (hTarget : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (hPartner : ∀ v : Fin n,
      d.rep v = d.rep (cfg.partner center) ↔ v = cfg.partner center) :
    1 ≤ ConfigurationCommon.endpointContribution d (cfg.pairPotential d center)
      center := by
  have hHeight := cfg.targetHeight_pos d hCore hCenter hZero
  have hFirstLe : cfg.targetHeight d center ≤ d.length (cfg.firstArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center) (cfg.armMin_le_first d center)
  have hSecondLe : cfg.targetHeight d center ≤
      d.length (cfg.secondArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center)
      (cfg.armMin_le_second d center)
  have hFirstLength : 0 < d.length (cfg.firstArm center) := by omega
  have hSecondLength : 0 < d.length (cfg.secondArm center) := by omega
  have hFirst := armContribution_nonneg d center (cfg.firstArm center)
    hFirstLe hFirstLength
  have hSecond := armContribution_nonneg d center (cfg.secondArm center)
    hSecondLe hSecondLength
  have hMiddle := cfg.middleTargetContribution_nonneg d hMiddlePos
  rw [cfg.endpointContribution_target_eq d hCore hCenter hTarget hPartner]
  by_cases hArm : cfg.targetHeight d center = cfg.armMin d center
  · rcases cfg.armMin_eq_first_or_second d center with hF | hS
    · have hOne := armContribution_eq_one_of_full d center (cfg.firstArm center)
        (hArm.trans hF) hFirstLength
      omega
    · have hOne := armContribution_eq_one_of_full d center
        (cfg.secondArm center) (hArm.trans hS) hSecondLength
      omega
  · rcases cfg.targetHeight_eq_armMin_or_full_middle d center with h | hFull
    · exact (hArm h).elim
    · have hOne := cfg.middleTargetContribution_eq_one_of_full d hFull hMiddlePos
      omega

theorem partnerFirstArm_length_pos (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hPartner : ∀ v : Fin n,
      d.rep v = d.rep (cfg.partner center) ↔ v = cfg.partner center) :
    0 < d.length (cfg.firstArm (cfg.partner center)) := by
  rcases Nat.eq_zero_or_pos (d.length (cfg.firstArm (cfg.partner center))) with
      h | h
  · have hEq := (hPartner _).mp
      (cfg.firstPartnerChip_rep_eq_of_length_zero d hCore hCenter h)
    exact absurd (hEq ▸ cfg.firstChip_isChip _
      (cfg.partner_isCenter center hCenter))
      (cfg.partner_not_chip center hCenter)
  · exact h

theorem partnerSecondArm_length_pos (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hPartner : ∀ v : Fin n,
      d.rep v = d.rep (cfg.partner center) ↔ v = cfg.partner center) :
    0 < d.length (cfg.secondArm (cfg.partner center)) := by
  rcases Nat.eq_zero_or_pos (d.length (cfg.secondArm (cfg.partner center))) with
      h | h
  · have hEq := (hPartner _).mp
      (cfg.secondPartnerChip_rep_eq_of_length_zero d hCore hCenter h)
    exact absurd (hEq ▸ cfg.secondChip_isChip _
      (cfg.partner_isCenter center hCenter))
      (cfg.partner_not_chip center hCenter)
  · exact h

theorem endpointContribution_partner_nonneg (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hMiddlePos : 0 < d.length (cfg.middleSlot center))
    (hTarget : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (hPartner : ∀ v : Fin n,
      d.rep v = d.rep (cfg.partner center) ↔ v = cfg.partner center) :
    0 ≤ ConfigurationCommon.endpointContribution d (cfg.pairPotential d center)
      (cfg.partner center) := by
  have hFirstLength := cfg.partnerFirstArm_length_pos d hCore hCenter hPartner
  have hSecondLength := cfg.partnerSecondArm_length_pos d hCore hCenter hPartner
  have hpFirst := armContribution_nonneg d (cfg.partner center)
    (cfg.firstArm (cfg.partner center))
    (le_trans (cfg.partnerHeight_le_partnerArmMin d center)
      (cfg.armMin_le_first d (cfg.partner center))) hFirstLength
  have hpSecond := armContribution_nonneg d (cfg.partner center)
    (cfg.secondArm (cfg.partner center))
    (le_trans (cfg.partnerHeight_le_partnerArmMin d center)
      (cfg.armMin_le_second d (cfg.partner center))) hSecondLength
  rw [cfg.endpointContribution_partner_eq d hCore hCenter hTarget hPartner,
    cfg.middlePartnerContribution_eq d hMiddlePos]
  rcases Nat.eq_zero_or_pos
      (cfg.targetHeight d center - cfg.partnerHeight d center) with hδ | hδ
  · rw [hδ, drain_eq_zero]
    omega
  · rw [drain_eq_one hδ]
    have hLt : cfg.partnerHeight d center < cfg.targetHeight d center := by
      have := cfg.partnerHeight_le_targetHeight d center
      omega
    have hFullMin := cfg.partnerHeight_eq_partnerArmMin_of_lt d center hLt
    rcases cfg.armMin_eq_first_or_second d (cfg.partner center) with hF | hS
    · have hOne := armContribution_eq_one_of_full d (cfg.partner center)
        (cfg.firstArm (cfg.partner center)) (hFullMin.trans hF) hFirstLength
      omega
    · have hOne := armContribution_eq_one_of_full d (cfg.partner center)
        (cfg.secondArm (cfg.partner center)) (hFullMin.trans hS) hSecondLength
      omega

theorem endpointContribution_merged_ge_one (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    (hMiddleZero : d.length (cfg.middleSlot center) = 0)
    (hMerged : d.rep (cfg.partner center) = d.rep center)
    (hClass : ∀ v : Fin n,
      d.rep v = d.rep center ↔ v = center ∨ v = cfg.partner center) :
    1 ≤ ConfigurationCommon.endpointContribution d (cfg.pairPotential d center)
        center +
      ConfigurationCommon.endpointContribution d (cfg.pairPotential d center)
        (cfg.partner center) := by
  have hHeightEq :=
    cfg.targetHeight_eq_partnerHeight_of_middle_zero d center hMiddleZero
  have hHeightPos := cfg.targetHeight_pos d hCore hCenter hZero
  have hTargetFirstLe : cfg.targetHeight d center ≤
      d.length (cfg.firstArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center) (cfg.armMin_le_first d center)
  have hTargetSecondLe : cfg.targetHeight d center ≤
      d.length (cfg.secondArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center)
      (cfg.armMin_le_second d center)
  have hPartnerFirstLe : cfg.targetHeight d center ≤
      d.length (cfg.firstArm (cfg.partner center)) := by
    rw [hHeightEq]
    exact le_trans (cfg.partnerHeight_le_partnerArmMin d center)
      (cfg.armMin_le_first d (cfg.partner center))
  have hPartnerSecondLe : cfg.targetHeight d center ≤
      d.length (cfg.secondArm (cfg.partner center)) := by
    rw [hHeightEq]
    exact le_trans (cfg.partnerHeight_le_partnerArmMin d center)
      (cfg.armMin_le_second d (cfg.partner center))
  have hTF := armContribution_nonneg d center (cfg.firstArm center)
    hTargetFirstLe (by omega)
  have hTS := armContribution_nonneg d center (cfg.secondArm center)
    hTargetSecondLe (by omega)
  have hPF := armContribution_nonneg d (cfg.partner center)
    (cfg.firstArm (cfg.partner center)) hPartnerFirstLe (by omega)
  have hPS := armContribution_nonneg d (cfg.partner center)
    (cfg.secondArm (cfg.partner center)) hPartnerSecondLe (by omega)
  rw [cfg.endpointContribution_merged_eq_arms d hCore hCenter hMerged hClass
    hMiddleZero]
  have hMin := cfg.targetHeight_eq_min_armMins_of_middle_zero d center
    hMiddleZero
  rcases min_choice (cfg.armMin d center) (cfg.armMin d (cfg.partner center))
      with hTargetMin | hPartnerMin
  · have hAtTarget : cfg.targetHeight d center = cfg.armMin d center :=
      hMin.trans hTargetMin
    rcases cfg.armMin_eq_first_or_second d center with hF | hS
    · have hOne := armContribution_eq_one_of_full d center (cfg.firstArm center)
        (hAtTarget.trans hF) (by omega)
      omega
    · have hOne := armContribution_eq_one_of_full d center
        (cfg.secondArm center) (hAtTarget.trans hS) (by omega)
      omega
  · have hAtPartner : cfg.targetHeight d center =
        cfg.armMin d (cfg.partner center) := hMin.trans hPartnerMin
    rcases cfg.armMin_eq_first_or_second d (cfg.partner center) with hF | hS
    · have hOne := armContribution_eq_one_of_full d (cfg.partner center)
        (cfg.firstArm (cfg.partner center)) (hAtPartner.trans hF) (by omega)
      omega
    · have hOne := armContribution_eq_one_of_full d (cfg.partner center)
        (cfg.secondArm (cfg.partner center)) (hAtPartner.trans hS) (by omega)
      omega

theorem middleArmContribution_nonneg {center : Fin n}
    (hPartnerHeight : cfg.partnerHeight d center = 0)
    (hMiddlePos : 0 < d.length (cfg.middleSlot center)) :
    0 ≤ armContribution d center (cfg.middleSlot center)
      (cfg.targetHeight d center) :=
  armContribution_nonneg d center (cfg.middleSlot center)
    (cfg.targetHeight_le_middle_of_partnerHeight_zero d center hPartnerHeight)
    hMiddlePos

theorem endpointContribution_targetOnly_ge_one (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    (hPartnerHeight : cfg.partnerHeight d center = 0)
    (hMiddlePos : 0 < d.length (cfg.middleSlot center))
    (hSingleton : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center) :
    1 ≤ ConfigurationCommon.endpointContribution d
      (cfg.targetOnlyPotential d center) center := by
  have hHeight := cfg.targetHeight_pos d hCore hCenter hZero
  have hFirstLe : cfg.targetHeight d center ≤ d.length (cfg.firstArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center) (cfg.armMin_le_first d center)
  have hSecondLe : cfg.targetHeight d center ≤
      d.length (cfg.secondArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center)
      (cfg.armMin_le_second d center)
  have hFirst := armContribution_nonneg d center (cfg.firstArm center)
    hFirstLe (by omega)
  have hSecond := armContribution_nonneg d center (cfg.secondArm center)
    hSecondLe (by omega)
  have hMiddle := cfg.middleArmContribution_nonneg d hPartnerHeight hMiddlePos
  rw [cfg.endpointContribution_targetOnly_eq d hCore hCenter hSingleton]
  by_cases hArm : cfg.targetHeight d center = cfg.armMin d center
  · rcases cfg.armMin_eq_first_or_second d center with hF | hS
    · have hOne := armContribution_eq_one_of_full d center (cfg.firstArm center)
        (hArm.trans hF) (by omega)
      omega
    · have hOne := armContribution_eq_one_of_full d center
        (cfg.secondArm center) (hArm.trans hS) (by omega)
      omega
  · have hFull : cfg.targetHeight d center =
        d.length (cfg.middleSlot center) := by
      rcases cfg.targetHeight_eq_armMin_or_full_middle d center with h | h
      · exact (hArm h).elim
      · omega
    have hOne := armContribution_eq_one_of_full d center (cfg.middleSlot center)
      hFull hMiddlePos
    omega

/-! ### The Laplacian away from the fired classes -/

theorem coreRise_eq_zero_of_not_active (hCore : d.core = cfg.core)
    {potential : Fin n → ℤ} {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hSupport : ∀ v : Fin n, v ≠ center → v ≠ cfg.partner center →
      potential v = 0)
    {e : Fin p} (h1 : e ≠ cfg.firstArm center) (h2 : e ≠ cfg.secondArm center)
    (h3 : e ≠ cfg.middleSlot center)
    (h4 : e ≠ cfg.firstArm (cfg.partner center))
    (h5 : e ≠ cfg.secondArm (cfg.partner center)) :
    d.coreRise potential e = 0 := by
  obtain ⟨hT, hH⟩ := cfg.not_incident_of_ne hCenter h1 h2 h3
  obtain ⟨hT', hH'⟩ := cfg.not_incident_of_ne
    (cfg.partner_isCenter center hCenter) h4 h5
    (by rw [cfg.middleSlot_partner center hCenter]; exact h3)
  simp only [DegSpec.coreRise, hCore]
  rw [hSupport _ hH hH', hSupport _ hT hT']
  ring

theorem coreRise_eq_zero_of_not_center (hCore : d.core = cfg.core)
    {potential : Fin n → ℤ} {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hSupport : ∀ v : Fin n, v ≠ center → potential v = 0)
    {e : Fin p} (h1 : e ≠ cfg.firstArm center) (h2 : e ≠ cfg.secondArm center)
    (h3 : e ≠ cfg.middleSlot center) :
    d.coreRise potential e = 0 := by
  obtain ⟨hT, hH⟩ := cfg.not_incident_of_ne hCenter h1 h2 h3
  simp only [DegSpec.coreRise, hCore]
  rw [hSupport _ hH, hSupport _ hT]
  ring

theorem endpointPair_middle_eq_zero (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true) (potential : Fin n → ℤ)
    (r : Fin n) (h1 : d.rep center ≠ d.rep r)
    (h2 : d.rep (cfg.partner center) ≠ d.rep r) :
    ConfigurationCommon.endpointPair d potential (cfg.middleSlot center) r = 0 := by
  rcases cfg.ends_middleSlot d hCore hCenter with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · exact endpointPair_eq_zero_of_reps d potential _ r (by rw [ht]; exact h1)
      (by rw [hh]; exact h2)
  · exact endpointPair_eq_zero_of_reps d potential _ r (by rw [ht]; exact h2)
      (by rw [hh]; exact h1)

theorem prin_pair_nonTarget_eq (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hHeightPos : 0 < cfg.targetHeight d center)
    (hTarget : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (hPartner : ∀ v : Fin n,
      d.rep v = d.rep (cfg.partner center) ↔ v = cfg.partner center)
    (hPartnerFirstLength : 0 < d.length (cfg.firstArm (cfg.partner center)))
    (hPartnerSecondLength : 0 < d.length (cfg.secondArm (cfg.partner center)))
    (r : Fin n) (hNotTarget : d.rep r ≠ d.rep center)
    (hNotPartner : d.rep r ≠ d.rep (cfg.partner center)) :
    prin d.graph (d.interpolatedScript (cfg.pairPotential d center))
        (d.coreVertex r) =
      -chipInd d r (cfg.firstChip center) -
      chipInd d r (cfg.secondChip center) -
      drain (cfg.partnerHeight d center) *
        (chipInd d r (cfg.firstChip (cfg.partner center)) +
          chipInd d r (cfg.secondChip (cfg.partner center))) := by
  have hp := cfg.partner_isCenter center hCenter
  have hInv := cfg.pairPotential_repInvariant d center
  have hPartnerValue := cfg.pairPotential_partner d center
    (cfg.rep_partner_ne d center hCenter hTarget)
  have hSupport : ∀ v : Fin n, v ≠ center → v ≠ cfg.partner center →
      cfg.pairPotential d center v = 0 := by
    intro v hv1 hv2
    exact cfg.pairPotential_eq_zero d center (fun h => hv1 ((hTarget v).mp h))
      (fun h => hv2 ((hPartner v).mp h))
  have hTargetFirstLe : cfg.targetHeight d center ≤
      d.length (cfg.firstArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center) (cfg.armMin_le_first d center)
  have hTargetSecondLe : cfg.targetHeight d center ≤
      d.length (cfg.secondArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center)
      (cfg.armMin_le_second d center)
  have hPartnerFirstLe : cfg.partnerHeight d center ≤
      d.length (cfg.firstArm (cfg.partner center)) :=
    le_trans (cfg.partnerHeight_le_partnerArmMin d center)
      (cfg.armMin_le_first d (cfg.partner center))
  have hPartnerSecondLe : cfg.partnerHeight d center ≤
      d.length (cfg.secondArm (cfg.partner center)) :=
    le_trans (cfg.partnerHeight_le_partnerArmMin d center)
      (cfg.armMin_le_second d (cfg.partner center))
  rw [d.prin_interpolatedScript_coreVertex_eq_endpointSum hInv]
  change (∑ e : Fin p,
    ConfigurationCommon.endpointPair d (cfg.pairPotential d center) e r) = _
  rw [sum_five _ (cfg.firstArm_ne_secondArm center hCenter)
    (cfg.firstArm_ne_middleSlot hCenter)
    (cfg.firstArm_ne_partnerFirstArm hCenter)
    (cfg.firstArm_ne_partnerSecondArm hCenter)
    (cfg.secondArm_ne_middleSlot hCenter)
    (cfg.secondArm_ne_partnerFirstArm hCenter)
    (cfg.secondArm_ne_partnerSecondArm hCenter)
    (cfg.middleSlot_ne_partnerFirstArm hCenter)
    (cfg.middleSlot_ne_partnerSecondArm hCenter)
    (cfg.firstArm_ne_secondArm _ hp)
    (fun x h1 h2 h3 h4 h5 =>
      ConfigurationCommon.endpointPair_eq_zero_of_rise_eq_zero d _ x r
        (cfg.coreRise_eq_zero_of_not_active d hCore hCenter hSupport h1 h2 h3 h4
          h5))]
  rw [endpointPair_arm d _ (cfg.ends_firstArm d hCore hCenter)
      (cfg.pairPotential_center d center)
      (cfg.pairPotential_chip_eq_zero d center
        (cfg.firstChip_isChip center hCenter) hCenter hTarget hPartner)
      (by omega) hTargetFirstLe hNotTarget.symm,
    endpointPair_arm d _ (cfg.ends_secondArm d hCore hCenter)
      (cfg.pairPotential_center d center)
      (cfg.pairPotential_chip_eq_zero d center
        (cfg.secondChip_isChip center hCenter) hCenter hTarget hPartner)
      (by omega) hTargetSecondLe hNotTarget.symm,
    cfg.endpointPair_middle_eq_zero d hCore hCenter _ r hNotTarget.symm
      hNotPartner.symm,
    endpointPair_arm d _ (cfg.ends_firstArm d hCore hp) hPartnerValue
      (cfg.pairPotential_chip_eq_zero d center (cfg.firstChip_isChip _ hp)
        hCenter hTarget hPartner)
      hPartnerFirstLength hPartnerFirstLe hNotPartner.symm,
    endpointPair_arm d _ (cfg.ends_secondArm d hCore hp) hPartnerValue
      (cfg.pairPotential_chip_eq_zero d center (cfg.secondChip_isChip _ hp)
        hCenter hTarget hPartner)
      hPartnerSecondLength hPartnerSecondLe hNotPartner.symm,
    drain_eq_one hHeightPos]
  simp only [chipInd]
  ring

theorem prin_targetOnly_nonTarget_eq (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hHeightPos : 0 < cfg.targetHeight d center)
    (hPartnerHeight : cfg.partnerHeight d center = 0)
    (hMiddlePos : 0 < d.length (cfg.middleSlot center))
    (hSingleton : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (r : Fin n) (hNotTarget : d.rep r ≠ d.rep center) :
    prin d.graph (d.interpolatedScript (cfg.targetOnlyPotential d center))
        (d.coreVertex r) =
      -chipInd d r (cfg.firstChip center) -
      chipInd d r (cfg.secondChip center) -
      chipInd d r (cfg.partner center) := by
  have hInv := ConfigurationCommon.centerPotential_repInvariant d center
    (cfg.targetHeight d center)
  have hSupport : ∀ v : Fin n, v ≠ center →
      cfg.targetOnlyPotential d center v = 0 := by
    intro v hv1
    exact cfg.targetOnlyPotential_eq_zero d center
      (fun h => hv1 ((hSingleton v).mp h))
  have hTargetFirstLe : cfg.targetHeight d center ≤
      d.length (cfg.firstArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center) (cfg.armMin_le_first d center)
  have hTargetSecondLe : cfg.targetHeight d center ≤
      d.length (cfg.secondArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center)
      (cfg.armMin_le_second d center)
  have hMiddleLe := cfg.targetHeight_le_middle_of_partnerHeight_zero d center
    hPartnerHeight
  rw [d.prin_interpolatedScript_coreVertex_eq_endpointSum hInv]
  change (∑ e : Fin p,
    ConfigurationCommon.endpointPair d (cfg.targetOnlyPotential d center) e r) = _
  rw [sum_three _ (cfg.firstArm_ne_secondArm center hCenter)
    (cfg.firstArm_ne_middleSlot hCenter) (cfg.secondArm_ne_middleSlot hCenter)
    (fun x h1 h2 h3 =>
      ConfigurationCommon.endpointPair_eq_zero_of_rise_eq_zero d _ x r
        (cfg.coreRise_eq_zero_of_not_center d hCore hCenter hSupport h1 h2 h3))]
  rw [endpointPair_arm d _ (cfg.ends_firstArm d hCore hCenter)
      (cfg.targetOnlyPotential_center d center)
      (cfg.targetOnlyPotential_eq_zero d center
        (cfg.rep_chip_ne_center d center (cfg.firstChip_isChip center hCenter)
          hCenter hSingleton))
      (by omega) hTargetFirstLe hNotTarget.symm,
    endpointPair_arm d _ (cfg.ends_secondArm d hCore hCenter)
      (cfg.targetOnlyPotential_center d center)
      (cfg.targetOnlyPotential_eq_zero d center
        (cfg.rep_chip_ne_center d center (cfg.secondChip_isChip center hCenter)
          hCenter hSingleton))
      (by omega) hTargetSecondLe hNotTarget.symm,
    endpointPair_arm d _ (cfg.ends_middleSlot d hCore hCenter)
      (cfg.targetOnlyPotential_center d center)
      (cfg.targetOnlyPotential_eq_zero d center
        (cfg.rep_partner_ne d center hCenter hSingleton))
      hMiddlePos hMiddleLe hNotTarget.symm,
    drain_eq_one hHeightPos]
  simp only [chipInd]
  ring

theorem prin_merged_nonTarget_eq (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hMiddleZero : d.length (cfg.middleSlot center) = 0)
    (hMerged : d.rep (cfg.partner center) = d.rep center)
    (hClass : ∀ v : Fin n,
      d.rep v = d.rep center ↔ v = center ∨ v = cfg.partner center)
    (hHeightPos : 0 < cfg.targetHeight d center)
    (r : Fin n) (hNotClass : d.rep r ≠ d.rep center) :
    prin d.graph (d.interpolatedScript (cfg.pairPotential d center))
        (d.coreVertex r) =
      -chipInd d r (cfg.firstChip center) -
      chipInd d r (cfg.secondChip center) -
      chipInd d r (cfg.firstChip (cfg.partner center)) -
      chipInd d r (cfg.secondChip (cfg.partner center)) := by
  have hp := cfg.partner_isCenter center hCenter
  have hInv := cfg.pairPotential_repInvariant d center
  have hHeightEq :=
    cfg.targetHeight_eq_partnerHeight_of_middle_zero d center hMiddleZero
  have hPartnerValue := cfg.pairPotential_partner_merged d center hMerged
  have hSupport : ∀ v : Fin n, v ≠ center → v ≠ cfg.partner center →
      cfg.pairPotential d center v = 0 := by
    intro v hv1 hv2
    have h1 : d.rep v ≠ d.rep center := by
      intro h
      rcases (hClass v).mp h with rfl | rfl
      · exact hv1 rfl
      · exact hv2 rfl
    exact cfg.pairPotential_eq_zero d center h1 (by rw [hMerged]; exact h1)
  have hTargetFirstLe : cfg.targetHeight d center ≤
      d.length (cfg.firstArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center) (cfg.armMin_le_first d center)
  have hTargetSecondLe : cfg.targetHeight d center ≤
      d.length (cfg.secondArm center) :=
    le_trans (cfg.targetHeight_le_armMin d center)
      (cfg.armMin_le_second d center)
  have hPartnerFirstLe : cfg.targetHeight d center ≤
      d.length (cfg.firstArm (cfg.partner center)) := by
    rw [hHeightEq]
    exact le_trans (cfg.partnerHeight_le_partnerArmMin d center)
      (cfg.armMin_le_first d (cfg.partner center))
  have hPartnerSecondLe : cfg.targetHeight d center ≤
      d.length (cfg.secondArm (cfg.partner center)) := by
    rw [hHeightEq]
    exact le_trans (cfg.partnerHeight_le_partnerArmMin d center)
      (cfg.armMin_le_second d (cfg.partner center))
  have hNotPartner : d.rep (cfg.partner center) ≠ d.rep r := by
    rw [hMerged]
    exact hNotClass.symm
  rw [d.prin_interpolatedScript_coreVertex_eq_endpointSum hInv]
  change (∑ e : Fin p,
    ConfigurationCommon.endpointPair d (cfg.pairPotential d center) e r) = _
  rw [sum_five _ (cfg.firstArm_ne_secondArm center hCenter)
    (cfg.firstArm_ne_middleSlot hCenter)
    (cfg.firstArm_ne_partnerFirstArm hCenter)
    (cfg.firstArm_ne_partnerSecondArm hCenter)
    (cfg.secondArm_ne_middleSlot hCenter)
    (cfg.secondArm_ne_partnerFirstArm hCenter)
    (cfg.secondArm_ne_partnerSecondArm hCenter)
    (cfg.middleSlot_ne_partnerFirstArm hCenter)
    (cfg.middleSlot_ne_partnerSecondArm hCenter)
    (cfg.firstArm_ne_secondArm _ hp)
    (fun x h1 h2 h3 h4 h5 =>
      ConfigurationCommon.endpointPair_eq_zero_of_rise_eq_zero d _ x r
        (cfg.coreRise_eq_zero_of_not_active d hCore hCenter hSupport h1 h2 h3 h4
          h5))]
  rw [endpointPair_arm d _ (cfg.ends_firstArm d hCore hCenter)
      (cfg.pairPotential_center d center)
      (cfg.pairPotential_chip_eq_zero_merged d center
        (cfg.firstChip_isChip center hCenter) hCenter hMerged hClass)
      (by omega) hTargetFirstLe hNotClass.symm,
    endpointPair_arm d _ (cfg.ends_secondArm d hCore hCenter)
      (cfg.pairPotential_center d center)
      (cfg.pairPotential_chip_eq_zero_merged d center
        (cfg.secondChip_isChip center hCenter) hCenter hMerged hClass)
      (by omega) hTargetSecondLe hNotClass.symm,
    cfg.endpointPair_middle_eq_zero d hCore hCenter _ r hNotClass.symm
      hNotPartner,
    endpointPair_arm d _ (cfg.ends_firstArm d hCore hp) hPartnerValue
      (cfg.pairPotential_chip_eq_zero_merged d center
        (cfg.firstChip_isChip _ hp) hCenter hMerged hClass)
      (by omega) hPartnerFirstLe hNotPartner,
    endpointPair_arm d _ (cfg.ends_secondArm d hCore hp) hPartnerValue
      (cfg.pairPotential_chip_eq_zero_merged d center
        (cfg.secondChip_isChip _ hp) hCenter hMerged hClass)
      (by omega) hPartnerSecondLe hNotPartner,
    drain_eq_one hHeightPos]
  simp only [chipInd]
  ring

/-! ### Effectivity of the residual divisor -/

/-- Only the contracted core classes need checking: at a subdivision-interior
vertex the interpolated script is nonnegative for free. -/
theorem residual_effective_of_coreVertex {potential : Fin n → ℤ}
    (hInv : d.RepInvariant potential) (center : Fin n)
    (hCoreCase : ∀ r : Fin n,
      0 ≤ cfg.divisor d (d.coreVertex r) -
        one_chip (G := d.graph) (d.coreVertex center) (d.coreVertex r) +
        prin d.graph (d.interpolatedScript potential) (d.coreVertex r)) :
    effective (cfg.divisor d - one_chip (d.coreVertex center) +
      prin d.graph (d.interpolatedScript potential)) := by
  intro vertex
  rcases vertex with coreClass | interior
  · obtain ⟨r, hr⟩ := coreClass
    have hVertex : (Sum.inl ⟨r, hr⟩ : d.Vertex) = d.coreVertex r := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hr.symm
    rw [hVertex]
    exact hCoreCase r
  · obtain ⟨e, o⟩ := interior
    change 0 ≤ cfg.divisor d (d.interiorVertex e o) -
      one_chip (G := d.graph) (d.coreVertex center) (d.interiorVertex e o) +
      prin d.graph (d.interpolatedScript potential) (d.interiorVertex e o)
    have hNe : d.interiorVertex e o ≠ d.coreVertex center := by
      simp [DegSpec.coreVertex, DegSpec.interiorVertex]
    rw [cfg.divisor_interiorVertex_eq_zero]
    simp only [one_chip, if_neg hNe, sub_zero, zero_add]
    exact d.prin_interpolatedScript_interiorVertex_nonneg hInv e o

theorem pair_residual_effective (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    (hMiddlePos : 0 < d.length (cfg.middleSlot center))
    (hTarget : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (hPartner : ∀ v : Fin n,
      d.rep v = d.rep (cfg.partner center) ↔ v = cfg.partner center) :
    effective (cfg.divisor d - one_chip (d.coreVertex center) +
      prin d.graph (d.interpolatedScript (cfg.pairPotential d center))) := by
  have hInv := cfg.pairPotential_repInvariant d center
  have hHeightPos := cfg.targetHeight_pos d hCore hCenter hZero
  have hPF := cfg.partnerFirstArm_length_pos d hCore hCenter hPartner
  have hPS := cfg.partnerSecondArm_length_pos d hCore hCenter hPartner
  refine cfg.residual_effective_of_coreVertex d hInv center ?_
  intro r
  by_cases hAtTarget : d.rep r = d.rep center
  · have hrCenter : r = center := (hTarget r).mp hAtTarget
    subst hrCenter
    rw [hZero, d.prin_interpolatedScript_coreVertex_eq_classSum hInv]
    have hFilter : Finset.univ.filter
        (fun v : Fin n => d.rep v = d.rep r) = {r} := by
      ext v
      simp [hTarget v]
    rw [hFilter]
    simp only [Finset.sum_singleton]
    have hContribution := cfg.endpointContribution_target_ge_one d hCore
      hCenter hZero hMiddlePos hTarget hPartner
    change (0 : ℤ) ≤ 0 - one_chip (G := d.graph) (d.coreVertex r)
      (d.coreVertex r) +
      ConfigurationCommon.endpointContribution d (cfg.pairPotential d r) r
    simp only [one_chip]
    omega
  · by_cases hAtPartner : d.rep r = d.rep (cfg.partner center)
    · have hCoreNe : d.coreVertex center ≠ d.coreVertex r := by
        intro hEq
        exact hAtTarget ((d.coreVertex_eq_iff r center).mp hEq.symm)
      rw [show one_chip (G := d.graph) (d.coreVertex center)
          (d.coreVertex r) = 0 by simp [one_chip, hCoreNe.symm]]
      rw [d.prin_interpolatedScript_coreVertex_eq_classSum hInv]
      have hFilter : Finset.univ.filter
          (fun v : Fin n => d.rep v = d.rep r) = {cfg.partner center} := by
        ext v
        simp [hAtPartner, hPartner v]
      rw [hFilter]
      simp only [Finset.sum_singleton, sub_zero]
      have hContribution := cfg.endpointContribution_partner_nonneg d hCore
        hCenter hMiddlePos hTarget hPartner
      have h1 := cfg.divisor_effective d (d.coreVertex r)
      change (0 : ℤ) ≤ cfg.divisor d (d.coreVertex r) +
        ConfigurationCommon.endpointContribution d (cfg.pairPotential d center)
          (cfg.partner center)
      omega
    · have hCoreNe : d.coreVertex center ≠ d.coreVertex r := by
        intro hEq
        exact hAtTarget ((d.coreVertex_eq_iff r center).mp hEq.symm)
      rw [show one_chip (G := d.graph) (d.coreVertex center)
          (d.coreVertex r) = 0 by simp [one_chip, hCoreNe.symm]]
      rw [cfg.divisor_coreVertex_eq,
        cfg.prin_pair_nonTarget_eq d hCore hCenter hHeightPos hTarget hPartner
          hPF hPS r hAtTarget hAtPartner,
        cfg.chipSum center hCenter (chipInd d r)]
      have hP1 := chipInd_nonneg d r (cfg.firstChip (cfg.partner center))
      have hP2 := chipInd_nonneg d r (cfg.secondChip (cfg.partner center))
      have hd := drain_bounds (cfg.partnerHeight d center)
      have hProduct : 0 ≤ (1 - drain (cfg.partnerHeight d center)) *
          (chipInd d r (cfg.firstChip (cfg.partner center)) +
            chipInd d r (cfg.secondChip (cfg.partner center))) :=
        mul_nonneg (by omega) (by omega)
      have hExpand : (1 - drain (cfg.partnerHeight d center)) *
          (chipInd d r (cfg.firstChip (cfg.partner center)) +
            chipInd d r (cfg.secondChip (cfg.partner center))) =
          chipInd d r (cfg.firstChip (cfg.partner center)) +
            chipInd d r (cfg.secondChip (cfg.partner center)) -
            drain (cfg.partnerHeight d center) *
              (chipInd d r (cfg.firstChip (cfg.partner center)) +
                chipInd d r (cfg.secondChip (cfg.partner center))) := by ring
      rw [hExpand] at hProduct
      linarith

theorem targetOnly_residual_effective (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    (hPartnerHeight : cfg.partnerHeight d center = 0)
    (hMiddlePos : 0 < d.length (cfg.middleSlot center))
    (hSingleton : ∀ v : Fin n, d.rep v = d.rep center ↔ v = center)
    (hPartnerChip :
      d.rep (cfg.firstChip (cfg.partner center)) = d.rep (cfg.partner center) ∨
      d.rep (cfg.secondChip (cfg.partner center)) =
        d.rep (cfg.partner center)) :
    effective (cfg.divisor d - one_chip (d.coreVertex center) +
      prin d.graph
        (d.interpolatedScript (cfg.targetOnlyPotential d center))) := by
  have hInv := ConfigurationCommon.centerPotential_repInvariant d center
    (cfg.targetHeight d center)
  have hHeightPos := cfg.targetHeight_pos d hCore hCenter hZero
  refine cfg.residual_effective_of_coreVertex d hInv center ?_
  intro r
  by_cases hAtTarget : d.rep r = d.rep center
  · have hrCenter : r = center := (hSingleton r).mp hAtTarget
    subst hrCenter
    rw [hZero, d.prin_interpolatedScript_coreVertex_eq_classSum hInv]
    have hFilter : Finset.univ.filter
        (fun v : Fin n => d.rep v = d.rep r) = {r} := by
      ext v
      simp [hSingleton v]
    rw [hFilter]
    simp only [Finset.sum_singleton]
    have hContribution := cfg.endpointContribution_targetOnly_ge_one d hCore
      hCenter hZero hPartnerHeight hMiddlePos hSingleton
    change (0 : ℤ) ≤ 0 - one_chip (G := d.graph) (d.coreVertex r)
      (d.coreVertex r) +
      ConfigurationCommon.endpointContribution d (cfg.targetOnlyPotential d r) r
    simp only [one_chip]
    omega
  · have hCoreNe : d.coreVertex center ≠ d.coreVertex r := by
      intro hEq
      exact hAtTarget ((d.coreVertex_eq_iff r center).mp hEq.symm)
    rw [show one_chip (G := d.graph) (d.coreVertex center)
        (d.coreVertex r) = 0 by simp [one_chip, hCoreNe.symm]]
    rw [cfg.divisor_coreVertex_eq,
      cfg.prin_targetOnly_nonTarget_eq d hCore hCenter hHeightPos
        hPartnerHeight hMiddlePos hSingleton r hAtTarget,
      cfg.chipSum center hCenter (chipInd d r)]
    have h1 := chipInd_nonneg d r (cfg.firstChip center)
    have h2 := chipInd_nonneg d r (cfg.secondChip center)
    have hP1 := chipInd_nonneg d r (cfg.firstChip (cfg.partner center))
    have hP2 := chipInd_nonneg d r (cfg.secondChip (cfg.partner center))
    rcases hPartnerChip with hChip | hChip
    · have hEq : chipInd d r (cfg.partner center) =
          chipInd d r (cfg.firstChip (cfg.partner center)) := by
        simp only [chipInd, hChip]
      rw [hEq]
      linarith
    · have hEq : chipInd d r (cfg.partner center) =
          chipInd d r (cfg.secondChip (cfg.partner center)) := by
        simp only [chipInd, hChip]
      rw [hEq]
      linarith

theorem merged_residual_effective (hCore : d.core = cfg.core)
    {center : Fin n} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    (hMiddleZero : d.length (cfg.middleSlot center) = 0)
    (hMerged : d.rep (cfg.partner center) = d.rep center)
    (hClass : ∀ v : Fin n,
      d.rep v = d.rep center ↔ v = center ∨ v = cfg.partner center) :
    effective (cfg.divisor d - one_chip (d.coreVertex center) +
      prin d.graph (d.interpolatedScript (cfg.pairPotential d center))) := by
  have hInv := cfg.pairPotential_repInvariant d center
  have hHeightPos := cfg.targetHeight_pos d hCore hCenter hZero
  refine cfg.residual_effective_of_coreVertex d hInv center ?_
  intro r
  by_cases hAtClass : d.rep r = d.rep center
  · have hVertexEq : d.coreVertex r = d.coreVertex center :=
      (d.coreVertex_eq_iff r center).mpr hAtClass
    rw [hVertexEq, hZero, d.prin_interpolatedScript_coreVertex_eq_classSum hInv]
    have hFilter : Finset.univ.filter
        (fun v : Fin n => d.rep v = d.rep center) =
          {center, cfg.partner center} := by
      ext v
      simp [hClass v]
    rw [hFilter]
    have hNe := cfg.partner_ne center hCenter
    simp only [Finset.sum_insert, Finset.mem_singleton, Ne.symm hNe,
      not_false_eq_true, Finset.sum_singleton]
    have hContribution := cfg.endpointContribution_merged_ge_one d hCore
      hCenter hZero hMiddleZero hMerged hClass
    change (0 : ℤ) ≤ 0 - one_chip (G := d.graph) (d.coreVertex center)
      (d.coreVertex center) +
      (ConfigurationCommon.endpointContribution d (cfg.pairPotential d center)
          center +
        ConfigurationCommon.endpointContribution d (cfg.pairPotential d center)
          (cfg.partner center))
    simp only [one_chip]
    omega
  · have hCoreNe : d.coreVertex center ≠ d.coreVertex r := by
      intro hEq
      exact hAtClass ((d.coreVertex_eq_iff r center).mp hEq.symm)
    rw [show one_chip (G := d.graph) (d.coreVertex center)
        (d.coreVertex r) = 0 by simp [one_chip, hCoreNe.symm]]
    rw [cfg.divisor_coreVertex_eq,
      cfg.prin_merged_nonTarget_eq d hCore hCenter hMiddleZero hMerged hClass
        hHeightPos r hAtClass,
      cfg.chipSum center hCenter (chipInd d r)]
    linarith

/-! ### The configuration-3 divisor reaches every contracted class -/

/-- **Configuration 3 at one declared centre.**  This is the statement a row
consumes, one centre at a time, so that several local pictures compose. -/
theorem reaches_center (hCore : d.core = cfg.core)
    (F : Finset (Fin p))
    (hRepReach : ∀ x y : Fin n, d.rep x = d.rep y ↔ ReachIn cfg.core F x y)
    (hFZero : ∀ e : Fin p, e ∈ F ↔ d.length e = 0)
    {center : Fin n} (hCenter : cfg.isCenter center = true) :
    Reaches d.graph (cfg.divisor d) (d.coreVertex center) := by
  by_cases hZero : cfg.divisor d (d.coreVertex center) = 0
  · have hArmMin := cfg.armMin_pos d hCore hCenter hZero
    have hTargetFirst : 0 < d.length (cfg.firstArm center) := by
      have := cfg.armMin_le_first d center
      omega
    have hTargetSecond : 0 < d.length (cfg.secondArm center) := by
      have := cfg.armMin_le_second d center
      omega
    rcases Nat.eq_zero_or_pos (d.length (cfg.middleSlot center)) with
        hMiddleZero | hMiddlePos
    · have hMerged : d.rep (cfg.partner center) = d.rep center := by
        have hRep := d.rep_zero (cfg.middleSlot center) hMiddleZero
        rcases cfg.ends_middleSlot d hCore hCenter with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · simpa [ht, hh] using hRep.symm
        · simpa [ht, hh] using hRep
      have hClass : ∀ v : Fin n,
          d.rep v = d.rep center ↔ v = center ∨ v = cfg.partner center := by
        intro v
        constructor
        · exact cfg.rep_eq_center_or_partner_of_divisor_zero d F hRepReach
            hCenter hZero
        · rintro (rfl | rfl)
          · rfl
          · exact hMerged
      exact (DharMove.ofScript
        (d.interpolatedScript (cfg.pairPotential d center))
        (cfg.merged_residual_effective d hCore hCenter hZero hMiddleZero
          hMerged hClass)).reaches
    · have hTargetSingleton := cfg.singleton_class_of_slots_positive d F
        hRepReach hFZero hCenter hTargetFirst hTargetSecond hMiddlePos
      rcases Nat.eq_zero_or_pos (d.length (cfg.firstArm (cfg.partner center)))
          with hPartnerFirstZero | hPartnerFirstPos
      · exact (DharMove.ofScript
          (d.interpolatedScript (cfg.targetOnlyPotential d center))
          (cfg.targetOnly_residual_effective d hCore hCenter hZero
            (cfg.partnerHeight_eq_zero_of_firstPartnerArm_zero d center
              hPartnerFirstZero)
            hMiddlePos hTargetSingleton
            (Or.inl (cfg.firstPartnerChip_rep_eq_of_length_zero d hCore hCenter
              hPartnerFirstZero)))).reaches
      · rcases Nat.eq_zero_or_pos
            (d.length (cfg.secondArm (cfg.partner center))) with
              hPartnerSecondZero | hPartnerSecondPos
        · exact (DharMove.ofScript
            (d.interpolatedScript (cfg.targetOnlyPotential d center))
            (cfg.targetOnly_residual_effective d hCore hCenter hZero
              (cfg.partnerHeight_eq_zero_of_secondPartnerArm_zero d center
                hPartnerSecondZero)
              hMiddlePos hTargetSingleton
              (Or.inr (cfg.secondPartnerChip_rep_eq_of_length_zero d hCore
                hCenter hPartnerSecondZero)))).reaches
        · have hPartnerSingleton := cfg.singleton_class_of_slots_positive d F
            hRepReach hFZero (cfg.partner_isCenter center hCenter)
            hPartnerFirstPos hPartnerSecondPos
            (by rw [cfg.middleSlot_partner center hCenter]; exact hMiddlePos)
          exact (DharMove.ofScript
            (d.interpolatedScript (cfg.pairPotential d center))
            (cfg.pair_residual_effective d hCore hCenter hZero hMiddlePos
              hTargetSingleton hPartnerSingleton)).reaches
  · have hEffective := cfg.divisor_effective d
    have hChip : 1 ≤ cfg.divisor d (d.coreVertex center) := by
      have hNonneg := hEffective (d.coreVertex center)
      omega
    exact reaches_of_effective_representative
      (linear_equiv.refl d.graph (cfg.divisor d)) hEffective hChip

/-- **Configuration 3 on a closed face.**  A row every one of whose chip-free
vertices is a declared centre gets the whole closed-orthant AR
construction.

`core_nonempty` is the one place in this file where the core size is used at
all.  It used to be `0 < 8`, discharged by `norm_num`; it is now a hypothesis,
exactly as in `Guarding.GuardingSet.closedConstruction`. -/
theorem closedConstruction (core_nonempty : 0 < n) (hConnected : cfg.core.Connected)
    (hCenters : ∀ v : Fin n, ¬cfg.IsChip v → cfg.isCenter v = true) :
    ClosedSubdivisionDharConstruction cfg.core core_nonempty :=
  ClosedSubdivisionDharConstruction.ofReachesCoreClasses core_nonempty
    hConnected (fun d => cfg.divisor d) (fun d => cfg.divisor_effective d)
    (fun d => cfg.deg_divisor d)
    (fun d hCore hRepReach center => by
      by_cases hChip : cfg.IsChip center
      · exact reaches_of_effective_representative
          (linear_equiv.refl d.graph (cfg.divisor d)) (cfg.divisor_effective d)
          (cfg.one_le_divisor_at_chip d hChip)
      · exact cfg.reaches_center d hCore (zeroSlots d.length) hRepReach
          (mem_zeroSlots d.length) (hCenters center hChip))

end ConfigThree

end AtanasovRanganathan.ConfigurationThree
