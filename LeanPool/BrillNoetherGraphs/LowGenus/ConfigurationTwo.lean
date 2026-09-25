/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThree

/-!
# Atanasov--Ranganathan configuration 2, generic in the core

Configuration 2 of Atanasov--Ranganathan, Proposition 5.1, is the local
picture at a chip-free core vertex all three of whose slots end on a chip
vertex -- a *tripod centre*.  Interpolate the same negative height along the
three arms, choosing that height to be the shortest arm length.  Every arm
consumes at most its endpoint chip, and a shortest arm delivers a chip to the
centre.

This file states that picture once, as a `ConfigTwo` bundle of the lookup data
together with the incidence facts a row must check, and proves the centre's
residual-effectivity and reach lemmas from those facts alone.  A row supplies
the tables and discharges the `Prop` fields; nothing else.

Unlike `ConfigThree`, the centres are named by an explicit predicate
`isCenter` rather than "every chip-free vertex".  Rows 11 and 12 combine
several local pictures, so a row may declare only some of its chip-free
vertices to be tripod centres and cover the rest by other means; the
conclusions here are stated one centre at a time so that several instances
compose.  A row all of whose chip-free vertices are tripod centres gets the
whole closed-orthant construction from `closedConstruction`.

The generic slot arithmetic (`Ends`, `sum_three`, `slotTerm`, `slotValue`,
`armContribution`, `endpointPair_arm`) is shared with configuration 3 and
currently lives in `ConfigurationThree.lean`; that is why this file imports
it.  Neither structure mentions the other.
-/

@[expose] public section

namespace AtanasovRanganathan.ConfigurationTwo

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open GenusFiveCoreAtlas
open ConfigurationCommon
open ConfigurationThree

/-- The indicator of "the chip at `v` sits in the contracted class of `r`". -/
def chipInd (d : DegSpec 8 12) (r v : Fin 8) : ℤ :=
  if d.rep v = d.rep r then 1 else 0

theorem chipInd_nonneg (d : DegSpec 8 12) (r v : Fin 8) :
    0 ≤ chipInd d r v := by
  unfold chipInd
  split_ifs <;> omega

/-- The minimum of three naturals is one of them. -/
theorem min_three_eq_one (a b c : ℕ) :
    min a (min b c) = a ∨ min a (min b c) = b ∨ min a (min b c) = c := by
  rcases le_total a (min b c) with h | h
  · exact Or.inl (Nat.min_eq_left h)
  · rw [Nat.min_eq_right h]
    rcases le_total b c with hbc | hcb
    · exact Or.inr (Or.inl (Nat.min_eq_left hbc))
    · exact Or.inr (Or.inr (Nat.min_eq_right hcb))

/-- The lookup data of one AR configuration-2 family, together with exactly
the incidence facts the calculation uses.

The four chips carry the divisor.  Each declared centre `v` is chip free, its
three slots `firstArm v`, `secondArm v`, `thirdArm v` end on the chips
`firstChip v`, `secondChip v`, `thirdChip v`, and `spareChip v` names the
fourth chip, which the centre does not touch. -/
structure ConfigTwo where
  /-- The eight-vertex core graph carrying configuration two. -/
  core : Core
  /-- The first of the four designated chip vertices of configuration two. -/
  chipOne : Fin 8
  /-- The second of the four designated chip vertices of configuration two. -/
  chipTwo : Fin 8
  /-- The third of the four designated chip vertices of configuration two. -/
  chipThree : Fin 8
  /-- The fourth of the four designated chip vertices of configuration two. -/
  chipFour : Fin 8
  /-- The Boolean selector of the center vertices, none of which is a designated chip vertex. -/
  isCenter : Fin 8 → Bool
  /-- The slot joining a center to the first chip assigned to that center. -/
  firstArm : Fin 8 → Fin 12
  /-- The slot joining a center to the second chip assigned to that center. -/
  secondArm : Fin 8 → Fin 12
  /-- The slot joining a center to the third chip assigned to that center. -/
  thirdArm : Fin 8 → Fin 12
  /-- The designated chip vertex at the far end of the center's first arm. -/
  firstChip : Fin 8 → Fin 8
  /-- The designated chip vertex at the far end of the center's second arm. -/
  secondChip : Fin 8 → Fin 8
  /-- The designated chip vertex at the far end of the center's third arm. -/
  thirdChip : Fin 8 → Fin 8
  /-- The fourth chip vertex, complementary to the three assigned arm endpoints. -/
  spareChip : Fin 8 → Fin 8
  center_not_chip : ∀ v : Fin 8, isCenter v = true →
    ¬ IsChipOf chipOne chipTwo chipThree chipFour v
  firstChip_isChip : ∀ v : Fin 8, isCenter v = true →
    IsChipOf chipOne chipTwo chipThree chipFour (firstChip v)
  secondChip_isChip : ∀ v : Fin 8, isCenter v = true →
    IsChipOf chipOne chipTwo chipThree chipFour (secondChip v)
  thirdChip_isChip : ∀ v : Fin 8, isCenter v = true →
    IsChipOf chipOne chipTwo chipThree chipFour (thirdChip v)
  firstArm_ends : ∀ v : Fin 8, isCenter v = true →
    Ends core (firstArm v) v (firstChip v)
  secondArm_ends : ∀ v : Fin 8, isCenter v = true →
    Ends core (secondArm v) v (secondChip v)
  thirdArm_ends : ∀ v : Fin 8, isCenter v = true →
    Ends core (thirdArm v) v (thirdChip v)
  firstArm_ne_secondArm : ∀ v : Fin 8, isCenter v = true →
    firstArm v ≠ secondArm v
  firstArm_ne_thirdArm : ∀ v : Fin 8, isCenter v = true →
    firstArm v ≠ thirdArm v
  secondArm_ne_thirdArm : ∀ v : Fin 8, isCenter v = true →
    secondArm v ≠ thirdArm v
  incident_slots : ∀ v : Fin 8, isCenter v = true → ∀ e : Fin 12,
    core.tail e = v ∨ core.head e = v →
      e = firstArm v ∨ e = secondArm v ∨ e = thirdArm v
  chipSum : ∀ v : Fin 8, isCenter v = true → ∀ f : Fin 8 → ℤ,
    f chipOne + f chipTwo + f chipThree + f chipFour =
      f (firstChip v) + f (secondChip v) + f (thirdChip v) + f (spareChip v)

namespace ConfigTwo

variable (cfg : ConfigTwo)

/-- The four displayed chip vertices. -/
abbrev IsChip (v : Fin 8) : Prop :=
  IsChipOf cfg.chipOne cfg.chipTwo cfg.chipThree cfg.chipFour v

theorem chip_ne_center {chip center : Fin 8} (hChip : cfg.IsChip chip)
    (hCenter : cfg.isCenter center = true) : chip ≠ center := by
  rintro rfl
  exact cfg.center_not_chip chip hCenter hChip

/-! ### The displayed divisor -/

variable (d : DegSpec 8 12)

/-- One chip on each of the four displayed vertices. -/
def divisor : CFDiv d.graph :=
  fourChipDivisor (d.coreVertex cfg.chipOne) (d.coreVertex cfg.chipTwo)
    (d.coreVertex cfg.chipThree) (d.coreVertex cfg.chipFour)

theorem divisor_effective : effective (cfg.divisor d) :=
  fourChipDivisor_effective _ _ _ _

theorem deg_divisor : deg (cfg.divisor d) = 4 :=
  deg_fourChipDivisor _ _ _ _

theorem one_le_divisor_at_chip {chip : Fin 8} (hChip : cfg.IsChip chip) :
    1 ≤ cfg.divisor d (d.coreVertex chip) := by
  rcases hChip with rfl | rfl | rfl | rfl
  · exact fourChipDivisor_has_chip_first _ _ _ _
  · exact fourChipDivisor_has_chip_second _ _ _ _
  · exact fourChipDivisor_has_chip_third _ _ _ _
  · exact fourChipDivisor_has_chip_fourth _ _ _ _

theorem one_le_divisor_of_chip_rep_eq {chip center : Fin 8}
    (hChip : cfg.IsChip chip) (hEq : d.rep chip = d.rep center) :
    1 ≤ cfg.divisor d (d.coreVertex center) := by
  have hVertex : d.coreVertex chip = d.coreVertex center :=
    (d.coreVertex_eq_iff chip center).mpr hEq
  rw [← hVertex]
  exact cfg.one_le_divisor_at_chip d hChip

theorem divisor_coreVertex_eq (r : Fin 8) :
    cfg.divisor d (d.coreVertex r) =
      chipInd d r cfg.chipOne + chipInd d r cfg.chipTwo +
        chipInd d r cfg.chipThree + chipInd d r cfg.chipFour := by
  simp [divisor, chipInd, fourChipDivisor, oneChip, d.coreVertex_eq_iff,
    eq_comm]

theorem divisor_interiorVertex_eq_zero (e : Fin 12)
    (o : Fin (d.length e - 1)) :
    cfg.divisor d (d.interiorVertex e o) = 0 := by
  simp [divisor, fourChipDivisor, oneChip, DegSpec.coreVertex,
    DegSpec.interiorVertex]

/-- A slot from a chip-free class to a chip cannot have collapsed. -/
theorem length_pos_of_incident_chip {center chip : Fin 8} {edge : Fin 12}
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

/-! ### Incidence facts transported to a degenerate spec -/

theorem ends_firstArm (hCore : d.core = cfg.core) {center : Fin 8}
    (hCenter : cfg.isCenter center = true) :
    Ends d.core (cfg.firstArm center) center (cfg.firstChip center) := by
  rw [hCore]
  exact cfg.firstArm_ends center hCenter

theorem ends_secondArm (hCore : d.core = cfg.core) {center : Fin 8}
    (hCenter : cfg.isCenter center = true) :
    Ends d.core (cfg.secondArm center) center (cfg.secondChip center) := by
  rw [hCore]
  exact cfg.secondArm_ends center hCenter

theorem ends_thirdArm (hCore : d.core = cfg.core) {center : Fin 8}
    (hCenter : cfg.isCenter center = true) :
    Ends d.core (cfg.thirdArm center) center (cfg.thirdChip center) := by
  rw [hCore]
  exact cfg.thirdArm_ends center hCenter

theorem not_incident_of_ne {center : Fin 8}
    (hCenter : cfg.isCenter center = true) {e : Fin 12}
    (h1 : e ≠ cfg.firstArm center) (h2 : e ≠ cfg.secondArm center)
    (h3 : e ≠ cfg.thirdArm center) :
    cfg.core.tail e ≠ center ∧ cfg.core.head e ≠ center := by
  constructor <;> intro h
  · rcases cfg.incident_slots center hCenter e (Or.inl h) with h' | h' | h'
    exacts [h1 h', h2 h', h3 h']
  · rcases cfg.incident_slots center hCenter e (Or.inr h) with h' | h' | h'
    exacts [h1 h', h2 h', h3 h']

/-! ### The interpolation height -/

/-- The shortest of the three arms at a centre. -/
def tripodHeight (center : Fin 8) : ℕ :=
  min (d.length (cfg.firstArm center))
    (min (d.length (cfg.secondArm center)) (d.length (cfg.thirdArm center)))

theorem tripodHeight_le_first (center : Fin 8) :
    cfg.tripodHeight d center ≤ d.length (cfg.firstArm center) := by
  simp [tripodHeight]

theorem tripodHeight_le_second (center : Fin 8) :
    cfg.tripodHeight d center ≤ d.length (cfg.secondArm center) := by
  simp [tripodHeight]

theorem tripodHeight_le_third (center : Fin 8) :
    cfg.tripodHeight d center ≤ d.length (cfg.thirdArm center) := by
  simp [tripodHeight]

theorem tripodHeight_eq_arm (center : Fin 8) :
    cfg.tripodHeight d center = d.length (cfg.firstArm center) ∨
      cfg.tripodHeight d center = d.length (cfg.secondArm center) ∨
      cfg.tripodHeight d center = d.length (cfg.thirdArm center) :=
  min_three_eq_one _ _ _

theorem tripodHeight_pos (hCore : d.core = cfg.core) {center : Fin 8}
    (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0) :
    0 < cfg.tripodHeight d center := by
  have hFirst := cfg.length_pos_of_incident_chip d
    (cfg.firstChip_isChip center hCenter) (cfg.ends_firstArm d hCore hCenter)
    hZero
  have hSecond := cfg.length_pos_of_incident_chip d
    (cfg.secondChip_isChip center hCenter) (cfg.ends_secondArm d hCore hCenter)
    hZero
  have hThird := cfg.length_pos_of_incident_chip d
    (cfg.thirdChip_isChip center hCenter) (cfg.ends_thirdArm d hCore hCenter)
    hZero
  simp only [tripodHeight]
  omega

/-! ### Which core classes a tripod centre can meet -/

/-- Every neighbour of a tripod centre is a chip vertex. -/
theorem adjacent_chip {l : List (Fin 12)} {center v : Fin 8}
    (hCenter : cfg.isCenter center = true)
    (hAdjacent : AdjInList cfg.core l center v) : cfg.IsChip v := by
  obtain ⟨e, _he, huv⟩ := hAdjacent
  have hEnds : Ends cfg.core e center v := by
    rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
  have hInc : cfg.core.tail e = center ∨ cfg.core.head e = center := by
    rcases hEnds with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2
  have hNot := cfg.center_not_chip center hCenter
  rcases cfg.incident_slots center hCenter e hInc with rfl | rfl | rfl
  · rcases hEnds.pair_eq (cfg.firstArm_ends center hCenter) with ⟨_, h⟩ | ⟨h, _⟩
    · exact h ▸ cfg.firstChip_isChip center hCenter
    · exact absurd (h ▸ cfg.firstChip_isChip center hCenter) hNot
  · rcases hEnds.pair_eq (cfg.secondArm_ends center hCenter) with
        ⟨_, h⟩ | ⟨h, _⟩
    · exact h ▸ cfg.secondChip_isChip center hCenter
    · exact absurd (h ▸ cfg.secondChip_isChip center hCenter) hNot
  · rcases hEnds.pair_eq (cfg.thirdArm_ends center hCenter) with
        ⟨_, h⟩ | ⟨h, _⟩
    · exact h ▸ cfg.thirdChip_isChip center hCenter
    · exact absurd (h ▸ cfg.thirdChip_isChip center hCenter) hNot

/-- A zero-edge class containing a chip-free tripod centre is a singleton. -/
theorem reach_eq_center_of_no_chip {F : Finset (Fin 12)} {center v : Fin 8}
    (hCenter : cfg.isCenter center = true)
    (hNoChip : ∀ s : Fin 8, cfg.IsChip s → ¬ReachIn cfg.core F center s)
    (hReach : ReachIn cfg.core F center v) : v = center := by
  induction hReach with
  | refl => rfl
  | @tail b c hPrefix hLast ih =>
      subst b
      exact (hNoChip c (cfg.adjacent_chip hCenter hLast)
        (hPrefix.tail hLast)).elim

/-- A zero-divisor class at a tripod centre is that centre alone. -/
theorem singleton_class_of_divisor_zero (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn cfg.core F x y)
    {center : Fin 8} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0) :
    ∀ v : Fin 8, d.rep v = d.rep center ↔ v = center := by
  have hNoChip : ∀ s : Fin 8, cfg.IsChip s →
      ¬ReachIn cfg.core F center s := by
    intro s hs hReach
    have hRep : d.rep s = d.rep center :=
      (hRepReach s center).mpr
        (reachInList_symmetric cfg.core (edgeList F) hReach)
    have hOne := cfg.one_le_divisor_of_chip_rep_eq d hs hRep
    omega
  intro v
  constructor
  · intro hEq
    exact cfg.reach_eq_center_of_no_chip hCenter hNoChip
      ((hRepReach center v).mp hEq.symm)
  · rintro rfl
    rfl

/-! ### The interpolated potential -/

/-- The closed-face core potential for configuration 2: the tripod height on
the centre's class and zero elsewhere. -/
abbrev centerPotential (center : Fin 8) : Fin 8 → ℤ :=
  ConfigurationCommon.centerPotential d center (cfg.tripodHeight d center)

theorem centerPotential_center (center : Fin 8) :
    cfg.centerPotential d center center =
      -(cfg.tripodHeight d center : ℤ) := by
  simp [ConfigurationCommon.centerPotential]

theorem centerPotential_eq_zero (center : Fin 8) {v : Fin 8}
    (h : d.rep v ≠ d.rep center) : cfg.centerPotential d center v = 0 := by
  simp [ConfigurationCommon.centerPotential, h]

theorem rep_chip_ne_center (center : Fin 8) {chip : Fin 8}
    (hChip : cfg.IsChip chip) (hCenter : cfg.isCenter center = true)
    (hSingleton : ∀ v : Fin 8, d.rep v = d.rep center ↔ v = center) :
    d.rep chip ≠ d.rep center := fun h =>
  cfg.center_not_chip center hCenter ((hSingleton chip).mp h ▸ hChip)

/-! ### The chip delivered to the centre -/

theorem endpointContribution_eq_center_slots (hCore : d.core = cfg.core)
    (potential : Fin 8 → ℤ) {center : Fin 8}
    (hCenter : cfg.isCenter center = true) :
    ConfigurationCommon.endpointContribution d potential center =
      slotTerm d potential (cfg.firstArm center) center +
      slotTerm d potential (cfg.secondArm center) center +
      slotTerm d potential (cfg.thirdArm center) center := by
  rw [endpointContribution_eq_sum]
  refine sum_three _ (cfg.firstArm_ne_secondArm center hCenter)
    (cfg.firstArm_ne_thirdArm center hCenter)
    (cfg.secondArm_ne_thirdArm center hCenter) ?_
  intro x h1 h2 h3
  obtain ⟨hT, hH⟩ := cfg.not_incident_of_ne hCenter h1 h2 h3
  simp only [slotTerm, hCore, if_neg hT, if_neg hH, add_zero]

theorem endpointContribution_center_eq_arms (hCore : d.core = cfg.core)
    {center : Fin 8} (hCenter : cfg.isCenter center = true)
    (hSingleton : ∀ v : Fin 8, d.rep v = d.rep center ↔ v = center) :
    ConfigurationCommon.endpointContribution d (cfg.centerPotential d center)
        center =
      armContribution d center (cfg.firstArm center)
          (cfg.tripodHeight d center) +
      armContribution d center (cfg.secondArm center)
          (cfg.tripodHeight d center) +
      armContribution d center (cfg.thirdArm center)
          (cfg.tripodHeight d center) := by
  rw [cfg.endpointContribution_eq_center_slots d hCore _ hCenter,
    slotTerm_eq_slotValue d _ (cfg.ends_firstArm d hCore hCenter)
      (cfg.chip_ne_center (cfg.firstChip_isChip center hCenter) hCenter),
    slotTerm_eq_slotValue d _ (cfg.ends_secondArm d hCore hCenter)
      (cfg.chip_ne_center (cfg.secondChip_isChip center hCenter) hCenter),
    slotTerm_eq_slotValue d _ (cfg.ends_thirdArm d hCore hCenter)
      (cfg.chip_ne_center (cfg.thirdChip_isChip center hCenter) hCenter),
    cfg.centerPotential_center d center,
    cfg.centerPotential_eq_zero d center
      (cfg.rep_chip_ne_center d center (cfg.firstChip_isChip center hCenter)
        hCenter hSingleton),
    cfg.centerPotential_eq_zero d center
      (cfg.rep_chip_ne_center d center (cfg.secondChip_isChip center hCenter)
        hCenter hSingleton),
    cfg.centerPotential_eq_zero d center
      (cfg.rep_chip_ne_center d center (cfg.thirdChip_isChip center hCenter)
        hCenter hSingleton)]
  simp only [armContribution_eq_slotValue]

theorem endpointContribution_center_ge_one (hCore : d.core = cfg.core)
    {center : Fin 8} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    (hSingleton : ∀ v : Fin 8, d.rep v = d.rep center ↔ v = center) :
    1 ≤ ConfigurationCommon.endpointContribution d
      (cfg.centerPotential d center) center := by
  have hHeight := cfg.tripodHeight_pos d hCore hCenter hZero
  have hFirstLe := cfg.tripodHeight_le_first d center
  have hSecondLe := cfg.tripodHeight_le_second d center
  have hThirdLe := cfg.tripodHeight_le_third d center
  have hFirst := armContribution_nonneg d center (cfg.firstArm center)
    hFirstLe (by omega)
  have hSecond := armContribution_nonneg d center (cfg.secondArm center)
    hSecondLe (by omega)
  have hThird := armContribution_nonneg d center (cfg.thirdArm center)
    hThirdLe (by omega)
  rw [cfg.endpointContribution_center_eq_arms d hCore hCenter hSingleton]
  rcases cfg.tripodHeight_eq_arm d center with hFull | hFull | hFull
  · have hOne := armContribution_eq_one_of_full d center (cfg.firstArm center)
      hFull (by omega)
    omega
  · have hOne := armContribution_eq_one_of_full d center (cfg.secondArm center)
      hFull (by omega)
    omega
  · have hOne := armContribution_eq_one_of_full d center (cfg.thirdArm center)
      hFull (by omega)
    omega

/-! ### The Laplacian away from the fired class -/

theorem coreRise_eq_zero_of_not_center (hCore : d.core = cfg.core)
    {potential : Fin 8 → ℤ} {center : Fin 8}
    (hCenter : cfg.isCenter center = true)
    (hSupport : ∀ v : Fin 8, v ≠ center → potential v = 0)
    {e : Fin 12} (h1 : e ≠ cfg.firstArm center)
    (h2 : e ≠ cfg.secondArm center) (h3 : e ≠ cfg.thirdArm center) :
    d.coreRise potential e = 0 := by
  obtain ⟨hT, hH⟩ := cfg.not_incident_of_ne hCenter h1 h2 h3
  simp only [DegSpec.coreRise, hCore]
  rw [hSupport _ hH, hSupport _ hT]
  ring

theorem prin_center_nonTarget_eq (hCore : d.core = cfg.core)
    {center : Fin 8} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    (hSingleton : ∀ v : Fin 8, d.rep v = d.rep center ↔ v = center)
    (r : Fin 8) (hNotTarget : d.rep r ≠ d.rep center) :
    prin d.graph (d.interpolatedScript (cfg.centerPotential d center))
        (d.coreVertex r) =
      -chipInd d r (cfg.firstChip center) -
      chipInd d r (cfg.secondChip center) -
      chipInd d r (cfg.thirdChip center) := by
  have hInv := ConfigurationCommon.centerPotential_repInvariant d center
    (cfg.tripodHeight d center)
  have hHeightPos := cfg.tripodHeight_pos d hCore hCenter hZero
  have hSupport : ∀ v : Fin 8, v ≠ center →
      cfg.centerPotential d center v = 0 := by
    intro v hv
    exact cfg.centerPotential_eq_zero d center
      (fun h => hv ((hSingleton v).mp h))
  have hFirstLe := cfg.tripodHeight_le_first d center
  have hSecondLe := cfg.tripodHeight_le_second d center
  have hThirdLe := cfg.tripodHeight_le_third d center
  rw [d.prin_interpolatedScript_coreVertex_eq_endpointSum hInv]
  change (∑ e : Fin 12,
    ConfigurationCommon.endpointPair d (cfg.centerPotential d center) e r) = _
  rw [sum_three _ (cfg.firstArm_ne_secondArm center hCenter)
    (cfg.firstArm_ne_thirdArm center hCenter)
    (cfg.secondArm_ne_thirdArm center hCenter)
    (fun x h1 h2 h3 =>
      ConfigurationCommon.endpointPair_eq_zero_of_rise_eq_zero d _ x r
        (cfg.coreRise_eq_zero_of_not_center d hCore hCenter hSupport
          h1 h2 h3))]
  rw [endpointPair_arm d _ (cfg.ends_firstArm d hCore hCenter)
      (cfg.centerPotential_center d center)
      (cfg.centerPotential_eq_zero d center
        (cfg.rep_chip_ne_center d center (cfg.firstChip_isChip center hCenter)
          hCenter hSingleton))
      (by omega) hFirstLe hNotTarget.symm,
    endpointPair_arm d _ (cfg.ends_secondArm d hCore hCenter)
      (cfg.centerPotential_center d center)
      (cfg.centerPotential_eq_zero d center
        (cfg.rep_chip_ne_center d center (cfg.secondChip_isChip center hCenter)
          hCenter hSingleton))
      (by omega) hSecondLe hNotTarget.symm,
    endpointPair_arm d _ (cfg.ends_thirdArm d hCore hCenter)
      (cfg.centerPotential_center d center)
      (cfg.centerPotential_eq_zero d center
        (cfg.rep_chip_ne_center d center (cfg.thirdChip_isChip center hCenter)
          hCenter hSingleton))
      (by omega) hThirdLe hNotTarget.symm,
    drain_eq_one hHeightPos]
  simp only [chipInd]
  ring

/-! ### Residual effectivity and reach -/

theorem residual_effective_of_coreVertex {potential : Fin 8 → ℤ}
    (hInv : d.RepInvariant potential) (center : Fin 8)
    (hCoreCase : ∀ r : Fin 8,
      0 ≤ cfg.divisor d (d.coreVertex r) -
        oneChip (G := d.graph) (d.coreVertex center) (d.coreVertex r) +
        prin d.graph (d.interpolatedScript potential) (d.coreVertex r)) :
    effective (cfg.divisor d - oneChip (d.coreVertex center) +
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
      oneChip (G := d.graph) (d.coreVertex center) (d.interiorVertex e o) +
      prin d.graph (d.interpolatedScript potential) (d.interiorVertex e o)
    have hNe : d.interiorVertex e o ≠ d.coreVertex center := by
      simp [DegSpec.coreVertex, DegSpec.interiorVertex]
    rw [cfg.divisor_interiorVertex_eq_zero]
    simp only [oneChip, if_neg hNe, sub_zero, zero_add]
    exact d.prin_interpolatedScript_interiorVertex_nonneg hInv e o

/-- **Configuration 2 at one centre.**  Firing the tripod script leaves an
effective divisor after removing one chip from the centre's class. -/
theorem center_residual_effective (hCore : d.core = cfg.core)
    {center : Fin 8} (hCenter : cfg.isCenter center = true)
    (hZero : cfg.divisor d (d.coreVertex center) = 0)
    (hSingleton : ∀ v : Fin 8, d.rep v = d.rep center ↔ v = center) :
    effective (cfg.divisor d - oneChip (d.coreVertex center) +
      prin d.graph
        (d.interpolatedScript (cfg.centerPotential d center))) := by
  have hInv := ConfigurationCommon.centerPotential_repInvariant d center
    (cfg.tripodHeight d center)
  refine cfg.residual_effective_of_coreVertex d hInv center ?_
  intro r
  by_cases hAtTarget : d.rep r = d.rep center
  · have hrCenter : r = center := (hSingleton r).mp hAtTarget
    subst hrCenter
    rw [hZero, d.prin_interpolatedScript_coreVertex_eq_classSum hInv]
    have hFilter : Finset.univ.filter
        (fun v : Fin 8 => d.rep v = d.rep r) = {r} := by
      ext v
      simp [hSingleton v]
    rw [hFilter]
    simp only [Finset.sum_singleton]
    have hContribution := cfg.endpointContribution_center_ge_one d hCore
      hCenter hZero hSingleton
    change (0 : ℤ) ≤ 0 - oneChip (G := d.graph) (d.coreVertex r)
      (d.coreVertex r) +
      ConfigurationCommon.endpointContribution d (cfg.centerPotential d r) r
    simp only [oneChip]
    omega
  · have hCoreNe : d.coreVertex center ≠ d.coreVertex r := by
      intro hEq
      exact hAtTarget ((d.coreVertex_eq_iff r center).mp hEq.symm)
    rw [show oneChip (G := d.graph) (d.coreVertex center)
        (d.coreVertex r) = 0 by simp [oneChip, hCoreNe.symm]]
    rw [cfg.divisor_coreVertex_eq,
      cfg.prin_center_nonTarget_eq d hCore hCenter hZero hSingleton r
        hAtTarget,
      cfg.chipSum center hCenter (chipInd d r)]
    have hSpare := chipInd_nonneg d r (cfg.spareChip center)
    linarith

/-- **Configuration 2 reaches its centre.**  This is the statement a row
consumes, one centre at a time, so that several local pictures compose. -/
theorem reaches_center (hCore : d.core = cfg.core) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8,
      d.rep x = d.rep y ↔ ReachIn cfg.core F x y)
    {center : Fin 8} (hCenter : cfg.isCenter center = true) :
    Reaches d.graph (cfg.divisor d) (d.coreVertex center) := by
  by_cases hZero : cfg.divisor d (d.coreVertex center) = 0
  · exact (DharMove.ofScript
      (d.interpolatedScript (cfg.centerPotential d center))
      (cfg.center_residual_effective d hCore hCenter hZero
        (cfg.singleton_class_of_divisor_zero d F hRepReach hCenter
          hZero))).reaches
  · have hEffective := cfg.divisor_effective d
    have hChip : 1 ≤ cfg.divisor d (d.coreVertex center) := by
      have hNonneg := hEffective (d.coreVertex center)
      omega
    exact reaches_of_effective_representative
      (linearEquiv.refl d.graph (cfg.divisor d)) hEffective hChip

/-- **Configuration 2 on a closed face.**  A row every one of whose chip-free
vertices is a tripod centre gets the whole closed-orthant AR construction. -/
theorem closedConstruction (hConnected : cfg.core.Connected)
    (hCenters : ∀ v : Fin 8, ¬cfg.IsChip v → cfg.isCenter v = true) :
    ClosedSubdivisionDharConstruction cfg.core (by norm_num) :=
  ClosedSubdivisionDharConstruction.ofReachesCoreClasses (by norm_num)
    hConnected (fun d => cfg.divisor d) (fun d => cfg.divisor_effective d)
    (fun d => cfg.deg_divisor d)
    (fun d hCore hRepReach center => by
      by_cases hChip : cfg.IsChip center
      · exact reaches_of_effective_representative
          (linearEquiv.refl d.graph (cfg.divisor d)) (cfg.divisor_effective d)
          (cfg.one_le_divisor_at_chip d hChip)
      · exact cfg.reaches_center d hCore (zeroSlots d.length) hRepReach
          (hCenters center hChip))

end ConfigTwo

end AtanasovRanganathan.ConfigurationTwo
