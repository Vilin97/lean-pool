/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationTwo

/-!
# Guarding sets: the abstract glue of an Atanasov--Ranganathan row proof

Read the finished genus-five rows side by side and the same shape appears in
every one of them.  A row fixes a **core-supported chip assignment** and then
shows that every *chip-free* core vertex is the centre of some local picture
from the configuration library; the chip vertices need no argument at all,
because a divisor that already has a chip at `v` reaches `v`.  `GenusFiveRow12`
writes that idiom out in the open: its `centers_cover` says the two `isCenter`
tables between them name every chip-free vertex, and the two pictures'
`reaches_center` lemmas are then glued by hand.

This file names the idiom.  A `GuardingSet` for a core is a nonnegative core
weight of total degree four together with, for each chip-free vertex, a proof
that the induced divisor reaches that vertex on every degenerate spec.  The
main theorem turns one into a `ClosedSubdivisionDharConstruction`, so a row
proof becomes: *exhibit a guarding set*.

## Which rows of the atlas are guarding sets

Thirteen of the sixteen genus-five rows close through `closedConstruction`
below.  The other three cannot, and the reason splits in two:

| rows | status |
|---|---|
| 01, 02, 03, 04, 06, 07, 09, 12, 14 | a `GuardingSet` is the row's proof |
| 11, 13, 15, 16 | one configuration instance covers *every* chip-free vertex, so `ConfigTwo.closedConstruction` / `ConfigThree.closedConstruction` already close them in a line -- see the note below |
| 05 | a core-supported uniform divisor exists (`1_{2,3,4,5}`), but no library picture recognises its chip-free set: two banana pairs with **unequal** arms.  A *library gap* |
| 08, 10 | **no** core-supported degree-four divisor is uniformly rank one.  An interior chip is forced, and no unmarked guarding set can exist at this degree |

The two failure modes are the genus-five instances of
auxiliary calculations §2a, and the classification there was reached
with a rank oracle (direct Dhar reduction), not a certificate-search proxy.
Row 05's entry is a correction: its own docstring used to claim it had no
core-supported divisor at all, and so did row 01's before row 01 was reproved
from `{2, 3, 4, 5}`.

Rows 11, 13, 15 and 16 are *not* converted, and the obstruction is structural
rather than cosmetic: `ConfigTwo` and `ConfigThree` do not require their four
chip vertices to be pairwise distinct -- `chipSum` stands in for that -- so a
generic instance's displayed `fourChipDivisor` need not be the class divisor
of any weight, and `ConfigX.closedConstruction` cannot be re-derived from
`closedConstruction` at the library level.  On those four rows the chips do
happen to be distinct, but paying `coreClassDivisor_eq_fourChipDivisor` to say
so makes the proof longer, not shorter.

Nothing here is new mathematics; it is the statement that the per-row gluing
step is generic.  What that buys is a precise reduction: with this theorem in
hand, Brill--Noether existence for a family of cores is exactly the pure graph
theory question "does every core in the family admit a guarding set?", with no
Dhar arithmetic left in it.  The numerical side of that question is probed in
auxiliary calculations.

## Why the chip side is free

`chip_reaches` below is the whole argument for a vertex that carries a chip:
the class of `v` in the contracted core carries at least the weight of `v`
itself, because all the other weights are nonnegative, so the divisor is its
own effective representative with a chip at `v`.

## Relation to the configuration library

Every configuration file already proves exactly the field `guard` asks for,
one centre at a time and stated against an arbitrary `DegSpec` whose core is
the fixed one and whose representative map is reachability through the zero
slots -- see `ConfigurationTwo.ConfigTwo.reaches_center`,
`ConfigurationThree.ConfigThree.reaches_center`, and the `reaches` lemmas of
the reservoir, banana-tail, chipped-triangle and three-chain files.  The one
adjustment is bookkeeping: those files display their divisor as a
`fourChipDivisor` on four named core vertices, whereas a guarding set carries
a weight function.  `coreClassDivisor_eq_fourChipDivisor` below is that
translation, proved for four pairwise-distinct chips.
-/

namespace AtanasovRanganathan.Guarding

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations

variable {n p : ℕ}

/-- **A guarding set for a core.**

`chips` is the divisor, supported on core vertices; `guard` is the only
per-graph content of an AR row proof, and the configuration library is the
list of ways it is ever discharged. -/
structure GuardingSet (core : Core n p) where
  /-- The core-supported chip assignment. -/
  chips : Fin n → ℤ
  /-- Chips are chips. -/
  chips_nonneg : ∀ v : Fin n, 0 ≤ chips v
  /-- The critical pencil's degree. -/
  chips_deg : ∑ v : Fin n, chips v = 4
  /-- Every chip-free core vertex is reached, on every degenerate spec over
  this core whose classes are the zero-slot components.  This is precisely the
  statement each configuration file proves for its centres. -/
  guard : ∀ v : Fin n, chips v = 0 → ∀ d : DegSpec n p, d.core = core →
    (∀ x y : Fin n,
      d.rep x = d.rep y ↔ ReachIn core (zeroSlots d.length) x y) →
    Reaches d.graph (d.coreClassDivisor chips) (d.coreVertex v)

namespace GuardingSet

variable {core : Core n p} (G : GuardingSet core)

/-- The displayed divisor on one degenerate spec. -/
abbrev divisor (d : DegSpec n p) : CFDiv d.graph := d.coreClassDivisor G.chips

theorem divisor_effective (d : DegSpec n p) : effective (G.divisor d) :=
  d.coreClassDivisor_effective G.chips G.chips_nonneg

theorem divisor_degree (d : DegSpec n p) : deg (G.divisor d) = 4 := by
  rw [DegSpec.deg_coreClassDivisor]
  exact G.chips_deg

/-- A vertex carrying a chip contributes its own weight to its class, and the
other members of the class contribute nothing negative.  A corollary of
`DegSpec.one_le_coreClassDivisor_of_chip`, which is the same fact for an
arbitrary core weight. -/
theorem one_le_divisor_of_chip {d : DegSpec n p} {v : Fin n}
    (hv : 1 ≤ G.chips v) : 1 ≤ G.divisor d (d.coreVertex v) :=
  d.one_le_coreClassDivisor_of_chip G.chips G.chips_nonneg hv

/-- **A centre whose contracted class carries a chip needs no picture.**  The
divisor is its own effective representative, and it already has a chip at the
class, so `v` is reached.

This is the abstract form of `chip_reaches`: its proof never used
`1 ≤ G.chips v`, only `1 ≤ G.divisor d (d.coreVertex v)`, which is strictly
weaker — the chip may sit on any *other* member of `v`'s contracted class.
That is what makes the collapsed-arm cases of a row's guard obligation
disappear rather than having to be discharged. -/
theorem classChip_reaches {d : DegSpec n p} {v : Fin n}
    (hClass : 1 ≤ G.divisor d (d.coreVertex v)) :
    Reaches d.graph (G.divisor d) (d.coreVertex v) :=
  reaches_of_effective_representative
    (linearEquiv.refl d.graph (G.divisor d)) (G.divisor_effective d) hClass

/-- **A vertex carrying a chip needs no picture.** -/
theorem chip_reaches {d : DegSpec n p} {v : Fin n} (hv : 1 ≤ G.chips v) :
    Reaches d.graph (G.divisor d) (d.coreVertex v) :=
  G.classChip_reaches (G.one_le_divisor_of_chip hv)

/-- Every contracted core class is reached: the chip vertices for free, the
chip-free ones by their guarding picture. -/
theorem reaches_coreVertex (d : DegSpec n p) (hCore : d.core = core)
    (hRepReach : ∀ x y : Fin n,
      d.rep x = d.rep y ↔ ReachIn core (zeroSlots d.length) x y)
    (v : Fin n) : Reaches d.graph (G.divisor d) (d.coreVertex v) := by
  rcases eq_or_lt_of_le (G.chips_nonneg v) with hzero | hpos
  · exact G.guard v hzero.symm d hCore hRepReach
  · exact G.chip_reaches (by omega)

/-- **The main theorem.**  A guarding set is a closed-orthant
Atanasov--Ranganathan construction: the displayed divisor is a rank-one pencil
of degree four simultaneously on the open cell and on every nonloopy forest
face of the length orthant.

This is the abstract form of every row's closing theorem.  `GenusFiveRow12`'s
`centers_cover` argument is the special case where the guard is discharged by
one `ConfigTwo` and one `ConfigThree` instance. -/
theorem closedConstruction (G : GuardingSet core) (core_nonempty : 0 < n)
    (hConnected : core.Connected) :
    ClosedSubdivisionDharConstruction core core_nonempty :=
  ClosedSubdivisionDharConstruction.ofReachesCoreClasses core_nonempty
    hConnected G.divisor G.divisor_effective G.divisor_degree
    G.reaches_coreVertex

end GuardingSet

/-! ## Translating the library's displayed divisor

The configuration files display their divisor as `fourChipDivisor` on four
named core vertices.  A guarding set carries a weight function instead, so
that "chip free" is a statement about the weight and not about a list.  The
two agree as soon as the four names are pairwise distinct. -/

/-- The weight of the four-chip divisor: one on each named vertex. -/
def fourChipWeight (a b c e : Fin n) (v : Fin n) : ℤ :=
  if ConfigurationThree.IsChipOf a b c e v then 1 else 0

theorem fourChipWeight_nonneg (a b c e v : Fin n) : 0 ≤ fourChipWeight a b c e v := by
  unfold fourChipWeight
  split_ifs <;> norm_num

theorem fourChipWeight_eq_zero_iff {a b c e v : Fin n} :
    fourChipWeight a b c e v = 0 ↔ ¬ ConfigurationThree.IsChipOf a b c e v := by
  unfold fourChipWeight
  split_ifs with h <;> simp [h]

theorem one_le_fourChipWeight {a b c e v : Fin n}
    (h : ConfigurationThree.IsChipOf a b c e v) : 1 ≤ fourChipWeight a b c e v := by
  simp [fourChipWeight, h]

/-- Summing anything against the four-chip indicator picks out the four
named vertices, as soon as they are pairwise distinct. -/
theorem sum_over_four_chips {a b c e : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) (g : Fin n → ℤ) :
    ∑ v : Fin n, (if ConfigurationThree.IsChipOf a b c e v then g v else 0)
      = g a + g b + g c + g e := by
  classical
  have hmem : ∀ v : Fin n,
      (if ConfigurationThree.IsChipOf a b c e v then g v else 0)
        = if v ∈ ({a, b, c, e} : Finset (Fin n)) then g v else 0 := by
    intro v
    refine if_congr ?_ rfl rfl
    simp [ConfigurationThree.IsChipOf]
  rw [Finset.sum_congr rfl fun v _ => hmem v, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_insert (by simp [hab, hac, hae]),
    Finset.sum_insert (by simp [hbc, hbe]),
    Finset.sum_insert (by simp [hce]), Finset.sum_singleton, add_assoc,
    add_assoc]

theorem fourChipWeight_deg {a b c e : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    ∑ v : Fin n, fourChipWeight a b c e v = 4 := by
  have h := sum_over_four_chips hab hac hae hbc hbe hce (fun _ => (1 : ℤ))
  simpa [fourChipWeight] using h

/-- **The library's displayed divisor is a core-class divisor.**  With four
pairwise-distinct chip vertices, `fourChipDivisor` on their contracted classes
is exactly the class divisor of the indicator weight, so a configuration
instance can be read as a guarding picture without changing its divisor. -/
theorem coreClassDivisor_eq_fourChipDivisor (d : DegSpec n p) {a b c e : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e)
    (hce : c ≠ e) :
    d.coreClassDivisor (fourChipWeight a b c e) =
      fourChipDivisor (d.coreVertex a) (d.coreVertex b) (d.coreVertex c)
        (d.coreVertex e) := by
  classical
  have hclass : ∀ r : Fin n,
      d.coreClassDivisor (fourChipWeight a b c e) (d.coreVertex r) =
        fourChipDivisor (G := d.graph) (d.coreVertex a) (d.coreVertex b)
          (d.coreVertex c) (d.coreVertex e) (d.coreVertex r) := by
    intro r
    rw [DegSpec.coreClassDivisor_coreVertex, Finset.sum_filter]
    have hstep : ∀ v : Fin n,
        (if d.rep v = d.rep r then fourChipWeight a b c e v else 0) =
          (if ConfigurationThree.IsChipOf a b c e v then
            (if d.rep v = d.rep r then (1 : ℤ) else 0) else 0) := by
      intro v
      unfold fourChipWeight
      by_cases h : ConfigurationThree.IsChipOf a b c e v <;> simp [h]
    rw [Finset.sum_congr rfl fun v _ => hstep v,
      sum_over_four_chips hab hac hae hbc hbe hce
        (fun v => if d.rep v = d.rep r then (1 : ℤ) else 0)]
    simp only [fourChipDivisor, oneChip, Pi.add_apply, d.coreVertex_eq_iff,
      eq_comm]
  funext vertex
  rcases vertex with cls | interior
  · obtain ⟨r, hr⟩ := cls
    have hVertex : (Sum.inl ⟨r, hr⟩ : d.Vertex) = d.coreVertex r := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hr.symm
    rw [hVertex]
    exact hclass r
  · obtain ⟨f, o⟩ := interior
    change d.coreClassDivisor (fourChipWeight a b c e) (d.interiorVertex f o) = _
    simp [DegSpec.coreClassDivisor, fourChipDivisor, oneChip,
      DegSpec.coreVertex, DegSpec.interiorVertex]

end AtanasovRanganathan.Guarding
