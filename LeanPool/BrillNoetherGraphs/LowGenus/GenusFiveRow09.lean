/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ClosedConstructionTail
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationChippedTriangle
public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedRow
public import LeanPool.BrillNoetherGraphs.LowGenus.GuardingSet

/-!
# The Atanasov--Ranganathan construction on row 09

Row 09 is the last scope of AR's *straightforward cases* figure.  Its core is
two vertex-disjoint triangles joined by two cross edges and by a banana path,

```
 e0 : 0 -> 2 \                    e5 : 3 -> 4 \
 e1 : 2 -> 1  |  near triangle    e6 : 4 -> 5  |  far triangle
 e2 : 1 -> 0 /                    e7 : 5 -> 3 /
 e3 : 2 -> 5     cross            e8 : 0 -> 6     near banana leg
 e4 : 1 -> 4     cross            e9 : 3 -> 7     far banana leg
                                  e10, e11 : 6 == 7
```

The formalization uses the following length-independent divisor:

```
 D = [1] + [2] + [3] + [7]
```

It is core supported, has degree four, and is valid on the *whole* closed nonloopy forest
orthant: one chamber, no interior chip, no marks, no symmetry transport.

Its four chip-free vertices fall into two already-formalized local pictures.

* `{4, 5}` -- the **chipped triangle** of `ConfigurationChippedTriangle`: the
  far triangle `3-4-5` with the chip sitting on `3` and one chip arm from each
  vertex.  Read at the target `4` with `al = |e4|`, `be = |e3|`, `ga = |e9|`,
  `p = |e5|`, `q = |e6|`, `r = |e7|`, and at the target `5` with `al ↔ be`,
  `p ↔ r`.
* `{0, 6}` -- AR's **Fifth** picture, `ConfigurationFive`: outer centre `0`,
  inner centre `6`, cycle vertex `7`, boundary arms `la = |e0|` and `lb = |e2|`,
  middle `c = |e8|`, parallel slots `|e10|, |e11|`, far slot `b = |e9|`.

Both pictures see all four chips, and they share the slot `e9` and the chip at
`7`; nothing forbids that, since only `D_v ≤ D` is ever asked.  Every height is
a nested minimum of slot lengths, hence constant across a collapsed slot, so one
script covers the open cell and every nonloopy forest face at once.

Each triangle of core 09 is a *directed* 3-cycle, so the two boundary arms at
the outer centre `0` are read in opposite orientations (`e0` forward, `e2`
backward).  That is why `ConfigurationFive.outerTarget_center_nonneg` and
`innerTarget_center_nonneg` carry two independent `SlotLedger`s.

The endpoint plumbing is `ConfigurationMarkedRow`'s, instantiated at the
identically-zero mark `noMark`, which recovers the ordinary one-ramp script
definitionally; no slot of row 09 carries a chip in its interior.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow09

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
open ConfigurationMarkedThree
open ConfigurationMarkedRow
open ConfigurationChippedTriangle

/-! ## No marks

Row 09's divisor is core supported, so every slot is an ordinary single ramp.
Passing the identically-zero mark through `ConfigurationMarkedRow` recovers
exactly that, and buys the whole residual-effectivity wrapper unchanged. -/

/-- The zero mark: no slot of row 09 carries an interior chip. -/
def noMark : Fin 12 → ℕ := fun _ => 0

@[simp] theorem noMark_apply (e : Fin 12) : noMark e = 0 := rfl

/-- A height profile with no marks needs only class constancy. -/
theorem mkProfile {d : DegSpec 8 12} (hCore : d.core = row09Core)
    {h : Fin 8 → ℕ}
    (hconst : ∀ e : Fin 12, d.length e = 0 →
      h (row09Core.tail e) = h (row09Core.head e)) :
    Profile d noMark h := by
  refine ⟨fun e => Nat.zero_le _, ?_, ?_, ?_, ?_⟩
  · intro e he; simp [noMark] at he
  · intro e he; simp [noMark] at he
  · intro e he; simp [noMark] at he
  · intro e he
    rw [hCore]
    exact hconst e he

/-! ## The divisor -/

/-- `D = [1] + [2] + [3] + [7]`. -/
def chipWeight (v : Fin 8) : ℤ :=
  if v = 1 then 1 else if v = 2 then 1 else if v = 3 then 1
    else if v = 7 then 1 else 0

theorem chipWeight_nonneg (v : Fin 8) : 0 ≤ chipWeight v := by
  unfold chipWeight; split_ifs <;> norm_num

theorem sum_chipWeight : ∑ v : Fin 8, chipWeight v = 4 := by decide

/-- The row-09 divisor obtained by placing one chip at each of vertices 1, 2, 3, and 7 and
passing to core equivalence classes. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph := d.coreClassDivisor chipWeight

theorem rowDivisor_effective (d : DegSpec 8 12) : effective (rowDivisor d) :=
  d.coreClassDivisor_effective chipWeight chipWeight_nonneg

theorem rowDivisor_degree (d : DegSpec 8 12) : deg (rowDivisor d) = 4 := by
  rw [rowDivisor, d.deg_coreClassDivisor, sum_chipWeight]

theorem rowDivisor_coreVertex (d : DegSpec 8 12) (r : Fin 8) :
    rowDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v :=
  d.coreClassDivisor_coreVertex chipWeight r

/-! ## The nested-min heights

Two pictures, four readings, all four verbatim from
auxiliary calculations §3.3. -/

/-- `a = min |e0| |e2|`, the outer centre's arm minimum. -/
def armMin (d : DegSpec 8 12) : ℕ := min (d.length 0) (d.length 2)

/-- `m = min |e10| |e11|`, the banana minimum. -/
def parMin (d : DegSpec 8 12) : ℕ := min (d.length 10) (d.length 11)

/-- Outer-target reading: `o = min a (b + m + c)`. -/
def outerO (d : DegSpec 8 12) : ℕ :=
  min (armMin d) (d.length 9 + parMin d + d.length 8)

/-- Outer-target reading: `i = min o (b + m)`. -/
def outerI (d : DegSpec 8 12) : ℕ := min (outerO d) (d.length 9 + parMin d)

/-- Outer-target reading: `e = min i b`. -/
def outerE (d : DegSpec 8 12) : ℕ := min (outerI d) (d.length 9)

/-- Inner-target reading: `i = min (a + c) (b + m)`. -/
def innerI (d : DegSpec 8 12) : ℕ :=
  min (armMin d + d.length 8) (d.length 9 + parMin d)

/-- Inner-target reading: `o = min a i`. -/
def innerO (d : DegSpec 8 12) : ℕ := min (armMin d) (innerI d)

/-- Inner-target reading: `e = min b i`. -/
def innerE (d : DegSpec 8 12) : ℕ := min (d.length 9) (innerI d)

/-- The chipped triangle read at the target `4`:
`al = |e4|`, `be = |e3|`, `ga = |e9|`, `p = |e5|`, `q = |e6|`, `r = |e7|`. -/
def hcT4 (d : DegSpec 8 12) : ℕ :=
  chipHeight (d.length 4) (d.length 3) (d.length 9)

/-- Auxiliary side height for the chipped-triangle script targeting vertex 4, using arms 4 and 3
and slots 9 and 7. -/
def h0T4 (d : DegSpec 8 12) : ℕ :=
  sideHeight (d.length 4) (d.length 3) (d.length 9) (d.length 7)

/-- Height at target vertex 4 in the chipped-triangle script, with connecting slots 5 and 6 and
partner slot 7. -/
def htT4 (d : DegSpec 8 12) : ℕ :=
  targetHeight (d.length 4) (d.length 3) (d.length 9) (d.length 5) (d.length 6)
    (d.length 7)

/-- Height at partner vertex 5 in the chipped-triangle script targeting vertex 4. -/
def hvT4 (d : DegSpec 8 12) : ℕ :=
  partnerHeight (d.length 4) (d.length 3) (d.length 9) (d.length 5) (d.length 6)
    (d.length 7)

/-- The same picture read at the target `5`: `al ↔ be`, `p ↔ r`. -/
def hcT5 (d : DegSpec 8 12) : ℕ :=
  chipHeight (d.length 3) (d.length 4) (d.length 9)

/-- Auxiliary side height for the chipped-triangle script targeting vertex 5, with the two arms
exchanged. -/
def h0T5 (d : DegSpec 8 12) : ℕ :=
  sideHeight (d.length 3) (d.length 4) (d.length 9) (d.length 5)

/-- Height at target vertex 5 in the chipped-triangle script, exchanging the arms and the roles
of slots 5 and 7. -/
def htT5 (d : DegSpec 8 12) : ℕ :=
  targetHeight (d.length 3) (d.length 4) (d.length 9) (d.length 7) (d.length 6)
    (d.length 5)

/-- Height at partner vertex 4 in the chipped-triangle script targeting vertex 5. -/
def hvT5 (d : DegSpec 8 12) : ℕ :=
  partnerHeight (d.length 3) (d.length 4) (d.length 9) (d.length 7) (d.length 6)
    (d.length 5)

theorem boundsT4 (d : DegSpec 8 12) :
    (hcT4 d ≤ d.length 9 ∧ hcT4 d ≤ d.length 4 ∧ hcT4 d ≤ d.length 3)
      ∧ (hcT4 d = d.length 9 ∨ hcT4 d = d.length 4 ∨ hcT4 d = d.length 3)
      ∧ (h0T4 d ≤ d.length 3 ∧ h0T4 d ≤ hcT4 d + d.length 7 ∧ hcT4 d ≤ h0T4 d)
      ∧ (h0T4 d = d.length 3 ∨ h0T4 d = hcT4 d + d.length 7)
      ∧ (htT4 d ≤ d.length 4 ∧ htT4 d ≤ hcT4 d + d.length 5
          ∧ htT4 d ≤ h0T4 d + d.length 6 ∧ hcT4 d ≤ htT4 d)
      ∧ (htT4 d = d.length 4 ∨ htT4 d = hcT4 d + d.length 5
          ∨ htT4 d = h0T4 d + d.length 6)
      ∧ (hvT4 d ≤ h0T4 d ∧ hvT4 d ≤ htT4 d ∧ hcT4 d ≤ hvT4 d
          ∧ htT4 d ≤ hvT4 d + d.length 6 ∧ hvT4 d ≤ hcT4 d + d.length 7
          ∧ hvT4 d ≤ d.length 3)
      ∧ (hvT4 d = h0T4 d ∨ hvT4 d = htT4 d) :=
  bounds rfl rfl rfl rfl

theorem boundsT5 (d : DegSpec 8 12) :
    (hcT5 d ≤ d.length 9 ∧ hcT5 d ≤ d.length 3 ∧ hcT5 d ≤ d.length 4)
      ∧ (hcT5 d = d.length 9 ∨ hcT5 d = d.length 3 ∨ hcT5 d = d.length 4)
      ∧ (h0T5 d ≤ d.length 4 ∧ h0T5 d ≤ hcT5 d + d.length 5 ∧ hcT5 d ≤ h0T5 d)
      ∧ (h0T5 d = d.length 4 ∨ h0T5 d = hcT5 d + d.length 5)
      ∧ (htT5 d ≤ d.length 3 ∧ htT5 d ≤ hcT5 d + d.length 7
          ∧ htT5 d ≤ h0T5 d + d.length 6 ∧ hcT5 d ≤ htT5 d)
      ∧ (htT5 d = d.length 3 ∨ htT5 d = hcT5 d + d.length 7
          ∨ htT5 d = h0T5 d + d.length 6)
      ∧ (hvT5 d ≤ h0T5 d ∧ hvT5 d ≤ htT5 d ∧ hcT5 d ≤ hvT5 d
          ∧ htT5 d ≤ hvT5 d + d.length 6 ∧ hvT5 d ≤ hcT5 d + d.length 5
          ∧ hvT5 d ≤ d.length 4)
      ∧ (hvT5 d = h0T5 d ∨ hvT5 d = htT5 d) :=
  bounds rfl rfl rfl rfl

/-! ## The four height vectors -/

/-- Configuration 5 read at the outer centre `0`. -/
def heightOuter (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then outerO d else if v = 6 then outerI d
    else if v = 7 then outerE d else 0

/-- Configuration 5 read at the inner centre `6`. -/
def heightInner (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 0 then innerO d else if v = 6 then innerI d
    else if v = 7 then innerE d else 0

/-- The chipped triangle read at the target `4`. -/
def heightT4 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 3 then hcT4 d else if v = 4 then htT4 d
    else if v = 5 then hvT4 d else 0

/-- The chipped triangle read at the target `5`. -/
def heightT5 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 3 then hcT5 d else if v = 5 then htT5 d
    else if v = 4 then hvT5 d else 0

theorem profileOuter {d : DegSpec 8 12} (hCore : d.core = row09Core) :
    Profile d noMark (heightOuter d) := by
  refine mkProfile hCore ?_
  intro e
  fin_cases e
  all_goals
    simp [heightOuter, outerO, outerI, outerE, armMin, parMin, row09Core]
  all_goals omega

theorem profileInner {d : DegSpec 8 12} (hCore : d.core = row09Core) :
    Profile d noMark (heightInner d) := by
  refine mkProfile hCore ?_
  intro e
  fin_cases e
  all_goals
    simp [heightInner, innerO, innerI, innerE, armMin, parMin, row09Core]
  all_goals omega

theorem profileT4 {d : DegSpec 8 12} (hCore : d.core = row09Core) :
    Profile d noMark (heightT4 d) := by
  obtain ⟨⟨hcga, hcal, hcbe⟩, -, ⟨h0be, h0hc, hch0⟩, -,
    ⟨htal, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hvbe⟩, -⟩ :=
    boundsT4 d
  refine mkProfile hCore ?_
  intro e
  fin_cases e
  all_goals simp [heightT4, row09Core]
  all_goals omega

theorem profileT5 {d : DegSpec 8 12} (hCore : d.core = row09Core) :
    Profile d noMark (heightT5 d) := by
  obtain ⟨⟨hcga, hcbe, hcal⟩, -, ⟨h0al, h0hc, hch0⟩, -,
    ⟨htbe, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hval⟩, -⟩ :=
    boundsT5 d
  refine mkProfile hCore ?_
  intro e
  fin_cases e
  all_goals simp [heightT5, row09Core]
  all_goals omega

/-! ## The endpoint ledger, vertex by vertex

Each of the eight core vertices is trivalent, so `contribForm` has three terms
per vertex; they are the twenty-four slot ends of row 09 sorted by vertex. -/

/-- The sum of incident tail and head contributions at each row-09 core vertex for a prescribed
height profile. -/
def contribForm (d : DegSpec 8 12) (h : Fin 8 → ℕ) (v : Fin 8) : ℤ :=
  if v = 0 then
    tailContribution (d.length 0) (h 0) (h 2)
      + tailContribution (d.length 8) (h 0) (h 6)
      + headContribution (d.length 2) (h 1) (h 0)
  else if v = 1 then
    tailContribution (d.length 2) (h 1) (h 0)
      + tailContribution (d.length 4) (h 1) (h 4)
      + headContribution (d.length 1) (h 2) (h 1)
  else if v = 2 then
    tailContribution (d.length 1) (h 2) (h 1)
      + tailContribution (d.length 3) (h 2) (h 5)
      + headContribution (d.length 0) (h 0) (h 2)
  else if v = 3 then
    tailContribution (d.length 5) (h 3) (h 4)
      + tailContribution (d.length 9) (h 3) (h 7)
      + headContribution (d.length 7) (h 5) (h 3)
  else if v = 4 then
    tailContribution (d.length 6) (h 4) (h 5)
      + headContribution (d.length 4) (h 1) (h 4)
      + headContribution (d.length 5) (h 3) (h 4)
  else if v = 5 then
    tailContribution (d.length 7) (h 5) (h 3)
      + headContribution (d.length 3) (h 2) (h 5)
      + headContribution (d.length 6) (h 4) (h 5)
  else if v = 6 then
    tailContribution (d.length 10) (h 6) (h 7)
      + tailContribution (d.length 11) (h 6) (h 7)
      + headContribution (d.length 8) (h 0) (h 6)
  else
    headContribution (d.length 9) (h 3) (h 7)
      + headContribution (d.length 10) (h 6) (h 7)
      + headContribution (d.length 11) (h 6) (h 7)

theorem contrib_eq {d : DegSpec 8 12} (hCore : d.core = row09Core)
    {h : Fin 8 → ℕ} (hprof : Profile d noMark h)
    (hRep : ∀ v : Fin 8, h (d.rep v) = h v) (v : Fin 8) :
    positiveEndpointContribution d (heightPotential d h) noMark
        (markValue d noMark h) v = contribForm d h v := by
  rw [contribution_eq d hprof hRep]
  fin_cases v <;>
    simp +decide only [hCore, row09Core, Fin.isValue, Fin.zero_eta, slotTailForm, noMark,
      lt_self_iff_false, ↓reduceIte, slotHeadForm, Fin.sum_univ_succ, Matrix.cons_val_zero,
      add_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, zero_add,
      Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one,
      Fin.reduceEq, Finset.sum_const_zero, contribForm, Fin.mk_one, Fin.reduceFinMk,
      Finset.sum_singleton]<;>
    ring

/-! ## Chip allocations

A collapsed arm puts its chip in the centre's contracted class; the chipped
triangle additionally lends the chip on `3` to its partner when the slot between
them collapses.  Every transfer moves weight *inside* a class, so no class sum
changes. -/

/-- The allocation both configuration-5 readings use. -/
def allocFive (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  chipWeight v
    + (if d.length 0 = 0 then transferWeight 2 0 v else 0)
    + (if d.length 2 = 0 then transferWeight 1 0 v else 0)
    + (if parMin d = 0 then transferWeight 7 6 v else 0)
    + (if d.length 9 = 0 then transferWeight 3 7 v else 0)

/-- The allocation of the chipped triangle read at `4`. -/
def allocT4 (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  chipWeight v
    + (if d.length 4 = 0 then transferWeight 1 4 v else 0)
    + (if d.length 3 = 0 then transferWeight 2 5 v else 0)
    + (if d.length 9 = 0 then transferWeight 7 3 v else 0)
    + (if d.length 7 = 0 ∧ hcT4 d < d.length 3 then transferWeight 3 5 v else 0)

/-- The allocation of the chipped triangle read at `5`. -/
def allocT5 (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  chipWeight v
    + (if d.length 4 = 0 then transferWeight 1 4 v else 0)
    + (if d.length 3 = 0 then transferWeight 2 5 v else 0)
    + (if d.length 9 = 0 then transferWeight 7 3 v else 0)
    + (if d.length 5 = 0 ∧ hcT5 d < d.length 4 then transferWeight 3 4 v else 0)

section Rep

variable {d : DegSpec 8 12} (hCore : d.core = row09Core)
include hCore

theorem rep_zero_zero (hz : d.length 0 = 0) : d.rep 2 = d.rep 0 := by
  have h := d.rep_zero 0 hz; rw [hCore] at h; simpa [row09Core] using h.symm

theorem rep_zero_two (hz : d.length 2 = 0) : d.rep 1 = d.rep 0 := by
  have h := d.rep_zero 2 hz; rw [hCore] at h; simpa [row09Core] using h

theorem rep_zero_three (hz : d.length 3 = 0) : d.rep 2 = d.rep 5 := by
  have h := d.rep_zero 3 hz; rw [hCore] at h; simpa [row09Core] using h

theorem rep_zero_four (hz : d.length 4 = 0) : d.rep 1 = d.rep 4 := by
  have h := d.rep_zero 4 hz; rw [hCore] at h; simpa [row09Core] using h

theorem rep_zero_five (hz : d.length 5 = 0) : d.rep 3 = d.rep 4 := by
  have h := d.rep_zero 5 hz; rw [hCore] at h; simpa [row09Core] using h

theorem rep_zero_six (hz : d.length 6 = 0) : d.rep 4 = d.rep 5 := by
  have h := d.rep_zero 6 hz; rw [hCore] at h; simpa [row09Core] using h

theorem rep_zero_seven (hz : d.length 7 = 0) : d.rep 5 = d.rep 3 := by
  have h := d.rep_zero 7 hz; rw [hCore] at h; simpa [row09Core] using h

theorem rep_zero_eight (hz : d.length 8 = 0) : d.rep 0 = d.rep 6 := by
  have h := d.rep_zero 8 hz; rw [hCore] at h; simpa [row09Core] using h

theorem rep_zero_nine (hz : d.length 9 = 0) : d.rep 3 = d.rep 7 := by
  have h := d.rep_zero 9 hz; rw [hCore] at h; simpa [row09Core] using h

theorem rep_zero_par (hz : parMin d = 0) : d.rep 6 = d.rep 7 := by
  have hEither : d.length 10 = 0 ∨ d.length 11 = 0 := by
    simpa [parMin, Nat.min_eq_zero_iff] using hz
  rcases hEither with h | h
  · have hh := d.rep_zero 10 h; rw [hCore] at hh; simpa [row09Core] using hh
  · have hh := d.rep_zero 11 h; rw [hCore] at hh; simpa [row09Core] using hh

end Rep

theorem allocFive_classSum {d : DegSpec 8 12} (hCore : d.core = row09Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocFive d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  simp only [allocFive, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 2 0 (rep_zero_zero hCore),
    sum_conditional_transfer_eq_zero d _ 1 0 (rep_zero_two hCore),
    sum_conditional_transfer_eq_zero d _ 7 6
      (fun hz => (rep_zero_par hCore hz).symm),
    sum_conditional_transfer_eq_zero d _ 3 7 (rep_zero_nine hCore)]
  simp

theorem allocT4_classSum {d : DegSpec 8 12} (hCore : d.core = row09Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocT4 d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  simp only [allocT4, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 1 4 (rep_zero_four hCore),
    sum_conditional_transfer_eq_zero d _ 2 5 (rep_zero_three hCore),
    sum_conditional_transfer_eq_zero d _ 7 3
      (fun hz => (rep_zero_nine hCore hz).symm),
    sum_conditional_transfer_eq_zero d _ 3 5
      (fun hz => (rep_zero_seven hCore hz.1).symm)]
  simp

theorem allocT5_classSum {d : DegSpec 8 12} (hCore : d.core = row09Core)
    (r : Fin 8) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        allocT5 d v =
      ∑ v ∈ Finset.univ.filter (fun v : Fin 8 => d.rep v = d.rep r),
        chipWeight v := by
  classical
  simp only [allocT5, Finset.sum_add_distrib]
  rw [sum_conditional_transfer_eq_zero d _ 1 4 (rep_zero_four hCore),
    sum_conditional_transfer_eq_zero d _ 2 5 (rep_zero_three hCore),
    sum_conditional_transfer_eq_zero d _ 7 3
      (fun hz => (rep_zero_nine hCore hz).symm),
    sum_conditional_transfer_eq_zero d _ 3 4
      (fun hz => rep_zero_five hCore hz.1)]
  simp

/-! ## The outer centre `0` -/

/-- Representative of the outer target at vertex 0: move it to vertex 6 only when slot 8 is
contracted and the shorter arm exceeds the tail plus the shorter parallel slot. -/
def ownerOuter (d : DegSpec 8 12) : Fin 8 :=
  if d.length 8 = 0 then
    (if armMin d ≤ d.length 9 + parMin d then 0 else 6)
  else 0

/-- Coefficients after firing the outer-target script and subtracting one chip at its chosen
representative from the allocated divisor. -/
def outerCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    zeroChip (d.length 0) + zeroChip (d.length 2) -
        (if d.length 8 = 0 then
          (if armMin d ≤ d.length 9 + parMin d then 1 else 0) else 1) +
      (tailContribution (d.length 0) (outerO d) 0
        + headContribution (d.length 2) 0 (outerO d)
        + tailContribution (d.length 8) (outerO d) (outerI d))
  else if v = 1 then
    positiveChip (d.length 2) + tailContribution (d.length 2) 0 (outerO d)
  else if v = 2 then
    positiveChip (d.length 0) + headContribution (d.length 0) (outerO d) 0
  else if v = 3 then
    positiveChip (d.length 9) + tailContribution (d.length 9) 0 (outerE d)
  else if v = 6 then
    zeroChip (parMin d) -
        (if d.length 8 = 0 then
          (if armMin d ≤ d.length 9 + parMin d then 0 else 1) else 0) +
      (headContribution (d.length 8) (outerO d) (outerI d)
        + tailContribution (d.length 10) (outerI d) (outerE d)
        + tailContribution (d.length 11) (outerI d) (outerE d))
  else if v = 7 then
    positiveChip (parMin d) + zeroChip (d.length 9) +
      (headContribution (d.length 10) (outerI d) (outerE d)
        + headContribution (d.length 11) (outerI d) (outerE d)
        + headContribution (d.length 9) 0 (outerE d))
  else 0

theorem outerCoeff_eq (d : DegSpec 8 12) (v : Fin 8) :
    allocFive d v - indicatorWeight v (ownerOuter d)
        + contribForm d (heightOuter d) v = outerCoeff d v := by
  fin_cases v <;>
    by_cases hc : d.length 8 = 0 <;>
    by_cases hs : armMin d ≤ d.length 9 + parMin d <;>
    simp [outerCoeff, allocFive, ownerOuter, indicatorWeight, transferWeight,
      chipWeight, positiveChip, zeroChip, contribForm, heightOuter, hc, hs]
  all_goals (try ring1)
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals omega

theorem outerCoeff_nonneg (d : DegSpec 8 12) (v : Fin 8) :
    0 ≤ outerCoeff d v := by
  have ha : armMin d = min (d.length 0) (d.length 2) := rfl
  have hm : parMin d = min (d.length 10) (d.length 11) := rfl
  have ho : outerO d =
    min (armMin d) (d.length 9 + parMin d + d.length 8) := rfl
  have hi : outerI d = min (outerO d) (d.length 9 + parMin d) := rfl
  have he : outerE d = min (outerI d) (d.length 9) := rfl
  fin_cases v
  · exact outerTarget_center_nonneg forward reverse ha hm ho hi
  · exact reverse.positiveChip_add_head_nonneg
      (show outerO d ≤ d.length 2 by omega)
  · exact forward.positiveChip_add_head_nonneg
      (show outerO d ≤ d.length 0 by omega)
  · exact reverse.positiveChip_add_head_nonneg
      (show outerE d ≤ d.length 9 by omega)
  · simp [outerCoeff]
  · simp [outerCoeff]
  · exact outerTarget_inner_nonneg hm ho hi he
  · exact cycle_nonneg reverse hm
      (show outerE d ≤ outerI d by omega)
      (show outerE d ≤ d.length 9 by omega)
      (show outerE d = outerI d ∨ outerE d = d.length 9 by omega)
      (show outerI d ≤ outerE d + parMin d by omega)

theorem ownerOuter_rep {d : DegSpec 8 12} (hCore : d.core = row09Core) :
    d.rep (ownerOuter d) = d.rep 0 := by
  unfold ownerOuter
  split_ifs with hc hs
  · rfl
  · exact (rep_zero_eight hCore hc).symm
  · rfl

/-! ## The inner centre `6` -/

/-- Representative of the inner target at vertex 6: across contracted slot 8 choose vertex 0
when the shorter arm is at most the tail plus the shorter parallel slot. -/
def ownerInner (d : DegSpec 8 12) : Fin 8 :=
  if d.length 8 = 0 then
    (if armMin d ≤ d.length 9 + parMin d then 0 else 6)
  else 6

/-- Coefficients after firing the inner-target script and subtracting one chip at its chosen
representative from the allocated divisor. -/
def innerCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    zeroChip (d.length 0) + zeroChip (d.length 2) -
        (if d.length 8 = 0 then
          (if armMin d ≤ d.length 9 + parMin d then 1 else 0) else 0) +
      (tailContribution (d.length 0) (innerO d) 0
        + headContribution (d.length 2) 0 (innerO d)
        + tailContribution (d.length 8) (innerO d) (innerI d))
  else if v = 1 then
    positiveChip (d.length 2) + tailContribution (d.length 2) 0 (innerO d)
  else if v = 2 then
    positiveChip (d.length 0) + headContribution (d.length 0) (innerO d) 0
  else if v = 3 then
    positiveChip (d.length 9) + tailContribution (d.length 9) 0 (innerE d)
  else if v = 6 then
    zeroChip (parMin d) -
        (if d.length 8 = 0 then
          (if armMin d ≤ d.length 9 + parMin d then 0 else 1) else 1) +
      (headContribution (d.length 8) (innerO d) (innerI d)
        + tailContribution (d.length 10) (innerI d) (innerE d)
        + tailContribution (d.length 11) (innerI d) (innerE d))
  else if v = 7 then
    positiveChip (parMin d) + zeroChip (d.length 9) +
      (headContribution (d.length 10) (innerI d) (innerE d)
        + headContribution (d.length 11) (innerI d) (innerE d)
        + headContribution (d.length 9) 0 (innerE d))
  else 0

theorem innerCoeff_eq (d : DegSpec 8 12) (v : Fin 8) :
    allocFive d v - indicatorWeight v (ownerInner d)
        + contribForm d (heightInner d) v = innerCoeff d v := by
  fin_cases v <;>
    by_cases hc : d.length 8 = 0 <;>
    by_cases hs : armMin d ≤ d.length 9 + parMin d <;>
    simp [innerCoeff, allocFive, ownerInner, indicatorWeight, transferWeight,
      chipWeight, positiveChip, zeroChip, contribForm, heightInner, hc, hs]
  all_goals (try ring1)
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals omega

theorem innerCoeff_nonneg (d : DegSpec 8 12) (v : Fin 8) :
    0 ≤ innerCoeff d v := by
  have ha : armMin d = min (d.length 0) (d.length 2) := rfl
  have hm : parMin d = min (d.length 10) (d.length 11) := rfl
  have hi : innerI d =
    min (armMin d + d.length 8) (d.length 9 + parMin d) := rfl
  have ho : innerO d = min (armMin d) (innerI d) := rfl
  have he : innerE d = min (d.length 9) (innerI d) := rfl
  fin_cases v
  · exact innerTarget_center_nonneg forward reverse ha hm hi ho
  · exact reverse.positiveChip_add_head_nonneg
      (show innerO d ≤ d.length 2 by omega)
  · exact forward.positiveChip_add_head_nonneg
      (show innerO d ≤ d.length 0 by omega)
  · exact reverse.positiveChip_add_head_nonneg
      (show innerE d ≤ d.length 9 by omega)
  · simp [innerCoeff]
  · simp [innerCoeff]
  · exact innerTarget_inner_nonneg hm hi ho he
  · exact cycle_nonneg reverse hm
      (show innerE d ≤ innerI d by omega)
      (show innerE d ≤ d.length 9 by omega)
      (show innerE d = innerI d ∨ innerE d = d.length 9 by omega)
      (show innerI d ≤ innerE d + parMin d by omega)

theorem ownerInner_rep {d : DegSpec 8 12} (hCore : d.core = row09Core) :
    d.rep (ownerInner d) = d.rep 6 := by
  unfold ownerInner
  split_ifs with hc hs
  · exact rep_zero_eight hCore hc
  · rfl
  · rfl

/-! ## The chipped triangle at the target `4` -/

/-- Expanded coefficients after applying the chipped-triangle height script targeting vertex 4
to its allocated divisor. -/
def t4Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then
    positiveChip (d.length 4) + tailContribution (d.length 4) 0 (htT4 d)
  else if v = 2 then
    positiveChip (d.length 3) + tailContribution (d.length 3) 0 (hvT4 d)
  else if v = 3 then
    1 + zeroChip (d.length 9) - lend (d.length 7) (hcT4 d) (d.length 3)
      + (tailContribution (d.length 9) (hcT4 d) 0
          + tailContribution (d.length 5) (hcT4 d) (htT4 d)
          + headContribution (d.length 7) (hvT4 d) (hcT4 d))
  else if v = 4 then
    zeroChip (d.length 4)
      + (headContribution (d.length 4) 0 (htT4 d)
          + headContribution (d.length 5) (hcT4 d) (htT4 d)
          + tailContribution (d.length 6) (htT4 d) (hvT4 d))
  else if v = 5 then
    zeroChip (d.length 3) + lend (d.length 7) (hcT4 d) (d.length 3)
      + (headContribution (d.length 3) 0 (hvT4 d)
          + tailContribution (d.length 7) (hvT4 d) (hcT4 d)
          + headContribution (d.length 6) (htT4 d) (hvT4 d))
  else if v = 6 then 0
  else
    positiveChip (d.length 9) + headContribution (d.length 9) (hcT4 d) 0

theorem t4Coeff_eq (d : DegSpec 8 12) (v : Fin 8) :
    allocT4 d v + contribForm d (heightT4 d) v = t4Coeff d v := by
  fin_cases v <;>
    simp [t4Coeff, allocT4, transferWeight, indicatorWeight, chipWeight,
      positiveChip, zeroChip, lend, contribForm, heightT4]
  all_goals (try ring1)
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals omega

theorem t4Coeff_nonneg (d : DegSpec 8 12) (v : Fin 8) : 0 ≤ t4Coeff d v := by
  obtain ⟨⟨hcga, hcal, hcbe⟩, -, ⟨h0be, h0hc, hch0⟩, -,
    ⟨htal, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hvbe⟩, -⟩ :=
    boundsT4 d
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ positiveChip (d.length 4)
      + tailContribution (d.length 4) 0 (htT4 d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ positiveChip (d.length 3)
      + tailContribution (d.length 3) 0 (hvT4 d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 9)
        - lend (d.length 7) (hcT4 d) (d.length 3)
        + (tailContribution (d.length 9) (hcT4 d) 0
            + tailContribution (d.length 5) (hcT4 d) (htT4 d)
            + headContribution (d.length 7) (hvT4 d) (hcT4 d))
    have := triangleChipped_nonneg fwd fwd rev (k := (0 : ℤ))
      (al := d.length 4) (be := d.length 3) (ga := d.length 9)
      (p := d.length 5) (q := d.length 6) (r := d.length 7)
      (hc := hcT4 d) (h0 := h0T4 d) (ht := htT4 d) (hv := hvT4 d)
      rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ zeroChip (d.length 4)
        + (headContribution (d.length 4) 0 (htT4 d)
            + headContribution (d.length 5) (hcT4 d) (htT4 d)
            + tailContribution (d.length 6) (htT4 d) (hvT4 d))
    have := triangleTarget_nonneg rev rev fwd (k := (0 : ℤ))
      (al := d.length 4) (be := d.length 3) (ga := d.length 9)
      (p := d.length 5) (q := d.length 6) (r := d.length 7)
      (hc := hcT4 d) (h0 := h0T4 d) (ht := htT4 d) (hv := hvT4 d)
      rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ zeroChip (d.length 3)
        + lend (d.length 7) (hcT4 d) (d.length 3)
        + (headContribution (d.length 3) 0 (hvT4 d)
            + tailContribution (d.length 7) (hvT4 d) (hcT4 d)
            + headContribution (d.length 6) (htT4 d) (hvT4 d))
    have := trianglePartner_nonneg rev fwd rev (k := (0 : ℤ))
      (al := d.length 4) (be := d.length 3) (ga := d.length 9)
      (p := d.length 5) (q := d.length 6) (r := d.length 7)
      (hc := hcT4 d) (h0 := h0T4 d) (ht := htT4 d) (hv := hvT4 d)
      rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ positiveChip (d.length 9)
      + headContribution (d.length 9) (hcT4 d) 0
    exact positiveChip_add_head_nonneg (by omega)

/-- Representative receiving the vertex-4 chip: use vertex 4 when the script delivers there,
otherwise vertex 3 across contracted slot 5 without lending, and vertex 5 in the remaining case. -/
def ownerFour (d : DegSpec 8 12) : Fin 8 :=
  if Delivers (d.length 4) (d.length 5) (d.length 6) (hcT4 d) (h0T4 d) (htT4 d)
    then 4
  else if d.length 5 = 0 ∧ lend (d.length 7) (hcT4 d) (d.length 3) = 0 then 3
  else 5

theorem t4Coeff_owner (d : DegSpec 8 12) : 1 ≤ t4Coeff d (ownerFour d) := by
  obtain ⟨⟨hcga, hcal, hcbe⟩, -, ⟨h0be, h0hc, hch0⟩, -,
    ⟨htal, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hvbe⟩, -⟩ :=
    boundsT4 d
  unfold ownerFour
  by_cases hDel : Delivers (d.length 4) (d.length 5) (d.length 6) (hcT4 d)
      (h0T4 d) (htT4 d)
  · rw [ite_eq_left hDel]
    show (1 : ℤ) ≤ zeroChip (d.length 4)
        + (headContribution (d.length 4) 0 (htT4 d)
            + headContribution (d.length 5) (hcT4 d) (htT4 d)
            + tailContribution (d.length 6) (htT4 d) (hvT4 d))
    have := triangleTarget_nonneg rev rev fwd (k := (1 : ℤ))
      (al := d.length 4) (be := d.length 3) (ga := d.length 9)
      (p := d.length 5) (q := d.length 6) (r := d.length 7)
      (hc := hcT4 d) (h0 := h0T4 d) (ht := htT4 d) (hv := hvT4 d)
      rfl rfl rfl rfl (by norm_num) le_rfl (fun _ => hDel)
    simp only [fwd_tail, rev_tail] at this
    omega
  · rw [ite_eq_right hDel]
    by_cases hFall :
        d.length 5 = 0 ∧ lend (d.length 7) (hcT4 d) (d.length 3) = 0
    · rw [ite_eq_left hFall]
      show (1 : ℤ) ≤ 1 + zeroChip (d.length 9)
          - lend (d.length 7) (hcT4 d) (d.length 3)
          + (tailContribution (d.length 9) (hcT4 d) 0
              + tailContribution (d.length 5) (hcT4 d) (htT4 d)
              + headContribution (d.length 7) (hvT4 d) (hcT4 d))
      have := triangleChipped_nonneg fwd fwd rev (k := (1 : ℤ))
        (al := d.length 4) (be := d.length 3) (ga := d.length 9)
        (p := d.length 5) (q := d.length 6) (r := d.length 7)
        (hc := hcT4 d) (h0 := h0T4 d) (ht := htT4 d) (hv := hvT4 d)
        rfl rfl rfl rfl (by norm_num) le_rfl (fun _ => hFall)
      simp only [fwd_tail, rev_tail] at this
      omega
    · rw [ite_eq_right hFall]
      show (1 : ℤ) ≤ zeroChip (d.length 3)
          + lend (d.length 7) (hcT4 d) (d.length 3)
          + (headContribution (d.length 3) 0 (hvT4 d)
              + tailContribution (d.length 7) (hvT4 d) (hcT4 d)
              + headContribution (d.length 6) (htT4 d) (hvT4 d))
      have hOwn := partnerOwns_of_not_delivers (al := d.length 4)
        (be := d.length 3) (ga := d.length 9) (p := d.length 5)
        (q := d.length 6) (r := d.length 7) (hc := hcT4 d) (h0 := h0T4 d)
        (ht := htT4 d) (hv := hvT4 d) rfl rfl rfl rfl hDel hFall
      have := trianglePartner_nonneg rev fwd rev (k := (1 : ℤ))
        (al := d.length 4) (be := d.length 3) (ga := d.length 9)
        (p := d.length 5) (q := d.length 6) (r := d.length 7)
        (hc := hcT4 d) (h0 := h0T4 d) (ht := htT4 d) (hv := hvT4 d)
        rfl rfl rfl rfl (by norm_num) le_rfl (fun _ => hOwn)
      simp only [fwd_tail, rev_tail] at this
      omega

theorem ownerFour_rep {d : DegSpec 8 12} (hCore : d.core = row09Core) :
    d.rep (ownerFour d) = d.rep 4 := by
  unfold ownerFour
  by_cases hDel : Delivers (d.length 4) (d.length 5) (d.length 6) (hcT4 d)
      (h0T4 d) (htT4 d)
  · rw [ite_eq_left hDel]
  · rw [ite_eq_right hDel]
    by_cases hFall :
        d.length 5 = 0 ∧ lend (d.length 7) (hcT4 d) (d.length 3) = 0
    · rw [ite_eq_left hFall]
      exact rep_zero_five hCore hFall.1
    · rw [ite_eq_right hFall]
      rcases class_of_not_delivers (al := d.length 4) (be := d.length 3)
        (ga := d.length 9) (p := d.length 5) (q := d.length 6)
        (r := d.length 7) (hc := hcT4 d) (h0 := h0T4 d) (ht := htT4 d)
        (hv := hvT4 d) rfl rfl rfl rfl hDel hFall with h6 | ⟨h5, h7⟩
      · exact (rep_zero_six hCore h6).symm
      · rw [rep_zero_seven hCore h7]
        exact rep_zero_five hCore h5

/-! ## The chipped triangle at the target `5` -/

/-- Expanded coefficients after applying the chipped-triangle height script targeting vertex 5
to its allocated divisor. -/
def t5Coeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then 0
  else if v = 1 then
    positiveChip (d.length 4) + tailContribution (d.length 4) 0 (hvT5 d)
  else if v = 2 then
    positiveChip (d.length 3) + tailContribution (d.length 3) 0 (htT5 d)
  else if v = 3 then
    1 + zeroChip (d.length 9) - lend (d.length 5) (hcT5 d) (d.length 4)
      + (tailContribution (d.length 9) (hcT5 d) 0
          + headContribution (d.length 7) (htT5 d) (hcT5 d)
          + tailContribution (d.length 5) (hcT5 d) (hvT5 d))
  else if v = 4 then
    zeroChip (d.length 4) + lend (d.length 5) (hcT5 d) (d.length 4)
      + (headContribution (d.length 4) 0 (hvT5 d)
          + headContribution (d.length 5) (hcT5 d) (hvT5 d)
          + tailContribution (d.length 6) (hvT5 d) (htT5 d))
  else if v = 5 then
    zeroChip (d.length 3)
      + (headContribution (d.length 3) 0 (htT5 d)
          + tailContribution (d.length 7) (htT5 d) (hcT5 d)
          + headContribution (d.length 6) (hvT5 d) (htT5 d))
  else if v = 6 then 0
  else
    positiveChip (d.length 9) + headContribution (d.length 9) (hcT5 d) 0

theorem t5Coeff_eq (d : DegSpec 8 12) (v : Fin 8) :
    allocT5 d v + contribForm d (heightT5 d) v = t5Coeff d v := by
  fin_cases v <;>
    simp [t5Coeff, allocT5, transferWeight, indicatorWeight, chipWeight,
      positiveChip, zeroChip, lend, contribForm, heightT5]
  all_goals (try ring1)
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals omega

theorem t5Coeff_nonneg (d : DegSpec 8 12) (v : Fin 8) : 0 ≤ t5Coeff d v := by
  obtain ⟨⟨hcga, hcbe, hcal⟩, -, ⟨h0al, h0hc, hch0⟩, -,
    ⟨htbe, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hval⟩, -⟩ :=
    boundsT5 d
  fin_cases v
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ positiveChip (d.length 4)
      + tailContribution (d.length 4) 0 (hvT5 d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ positiveChip (d.length 3)
      + tailContribution (d.length 3) 0 (htT5 d)
    exact positiveChip_add_tail_nonneg (by omega)
  · show (0 : ℤ) ≤ 1 + zeroChip (d.length 9)
        - lend (d.length 5) (hcT5 d) (d.length 4)
        + (tailContribution (d.length 9) (hcT5 d) 0
            + headContribution (d.length 7) (htT5 d) (hcT5 d)
            + tailContribution (d.length 5) (hcT5 d) (hvT5 d))
    have := triangleChipped_nonneg fwd rev fwd (k := (0 : ℤ))
      (al := d.length 3) (be := d.length 4) (ga := d.length 9)
      (p := d.length 7) (q := d.length 6) (r := d.length 5)
      (hc := hcT5 d) (h0 := h0T5 d) (ht := htT5 d) (hv := hvT5 d)
      rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ zeroChip (d.length 4)
        + lend (d.length 5) (hcT5 d) (d.length 4)
        + (headContribution (d.length 4) 0 (hvT5 d)
            + headContribution (d.length 5) (hcT5 d) (hvT5 d)
            + tailContribution (d.length 6) (hvT5 d) (htT5 d))
    have := trianglePartner_nonneg rev rev fwd (k := (0 : ℤ))
      (al := d.length 3) (be := d.length 4) (ga := d.length 9)
      (p := d.length 7) (q := d.length 6) (r := d.length 5)
      (hc := hcT5 d) (h0 := h0T5 d) (ht := htT5 d) (hv := hvT5 d)
      rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ zeroChip (d.length 3)
        + (headContribution (d.length 3) 0 (htT5 d)
            + tailContribution (d.length 7) (htT5 d) (hcT5 d)
            + headContribution (d.length 6) (hvT5 d) (htT5 d))
    have := triangleTarget_nonneg rev fwd rev (k := (0 : ℤ))
      (al := d.length 3) (be := d.length 4) (ga := d.length 9)
      (p := d.length 7) (q := d.length 6) (r := d.length 5)
      (hc := hcT5 d) (h0 := h0T5 d) (ht := htT5 d) (hv := hvT5 d)
      rfl rfl rfl rfl le_rfl (by norm_num)
      (by intro hcon; exact absurd hcon (by norm_num))
    simp only [fwd_tail, rev_tail] at this
    omega
  · show (0 : ℤ) ≤ (0 : ℤ)
    norm_num
  · show (0 : ℤ) ≤ positiveChip (d.length 9)
      + headContribution (d.length 9) (hcT5 d) 0
    exact positiveChip_add_head_nonneg (by omega)

/-- Representative receiving the vertex-5 chip: use vertex 5 when the script delivers there,
otherwise vertex 3 across contracted slot 7 without lending, and vertex 4 in the remaining case. -/
def ownerFive (d : DegSpec 8 12) : Fin 8 :=
  if Delivers (d.length 3) (d.length 7) (d.length 6) (hcT5 d) (h0T5 d) (htT5 d)
    then 5
  else if d.length 7 = 0 ∧ lend (d.length 5) (hcT5 d) (d.length 4) = 0 then 3
  else 4

theorem t5Coeff_owner (d : DegSpec 8 12) : 1 ≤ t5Coeff d (ownerFive d) := by
  obtain ⟨⟨hcga, hcbe, hcal⟩, -, ⟨h0al, h0hc, hch0⟩, -,
    ⟨htbe, hthc, hth0, hcht⟩, -, ⟨hvh0, hvht, hchv, hthv, hvhcr, hval⟩, -⟩ :=
    boundsT5 d
  unfold ownerFive
  by_cases hDel : Delivers (d.length 3) (d.length 7) (d.length 6) (hcT5 d)
      (h0T5 d) (htT5 d)
  · rw [ite_eq_left hDel]
    show (1 : ℤ) ≤ zeroChip (d.length 3)
        + (headContribution (d.length 3) 0 (htT5 d)
            + tailContribution (d.length 7) (htT5 d) (hcT5 d)
            + headContribution (d.length 6) (hvT5 d) (htT5 d))
    have := triangleTarget_nonneg rev fwd rev (k := (1 : ℤ))
      (al := d.length 3) (be := d.length 4) (ga := d.length 9)
      (p := d.length 7) (q := d.length 6) (r := d.length 5)
      (hc := hcT5 d) (h0 := h0T5 d) (ht := htT5 d) (hv := hvT5 d)
      rfl rfl rfl rfl (by norm_num) le_rfl (fun _ => hDel)
    simp only [fwd_tail, rev_tail] at this
    omega
  · rw [ite_eq_right hDel]
    by_cases hFall :
        d.length 7 = 0 ∧ lend (d.length 5) (hcT5 d) (d.length 4) = 0
    · rw [ite_eq_left hFall]
      show (1 : ℤ) ≤ 1 + zeroChip (d.length 9)
          - lend (d.length 5) (hcT5 d) (d.length 4)
          + (tailContribution (d.length 9) (hcT5 d) 0
              + headContribution (d.length 7) (htT5 d) (hcT5 d)
              + tailContribution (d.length 5) (hcT5 d) (hvT5 d))
      have := triangleChipped_nonneg fwd rev fwd (k := (1 : ℤ))
        (al := d.length 3) (be := d.length 4) (ga := d.length 9)
        (p := d.length 7) (q := d.length 6) (r := d.length 5)
        (hc := hcT5 d) (h0 := h0T5 d) (ht := htT5 d) (hv := hvT5 d)
        rfl rfl rfl rfl (by norm_num) le_rfl (fun _ => hFall)
      simp only [fwd_tail, rev_tail] at this
      omega
    · rw [ite_eq_right hFall]
      show (1 : ℤ) ≤ zeroChip (d.length 4)
          + lend (d.length 5) (hcT5 d) (d.length 4)
          + (headContribution (d.length 4) 0 (hvT5 d)
              + headContribution (d.length 5) (hcT5 d) (hvT5 d)
              + tailContribution (d.length 6) (hvT5 d) (htT5 d))
      have hOwn := partnerOwns_of_not_delivers (al := d.length 3)
        (be := d.length 4) (ga := d.length 9) (p := d.length 7)
        (q := d.length 6) (r := d.length 5) (hc := hcT5 d) (h0 := h0T5 d)
        (ht := htT5 d) (hv := hvT5 d) rfl rfl rfl rfl hDel hFall
      have := trianglePartner_nonneg rev rev fwd (k := (1 : ℤ))
        (al := d.length 3) (be := d.length 4) (ga := d.length 9)
        (p := d.length 7) (q := d.length 6) (r := d.length 5)
        (hc := hcT5 d) (h0 := h0T5 d) (ht := htT5 d) (hv := hvT5 d)
        rfl rfl rfl rfl (by norm_num) le_rfl (fun _ => hOwn)
      simp only [fwd_tail, rev_tail] at this
      omega

theorem ownerFive_rep {d : DegSpec 8 12} (hCore : d.core = row09Core) :
    d.rep (ownerFive d) = d.rep 5 := by
  unfold ownerFive
  by_cases hDel : Delivers (d.length 3) (d.length 7) (d.length 6) (hcT5 d)
      (h0T5 d) (htT5 d)
  · rw [ite_eq_left hDel]
  · rw [ite_eq_right hDel]
    by_cases hFall :
        d.length 7 = 0 ∧ lend (d.length 5) (hcT5 d) (d.length 4) = 0
    · rw [ite_eq_left hFall]
      exact (rep_zero_seven hCore hFall.1).symm
    · rw [ite_eq_right hFall]
      rcases class_of_not_delivers (al := d.length 3) (be := d.length 4)
        (ga := d.length 9) (p := d.length 7) (q := d.length 6)
        (r := d.length 5) (hc := hcT5 d) (h0 := h0T5 d) (ht := htT5 d)
        (hv := hvT5 d) rfl rfl rfl rfl hDel hFall with h6 | ⟨h7, h5⟩
      · exact rep_zero_six hCore h6
      · rw [← rep_zero_five hCore h5]
        exact (rep_zero_seven hCore h7).symm

/-! ## Every contracted core class is reached -/

theorem rowDivisor_reaches_chipFree {d : DegSpec 8 12}
    (hCore : d.core = row09Core) (F : Finset (Fin 12))
    (hRepReach : ∀ x y : Fin 8, d.rep x = d.rep y ↔ ReachIn row09Core F x y)
    (hFZero : ∀ e : Fin 12, e ∈ F ↔ d.length e = 0) {center : Fin 8}
    (hFree : chipWeight center = 0) :
    Reaches d.graph (rowDivisor d) (d.coreVertex center) := by
  have hInterior : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      0 ≤ rowDivisor d (d.interiorVertex e o) :=
    fun e o => rowDivisor_effective d _
  have hChip : ∀ (e : Fin 12) (o : Fin (d.length e - 1)),
      o.val + 1 = noMark e → noMark e < d.length e →
      1 ≤ rowDivisor d (d.interiorVertex e o) := by
    intro e o hm _
    simp [noMark] at hm
  have hpOuter := profileOuter hCore
  have hpInner := profileInner hCore
  have hpT4 := profileT4 hCore
  have hpT5 := profileT5 hCore
  have hrOuter := height_rep_eq d hCore hpOuter.const F hRepReach hFZero
  have hrInner := height_rep_eq d hCore hpInner.const F hRepReach hFZero
  have hrT4 := height_rep_eq d hCore hpT4.const F hRepReach hFZero
  have hrT5 := height_rep_eq d hCore hpT5.const F hRepReach hFZero
  fin_cases center
  · exact (DharMove.ofScript _ (residual_effective d hpOuter hrOuter
      (rowDivisor_coreVertex d) hInterior hChip (allocFive_classSum hCore)
      (ownerOuter_rep hCore) (fun v => by
        rw [contrib_eq hCore hpOuter hrOuter v, outerCoeff_eq d v]
        exact outerCoeff_nonneg d v))).reaches
  · exact absurd hFree (by decide)
  · exact absurd hFree (by decide)
  · exact absurd hFree (by decide)
  · exact (DharMove.ofScript _ (residual_effective d hpT4 hrT4
      (rowDivisor_coreVertex d) hInterior hChip (allocT4_classSum hCore)
      (ownerFour_rep hCore) (fun v => by
        rw [contrib_eq hCore hpT4 hrT4 v]
        exact residual_of_coeff
          (fun w => by rw [t4Coeff_eq d w]; exact t4Coeff_nonneg d w)
          (by rw [t4Coeff_eq d (ownerFour d)]; exact t4Coeff_owner d)
          v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpT5 hrT5
      (rowDivisor_coreVertex d) hInterior hChip (allocT5_classSum hCore)
      (ownerFive_rep hCore) (fun v => by
        rw [contrib_eq hCore hpT5 hrT5 v]
        exact residual_of_coeff
          (fun w => by rw [t5Coeff_eq d w]; exact t5Coeff_nonneg d w)
          (by rw [t5Coeff_eq d (ownerFive d)]; exact t5Coeff_owner d)
          v))).reaches
  · exact (DharMove.ofScript _ (residual_effective d hpInner hrInner
      (rowDivisor_coreVertex d) hInterior hChip (allocFive_classSum hCore)
      (ownerInner_rep hCore) (fun v => by
        rw [contrib_eq hCore hpInner hrInner v, innerCoeff_eq d v]
        exact innerCoeff_nonneg d v))).reaches
  · exact absurd hFree (by decide)

/-- **AR row 09.**  The length-independent divisor `[1]+[2]+[3]+[7]`, valid
simultaneously on the open cell and every nonloopy forest face -- one chamber,
the whole closed orthant. -/
def row09Guard : GuardingSet row09Core where
  chips := chipWeight
  chips_nonneg := chipWeight_nonneg
  chips_deg := sum_chipWeight
  guard := fun _ hFree d hCore hRepReach =>
    rowDivisor_reaches_chipFree hCore (zeroSlots d.length) hRepReach
      (fun e => by simp) hFree

theorem row09_closedConstruction :
    ClosedSubdivisionDharConstruction row09Core (by norm_num) :=
  row09Guard.closedConstruction (by norm_num) row09_connected

end AtanasovRanganathan.GenusFiveRow09
