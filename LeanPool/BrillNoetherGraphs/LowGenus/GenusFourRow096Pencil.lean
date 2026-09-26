/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.RampScript
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.MultiBreakScript
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreSymmetry
public import LeanPool.BrillNoetherGraphs.Utilities.Segments.SegmentReflection
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionIso
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCubicAtlas

/-!
# A symbolic pencil for genus-four Core 096 (skeleton)

Row `096` of the genus-four pseudocore catalog is the **necklace of three
bananas**: bananas `β₀ = {v0,v5}` (arcs `e1,e2`), `β₁ = {v1,v4}` (arcs
`e4,e5`), `β₂ = {v2,v3}` (arcs `e6,e7`), joined in a cycle by the three
single slots `e0 : v0–v4` (length `a₀`), `e3 : v1–v3` (`a₁`), and
`e8 : v2–v5` (`a₂`).

The row is already closed (`RowProof.Row096Replacement.rowSolved_row096`) by a
17,705-node replayed Farkas cover in 274 kernel jobs.  This file is the
skeleton of a *symbolic* replacement in the style of
`GenusFourCore099/100/097`, from the divisor rule discovered and empirically
verified on 2026-08-13 (400/400 random positive length vectors, plus a
member-by-member verification of the complete regime-1 pencil on 45/45
vectors; see the accompanying analysis §6 and
auxiliary calculations):

Rotate by the order-three necklace rotation so that `a₀ = max(a₀,a₁,a₂)`,
and write `x = a₀ − a₁ − a₂`.

* **Regime 1 (`x ≤ 0`)**: `D = v0 + v5 + (point on e3 at distance a₀ − a₂
  from v1)`.  The pencil is the level set of the conserved quantity
  `τ = j + k + m = a₀`: one chip on each single slot at distances `j, k, m`
  from `v0, v1, v2` respectively, every such configuration with
  `j ≤ a₀, k ≤ a₁, m ≤ a₂` being equivalent, together with the six
  full-arc reflection families hanging off the three configurations where
  the two chips flanking a banana reach its endpoints.  Coverage is
  immediate interval arithmetic; the window `[max aᵢ, min (aᵢ+aⱼ)]` for
  `τ` is nonempty exactly by the triangle inequality.
* **Regime 2 (`x > 0`)**: `D = v0 + v5 + (point on the longer arc of β₂ at
  distance min(x, shorter arc length) from v3)` (after the arc swap of
  `e6/e7`, "longer arc = e6").

Every equivalence needed is an instance of the public `RampData` machinery in
`Utilities.Subdivision.RampScript`, through the single generic primitive `prin_cutRamp`
below: the Laplacian of a ramp supported on the slots crossing a cut moves one
chip by `t` along each of them.  Both regimes are cut marches only — no capped
reflections are needed, because the *anchor-only* route (the embedded core
vertices are a strong separator, so
`Certificate.CoreVertexReachability.bnExists_of_reaches_coreVertices` upgrades
reachability at the six core vertices to `rank ≥ 1`) removes the nine-slot
interior sweep from the obligation.  The "banana relay" of regime 2 is the
three-slot instance of `prin_cutRamp` at the cut `{e0,e6,e7}`.

This file is complete: no `sorry` remains.
-/

@[expose] public section

namespace LowGenus.GenusFourRow096Pencil

open Utilities

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.SubdivisionRamp
open AtanasovRanganathan.GenusFourCubicAtlas

theorem forall_fin_nine {P : Fin 9 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) :
    ∀ e : Fin 9, P e := by
  intro e
  fin_cases e
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]

theorem forall_fin_six {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ v : Fin 6, P v := by
  intro v
  fin_cases v
  exacts [h0, h1, h2, h3, h4, h5]

/-! ## The rotation and arc-swap automorphisms of the necklace -/

/-- The order-three rotation of the necklace on core vertices:
`v0 → v1 → v2 → v0`, `v4 → v3 → v5 → v4`. -/
def rotVertex : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 5, 3, 4]
  invFun := ![2, 0, 1, 4, 5, 3]
  left_inv := by decide
  right_inv := by decide

/-- The order-three rotation on edge slots: singles `e0 → e3 → e8 → e0`,
arcs `e1 → e4 → e6 → e1` and `e2 → e5 → e7 → e2`. -/
def rotSlot : Equiv.Perm (Fin 9) where
  toFun := ![3, 4, 5, 8, 6, 7, 1, 2, 0]
  invFun := ![8, 6, 7, 0, 1, 2, 4, 5, 3]
  left_inv := by decide
  right_inv := by decide

/-- The rotation preserves every slot's reading direction. -/
def rotReversed : Fin 9 → Bool := fun _ => false

-- v4.33: `backward.isDefEq.respectTransparency` now defaults to `true`; unifying
-- instance-implicit arguments through the semireducible core constructions no
-- longer unfolds them.  See the accompanying analysis.
theorem rot_tail : ∀ edge : Fin 9,
row096Core.tail (rotSlot edge) =
if rotReversed edge then rotVertex (row096Core.head edge)
else rotVertex (row096Core.tail edge) := by decide

-- v4.33: `backward.isDefEq.respectTransparency` now defaults to `true`; unifying
-- instance-implicit arguments through the semireducible core constructions no
-- longer unfolds them.  See the accompanying analysis.
theorem rot_head : ∀ edge : Fin 9,
row096Core.head (rotSlot edge) =
if rotReversed edge then rotVertex (row096Core.tail edge)
else rotVertex (row096Core.head edge) := by decide

/-- Swapping the two arcs of `β₂` (slots `e6`, `e7`), fixing everything
else. -/
def swapSlot : Equiv.Perm (Fin 9) where
  toFun := ![0, 1, 2, 3, 4, 5, 7, 6, 8]
  invFun := ![0, 1, 2, 3, 4, 5, 7, 6, 8]
  left_inv := by decide
  right_inv := by decide

/-- The arc swap fixes every core vertex and reverses no slot. -/
def swapVertex : Equiv.Perm (Fin 6) := Equiv.refl _

-- v4.33: `backward.isDefEq.respectTransparency` now defaults to `true`; unifying
-- instance-implicit arguments through the semireducible core constructions no
-- longer unfolds them.  See the accompanying analysis.
theorem swap_tail : ∀ edge : Fin 9,
row096Core.tail (swapSlot edge) =
if rotReversed edge then swapVertex (row096Core.head edge)
else swapVertex (row096Core.tail edge) := by decide

-- v4.33: `backward.isDefEq.respectTransparency` now defaults to `true`; unifying
-- instance-implicit arguments through the semireducible core constructions no
-- longer unfolds them.  See the accompanying analysis.
theorem swap_head : ∀ edge : Fin 9,
row096Core.head (swapSlot edge) =
if rotReversed edge then swapVertex (row096Core.tail edge)
else swapVertex (row096Core.head edge) := by decide

/-! ## The necklace core, as a predicate on an arbitrary spec

Stating the incidence data as a predicate lets the pencil and its sweep be
developed for an arbitrary `Spec 6 9`, with the public row-096 core
instantiating it at the end. -/

/-- The incidence structure of the necklace of three bananas: bananas
`β₀ = {v0,v5}` on arcs `e1,e2`, `β₁ = {v1,v4}` on `e4,e5`, `β₂ = {v2,v3}` on
`e6,e7`, joined by the singles `e0 : v0–v4`, `e3 : v1–v3`, `e8 : v2–v5`. -/
structure IsNecklace (spec : SubdivisionGraph.Spec 6 9) : Prop where
  t0 : spec.core.tail 0 = 0
  t1 : spec.core.tail 1 = 0
  t2 : spec.core.tail 2 = 0
  t3 : spec.core.tail 3 = 1
  t4 : spec.core.tail 4 = 1
  t5 : spec.core.tail 5 = 1
  t6 : spec.core.tail 6 = 2
  t7 : spec.core.tail 7 = 2
  t8 : spec.core.tail 8 = 2
  h0 : spec.core.head 0 = 4
  h1 : spec.core.head 1 = 5
  h2 : spec.core.head 2 = 5
  h3 : spec.core.head 3 = 3
  h4 : spec.core.head 4 = 4
  h5 : spec.core.head 5 = 4
  h6 : spec.core.head 6 = 3
  h7 : spec.core.head 7 = 3
  h8 : spec.core.head 8 = 5

/-- The catalog's split core is a necklace. -/
theorem isNecklace_row096Core (core_nonempty : 0 < 6)
    (core_loopless : ∀ edge : Fin 9,
      row096Core.tail edge ≠ row096Core.head edge)
    (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge) :
    IsNecklace (Spec.ofCore row096Core core_nonempty core_loopless
      length hLength) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The regime-1 pencil divisor

`D = v0 + v5 + (point on e3 at distance a₀ − a₂ from v1)`.  In regime 1 the
offset `a₀ − a₂` lies in `[0, a₁]`: nonnegative because `a₀` is maximal, and at
most `a₁` by the triangle inequality, so it names a genuine path position. -/

section Pencil

variable (spec : SubdivisionGraph.Spec 6 9)

/-- The interior offset of the third chip on slot `e3`: `a₀ − a₂`. -/
def kPos : ℕ := spec.length 0 - spec.length 8

theorem kPos_le (htri : spec.length 0 ≤ spec.length 3 + spec.length 8) :
    kPos spec ≤ spec.length 3 := by
  unfold kPos
  omega

/-- The regime-1 divisor. -/
def pencil1 (htri : spec.length 0 ≤ spec.length 3 + spec.length 8) :
    CFDiv spec.graph :=
  oneChip (spec.coreVertex 0) + oneChip (spec.coreVertex 5) +
    oneChip (spec.pathVertex 3 ⟨kPos spec, by
      have := kPos_le spec htri; omega⟩)

theorem deg_pencil1 (htri : spec.length 0 ≤ spec.length 3 + spec.length 8) :
    deg (pencil1 spec htri) = 3 := by
  unfold pencil1
  rw [deg.map_add, deg.map_add, deg_one_chip, deg_one_chip, deg_one_chip]
  norm_num

/-- The regime-2 relay depth `s = min(x, a₇)`, where `x = a₀ − a₁ − a₂`.  It is
both the distance of the third chip from `v3` along the long arc `e6` and the
length of the three-slot relay march across `β₂`. -/
def sPos : ℕ :=
  min (spec.length 0 - spec.length 3 - spec.length 8) (spec.length 7)

/-- The regime-2 divisor `D = v0 + v5 + (point on e6 at distance s from v3)`.
No hypothesis is needed to state it: the offset `length e6 - s` is a path
position of `e6` whatever the lengths are. -/
def pencil2 : CFDiv spec.graph :=
  oneChip (spec.coreVertex 0) + oneChip (spec.coreVertex 5) +
    oneChip (spec.pathVertex 6 ⟨spec.length 6 - sPos spec, by omega⟩)

theorem deg_pencil2 : deg (pencil2 spec) = 3 := by
  unfold pencil2
  rw [deg.map_add, deg.map_add, deg_one_chip, deg_one_chip, deg_one_chip]
  norm_num

end Pencil

/-! ## Chip bookkeeping and the two-slot march

All the regime-1 marches are instances of a single generic move: a ramp whose
sign vector is supported on two slots, `-1` on one and `+1` on the other.  Its
Laplacian carries one chip forward by `t` along the first slot and one chip
back by `t` along the second, so it preserves the total depth `τ`.  Proving
that once, for an arbitrary spec, is what keeps the rest of this file short.

The two `oneChip` readings below are stated with *nested* conditionals rather
than conjunctive ones on purpose: `split_ifs` treats a conjunction as a single
atom, so the conjunctive form makes the case split in `prin_twoSlotRamp`
exponentially larger than it needs to be. -/

section ChipBookkeeping

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p}

/-- A one-chip divisor at a path position, read at a core vertex: it registers
only at the two ends of its own slot. -/
theorem one_chip_pathVertex_core (e : Fin p) (q : spec.PathPosition e)
    (v : Fin n) :
    oneChip (G := spec.graph) (spec.pathVertex e q) (spec.coreVertex v) =
      (if q.val = 0 then (if spec.core.tail e = v then 1 else 0) else 0) +
        (if q.val = spec.length e then
          (if spec.core.head e = v then 1 else 0) else 0) := by
  have hpos := spec.length_pos e
  unfold SubdivisionGraph.Spec.pathVertex
  by_cases hz : q.val = 0
  · rw [dite_eq_left hz, ite_eq_right (show ¬(q.val = spec.length e) by omega), add_zero,
      ite_eq_left hz]
    simp [oneChip, SubdivisionGraph.Spec.coreVertex, eq_comm]
  · rw [dite_eq_right hz, ite_eq_right hz, zero_add]
    by_cases hl : q.val = spec.length e
    · rw [dite_eq_left hl, ite_eq_left hl]
      simp [oneChip, SubdivisionGraph.Spec.coreVertex, eq_comm]
    · rw [dite_eq_right hl, ite_eq_right hl]
      simp only [oneChip]
      exact ite_eq_right (coreVertex_ne_interiorVertex spec v e _)

/-- The same reading at an interior vertex: the chip registers exactly when the
slot matches and the depth matches. -/
theorem one_chip_pathVertex_int (e : Fin p) (q : spec.PathPosition e)
    (e' : Fin p) (off : Fin (spec.length e' - 1)) :
    oneChip (G := spec.graph) (spec.pathVertex e q)
        (spec.interiorVertex e' off) =
      if e = e' then (if off.val + 1 = q.val then 1 else 0) else 0 := by
  have hpos := spec.length_pos e
  have hoff := off.isLt
  unfold SubdivisionGraph.Spec.pathVertex
  by_cases hz : q.val = 0
  · rw [dite_eq_left hz]
    simp only [oneChip]
    rw [ite_eq_right fun hEq => (coreVertex_ne_interiorVertex spec _ e' off) hEq.symm]
    by_cases he : e = e'
    · rw [ite_eq_left he, ite_eq_right (by omega)]
    · rw [ite_eq_right he]
  · rw [dite_eq_right hz]
    by_cases hl : q.val = spec.length e
    · rw [dite_eq_left hl]
      simp only [oneChip]
      rw [ite_eq_right fun hEq =>
        (coreVertex_ne_interiorVertex spec _ e' off) hEq.symm]
      by_cases he : e = e'
      · subst he
        rw [ite_eq_left rfl, ite_eq_right (by omega)]
      · rw [ite_eq_right he]
    · rw [dite_eq_right hl]
      simp only [oneChip]
      by_cases he : e = e'
      · subst he
        rw [ite_eq_left rfl]
        by_cases hv : off.val + 1 = q.val
        · rw [ite_eq_left hv, ite_eq_left]
          exact (interiorVertex_eq_iff spec e e off _).mpr
            ⟨rfl, by change off.val = q.val - 1; omega⟩
        · rw [ite_eq_right hv, ite_eq_right]
          intro hEq
          have hv' : off.val = q.val - 1 :=
            ((interiorVertex_eq_iff spec e e off _).mp hEq).2
          exact hv (by omega)
      · rw [ite_eq_right he, ite_eq_right]
        intro hEq
        exact he ((interiorVertex_eq_iff spec e' e off _).mp hEq).1.symm

/-- A path position at depth `0` is the tail of its slot. -/
theorem pathVertex_eq_tail (e : Fin p) (q : spec.PathPosition e) (h : q.val = 0) :
    spec.pathVertex e q = spec.coreVertex (spec.core.tail e) := by
  unfold SubdivisionGraph.Spec.pathVertex
  rw [dite_eq_left h]

/-- A path position at full depth is the head of its slot. -/
theorem pathVertex_eq_head (e : Fin p) (q : spec.PathPosition e)
    (h : q.val = spec.length e) :
    spec.pathVertex e q = spec.coreVertex (spec.core.head e) := by
  have hpos := spec.length_pos e
  unfold SubdivisionGraph.Spec.pathVertex
  rw [dite_eq_right (by omega), dite_eq_left h]

/-- **The cut march**, in full generality.

Let the sign vector of a ramp be supported on a finite set `A` of slots, each
of which has room for the whole window.  Then the Laplacian of the ramp is,
slot by slot, `sgn e` times the move of one chip from path position `lo e + t`
*back* to `lo e`.  (So `sgn e = +1` pulls a chip backwards and `sgn e = -1`
pushes it forwards; that is the convention forced by `rampSlope`.)

`A` is typically the set of slots crossing a cut of the core, and then the
signs are the coboundary of the side indicator — see `cutSgn`/`rampData_cut`.
The regime-1 marches use two-slot cuts (`prin_twoSlotRamp` below); the
regime-2 banana relay uses the three-slot cut `{e0, e6, e7}`.

The path positions are taken as arguments constrained by their `.val` rather
than built from `lo` and `t` inside the statement, so that no `omega` proof
terms get buried in the `Fin` literals. -/
theorem prin_cutRamp {pot : Fin n → ℤ} {sgn : Fin p → ℤ} {lo : Fin p → ℕ}
    {t : ℕ} (h : RampData spec pot sgn lo t) (ht : 0 < t)
    (A : Finset (Fin p)) (hzero : ∀ e ∉ A, sgn e = 0)
    (hw : ∀ e ∈ A, lo e + t ≤ spec.length e)
    (pos pos' : ∀ e : Fin p, spec.PathPosition e)
    (hpos : ∀ e ∈ A, (pos e).val = lo e)
    (hpos' : ∀ e ∈ A, (pos' e).val = lo e + t) :
    prin spec.graph (rampScript spec pot sgn lo t) =
      ∑ e ∈ A, sgn e •
        (oneChip (spec.pathVertex e (pos e)) -
          oneChip (spec.pathVertex e (pos' e))) := by
  refine divisor_ext (fun v => ?_) (fun e' off => ?_)
  · -- Core vertices: only the active slots contribute to the endpoint sum, and
    -- there the two sides match term by term.
    rw [prin_ramp_coreVertex h v,
      ← Finset.sum_subset (Finset.subset_univ A)
        (by intro e _ he; simp [rampSlope, hzero e he]),
      Finset.sum_apply]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have hposE := spec.length_pos e
    have hwE := hw e he
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      one_chip_pathVertex_core, rampSlope_zero, rampSlope_last h,
      hpos e he, hpos' e he]
    rw [ite_eq_right (show ¬(lo e + t = 0) by omega),
      ite_eq_right (show ¬(lo e = spec.length e) by omega)]
    simp only [ht, and_true]
    split_ifs <;> ring
  · -- Interior vertices: the ramp only moves chips inside its own window.
    rw [prin_ramp_interiorVertex h e' off, Finset.sum_apply]
    have hoff := off.isLt
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      one_chip_pathVertex_int]
    by_cases heA : e' ∈ A
    · rw [Finset.sum_eq_single e'
        (fun e _ hne => by simp only [ite_eq_right hne, sub_zero, mul_zero])
        (fun hc => absurd heA hc)]
      have hd := rampSlope_diff sgn lo t e' (off.val + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hd
      rw [hd, ite_eq_left rfl, hpos e' heA, hpos' e' heA]
      simp only [ht, and_true]
      split_ifs <;> ring
    · rw [Finset.sum_eq_zero (fun e he => by
        have hc : ¬(e = e') := by rintro rfl; exact heA he
        simp only [ite_eq_right hc, sub_self, mul_zero])]
      simp [rampSlope, hzero e' heA]

/-- **The two-slot march.**

A ramp whose sign vector is `-1` on `α`, `+1` on `β` and zero elsewhere has a
Laplacian that carries one chip forward by `t` along `α` and one chip back by
`t` along `β`.  The two displacements cancel, so any total depth summed over
the active slots is conserved — which is the whole content of the regime-1
pencil.

This is `prin_cutRamp` at the two-element set `{α, β}`.

The four path positions are taken as arguments rather than built from `lo` and
`t` inside the statement, so that no proof terms are buried in the `Fin`
literals and callers can supply whatever positions they already have. -/
theorem prin_twoSlotRamp {pot : Fin n → ℤ} {sgn : Fin p → ℤ} {lo : Fin p → ℕ}
    {t : ℕ} (h : RampData spec pot sgn lo t) (ht : 0 < t)
    {α β : Fin p} (hαβ : α ≠ β) (hα : sgn α = -1) (hβ : sgn β = 1)
    (hzero : ∀ e, e ≠ α → e ≠ β → sgn e = 0)
    (hwα : lo α + t ≤ spec.length α) (hwβ : lo β + t ≤ spec.length β)
    (pα pα' : spec.PathPosition α) (pβ pβ' : spec.PathPosition β)
    (hpα : pα.val = lo α) (hpα' : pα'.val = lo α + t)
    (hpβ : pβ.val = lo β) (hpβ' : pβ'.val = lo β + t) :
    prin spec.graph (rampScript spec pot sgn lo t) =
      oneChip (spec.pathVertex α pα') - oneChip (spec.pathVertex α pα)
        + oneChip (spec.pathVertex β pβ)
        - oneChip (spec.pathVertex β pβ') := by
  -- Total position functions agreeing with the two supplied pairs on `{α, β}`;
  -- the `min` keeps them in range on the inactive slots.
  have hmem : ∀ e ∈ ({α, β} : Finset (Fin p)), e = α ∨ e = β := by
    intro e he
    simpa using he
  have hnot : ∀ e ∉ ({α, β} : Finset (Fin p)), e ≠ α ∧ e ≠ β := by
    intro e he
    exact ⟨by rintro rfl; exact he (by simp), by rintro rfl; exact he (by simp)⟩
  have key := prin_cutRamp h ht ({α, β} : Finset (Fin p))
    (fun e he => hzero e (hnot e he).1 (hnot e he).2)
    (fun e he => by rcases hmem e he with rfl | rfl <;> assumption)
    (fun e => ⟨min (lo e) (spec.length e), by omega⟩)
    (fun e => ⟨min (lo e + t) (spec.length e), by omega⟩)
    (fun e he => by
      rcases hmem e he with rfl | rfl <;> exact min_eq_left (by omega))
    (fun e he => by
      rcases hmem e he with rfl | rfl <;> exact min_eq_left (by omega))
  have e1 : (⟨min (lo α) (spec.length α), by omega⟩ : spec.PathPosition α) =
      pα := Fin.ext (by rw [hpα]; exact min_eq_left (by omega))
  have e2 : (⟨min (lo α + t) (spec.length α), by omega⟩ :
      spec.PathPosition α) = pα' :=
    Fin.ext (by rw [hpα']; exact min_eq_left (by omega))
  have e3 : (⟨min (lo β) (spec.length β), by omega⟩ : spec.PathPosition β) =
      pβ := Fin.ext (by rw [hpβ]; exact min_eq_left (by omega))
  have e4 : (⟨min (lo β + t) (spec.length β), by omega⟩ :
      spec.PathPosition β) = pβ' :=
    Fin.ext (by rw [hpβ']; exact min_eq_left (by omega))
  rw [key, Finset.sum_pair hαβ, hα, hβ, e1, e2, e3, e4]
  module

/-- **The three-slot march**, in the all-`-1` case.

A ramp whose sign vector is `-1` on each of three slots `α, β, γ` and zero
elsewhere advances one chip by `t` along each of them.  This is the banana
relay of regime 2 (cut `{e0,e6,e7}`, side `{v0,v2,v5}`) and the arrival at
`v4` (cut `{e0,e4,e5}`, the star of `v4`).

This is `prin_cutRamp` at the three-element set `{α, β, γ}`. -/
theorem prin_threeSlotRampNeg {pot : Fin n → ℤ} {sgn : Fin p → ℤ}
    {lo : Fin p → ℕ} {t : ℕ} (h : RampData spec pot sgn lo t) (ht : 0 < t)
    {α β γ : Fin p} (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα : sgn α = -1) (hβ : sgn β = -1) (hγ : sgn γ = -1)
    (hzero : ∀ e, e ≠ α → e ≠ β → e ≠ γ → sgn e = 0)
    (hwα : lo α + t ≤ spec.length α) (hwβ : lo β + t ≤ spec.length β)
    (hwγ : lo γ + t ≤ spec.length γ)
    (pα pα' : spec.PathPosition α) (pβ pβ' : spec.PathPosition β)
    (pγ pγ' : spec.PathPosition γ)
    (hpα : pα.val = lo α) (hpα' : pα'.val = lo α + t)
    (hpβ : pβ.val = lo β) (hpβ' : pβ'.val = lo β + t)
    (hpγ : pγ.val = lo γ) (hpγ' : pγ'.val = lo γ + t) :
    prin spec.graph (rampScript spec pot sgn lo t) =
      oneChip (spec.pathVertex α pα') - oneChip (spec.pathVertex α pα)
        + (oneChip (spec.pathVertex β pβ') - oneChip (spec.pathVertex β pβ))
        + (oneChip (spec.pathVertex γ pγ') -
            oneChip (spec.pathVertex γ pγ)) := by
  have hmem : ∀ e ∈ ({α, β, γ} : Finset (Fin p)), e = α ∨ e = β ∨ e = γ := by
    intro e he
    simpa using he
  have hnot : ∀ e ∉ ({α, β, γ} : Finset (Fin p)), e ≠ α ∧ e ≠ β ∧ e ≠ γ := by
    intro e he
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact he (by simp)
  have key := prin_cutRamp h ht ({α, β, γ} : Finset (Fin p))
    (fun e he => hzero e (hnot e he).1 (hnot e he).2.1 (hnot e he).2.2)
    (fun e he => by rcases hmem e he with rfl | rfl | rfl <;> assumption)
    (fun e => ⟨min (lo e) (spec.length e), by omega⟩)
    (fun e => ⟨min (lo e + t) (spec.length e), by omega⟩)
    (fun e he => by
      rcases hmem e he with rfl | rfl | rfl <;> exact min_eq_left (by omega))
    (fun e he => by
      rcases hmem e he with rfl | rfl | rfl <;> exact min_eq_left (by omega))
  have e1 : (⟨min (lo α) (spec.length α), by omega⟩ : spec.PathPosition α) =
      pα := Fin.ext (by rw [hpα]; exact min_eq_left (by omega))
  have e2 : (⟨min (lo α + t) (spec.length α), by omega⟩ :
      spec.PathPosition α) = pα' :=
    Fin.ext (by rw [hpα']; exact min_eq_left (by omega))
  have e3 : (⟨min (lo β) (spec.length β), by omega⟩ : spec.PathPosition β) =
      pβ := Fin.ext (by rw [hpβ]; exact min_eq_left (by omega))
  have e4 : (⟨min (lo β + t) (spec.length β), by omega⟩ :
      spec.PathPosition β) = pβ' :=
    Fin.ext (by rw [hpβ']; exact min_eq_left (by omega))
  have e5 : (⟨min (lo γ) (spec.length γ), by omega⟩ : spec.PathPosition γ) =
      pγ := Fin.ext (by rw [hpγ]; exact min_eq_left (by omega))
  have e6 : (⟨min (lo γ + t) (spec.length γ), by omega⟩ :
      spec.PathPosition γ) = pγ' :=
    Fin.ext (by rw [hpγ']; exact min_eq_left (by omega))
  rw [key, Finset.sum_insert (by simp [hαβ, hαγ]), Finset.sum_pair hβγ,
    hα, hβ, hγ, e1, e2, e3, e4, e5, e6]
  module

end ChipBookkeeping

/-! ## Three-chip configurations

Regime 2 moves its chips through five different slot triples, so it is stated
against a divisor of three chips at *arbitrary* vertices rather than against a
family indexed by a fixed triple of slots (as `tauDiv` is for regime 1). -/

section Config

variable {n p : ℕ}

/-- Three chips, at arbitrary vertices of a subdivision. -/
def cfg (spec : SubdivisionGraph.Spec n p) (u v w : spec.graph.V) :
    CFDiv spec.graph :=
  oneChip u + oneChip v + oneChip w

theorem effective_cfg (spec : SubdivisionGraph.Spec n p)
    (u v w : spec.graph.V) : effective (cfg spec u v w) := by
  intro z
  simp only [cfg, Pi.add_apply, oneChip]
  split_ifs <;> norm_num

/-- A configuration carries a chip at `z` as soon as one of its three vertices
is `z`. -/
theorem one_le_cfg (spec : SubdivisionGraph.Spec n p) (u v w z : spec.graph.V)
    (h : u = z ∨ v = z ∨ w = z) : 1 ≤ cfg spec u v w z := by
  have hnn : ∀ y : spec.graph.V, 0 ≤ oneChip (G := spec.graph) y z := by
    intro y
    simp only [oneChip]
    split_ifs <;> norm_num
  have hone : ∀ y : spec.graph.V, y = z → oneChip (G := spec.graph) y z = 1 := by
    intro y hy
    simp [oneChip, hy]
  simp only [cfg, Pi.add_apply]
  rcases h with h | h | h
  · have h1 := hone _ h
    have h2 := hnn v
    have h3 := hnn w
    omega
  · have h1 := hone _ h
    have h2 := hnn u
    have h3 := hnn w
    omega
  · have h1 := hone _ h
    have h2 := hnn u
    have h3 := hnn v
    omega

/-- Swapping the last two chips of a configuration. -/
theorem cfg_swap (spec : SubdivisionGraph.Spec n p) (u v w : spec.graph.V) :
    cfg spec u v w = cfg spec u w v := by
  unfold cfg
  abel

end Config

/-! ## The `τ`-family and the three regime-1 marches

Write `a₀ = length 0`, `a₁ = length 3`, `a₂ = length 8` for the three single
lengths.  The `τ`-family carries one chip on each single slot, at depths
`j, k, m` measured from `v0, v1, v2`; the two-slot marches below all preserve
`τ = j + k + m`, so the whole level set `τ = a₀` is one equivalence class.

Every march is a *cut* march: its potential is `t` on one side of a two-slot
cut of the necklace and `0` on the other, which makes `RampData.potential`
automatic. -/

section Regime1March

open Utilities.Certificate.SubdivisionRamp

/-- The potential of a cut march: height `t` on the chosen side. -/
def cutPot {n : ℕ} (S : Fin n → Bool) (t : ℕ) : Fin n → ℤ :=
  fun v => if S v then (t : ℤ) else 0

/-- The sign vector a cut potential forces: `±1` on the slots crossing the
cut, zero on the rest. -/
def cutSgn {n p : ℕ} (spec : SubdivisionGraph.Spec n p) (S : Fin n → Bool) :
    Fin p → ℤ :=
  fun e => (if S (spec.core.head e) then 1 else 0) -
    (if S (spec.core.tail e) then 1 else 0)

/-- A cut potential is always consistent with its own sign vector, so the only
thing a cut march has to check is its window. -/
theorem rampData_cut {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (S : Fin n → Bool) (lo : Fin p → ℕ) (t : ℕ)
    (hwin : ∀ e, lo e + t ≤ spec.length e ∨ cutSgn spec S e = 0) :
    RampData spec (cutPot S t) (cutSgn spec S) lo t where
  potential := by
    intro e
    simp only [cutPot, cutSgn]
    split_ifs <;> ring
  window := hwin

variable {spec : SubdivisionGraph.Spec 6 9}

/-- The `τ`-family: one chip on each single slot. -/
def tauDiv (spec : SubdivisionGraph.Spec 6 9) (j : spec.PathPosition 0)
    (k : spec.PathPosition 3) (m : spec.PathPosition 8) : CFDiv spec.graph :=
  oneChip (spec.pathVertex 0 j) + oneChip (spec.pathVertex 3 k) +
    oneChip (spec.pathVertex 8 m)

theorem effective_tauDiv (spec : SubdivisionGraph.Spec 6 9)
    (j : spec.PathPosition 0) (k : spec.PathPosition 3)
    (m : spec.PathPosition 8) : effective (tauDiv spec j k m) := by
  intro v
  simp only [tauDiv, Pi.add_apply, oneChip]
  split_ifs <;> norm_num

/-- A `τ`-family member carries a chip at `u` as soon as one of its three
positions names `u`. -/
theorem one_le_tauDiv_of_eq (spec : SubdivisionGraph.Spec 6 9)
    (j : spec.PathPosition 0) (k : spec.PathPosition 3) (m : spec.PathPosition 8)
    (u : Fin 6)
    (h : spec.pathVertex 0 j = spec.coreVertex u ∨
      spec.pathVertex 3 k = spec.coreVertex u ∨
      spec.pathVertex 8 m = spec.coreVertex u) :
    1 ≤ tauDiv spec j k m (spec.coreVertex u) := by
  have hnn : ∀ w : spec.graph.V,
      0 ≤ oneChip (G := spec.graph) w (spec.coreVertex u) := by
    intro w
    simp only [oneChip]
    split_ifs <;> norm_num
  have hone : ∀ w : spec.graph.V, w = spec.coreVertex u →
      oneChip (G := spec.graph) w (spec.coreVertex u) = 1 := by
    intro w hw
    simp [oneChip, hw]
  simp only [tauDiv, Pi.add_apply]
  rcases h with h | h | h
  · have h1 := hone _ h
    have h2 := hnn (spec.pathVertex 3 k)
    have h3 := hnn (spec.pathVertex 8 m)
    omega
  · have h1 := hone _ h
    have h2 := hnn (spec.pathVertex 0 j)
    have h3 := hnn (spec.pathVertex 8 m)
    omega
  · have h1 := hone _ h
    have h2 := hnn (spec.pathVertex 0 j)
    have h3 := hnn (spec.pathVertex 3 k)
    omega

/-- The regime-1 pencil *is* the `τ`-family member `T(0, a₀ − a₂, a₂)`: its two
core chips are the tail of `e0` and the head of `e8`. -/
theorem pencil1_eq_tauDiv (hn : IsNecklace spec)
    (htri : spec.length 0 ≤ spec.length 3 + spec.length 8)
    (j : spec.PathPosition 0) (k : spec.PathPosition 3)
    (m : spec.PathPosition 8) (hj : j.val = 0)
    (hk : k.val = spec.length 0 - spec.length 8)
    (hm : m.val = spec.length 8) :
    pencil1 spec htri = tauDiv spec j k m := by
  have hkeq : k = ⟨kPos spec, by have := kPos_le spec htri; omega⟩ :=
    Fin.ext (by rw [hk]; rfl)
  unfold pencil1 tauDiv
  rw [pathVertex_eq_tail 0 j hj, hn.t0, pathVertex_eq_head 8 m hm, hn.h8, hkeq]
  abel

/-- Side `{v0,v5}` of the two-slot cut `{e0,e8}`. -/
def sideA : Fin 6 → Bool := ![true, false, false, false, false, true]

/-- Side `{v0,v2,v3,v5}` of the two-slot cut `{e0,e3}`. -/
def sideB : Fin 6 → Bool := ![true, false, true, true, false, true]

/-- Side `{v0,v1,v4,v5}` of the two-slot cut `{e3,e8}`. -/
def sideC : Fin 6 → Bool := ![true, true, false, false, true, true]

/-- All eighteen incidence equalities, as a simp bundle. -/
theorem necklace_simp_lemmas (hn : IsNecklace spec) :
    spec.core.tail 0 = 0 ∧ spec.core.tail 1 = 0 ∧ spec.core.tail 2 = 0 ∧
    spec.core.tail 3 = 1 ∧ spec.core.tail 4 = 1 ∧ spec.core.tail 5 = 1 ∧
    spec.core.tail 6 = 2 ∧ spec.core.tail 7 = 2 ∧ spec.core.tail 8 = 2 ∧
    spec.core.head 0 = 4 ∧ spec.core.head 1 = 5 ∧ spec.core.head 2 = 5 ∧
    spec.core.head 3 = 3 ∧ spec.core.head 4 = 4 ∧ spec.core.head 5 = 4 ∧
    spec.core.head 6 = 3 ∧ spec.core.head 7 = 3 ∧ spec.core.head 8 = 5 :=
  ⟨hn.t0, hn.t1, hn.t2, hn.t3, hn.t4, hn.t5, hn.t6, hn.t7, hn.t8,
   hn.h0, hn.h1, hn.h2, hn.h3, hn.h4, hn.h5, hn.h6, hn.h7, hn.h8⟩

/-- **March A**, across the cut `{e0,e8}`: the chip on `e8` returns to `v2`
while the chip on `e0` advances by `a₂`. -/
theorem march_A (hn : IsNecklace spec) (hmax₂ : spec.length 8 ≤ spec.length 0)
    (j j' : spec.PathPosition 0) (k : spec.PathPosition 3)
    (m m' : spec.PathPosition 8)
    (hj : j.val = 0) (hj' : j'.val = spec.length 8)
    (hm : m.val = spec.length 8) (hm' : m'.val = 0) :
    tauDiv spec j k m +
        prin spec.graph (rampScript spec (cutPot sideA (spec.length 8))
          (cutSgn spec sideA) (fun _ => 0) (spec.length 8)) =
      tauDiv spec j' k m' := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, h0, h1, h2, h3, h4, h5, h6, h7,
    h8⟩ := necklace_simp_lemmas hn
  have hdata : RampData spec (cutPot sideA (spec.length 8))
      (cutSgn spec sideA) (fun _ => 0) (spec.length 8) :=
    rampData_cut spec sideA _ _ (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp [cutSgn, sideA, t0, t1, t2, t3, t4, t5, t6, t7, t8,
          h0, h1, h2, h3, h4, h5, h6, h7, h8]
      omega)
  rw [prin_twoSlotRamp hdata (spec.length_pos 8) (α := 0) (β := 8) (by decide)
    (by simp [cutSgn, sideA, t0, h0]) (by simp [cutSgn, sideA, t8, h8])
    (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro hne1 hne2 <;>
        first
          | exact absurd rfl hne1
          | exact absurd rfl hne2
          | simp [cutSgn, sideA, t1, t2, t3, t4, t5, t6, t7,
              h1, h2, h3, h4, h5, h6, h7])
    (by simpa using hmax₂) (by simp) j j' m' m
    (by simpa using hj) (by simpa using hj') (by simpa using hm')
    (by simpa using hm)]
  unfold tauDiv
  abel

/-- **March B**, across the cut `{e0,e3}`: the chip on `e3` returns to `v1`
while the chip on `e0` advances from `a₂` to `a₀`.

Needs `a₂ < a₀`; when `a₂ = a₀` the march is vacuous and march A alone already
lands on the configuration this produces. -/
theorem march_B (hn : IsNecklace spec)
    (htri : spec.length 0 ≤ spec.length 3 + spec.length 8)
    (hpos : spec.length 8 < spec.length 0)
    (j j' : spec.PathPosition 0) (k k' : spec.PathPosition 3)
    (m : spec.PathPosition 8)
    (hj : j.val = spec.length 8) (hj' : j'.val = spec.length 0)
    (hk : k.val = spec.length 0 - spec.length 8) (hk' : k'.val = 0) :
    tauDiv spec j k m +
        prin spec.graph (rampScript spec
          (cutPot sideB (spec.length 0 - spec.length 8)) (cutSgn spec sideB)
          (fun e => if e = 0 then spec.length 8 else 0)
          (spec.length 0 - spec.length 8)) =
      tauDiv spec j' k' m := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, h0, h1, h2, h3, h4, h5, h6, h7,
    h8⟩ := necklace_simp_lemmas hn
  have hdata : RampData spec (cutPot sideB (spec.length 0 - spec.length 8))
      (cutSgn spec sideB) (fun e => if e = 0 then spec.length 8 else 0)
      (spec.length 0 - spec.length 8) :=
    rampData_cut spec sideB _ _ (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp [cutSgn, sideB, t0, t1, t2, t3, t4, t5, t6, t7, t8,
          h0, h1, h2, h3, h4, h5, h6, h7, h8]
      all_goals omega)
  rw [prin_twoSlotRamp hdata (by omega) (α := 0) (β := 3) (by decide)
    (by simp [cutSgn, sideB, t0, h0]) (by simp [cutSgn, sideB, t3, h3])
    (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro hne1 hne2 <;>
        first
          | exact absurd rfl hne1
          | exact absurd rfl hne2
          | simp [cutSgn, sideB, t1, t2, t4, t5, t6, t7, t8,
              h1, h2, h4, h5, h6, h7, h8])
    (by simp; omega) (by simp; omega) j j' k' k
    (by simpa using hj) (by simp; omega) (by simpa using hk')
    (by simp; omega)]
  unfold tauDiv
  abel

/-- **March C**, across the cut `{e3,e8}`: the chip on `e3` advances to the far
end `v3` while the chip on `e8` retreats, conserving `τ`.

Needs `a₀ < a₁ + a₂`; at the triangle boundary the march is vacuous, and there
the pencil's own middle chip already sits on `v3`. -/
theorem march_C (hn : IsNecklace spec) (hmax₁ : spec.length 3 ≤ spec.length 0)
    (hmax₂ : spec.length 8 ≤ spec.length 0)
    (hpos : spec.length 0 < spec.length 3 + spec.length 8)
    (j : spec.PathPosition 0) (k k' : spec.PathPosition 3)
    (m m' : spec.PathPosition 8)
    (hk : k.val = spec.length 0 - spec.length 8) (hk' : k'.val = spec.length 3)
    (hm : m.val = spec.length 8)
    (hm' : m'.val = spec.length 0 - spec.length 3) :
    tauDiv spec j k m +
        prin spec.graph (rampScript spec
          (cutPot sideC (spec.length 3 + spec.length 8 - spec.length 0))
          (cutSgn spec sideC)
          (fun e => if e = 3 then spec.length 0 - spec.length 8
            else if e = 8 then spec.length 0 - spec.length 3 else 0)
          (spec.length 3 + spec.length 8 - spec.length 0)) =
      tauDiv spec j k' m' := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, h0, h1, h2, h3, h4, h5, h6, h7,
    h8⟩ := necklace_simp_lemmas hn
  have hdata : RampData spec
      (cutPot sideC (spec.length 3 + spec.length 8 - spec.length 0))
      (cutSgn spec sideC)
      (fun e => if e = 3 then spec.length 0 - spec.length 8
        else if e = 8 then spec.length 0 - spec.length 3 else 0)
      (spec.length 3 + spec.length 8 - spec.length 0) :=
    rampData_cut spec sideC _ _ (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp [cutSgn, sideC, t0, t1, t2, t3, t4, t5, t6, t7, t8,
          h0, h1, h2, h3, h4, h5, h6, h7, h8]
      all_goals omega)
  rw [prin_twoSlotRamp hdata (by omega) (α := 3) (β := 8) (by decide)
    (by simp [cutSgn, sideC, t3, h3]) (by simp [cutSgn, sideC, t8, h8])
    (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro hne1 hne2 <;>
        first
          | exact absurd rfl hne1
          | exact absurd rfl hne2
          | simp [cutSgn, sideC, t0, t1, t2, t4, t5, t6, t7,
              h0, h1, h2, h4, h5, h6, h7])
    (by simp; omega) (by simp; omega) k k' m' m
    (by simpa using hk) (by simp; omega) (by simp; omega)
    (by simp; omega)]
  unfold tauDiv
  abel

end Regime1March

/-! ## The single regime-1 obligation

`bnExists_regime1` is reduced to *one* statement: that the pencil reaches the
six core vertices.  Nothing about interior vertices is needed.

That is the anchor-only route back-ported into
the accompanying analysis from the row-proof-format branch:
the embedded core vertices are a strong separator of any positive
subdivision, so `Certificate.CoreVertexReachability.bnExists_of_reaches_coreVertices`
upgrades reachability at the core to `rank ≥ 1` outright.  The capped
reflections that sweep the nine slots are needed only to *exhibit* the pencil,
not to prove the rank statement — which is what makes this proposal much
smaller than the row-100 file it is modelled on.

Stated against `IsNecklace` rather than the catalog row so the marches can be
developed for an arbitrary spec. -/

section Regime1Coverage

variable (spec : SubdivisionGraph.Spec 6 9)

/-- Coverage bookkeeping, once: a script carrying the pencil to a `τ`-family
member one of whose three positions names `u` proves that the pencil reaches
`u`.  Effectivity is automatic (`effective_tauDiv`), and the chip bound is
`one_le_tauDiv_of_eq`. -/
private theorem reaches_of_tau
    (htri : spec.length 0 ≤ spec.length 3 + spec.length 8)
    (script : firingScript spec.graph) (j : spec.PathPosition 0)
    (k : spec.PathPosition 3) (m : spec.PathPosition 8)
    (heq : pencil1 spec htri + prin spec.graph script = tauDiv spec j k m)
    (u : Fin 6)
    (hcov : spec.pathVertex 0 j = spec.coreVertex u ∨
      spec.pathVertex 3 k = spec.coreVertex u ∨
      spec.pathVertex 8 m = spec.coreVertex u) :
    Certificate.StrongSeparator.Reaches spec.graph (pencil1 spec htri)
      (spec.coreVertex u) :=
  spec.reaches_of_script (pencil1 spec htri) script _
    (by rw [heq]; exact effective_tauDiv spec j k m)
    (by rw [heq]; exact one_le_tauDiv_of_eq spec j k m u hcov)

/-- Every core vertex is reached by the regime-1 pencil.

**Route, worked out and checked by hand 2026-08-13.**  Introduce the
`τ`-family `T(j,k,m)` = one chip on each single slot, at distances `j, k, m`
from `v0, v1, v2` (i.e. `pathVertex 0 j + pathVertex 3 k + pathVertex 8 m`).
Then:

* `pencil1 = T(0, a₀ − a₂, a₂)`, because `pathVertex 0 0 = v0` (`pathVertex_zero`
  and `hn.t0`) and `pathVertex 8 a₂ = v5` (`pathVertex_length` and `hn.h8`);
* the six core vertices are covered by just **three** members of the level set
  `j + k + m = a₀`:
  - `v0`, `v5` : `T(0, a₀ − a₂, a₂)`, the pencil itself;
  - `v1`, `v2`, `v4` : `T(a₀, 0, 0)` — chips at the head of `e0` (`= v4`, by
    `hn.h0`), the tail of `e3` (`= v1`, `hn.t3`) and the tail of `e8`
    (`= v2`, `hn.t8`);
  - `v3` : `T(a₀ − a₁ − m, a₁, m)` with `m = min a₂ (a₀ − a₁)`, whose middle
    chip is at the head of `e3` (`= v3`, `hn.h3`).  The bounds need
    `a₁ ≤ a₀` (`hmax₁`) and `m ≤ a₀ − a₁` (from the `min`).

The marches themselves are now proved: `march_A`, `march_B` and `march_C`
above realize exactly the three equivalences this needs.  What is left is
purely the coverage bookkeeping — instantiate the marches at the six vertices
and identify the endpoints via `pathVertex_zero`/`pathVertex_length` and the
`IsNecklace` fields — together with the two degenerate cases that the marches
carry as hypotheses:

* `a₂ = a₀`: march B is vacuous, and march A alone already lands on
  `T(a₀, 0, 0)`, so `v1, v2, v4` are still covered.
* `a₀ = a₁ + a₂` (the triangle boundary): march C is vacuous, but there
  `a₀ − a₂ = a₁`, so the pencil's own middle chip already sits on
  `pathVertex 3 a₁ = v3`.

Chaining A and B uses `prin` additivity: the script is `scriptA + scriptB` and
`map_add` splits its Laplacian.

Note the interior slots need no attention at all: by the strong-separator
route this lemma is the whole obligation. -/
theorem regime1_reaches_core (hn : IsNecklace spec)
    (htri : spec.length 0 ≤ spec.length 3 + spec.length 8)
    (hmax₁ : spec.length 3 ≤ spec.length 0)
    (hmax₂ : spec.length 8 ≤ spec.length 0) (u : Fin 6) :
    Certificate.StrongSeparator.Reaches spec.graph (pencil1 spec htri)
      (spec.coreVertex u) := by
  -- The nine path positions the three members need, named by their depths.
  obtain ⟨jz, hjz⟩ : ∃ j : spec.PathPosition 0, j.val = 0 :=
    ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨jmid, hjmid⟩ : ∃ j : spec.PathPosition 0, j.val = spec.length 8 :=
    ⟨⟨spec.length 8, by omega⟩, rfl⟩
  obtain ⟨jfull, hjfull⟩ : ∃ j : spec.PathPosition 0, j.val = spec.length 0 :=
    ⟨⟨spec.length 0, by omega⟩, rfl⟩
  obtain ⟨kz, hkz⟩ : ∃ k : spec.PathPosition 3, k.val = 0 :=
    ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨kmid, hkmid⟩ : ∃ k : spec.PathPosition 3,
      k.val = spec.length 0 - spec.length 8 :=
    ⟨⟨spec.length 0 - spec.length 8, by omega⟩, rfl⟩
  obtain ⟨kfull, hkfull⟩ : ∃ k : spec.PathPosition 3, k.val = spec.length 3 :=
    ⟨⟨spec.length 3, by omega⟩, rfl⟩
  obtain ⟨mz, hmz⟩ : ∃ m : spec.PathPosition 8, m.val = 0 :=
    ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨mmid, hmmid⟩ : ∃ m : spec.PathPosition 8,
      m.val = spec.length 0 - spec.length 3 :=
    ⟨⟨spec.length 0 - spec.length 3, by omega⟩, rfl⟩
  obtain ⟨mfull, hmfull⟩ : ∃ m : spec.PathPosition 8, m.val = spec.length 8 :=
    ⟨⟨spec.length 8, by omega⟩, rfl⟩
  -- The pencil is `T(0, a₀ − a₂, a₂)`.
  have hpen : pencil1 spec htri = tauDiv spec jz kmid mfull :=
    pencil1_eq_tauDiv hn htri jz kmid mfull hjz hkmid hmfull
  -- The member `T(a₀, 0, 0)`, covering `v1`, `v2` and `v4` at once.  March A
  -- alone suffices when `a₂ = a₀`, where march B would be vacuous.
  obtain ⟨s000, h000⟩ : ∃ s, pencil1 spec htri + prin spec.graph s =
      tauDiv spec jfull kz mz := by
    obtain ⟨sA, hA⟩ : ∃ s, tauDiv spec jz kmid mfull + prin spec.graph s =
        tauDiv spec jmid kmid mz :=
      ⟨_, march_A hn hmax₂ jz jmid kmid mfull mz hjz hjmid hmfull hmz⟩
    by_cases hlt : spec.length 8 < spec.length 0
    · obtain ⟨sB, hB⟩ : ∃ s, tauDiv spec jmid kmid mz + prin spec.graph s =
          tauDiv spec jfull kz mz :=
        ⟨_, march_B hn htri hlt jmid jfull kmid kz mz hjmid hjfull hkmid hkz⟩
      exact ⟨sA + sB, by rw [map_add, ← add_assoc, hpen, hA, hB]⟩
    · have hj : jmid = jfull := Fin.ext (by omega)
      have hk : kmid = kz := Fin.ext (by omega)
      exact ⟨sA, by rw [hpen, hA, hj, hk]⟩
  -- The member `T(0, a₁, a₀ − a₁)`, covering `v3`.  At the triangle boundary
  -- march C is vacuous, but there `a₀ − a₂ = a₁`, so the pencil already is it.
  obtain ⟨sv3, hv3⟩ : ∃ s, pencil1 spec htri + prin spec.graph s =
      tauDiv spec jz kfull mmid := by
    by_cases hlt : spec.length 0 < spec.length 3 + spec.length 8
    · obtain ⟨sC, hC⟩ : ∃ s, tauDiv spec jz kmid mfull + prin spec.graph s =
          tauDiv spec jz kfull mmid :=
        ⟨_, march_C hn hmax₁ hmax₂ hlt jz kmid kfull mfull mmid hkmid hkfull
          hmfull hmmid⟩
      exact ⟨sC, by rw [hpen, hC]⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, add_zero]
      exact pencil1_eq_tauDiv hn htri jz kfull mmid hjz (by omega) (by omega)
  revert u
  refine forall_fin_six ?_ ?_ ?_ ?_ ?_ ?_
  · -- `v0`: the pencil's own chip on `e0`, at depth `0` = tail of `e0`.
    exact reaches_of_tau spec htri 0 jz kmid mfull
      (by rw [map_zero, add_zero]; exact hpen) 0
      (Or.inl (by rw [pathVertex_eq_tail 0 jz hjz, hn.t0]))
  · -- `v1`: the chip of `T(a₀,0,0)` on `e3`, at depth `0` = tail of `e3`.
    exact reaches_of_tau spec htri s000 jfull kz mz h000 1
      (Or.inr (Or.inl (by rw [pathVertex_eq_tail 3 kz hkz, hn.t3])))
  · -- `v2`: the chip of `T(a₀,0,0)` on `e8`, at depth `0` = tail of `e8`.
    exact reaches_of_tau spec htri s000 jfull kz mz h000 2
      (Or.inr (Or.inr (by rw [pathVertex_eq_tail 8 mz hmz, hn.t8])))
  · -- `v3`: the chip of `T(0,a₁,a₀−a₁)` on `e3`, at full depth = head of `e3`.
    exact reaches_of_tau spec htri sv3 jz kfull mmid hv3 3
      (Or.inr (Or.inl (by rw [pathVertex_eq_head 3 kfull hkfull, hn.h3])))
  · -- `v4`: the chip of `T(a₀,0,0)` on `e0`, at full depth = head of `e0`.
    exact reaches_of_tau spec htri s000 jfull kz mz h000 4
      (Or.inl (by rw [pathVertex_eq_head 0 jfull hjfull, hn.h0]))
  · -- `v5`: the pencil's own chip on `e8`, at depth `a₂` = head of `e8`.
    exact reaches_of_tau spec htri 0 jz kmid mfull
      (by rw [map_zero, add_zero]; exact hpen) 5
      (Or.inr (Or.inr (by rw [pathVertex_eq_head 8 mfull hmfull, hn.h8])))

end Regime1Coverage

/-! ## Regime 2: the banana relay

Regime 2 is `x = a₀ − a₁ − a₂ > 0` in the chart where `a₀` is a longest single
and `e6` is the longer arc of `β₂`.  Write `s = min(x, a₇)`; the divisor is

    D = v0 + v5 + (point on e6 at distance s from v3).

The pencil is a single chain of marches, all of them cut marches with the chip
on `e0` advancing, and the sides forming an increasing chain

    {v0,v5} ⊂ {v0,v2,v5} ⊂ {v0,v2,v3,v5} ⊂ {v0,v1,v2,v3,v5}

as the two trailing chips walk backwards around the necklace `v5 → v2 → v3 →
v1 → v4`.  Crossing the banana `β₂` is the "relay": the parked chip on `e6`
and the arriving chip (now on `e7`) advance *together*, which is the
three-slot cut `{e0,e6,e7}`; crossing `β₁` at the end is the three-slot cut
`{e0,e4,e5}`, i.e. the star of `v4`.  The chain, with the `e0` depth in
brackets:

    [0]      v0 + (e6 at a₆−s) + v5
    [a₂]     · + (e6 at a₆−s) + v2            (cut {e0,e8})
    [a₂+s]   · + v3 + (e7 at s)               (cut {e0,e6,e7}, the relay)
    [a₂+s+a₁] · + (e7 at s) + v1              (cut {e0,e3})

which already covers `v0, v1, v2, v3, v5`.  For `v4`, put `r = x − s`.  If
`r = 0` the last configuration already has its `e0` chip at `v4`.  Otherwise
`s = a₇`, so the chip on `e7` is a second chip at `v3`; one more `{e0,e3}`
march of length `min(a₁, r)` either lands the `e0` chip on `v4` or leaves two
chips at `v1`, and then the star march at `v4` delivers a chip to `v4`
whichever of its three slots runs out first. -/

section Regime2

open Utilities.Certificate.SubdivisionRamp

variable {spec : SubdivisionGraph.Spec 6 9}

/-- Side `{v0,v2,v5}` of the three-slot cut `{e0,e6,e7}`: the banana relay. -/
def sideR : Fin 6 → Bool := ![true, false, true, false, false, true]

/-- Side `{v0,v1,v2,v3,v5}` of the three-slot cut `{e0,e4,e5}`: the star of
`v4`. -/
def sideD : Fin 6 → Bool := ![true, true, true, true, false, true]

/-- Coverage bookkeeping for configurations, once. -/
theorem reaches_of_cfg (D : CFDiv spec.graph)
    (script : firingScript spec.graph) (u v w z : spec.graph.V)
    (heq : D + prin spec.graph script = cfg spec u v w)
    (hz : u = z ∨ v = z ∨ w = z) :
    Certificate.StrongSeparator.Reaches spec.graph D z :=
  spec.reaches_of_script D script z
    (by rw [heq]; exact effective_cfg spec u v w)
    (by rw [heq]; exact one_le_cfg spec u v w z hz)

/-- **The `{e0,e8}` march**: a chip retreats by `t` along `e8` while a chip
advances by `t` along `e0`.  A third chip, anywhere, is untouched. -/
theorem march_cutA (hn : IsNecklace spec) (lo0 lo8 t : ℕ) (ht : 0 < t)
    (hw0 : lo0 + t ≤ spec.length 0) (hw8 : lo8 + t ≤ spec.length 8)
    (j j' : spec.PathPosition 0) (m m' : spec.PathPosition 8)
    (hj : j.val = lo0) (hj' : j'.val = lo0 + t)
    (hm : m.val = lo8 + t) (hm' : m'.val = lo8) (w : spec.graph.V) :
    cfg spec (spec.pathVertex 0 j) w (spec.pathVertex 8 m) +
        prin spec.graph (rampScript spec (cutPot sideA t) (cutSgn spec sideA)
          (fun e => if e = 0 then lo0 else lo8) t) =
      cfg spec (spec.pathVertex 0 j') w (spec.pathVertex 8 m') := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, h0, h1, h2, h3, h4, h5, h6, h7,
    h8⟩ := necklace_simp_lemmas hn
  have hdata : RampData spec (cutPot sideA t) (cutSgn spec sideA)
      (fun e => if e = 0 then lo0 else lo8) t :=
    rampData_cut spec sideA _ _ (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp [cutSgn, sideA, t0, t1, t2, t3, t4, t5, t6, t7, t8,
          h0, h1, h2, h3, h4, h5, h6, h7, h8]
      all_goals omega)
  rw [prin_twoSlotRamp hdata ht (α := 0) (β := 8) (by decide)
    (by simp [cutSgn, sideA, t0, h0]) (by simp [cutSgn, sideA, t8, h8])
    (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro hne1 hne2 <;>
        first
          | exact absurd rfl hne1
          | exact absurd rfl hne2
          | simp [cutSgn, sideA, t1, t2, t3, t4, t5, t6, t7,
              h1, h2, h3, h4, h5, h6, h7])
    (by simpa using hw0) (by simpa using hw8) j j' m' m
    (by simpa using hj) (by simp; omega) (by simpa using hm')
    (by simp; omega)]
  unfold cfg
  abel

/-- **The `{e0,e3}` march**: a chip retreats by `t` along `e3` while a chip
advances by `t` along `e0`.  A third chip, anywhere, is untouched. -/
theorem march_cutB (hn : IsNecklace spec) (lo0 lo3 t : ℕ) (ht : 0 < t)
    (hw0 : lo0 + t ≤ spec.length 0) (hw3 : lo3 + t ≤ spec.length 3)
    (j j' : spec.PathPosition 0) (k k' : spec.PathPosition 3)
    (hj : j.val = lo0) (hj' : j'.val = lo0 + t)
    (hk : k.val = lo3 + t) (hk' : k'.val = lo3) (w : spec.graph.V) :
    cfg spec (spec.pathVertex 0 j) w (spec.pathVertex 3 k) +
        prin spec.graph (rampScript spec (cutPot sideB t) (cutSgn spec sideB)
          (fun e => if e = 0 then lo0 else lo3) t) =
      cfg spec (spec.pathVertex 0 j') w (spec.pathVertex 3 k') := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, h0, h1, h2, h3, h4, h5, h6, h7,
    h8⟩ := necklace_simp_lemmas hn
  have hdata : RampData spec (cutPot sideB t) (cutSgn spec sideB)
      (fun e => if e = 0 then lo0 else lo3) t :=
    rampData_cut spec sideB _ _ (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp [cutSgn, sideB, t0, t1, t2, t3, t4, t5, t6, t7, t8,
          h0, h1, h2, h3, h4, h5, h6, h7, h8]
      all_goals omega)
  rw [prin_twoSlotRamp hdata ht (α := 0) (β := 3) (by decide)
    (by simp [cutSgn, sideB, t0, h0]) (by simp [cutSgn, sideB, t3, h3])
    (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro hne1 hne2 <;>
        first
          | exact absurd rfl hne1
          | exact absurd rfl hne2
          | simp [cutSgn, sideB, t1, t2, t4, t5, t6, t7, t8,
              h1, h2, h4, h5, h6, h7, h8])
    (by simpa using hw0) (by simpa using hw3) j j' k' k
    (by simpa using hj) (by simp; omega) (by simpa using hk')
    (by simp; omega)]
  unfold cfg
  abel

/-- **The relay**: the three-slot `{e0,e6,e7}` march.  The chip parked on the
long arc `e6` and the chip arriving on the short arc `e7` advance together
with the chip on `e0`. -/
theorem march_relay (hn : IsNecklace spec) (lo0 lo6 lo7 t : ℕ) (ht : 0 < t)
    (hw0 : lo0 + t ≤ spec.length 0) (hw6 : lo6 + t ≤ spec.length 6)
    (hw7 : lo7 + t ≤ spec.length 7)
    (j j' : spec.PathPosition 0) (q q' : spec.PathPosition 6)
    (r r' : spec.PathPosition 7)
    (hj : j.val = lo0) (hj' : j'.val = lo0 + t)
    (hq : q.val = lo6) (hq' : q'.val = lo6 + t)
    (hr : r.val = lo7) (hr' : r'.val = lo7 + t) :
    cfg spec (spec.pathVertex 0 j) (spec.pathVertex 6 q) (spec.pathVertex 7 r) +
        prin spec.graph (rampScript spec (cutPot sideR t) (cutSgn spec sideR)
          (fun e => if e = 0 then lo0 else if e = 6 then lo6 else lo7) t) =
      cfg spec (spec.pathVertex 0 j') (spec.pathVertex 6 q')
        (spec.pathVertex 7 r') := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, h0, h1, h2, h3, h4, h5, h6, h7,
    h8⟩ := necklace_simp_lemmas hn
  have hdata : RampData spec (cutPot sideR t) (cutSgn spec sideR)
      (fun e => if e = 0 then lo0 else if e = 6 then lo6 else lo7) t :=
    rampData_cut spec sideR _ _ (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp [cutSgn, sideR, t0, t1, t2, t3, t4, t5, t6, t7, t8,
          h0, h1, h2, h3, h4, h5, h6, h7, h8]
      all_goals omega)
  rw [prin_threeSlotRampNeg hdata ht (α := 0) (β := 6) (γ := 7) (by decide)
    (by decide) (by decide)
    (by simp [cutSgn, sideR, t0, h0]) (by simp [cutSgn, sideR, t6, h6])
    (by simp [cutSgn, sideR, t7, h7])
    (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        intro hne1 hne2 hne3 <;>
        first
          | exact absurd rfl hne1
          | exact absurd rfl hne2
          | exact absurd rfl hne3
          | simp [cutSgn, sideR, t1, t2, t3, t4, t5, t8,
              h1, h2, h3, h4, h5, h8])
    (by simpa using hw0) (by simp; omega) (by simp; omega) j j' q q' r r'
    (by simpa using hj) (by simp; omega) (by simp; omega) (by simp; omega)
    (by simp; omega) (by simp; omega)]
  unfold cfg
  abel

/-- **The star march at `v4`**: the three-slot `{e0,e4,e5}` march, i.e. firing
the complement of `v4`.  Two chips at `v1` enter the banana `β₁` while the
chip on `e0` advances. -/
theorem march_star (hn : IsNecklace spec) (lo0 lo4 lo5 t : ℕ) (ht : 0 < t)
    (hw0 : lo0 + t ≤ spec.length 0) (hw4 : lo4 + t ≤ spec.length 4)
    (hw5 : lo5 + t ≤ spec.length 5)
    (j j' : spec.PathPosition 0) (b b' : spec.PathPosition 4)
    (c c' : spec.PathPosition 5)
    (hj : j.val = lo0) (hj' : j'.val = lo0 + t)
    (hb : b.val = lo4) (hb' : b'.val = lo4 + t)
    (hc : c.val = lo5) (hc' : c'.val = lo5 + t) :
    cfg spec (spec.pathVertex 0 j) (spec.pathVertex 4 b) (spec.pathVertex 5 c) +
        prin spec.graph (rampScript spec (cutPot sideD t) (cutSgn spec sideD)
          (fun e => if e = 0 then lo0 else if e = 4 then lo4 else lo5) t) =
      cfg spec (spec.pathVertex 0 j') (spec.pathVertex 4 b')
        (spec.pathVertex 5 c') := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, h0, h1, h2, h3, h4, h5, h6, h7,
    h8⟩ := necklace_simp_lemmas hn
  have hdata : RampData spec (cutPot sideD t) (cutSgn spec sideD)
      (fun e => if e = 0 then lo0 else if e = 4 then lo4 else lo5) t :=
    rampData_cut spec sideD _ _ (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp [cutSgn, sideD, t0, t1, t2, t3, t4, t5, t6, t7, t8,
          h0, h1, h2, h3, h4, h5, h6, h7, h8]
      all_goals omega)
  rw [prin_threeSlotRampNeg hdata ht (α := 0) (β := 4) (γ := 5) (by decide)
    (by decide) (by decide)
    (by simp [cutSgn, sideD, t0, h0]) (by simp [cutSgn, sideD, t4, h4])
    (by simp [cutSgn, sideD, t5, h5])
    (by
      refine forall_fin_nine ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        intro hne1 hne2 hne3 <;>
        first
          | exact absurd rfl hne1
          | exact absurd rfl hne2
          | exact absurd rfl hne3
          | simp [cutSgn, sideD, t1, t2, t3, t6, t7, t8,
              h1, h2, h3, h6, h7, h8])
    (by simpa using hw0) (by simp; omega) (by simp; omega) j j' b b' c c'
    (by simpa using hj) (by simp; omega) (by simp; omega) (by simp; omega)
    (by simp; omega) (by simp; omega)]
  unfold cfg
  abel

/-- **Arrival at `v4`.**  Whenever the pencil reaches a configuration with two
chips at `v1` and one on `e0`, it reaches `v4`: either the `e0` chip is already
at the head of `e0`, or the star march at `v4` runs for
`t = min(a₄, a₅, a₀ − j)` steps and whichever of the three slots attains the
minimum delivers its chip to `v4`. -/
theorem reaches_v4_of_star (hn : IsNecklace spec) (D : CFDiv spec.graph)
    (script : firingScript spec.graph) (j : spec.PathPosition 0)
    (heq : D + prin spec.graph script =
      cfg spec (spec.pathVertex 0 j) (spec.coreVertex 1) (spec.coreVertex 1)) :
    Certificate.StrongSeparator.Reaches spec.graph D (spec.coreVertex 4) := by
  have hp0 := spec.length_pos 0
  have hp4 := spec.length_pos 4
  have hp5 := spec.length_pos 5
  have hjlt := j.isLt
  by_cases hfull : j.val = spec.length 0
  · exact reaches_of_cfg D script _ _ _ _ heq
      (Or.inl (by rw [pathVertex_eq_head 0 j hfull, hn.h0]))
  · obtain ⟨b0, hb0⟩ : ∃ b : spec.PathPosition 4, b.val = 0 :=
      ⟨⟨0, by omega⟩, rfl⟩
    obtain ⟨c0, hc0⟩ : ∃ c : spec.PathPosition 5, c.val = 0 :=
      ⟨⟨0, by omega⟩, rfl⟩
    obtain ⟨b1, hb1⟩ : ∃ b : spec.PathPosition 4,
        b.val = min (min (spec.length 4) (spec.length 5))
          (spec.length 0 - j.val) :=
      ⟨⟨min (min (spec.length 4) (spec.length 5)) (spec.length 0 - j.val),
        by omega⟩, rfl⟩
    obtain ⟨c1, hc1⟩ : ∃ c : spec.PathPosition 5,
        c.val = min (min (spec.length 4) (spec.length 5))
          (spec.length 0 - j.val) :=
      ⟨⟨min (min (spec.length 4) (spec.length 5)) (spec.length 0 - j.val),
        by omega⟩, rfl⟩
    obtain ⟨j1, hj1⟩ : ∃ q : spec.PathPosition 0,
        q.val = j.val + min (min (spec.length 4) (spec.length 5))
          (spec.length 0 - j.val) :=
      ⟨⟨j.val + min (min (spec.length 4) (spec.length 5))
        (spec.length 0 - j.val), by omega⟩, rfl⟩
    have hv1a : spec.coreVertex 1 = spec.pathVertex 4 b0 := by
      rw [pathVertex_eq_tail 4 b0 hb0, hn.t4]
    have hv1b : spec.coreVertex 1 = spec.pathVertex 5 c0 := by
      rw [pathVertex_eq_tail 5 c0 hc0, hn.t5]
    have heq' : D + prin spec.graph script =
        cfg spec (spec.pathVertex 0 j) (spec.pathVertex 4 b0)
          (spec.pathVertex 5 c0) := by
      rw [heq, ← hv1a, ← hv1b]
    obtain ⟨sD, hD⟩ : ∃ s,
        cfg spec (spec.pathVertex 0 j) (spec.pathVertex 4 b0)
            (spec.pathVertex 5 c0) + prin spec.graph s =
          cfg spec (spec.pathVertex 0 j1) (spec.pathVertex 4 b1)
            (spec.pathVertex 5 c1) :=
      ⟨_, march_star hn j.val 0 0
        (min (min (spec.length 4) (spec.length 5)) (spec.length 0 - j.val))
        (by omega) (by omega) (by omega) (by omega) j j1 b0 b1 c0 c1 rfl
        (by omega) hb0 (by omega) hc0 (by omega)⟩
    have hs2 : D + prin spec.graph (script + sD) =
        cfg spec (spec.pathVertex 0 j1) (spec.pathVertex 4 b1)
          (spec.pathVertex 5 c1) := by
      rw [map_add, ← add_assoc, heq']
      exact hD
    have hmin : min (min (spec.length 4) (spec.length 5))
          (spec.length 0 - j.val) = spec.length 4 ∨
        min (min (spec.length 4) (spec.length 5))
          (spec.length 0 - j.val) = spec.length 5 ∨
        j.val + min (min (spec.length 4) (spec.length 5))
          (spec.length 0 - j.val) = spec.length 0 := by omega
    rcases hmin with hm | hm | hm
    · exact reaches_of_cfg D (script + sD) _ _ _ _ hs2
        (Or.inr (Or.inl (by rw [pathVertex_eq_head 4 b1 (by omega), hn.h4])))
    · exact reaches_of_cfg D (script + sD) _ _ _ _ hs2
        (Or.inr (Or.inr (by rw [pathVertex_eq_head 5 c1 (by omega), hn.h5])))
    · exact reaches_of_cfg D (script + sD) _ _ _ _ hs2
        (Or.inl (by rw [pathVertex_eq_head 0 j1 (by omega), hn.h0]))

/-- **Every core vertex is reached by the regime-2 pencil.**

The chain of marches is the one described in the section docstring; only the
six core vertices are needed, by the strong-separator route. -/
theorem regime2_reaches_core (hn : IsNecklace spec)
    (hx : spec.length 3 + spec.length 8 < spec.length 0)
    (harc : spec.length 7 ≤ spec.length 6) (u : Fin 6) :
    Certificate.StrongSeparator.Reaches spec.graph (pencil2 spec)
      (spec.coreVertex u) := by
  have hp0 := spec.length_pos 0
  have hp3 := spec.length_pos 3
  have hp6 := spec.length_pos 6
  have hp7 := spec.length_pos 7
  have hp8 := spec.length_pos 8
  have hs : sPos spec =
      min (spec.length 0 - spec.length 3 - spec.length 8) (spec.length 7) := rfl
  -- The nine path positions the chain visits, named by their depths.
  obtain ⟨j0, hj0⟩ : ∃ j : spec.PathPosition 0, j.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨j1, hj1⟩ : ∃ j : spec.PathPosition 0, j.val = spec.length 8 :=
    ⟨⟨spec.length 8, by omega⟩, rfl⟩
  obtain ⟨j2, hj2⟩ : ∃ j : spec.PathPosition 0,
      j.val = spec.length 8 + sPos spec :=
    ⟨⟨spec.length 8 + sPos spec, by omega⟩, rfl⟩
  obtain ⟨j3, hj3⟩ : ∃ j : spec.PathPosition 0,
      j.val = spec.length 8 + sPos spec + spec.length 3 :=
    ⟨⟨spec.length 8 + sPos spec + spec.length 3, by omega⟩, rfl⟩
  obtain ⟨q0, hq0⟩ : ∃ q : spec.PathPosition 6,
      q.val = spec.length 6 - sPos spec :=
    ⟨⟨spec.length 6 - sPos spec, by omega⟩, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ q : spec.PathPosition 6, q.val = spec.length 6 :=
    ⟨⟨spec.length 6, by omega⟩, rfl⟩
  obtain ⟨r0, hr0⟩ : ∃ r : spec.PathPosition 7, r.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨r1, hr1⟩ : ∃ r : spec.PathPosition 7, r.val = sPos spec :=
    ⟨⟨sPos spec, by omega⟩, rfl⟩
  obtain ⟨m0, hm0⟩ : ∃ m : spec.PathPosition 8, m.val = spec.length 8 :=
    ⟨⟨spec.length 8, by omega⟩, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m : spec.PathPosition 8, m.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨k0, hk0⟩ : ∃ k : spec.PathPosition 3, k.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ k : spec.PathPosition 3, k.val = spec.length 3 :=
    ⟨⟨spec.length 3, by omega⟩, rfl⟩
  -- The pencil, read as a configuration.
  have hpen : pencil2 spec = cfg spec (spec.pathVertex 0 j0)
      (spec.pathVertex 6 q0) (spec.pathVertex 8 m0) := by
    have hq : q0 = ⟨spec.length 6 - sPos spec, by omega⟩ := Fin.ext (by rw [hq0])
    unfold pencil2 cfg
    rw [pathVertex_eq_tail 0 j0 hj0, hn.t0, pathVertex_eq_head 8 m0 hm0, hn.h8,
      hq]
    abel
  -- Step 1: the `{e0,e8}` march brings the trailing chip from `v5` to `v2`.
  obtain ⟨sA, hA⟩ : ∃ s,
      cfg spec (spec.pathVertex 0 j0) (spec.pathVertex 6 q0)
          (spec.pathVertex 8 m0) + prin spec.graph s =
        cfg spec (spec.pathVertex 0 j1) (spec.pathVertex 6 q0)
          (spec.pathVertex 8 m1) :=
    ⟨_, march_cutA hn 0 0 (spec.length 8) (by omega) (by omega) (by omega)
      j0 j1 m0 m1 hj0 (by omega) (by omega) hm1 (spec.pathVertex 6 q0)⟩
  have hsc1 : pencil2 spec + prin spec.graph sA =
      cfg spec (spec.pathVertex 0 j1) (spec.pathVertex 6 q0)
        (spec.pathVertex 8 m1) := by
    rw [hpen]
    exact hA
  -- Step 2: the relay across `β₂`.
  have hv2 : spec.pathVertex 8 m1 = spec.pathVertex 7 r0 := by
    rw [pathVertex_eq_tail 8 m1 hm1, pathVertex_eq_tail 7 r0 hr0, hn.t8, hn.t7]
  obtain ⟨sR, hR⟩ : ∃ s,
      cfg spec (spec.pathVertex 0 j1) (spec.pathVertex 6 q0)
          (spec.pathVertex 7 r0) + prin spec.graph s =
        cfg spec (spec.pathVertex 0 j2) (spec.pathVertex 6 q1)
          (spec.pathVertex 7 r1) :=
    ⟨_, march_relay hn (spec.length 8) (spec.length 6 - sPos spec) 0
      (sPos spec) (by omega) (by omega) (by omega) (by omega) j1 j2 q0 q1 r0 r1
      hj1 (by omega) hq0 (by omega) hr0 (by omega)⟩
  have hsc2 : pencil2 spec + prin spec.graph (sA + sR) =
      cfg spec (spec.pathVertex 0 j2) (spec.pathVertex 6 q1)
        (spec.pathVertex 7 r1) := by
    rw [map_add, ← add_assoc, hsc1, hv2]
    exact hR
  -- Step 3: the `{e0,e3}` march brings the leading trailer from `v3` to `v1`.
  have hv3 : spec.pathVertex 6 q1 = spec.pathVertex 3 k1 := by
    rw [pathVertex_eq_head 6 q1 hq1, pathVertex_eq_head 3 k1 hk1, hn.h6, hn.h3]
  obtain ⟨sB, hB⟩ : ∃ s,
      cfg spec (spec.pathVertex 0 j2) (spec.pathVertex 7 r1)
          (spec.pathVertex 3 k1) + prin spec.graph s =
        cfg spec (spec.pathVertex 0 j3) (spec.pathVertex 7 r1)
          (spec.pathVertex 3 k0) :=
    ⟨_, march_cutB hn (spec.length 8 + sPos spec) 0 (spec.length 3)
      (by omega) (by omega) (by omega) j2 j3 k1 k0 hj2 (by omega) (by omega) hk0
      (spec.pathVertex 7 r1)⟩
  have hsc3 : pencil2 spec + prin spec.graph (sA + sR + sB) =
      cfg spec (spec.pathVertex 0 j3) (spec.pathVertex 7 r1)
        (spec.pathVertex 3 k0) := by
    rw [map_add, ← add_assoc, hsc2, hv3, cfg_swap]
    exact hB
  revert u
  refine forall_fin_six ?_ ?_ ?_ ?_ ?_ ?_
  · -- `v0`: the pencil's own chip at the tail of `e0`.
    exact reaches_of_cfg _ 0 _ _ _ _ (by rw [map_zero, add_zero]; exact hpen)
      (Or.inl (by rw [pathVertex_eq_tail 0 j0 hj0, hn.t0]))
  · -- `v1`: the leading trailer after step 3, at the tail of `e3`.
    exact reaches_of_cfg _ (sA + sR + sB) _ _ _ _ hsc3
      (Or.inr (Or.inr (by rw [pathVertex_eq_tail 3 k0 hk0, hn.t3])))
  · -- `v2`: the trailing chip after step 1, at the tail of `e8`.
    exact reaches_of_cfg _ sA _ _ _ _ hsc1
      (Or.inr (Or.inr (by rw [pathVertex_eq_tail 8 m1 hm1, hn.t8])))
  · -- `v3`: the relayed chip after step 2, at the head of `e6`.
    exact reaches_of_cfg _ (sA + sR) _ _ _ _ hsc2
      (Or.inr (Or.inl (by rw [pathVertex_eq_head 6 q1 hq1, hn.h6])))
  · -- `v4`: the three-case tail of the chain.
    by_cases hzero :
        spec.length 8 + sPos spec + spec.length 3 = spec.length 0
    · -- `r = 0`: step 3 already parks the `e0` chip on the head of `e0`.
      exact reaches_of_cfg _ (sA + sR + sB) _ _ _ _ hsc3
        (Or.inl (by rw [pathVertex_eq_head 0 j3 (by omega), hn.h0]))
    · -- `r > 0` forces `s = a₇`, so the chip on `e7` is a second chip at `v3`.
      have hs7 : sPos spec = spec.length 7 := by omega
      have hv3' : spec.pathVertex 7 r1 = spec.pathVertex 3 k1 := by
        rw [pathVertex_eq_head 7 r1 (by omega), pathVertex_eq_head 3 k1 hk1,
          hn.h7, hn.h3]
      obtain ⟨k2, hk2⟩ : ∃ k : spec.PathPosition 3,
          k.val = spec.length 3 - min (spec.length 3)
            (spec.length 0 - (spec.length 8 + sPos spec + spec.length 3)) :=
        ⟨⟨spec.length 3 - min (spec.length 3)
          (spec.length 0 - (spec.length 8 + sPos spec + spec.length 3)),
          by omega⟩, rfl⟩
      obtain ⟨j4, hj4⟩ : ∃ j : spec.PathPosition 0,
          j.val = spec.length 8 + sPos spec + spec.length 3 +
            min (spec.length 3)
              (spec.length 0 - (spec.length 8 + sPos spec + spec.length 3)) :=
        ⟨⟨spec.length 8 + sPos spec + spec.length 3 + min (spec.length 3)
          (spec.length 0 - (spec.length 8 + sPos spec + spec.length 3)),
          by omega⟩, rfl⟩
      obtain ⟨sC, hC⟩ : ∃ s,
          cfg spec (spec.pathVertex 0 j3) (spec.pathVertex 3 k0)
              (spec.pathVertex 3 k1) + prin spec.graph s =
            cfg spec (spec.pathVertex 0 j4) (spec.pathVertex 3 k0)
              (spec.pathVertex 3 k2) :=
        ⟨_, march_cutB hn (spec.length 8 + sPos spec + spec.length 3)
          (spec.length 3 - min (spec.length 3)
            (spec.length 0 - (spec.length 8 + sPos spec + spec.length 3)))
          (min (spec.length 3)
            (spec.length 0 - (spec.length 8 + sPos spec + spec.length 3)))
          (by omega) (by omega) (by omega) j3 j4 k1 k2 hj3 (by omega)
          (by omega) hk2 (spec.pathVertex 3 k0)⟩
      have hsc4 : pencil2 spec + prin spec.graph (sA + sR + sB + sC) =
          cfg spec (spec.pathVertex 0 j4) (spec.pathVertex 3 k0)
            (spec.pathVertex 3 k2) := by
        rw [map_add, ← add_assoc, hsc3, hv3', cfg_swap]
        exact hC
      by_cases hfin : min (spec.length 3)
          (spec.length 0 - (spec.length 8 + sPos spec + spec.length 3)) =
            spec.length 0 - (spec.length 8 + sPos spec + spec.length 3)
      · -- The march runs out of room on `e0` first: its chip lands on `v4`.
        exact reaches_of_cfg _ (sA + sR + sB + sC) _ _ _ _ hsc4
          (Or.inl (by rw [pathVertex_eq_head 0 j4 (by omega), hn.h0]))
      · -- Otherwise the march empties `e3`: two chips at `v1`, then the star.
        have hk2z : k2.val = 0 := by omega
        have hcv : spec.pathVertex 3 k0 = spec.coreVertex 1 := by
          rw [pathVertex_eq_tail 3 k0 hk0, hn.t3]
        have hcv2 : spec.pathVertex 3 k2 = spec.coreVertex 1 := by
          rw [pathVertex_eq_tail 3 k2 hk2z, hn.t3]
        refine reaches_v4_of_star hn _ (sA + sR + sB + sC) j4 ?_
        rw [hsc4, hcv, hcv2]
  · -- `v5`: the pencil's own chip at the head of `e8`.
    exact reaches_of_cfg _ 0 _ _ _ _ (by rw [map_zero, add_zero]; exact hpen)
      (Or.inr (Or.inr (by rw [pathVertex_eq_head 8 m0 hm0, hn.h8])))

end Regime2

/-! ## The two regime lemmas

Both are stated in the rotated chart `a₀ = max`: hypotheses
`length 3 ≤ length 0` and `length 8 ≤ length 0`. -/

section Regimes

variable (core_nonempty : 0 < 6)
  (core_loopless : ∀ edge : Fin 9,
    row096Core.tail edge ≠ row096Core.head edge)
  (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge)

/-- Regime 1: the three single lengths satisfy the triangle inequality.
`D = v0 + v5 + (point on e3 at distance a₀ − a₂ from v1)`, and the pencil is
the `τ = a₀` level family described in the module docstring.

The proof uses `RampData` marches for the `T(j,k,m)` equivalences and `capScript`
reflections at the three banana stations, exactly as in
the public ramp-script infrastructure. -/
theorem bnExists_regime1
    (hmax₁ : length 3 ≤ length 0) (hmax₂ : length 8 ≤ length 0)
    (htri : length 0 ≤ length 3 + length 8) :
    BNExists (Spec.ofCore row096Core core_nonempty core_loopless
      length hLength).graph 1 3 := by
  have hcoreConn : row096Core.Connected := by
    unfold Utilities.Certificate.ExplicitPotential.Core.Connected
    decide
  refine Certificate.CoreVertexReachability.bnExists_of_reaches_coreVertices _
    (SubdivisionGraph.Spec.graph_connected_of_coreConnected _ hcoreConn)
    (pencil1 _ htri) 3 (deg_pencil1 _ htri) ?_
  intro vertex
  exact regime1_reaches_core _
    (isNecklace_row096Core core_nonempty core_loopless length hLength)
    htri hmax₁ hmax₂ vertex

/-- Regime 2: `x = a₀ − a₁ − a₂ > 0`, and (after the `e6/e7` arc swap) the
arc `e6` of `β₂` is at least as long as `e7`.
`D = v0 + v5 + (point on e6 at distance min(x, length e7) from v3)`.

Verified empirically on 153/153 regime-2 random vectors
(auxiliary calculations); proved by `regime2_reaches_core`,
whose chain of cut marches is described in the section docstring above.  Only
the six core vertices are needed, by the strong-separator route. -/
theorem bnExists_regime2
    (hx : length 3 + length 8 < length 0)
    (harc : length 7 ≤ length 6) :
    BNExists (Spec.ofCore row096Core core_nonempty core_loopless
      length hLength).graph 1 3 := by
  have hcoreConn : row096Core.Connected := by
    unfold Utilities.Certificate.ExplicitPotential.Core.Connected
    decide
  refine Certificate.CoreVertexReachability.bnExists_of_reaches_coreVertices _
    (SubdivisionGraph.Spec.graph_connected_of_coreConnected _ hcoreConn)
    (pencil2 _) 3 (deg_pencil2 _) ?_
  intro vertex
  exact regime2_reaches_core
    (isNecklace_row096Core core_nonempty core_loopless length hLength)
    hx harc vertex

end Regimes

/-! ## Assembly: rotation and arc-swap case split -/

/-- Compatibility form of the public core-symmetry transport used by the
case split below. -/
private theorem bnExists_of_coreAuto {n p : ℕ}
    (core : ExplicitPotential.Core n p) (core_nonempty : 0 < n)
    (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (τ : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin p)) (rev : Fin p → Bool)
    (hTail : ∀ edge : Fin p, core.tail (σ edge) =
      if rev edge then τ (core.head edge) else τ (core.tail edge))
    (hHead : ∀ edge : Fin p, core.head (σ edge) =
      if rev edge then τ (core.tail edge) else τ (core.head edge))
    (length : Fin p → ℕ) (hLength : ∀ edge, 0 < length edge)
    (hLength' : ∀ edge, 0 < length (σ edge))
    (hBN : BNExists (Spec.ofCore core core_nonempty core_loopless
      (fun edge => length (σ edge)) hLength').graph 1 3) :
    BNExists (Spec.ofCore core core_nonempty core_loopless
      length hLength).graph 1 3 := by
  let symmetry : Utilities.Certificate.CoreOrbitReduction.CoreSymmetry core :=
    { vertexPerm := τ
      slotPerm := σ
      reversed := rev
      tail_eq := hTail
      head_eq := hHead }
  exact symmetry.bnExists_of_bnExists core_nonempty core_loopless
    (fun edge => length (σ edge)) length hLength' hLength (fun _ => rfl)
    1 3 hBN

/-- In the chart where slot `0` is a longest single, close the row by the
regime split, swapping the two `β₂` arcs first if `e6` is the shorter. -/
theorem bnExists_maxChart (core_nonempty : 0 < 6)
    (core_loopless : ∀ edge : Fin 9,
      row096Core.tail edge ≠ row096Core.head edge)
    (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge)
    (hmax₁ : length 3 ≤ length 0) (hmax₂ : length 8 ≤ length 0) :
    BNExists (Spec.ofCore row096Core core_nonempty core_loopless
      length hLength).graph 1 3 := by
  by_cases htri : length 0 ≤ length 3 + length 8
  · exact bnExists_regime1 core_nonempty core_loopless length hLength
      hmax₁ hmax₂ htri
  · have hx : length 3 + length 8 < length 0 := by omega
    by_cases harc : length 7 ≤ length 6
    · exact bnExists_regime2 core_nonempty core_loopless length hLength
        hx harc
    · have hs6 : swapSlot 6 = 7 := by decide
      have hs7 : swapSlot 7 = 6 := by decide
      have hs0 : swapSlot 0 = 0 := by decide
      have hs3 : swapSlot 3 = 3 := by decide
      have hs8 : swapSlot 8 = 8 := by decide
      refine bnExists_of_coreAuto row096Core
        core_nonempty core_loopless swapVertex swapSlot rotReversed
        swap_tail swap_head
        length hLength (fun edge => hLength _) ?_
      refine bnExists_regime2 core_nonempty core_loopless _ _ ?_ ?_
      · show length (swapSlot 3) + length (swapSlot 8) < length (swapSlot 0)
        rw [hs3, hs8, hs0]
        exact hx
      · show length (swapSlot 7) ≤ length (swapSlot 6)
        rw [hs6, hs7]
        omega

/-- Every positive integral subdivision of the necklace core carries a
degree-three rank-one divisor.

The proof rotates the maximal single slot into position `e0` with the
core-symmetry transport applied
to `rotVertex/rotSlot/rotReversed`, then
split on the triangle inequality, applying the arc swap `swapSlot` in
regime 2 if `length e6 < length e7`. -/
theorem bnExists_all (core_nonempty : 0 < 6)
    (core_loopless : ∀ edge : Fin 9,
      row096Core.tail edge ≠ row096Core.head edge)
    (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge) :
    BNExists (Spec.ofCore row096Core core_nonempty core_loopless
      length hLength).graph 1 3 := by
  have hr0 : rotSlot 0 = 3 := by decide
  have hr3 : rotSlot 3 = 8 := by decide
  have hr8 : rotSlot 8 = 0 := by decide
  have hrr0 : rotSlot (rotSlot 0) = 8 := by decide
  have hrr3 : rotSlot (rotSlot 3) = 0 := by decide
  have hrr8 : rotSlot (rotSlot 8) = 3 := by decide
  by_cases h0 : length 3 ≤ length 0 ∧ length 8 ≤ length 0
  · exact bnExists_maxChart core_nonempty core_loopless length hLength
      h0.1 h0.2
  · by_cases h3 : length 0 ≤ length 3 ∧ length 8 ≤ length 3
    · refine bnExists_of_coreAuto row096Core
        core_nonempty core_loopless rotVertex rotSlot rotReversed rot_tail
        rot_head length hLength (fun edge => hLength _) ?_
      refine bnExists_maxChart core_nonempty core_loopless _ _ ?_ ?_
      · show length (rotSlot 3) ≤ length (rotSlot 0)
        rw [hr3, hr0]
        exact h3.2
      · show length (rotSlot 8) ≤ length (rotSlot 0)
        rw [hr8, hr0]
        exact h3.1
    · have h8 : length 0 ≤ length 8 ∧ length 3 ≤ length 8 := by
        simp only [not_and_or, not_le] at h0 h3
        omega
      refine bnExists_of_coreAuto row096Core
        core_nonempty core_loopless rotVertex rotSlot rotReversed rot_tail
        rot_head length hLength (fun edge => hLength _) ?_
      refine bnExists_of_coreAuto row096Core
        core_nonempty core_loopless rotVertex rotSlot rotReversed rot_tail
        rot_head _ (fun edge => hLength _) (fun edge => hLength _) ?_
      refine bnExists_maxChart core_nonempty core_loopless _ _ ?_ ?_
      · show length (rotSlot (rotSlot 3)) ≤ length (rotSlot (rotSlot 0))
        rw [hrr3, hrr0]
        exact h8.1
      · show length (rotSlot (rotSlot 8)) ≤ length (rotSlot (rotSlot 0))
        rw [hrr8, hrr0]
        exact h8.2

end LowGenus.GenusFourRow096Pencil
