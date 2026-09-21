/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreExpansion
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocorePresentation

/-!
# A genus-generic trivalent expansion

Every connected ordered loopless core all of whose vertices carry at least
three slot ends is the image of a *cubic* ordered loopless core under an
equal-genus topological contraction.

The construction is the **centipede**: a core vertex `w` of valence `d` is
replaced by a path of `d - 2` trivalent vertices, each carrying one or two
free legs, and the `d` slot ends at `w` are distributed along those legs.
The fibre over `w` is a tree (a path), so contracting all fibres preserves
`b₁`.

Counting is uniform: writing `g = p - n + 1` for the genus of the core,
the expanded core has `2 (g - 1)` vertices and `3 (g - 1)` slots, which is
exactly what trivalence forces (`2E = 3V` and `E - V + 1 = g`).

The output is packaged as `Utilities.Subdivision.CoreExpansion.ExpansionData`, so
`Utilities.Subdivision.CoreExpansion.ExpansionData.certificate_topologicalValid` turns it into an
actual topological contraction certificate from a positive subdivision of the
expanded cubic core onto any positive subdivision of the given core.
-/
namespace Utilities.Subdivision.TrivalentExpansion
open Utilities.Certificate

open Utilities

open Finset
open ExplicitPotential
open SubdivisionGraph
open Utilities.Subdivision.CoreExpansion
open Utilities.Certificate.PseudocorePresentation
open Utilities.Certificate.PseudocorePresentation

/-! ## An adjacent-flip lemma -/

/-- Walking down from a point where `P` holds to a point where it fails
crosses an adjacent flip. -/
theorem exists_flip_down (P : ℕ → Prop) {a : ℕ} (ha : P a) :
    ∀ b : ℕ, a ≤ b → ¬ P b → ∃ k, k + 1 ≤ b ∧ P k ∧ ¬ P (k + 1) := by
  classical
  intro b
  induction b with
  | zero =>
      intro hle hnp
      have hzero : a = 0 := Nat.le_zero.mp hle
      rw [hzero] at ha
      exact absurd ha hnp
  | succ b ih =>
      intro hle hnp
      by_cases hb : P b
      · exact ⟨b, le_rfl, hb, hnp⟩
      · rcases Nat.lt_or_ge b a with hlt | hge
        · have heq : a = b + 1 := by omega
          rw [heq] at ha
          exact absurd ha hnp
        · obtain ⟨k, hk1, hk2, hk3⟩ := ih hge hb
          exact ⟨k, by omega, hk2, hk3⟩

/-- Two points of `Fin m` on opposite sides of a predicate are separated by an
adjacent flip inside `Fin m`. -/
theorem exists_adjacent_flip {m : ℕ} (P : ℕ → Prop) {a b : ℕ}
    (ham : a < m) (hbm : b < m) (ha : P a) (hb : ¬ P b) :
    ∃ k, k + 1 < m ∧ ((P k ∧ ¬ P (k + 1)) ∨ (¬ P k ∧ P (k + 1))) := by
  classical
  rcases le_total a b with hab | hba
  · obtain ⟨k, hk1, hk2, hk3⟩ := exists_flip_down P ha b hab hb
    exact ⟨k, by omega, Or.inl ⟨hk2, hk3⟩⟩
  · obtain ⟨k, hk1, hk2, hk3⟩ :=
      exists_flip_down (fun t => ¬ P t) hb a hba (not_not_intro ha)
    exact ⟨k, by omega, Or.inr ⟨hk2, not_not.mp hk3⟩⟩

/-! ## The centipede leg map -/

/-- Position along the centipede of the `k`-th slot end at a vertex of
valence `D`.  Ends `0` and `1` sit on the first centipede vertex, ends
`D - 2` and `D - 1` on the last, and each remaining end has a centipede
vertex to itself. -/
def legIndex (D k : ℕ) : ℕ := if k = 0 then 0 else min (k - 1) (D - 3)

theorem legIndex_lt {D : ℕ} (hD : 3 ≤ D) (k : ℕ) : legIndex D k < D - 2 := by
  unfold legIndex
  split_ifs <;> omega

/-! ## The expanded core, before it is indexed by `Fin` -/

section Construction

variable {n p : ℕ} (C : Core n p)

/-- Vertices of the expansion: for each core vertex `w`, a centipede of
`slotValence C w - 2` vertices. -/
abbrev BigV : Type := Σ w : Fin n, Fin (slotValence C w - 2)

/-- Slots of the expansion: the `slotValence C w - 3` centipede edges at each
core vertex, plus one carrier for each core slot. -/
abbrev BigE : Type := (Σ w : Fin n, Fin (slotValence C w - 3)) ⊕ Fin p

/-- An arbitrary enumeration of the slot ends at a core vertex. -/
noncomputable def endEquiv (w : Fin n) :
    (slotEnds C w) ≃ Fin (slotValence C w) :=
  (slotEnds C w).equivFin

variable (hDeg : ∀ w : Fin n, 3 ≤ slotValence C w)

/-- The centipede vertex carrying a given slot end. -/
noncomputable def legOf (w : Fin n) (x : slotEnds C w) :
    Fin (slotValence C w - 2) :=
  ⟨legIndex (slotValence C w) (endEquiv C w x), legIndex_lt (hDeg w) _⟩

/-- The tail end of a core slot, as an element of the slot-end set. -/
def tailEnd (j : Fin p) : slotEnds C (C.tail j) :=
  ⟨(j, false), by simp [mem_slotEnds]⟩

/-- The head end of a core slot, as an element of the slot-end set. -/
def headEnd (j : Fin p) : slotEnds C (C.head j) :=
  ⟨(j, true), by simp [mem_slotEnds]⟩

/-- Tail endpoint of an expansion slot. -/
noncomputable def bigTail : BigE C → BigV C
  | Sum.inl x => ⟨x.1, ⟨x.2.val, by have := x.2.isLt; omega⟩⟩
  | Sum.inr j => ⟨C.tail j, legOf C hDeg (C.tail j) (tailEnd C j)⟩

/-- Head endpoint of an expansion slot. -/
noncomputable def bigHead : BigE C → BigV C
  | Sum.inl x => ⟨x.1, ⟨x.2.val + 1, by have := x.2.isLt; omega⟩⟩
  | Sum.inr j => ⟨C.head j, legOf C hDeg (C.head j) (headEnd C j)⟩

/-! ## Counting -/

include hDeg in
theorem sum_valence_sub_two :
    (∑ w : Fin n, (slotValence C w - 2)) + 2 * n = 2 * p := by
  have hsum : ∑ w : Fin n, ((slotValence C w - 2) + 2)
      = ∑ w : Fin n, slotValence C w := by
    refine Finset.sum_congr rfl ?_
    intro w _
    have := hDeg w
    omega
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  have hhand := sum_slotValence C
  omega

include hDeg in
theorem sum_valence_sub_three :
    (∑ w : Fin n, (slotValence C w - 3)) + 3 * n = 2 * p := by
  have hsum : ∑ w : Fin n, ((slotValence C w - 3) + 3)
      = ∑ w : Fin n, slotValence C w := by
    refine Finset.sum_congr rfl ?_
    intro w _
    have := hDeg w
    omega
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  have hhand := sum_slotValence C
  omega

include hDeg in
theorem card_bigV : Fintype.card (BigV C) = 2 * (p - n) := by
  have h := sum_valence_sub_two C hDeg
  have h3 := sum_valence_sub_three C hDeg
  have hcard : Fintype.card (BigV C) = ∑ w : Fin n, (slotValence C w - 2) := by
    simp [Fintype.card_sigma]
  omega

include hDeg in
theorem card_bigE : Fintype.card (BigE C) = 3 * (p - n) := by
  have h := sum_valence_sub_two C hDeg
  have h3 := sum_valence_sub_three C hDeg
  have hcard : Fintype.card (BigE C)
      = (∑ w : Fin n, (slotValence C w - 3)) + p := by
    simp [Fintype.card_sum, Fintype.card_sigma]
  omega

/-! ## Indexing the expansion by `Fin` -/

/-- An indexing of the expansion vertices. -/
noncomputable def vEquiv : BigV C ≃ Fin (2 * (p - n)) :=
  Fintype.equivFinOfCardEq (card_bigV C hDeg)

/-- An indexing of the expansion slots. -/
noncomputable def eEquiv : BigE C ≃ Fin (3 * (p - n)) :=
  Fintype.equivFinOfCardEq (card_bigE C hDeg)

/-- The centipede expansion datum. -/
noncomputable def data : ExpansionData n p (2 * (p - n)) (3 * (p - n)) where
  bigCore :=
    { tail := fun e => vEquiv C hDeg (bigTail C hDeg ((eEquiv C hDeg).symm e))
      head := fun e => vEquiv C hDeg (bigHead C hDeg ((eEquiv C hDeg).symm e)) }
  fib := fun v => ((vEquiv C hDeg).symm v).1
  kind := fun e =>
    match (eEquiv C hDeg).symm e with
    | Sum.inl _ => SlotKind.contracted
    | Sum.inr j => SlotKind.single j
  owner := fun j => eEquiv C hDeg (Sum.inr j)
  side := fun _ => false

@[simp] theorem data_tail (a : BigE C) :
    (data C hDeg).bigCore.tail (eEquiv C hDeg a)
      = vEquiv C hDeg (bigTail C hDeg a) := by
  simp [data]

@[simp] theorem data_head (a : BigE C) :
    (data C hDeg).bigCore.head (eEquiv C hDeg a)
      = vEquiv C hDeg (bigHead C hDeg a) := by
  simp [data]

@[simp] theorem data_fib (x : BigV C) :
    (data C hDeg).fib (vEquiv C hDeg x) = x.1 := by
  simp [data]

@[simp] theorem data_kind_inl (x : Σ w : Fin n, Fin (slotValence C w - 3)) :
    (data C hDeg).kind (eEquiv C hDeg (Sum.inl x)) = SlotKind.contracted := by
  simp [data]

@[simp] theorem data_kind_inr (j : Fin p) :
    (data C hDeg).kind (eEquiv C hDeg (Sum.inr j)) = SlotKind.single j := by
  simp [data]

@[simp] theorem data_owner (j : Fin p) :
    (data C hDeg).owner j = eEquiv C hDeg (Sum.inr j) := rfl

@[simp] theorem data_side (j : Fin p) : (data C hDeg).side j = false := rfl

/-- Every expansion slot index comes from an abstract expansion slot. -/
theorem exists_slot (e : Fin (3 * (p - n))) : ∃ a : BigE C, eEquiv C hDeg a = e :=
  ⟨(eEquiv C hDeg).symm e, Equiv.apply_symm_apply _ _⟩

/-- Every expansion vertex index comes from an abstract expansion vertex. -/
theorem exists_vertex (v : Fin (2 * (p - n))) :
    ∃ x : BigV C, vEquiv C hDeg x = v :=
  ⟨(vEquiv C hDeg).symm v, Equiv.apply_symm_apply _ _⟩

theorem bigV_ne_of_fst {u v : BigV C} (h : u.1 ≠ v.1) : u ≠ v :=
  fun he => h (congrArg Sigma.fst he)

theorem bigV_ne_of_snd {u v : BigV C} (h : (u.2 : ℕ) ≠ (v.2 : ℕ)) : u ≠ v :=
  fun he => h (congrArg (fun z : BigV C => (z.2 : ℕ)) he)

/-! ## The expansion conditions -/

include hDeg in
theorem bigCore_loopless (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j)
    (e : Fin (3 * (p - n))) :
    (data C hDeg).bigCore.tail e ≠ (data C hDeg).bigCore.head e := by
  obtain ⟨a, rfl⟩ := exists_slot C hDeg e
  rw [data_tail, data_head]
  refine fun hEq => ?_
  have hAbs : bigTail C hDeg a = bigHead C hDeg a := (vEquiv C hDeg).injective hEq
  cases a with
  | inl x =>
      exact absurd (congrArg (fun z : BigV C => (z.2 : ℕ)) hAbs) (by simp [bigTail, bigHead])
  | inr j =>
      exact hLoop j (congrArg Sigma.fst hAbs)

include hDeg in
theorem slotCompatible (e : Fin (3 * (p - n))) :
    (data C hDeg).SlotCompatible C e := by
  obtain ⟨a, rfl⟩ := exists_slot C hDeg e
  cases a with
  | inl x =>
      refine ⟨fun _ => ?_, fun j hj => ?_, fun j₁ j₂ hj => ?_⟩
      · rw [data_tail, data_head, data_fib, data_fib]
        rfl
      · simp at hj
      · simp at hj
  | inr j =>
      refine ⟨fun h => ?_, fun j' hj => ?_, fun j₁ j₂ hj => ?_⟩
      · simp at h
      · rw [data_kind_inr] at hj
        cases hj
        rw [data_tail, data_head, data_fib, data_fib]
        exact ⟨rfl, rfl⟩
      · simp at hj

include hDeg in
theorem slotIndexed (e : Fin (3 * (p - n))) : (data C hDeg).SlotIndexed e := by
  obtain ⟨a, rfl⟩ := exists_slot C hDeg e
  cases a with
  | inl x => exact ⟨fun j hj => by simp at hj, fun j₁ j₂ hj => by simp at hj⟩
  | inr j =>
      refine ⟨fun j' hj => ?_, fun j₁ j₂ hj => by simp at hj⟩
      rw [data_kind_inr] at hj
      cases hj
      exact ⟨rfl, rfl⟩

include hDeg in
theorem slotClaimed (j : Fin p) : (data C hDeg).SlotClaimed j := by
  refine ⟨?_, fun j' hj => ?_, fun j₁ j₂ hj => ?_⟩
  · rw [data_owner, data_kind_inr]
    simp
  · rw [data_owner, data_kind_inr] at hj
    cases hj
    exact ⟨rfl, rfl⟩
  · rw [data_owner, data_kind_inr] at hj
    exact absurd hj (by simp)

include hDeg in
theorem markerIsolated (e : Fin (3 * (p - n))) :
    (data C hDeg).MarkerIsolated C e := by
  obtain ⟨a, rfl⟩ := exists_slot C hDeg e
  cases a with
  | inl x => exact fun j₁ j₂ hj => by simp at hj
  | inr j => exact fun j₁ j₂ hj => by simp at hj

include hDeg in
theorem exists_incident (w : Fin n) : ∃ j : Fin p, C.tail j = w ∨ C.head j = w := by
  have hpos : 0 < (slotEnds C w).card := by
    have := hDeg w
    unfold slotValence at this
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  refine ⟨x.1, ?_⟩
  have := (mem_slotEnds C w x).mp hx
  cases hside : x.2 with
  | false => rw [hside] at this; simp at this; exact Or.inl this
  | true => rw [hside] at this; simp at this; exact Or.inr this

/-! ## Fibre connectivity -/

include hDeg in
/-- Two centipede vertices over the same core vertex on opposite sides of a
subset are separated by a contracted slot of that centipede. -/
theorem fibre_crossing (T : Finset (Fin (2 * (p - n)))) (w : Fin n)
    (ia ib : Fin (slotValence C w - 2))
    (ha : vEquiv C hDeg ⟨w, ia⟩ ∈ T) (hb : vEquiv C hDeg ⟨w, ib⟩ ∉ T) :
    ∃ e : Fin (3 * (p - n)), (data C hDeg).kind e = SlotKind.contracted ∧
      (data C hDeg).fib ((data C hDeg).bigCore.tail e) = w ∧
      (((data C hDeg).bigCore.tail e ∈ T ∧ (data C hDeg).bigCore.head e ∉ T) ∨
        ((data C hDeg).bigCore.head e ∈ T ∧ (data C hDeg).bigCore.tail e ∉ T)) := by
  classical
  obtain ⟨k, hk, hflip⟩ :=
    exists_adjacent_flip
      (fun t => ∃ h : t < slotValence C w - 2, vEquiv C hDeg ⟨w, ⟨t, h⟩⟩ ∈ T)
      ia.isLt ib.isLt ⟨ia.isLt, ha⟩ (by rintro ⟨h, hmem⟩; exact hb hmem)
  have hk3 : k < slotValence C w - 3 := by omega
  have hkm : k < slotValence C w - 2 := by omega
  have hk1m : k + 1 < slotValence C w - 2 := hk
  refine ⟨eEquiv C hDeg (Sum.inl ⟨w, ⟨k, hk3⟩⟩), by simp, ?_, ?_⟩
  · rw [data_tail, data_fib]; rfl
  · have htail : (data C hDeg).bigCore.tail (eEquiv C hDeg (Sum.inl ⟨w, ⟨k, hk3⟩⟩))
        = vEquiv C hDeg ⟨w, ⟨k, hkm⟩⟩ := by rw [data_tail]; rfl
    have hhead : (data C hDeg).bigCore.head (eEquiv C hDeg (Sum.inl ⟨w, ⟨k, hk3⟩⟩))
        = vEquiv C hDeg ⟨w, ⟨k + 1, hk1m⟩⟩ := by rw [data_head]; rfl
    rw [htail, hhead]
    rcases hflip with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨_, hmem⟩ := h1
      exact Or.inl ⟨hmem, fun hcon => h2 ⟨hk1m, hcon⟩⟩
    · obtain ⟨_, hmem⟩ := h2
      exact Or.inr ⟨hmem, fun hcon => h1 ⟨hkm, hcon⟩⟩

include hDeg in
/-- **The expansion conditions hold.** -/
theorem conditions (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j) :
    (data C hDeg).Conditions C := by
  classical
  refine ⟨bigCore_loopless C hDeg hLoop, slotCompatible C hDeg, slotIndexed C hDeg,
    slotClaimed C hDeg, markerIsolated C hDeg, exists_incident C hDeg, ?_⟩
  rintro w T ⟨a, haT, hfa⟩ ⟨b, hbT, hfb⟩
  obtain ⟨xa, rfl⟩ := exists_vertex C hDeg a
  obtain ⟨xb, rfl⟩ := exists_vertex C hDeg b
  obtain ⟨wa, ia⟩ := xa
  obtain ⟨wb, ib⟩ := xb
  rw [data_fib] at hfa hfb
  simp only at hfa hfb
  subst hfa
  subst hfb
  exact fibre_crossing C hDeg T _ ia ib haT hbT

/-! ## The expanded core is cubic -/

include hDeg in
theorem mem_slotEnds_tail (a : BigE C) (x : BigV C) (h : bigTail C hDeg a = x) :
    (eEquiv C hDeg a, false) ∈
      slotEnds (data C hDeg).bigCore (vEquiv C hDeg x) := by
  rw [mem_slotEnds]
  simpa using congrArg (vEquiv C hDeg) h

include hDeg in
theorem mem_slotEnds_head (a : BigE C) (x : BigV C) (h : bigHead C hDeg a = x) :
    (eEquiv C hDeg a, true) ∈
      slotEnds (data C hDeg).bigCore (vEquiv C hDeg x) := by
  rw [mem_slotEnds]
  simpa using congrArg (vEquiv C hDeg) h

/-- The expansion slot end attached to a core slot end. -/
noncomputable def bigEndOfEnd (w : Fin n) (x : slotEnds C w) :
    Fin (3 * (p - n)) × Bool :=
  (eEquiv C hDeg (Sum.inr (x : Fin p × Bool).1), (x : Fin p × Bool).2)

theorem bigEndOfEnd_injective (w : Fin n) :
    Function.Injective (bigEndOfEnd C hDeg w) := by
  intro x y h
  simp only [bigEndOfEnd, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hj := Sum.inr.inj ((eEquiv C hDeg).injective h1)
  exact Subtype.ext (Prod.ext hj h2)

include hDeg in
theorem bigEndOfEnd_mem (w : Fin n) (x : slotEnds C w)
    (i : Fin (slotValence C w - 2)) (hleg : legOf C hDeg w x = i) :
    bigEndOfEnd C hDeg w x ∈
      slotEnds (data C hDeg).bigCore (vEquiv C hDeg ⟨w, i⟩) := by
  obtain ⟨⟨j, s⟩, hx⟩ := x
  have hx' := (mem_slotEnds C w (j, s)).mp hx
  cases s with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hx'
      subst hx'
      refine mem_slotEnds_tail C hDeg (Sum.inr j) ⟨C.tail j, i⟩ ?_
      have hend : tailEnd C j = (⟨(j, false), hx⟩ : slotEnds C (C.tail j)) :=
        Subtype.ext rfl
      show (⟨C.tail j, legOf C hDeg (C.tail j) (tailEnd C j)⟩ : BigV C) = ⟨C.tail j, i⟩
      rw [hend, hleg]
  | true =>
      simp only [if_true] at hx'
      subst hx'
      refine mem_slotEnds_head C hDeg (Sum.inr j) ⟨C.head j, i⟩ ?_
      have hend : headEnd C j = (⟨(j, true), hx⟩ : slotEnds C (C.head j)) :=
        Subtype.ext rfl
      show (⟨C.head j, legOf C hDeg (C.head j) (headEnd C j)⟩ : BigV C) = ⟨C.head j, i⟩
      rw [hend, hleg]

include hDeg in
/-- The expansion slot end attached to the `k`-th slot end at `w` lies over the
centipede vertex its leg index names. -/
theorem legEnd_mem (w : Fin n) (i : Fin (slotValence C w - 2))
    (k : ℕ) (hkD : k < slotValence C w)
    (hk : legIndex (slotValence C w) k = i.val) :
    bigEndOfEnd C hDeg w ((endEquiv C w).symm ⟨k, hkD⟩) ∈
      slotEnds (data C hDeg).bigCore (vEquiv C hDeg ⟨w, i⟩) := by
  refine bigEndOfEnd_mem C hDeg w _ i ?_
  apply Fin.ext
  show legIndex (slotValence C w)
      ((endEquiv C w) ((endEquiv C w).symm ⟨k, hkD⟩)).val = i.val
  rw [Equiv.apply_symm_apply]
  exact hk

theorem legEnd_ne (w : Fin n) {k k' : ℕ} (hk : k < slotValence C w)
    (hk' : k' < slotValence C w) (hne : k ≠ k') :
    bigEndOfEnd C hDeg w ((endEquiv C w).symm ⟨k, hk⟩)
      ≠ bigEndOfEnd C hDeg w ((endEquiv C w).symm ⟨k', hk'⟩) := by
  intro h
  exact hne (congrArg Fin.val
    ((endEquiv C w).symm.injective (bigEndOfEnd_injective C hDeg w h)))

theorem legEnd_ne_contracted (w : Fin n) {k : ℕ} (hk : k < slotValence C w)
    (x : Σ w : Fin n, Fin (slotValence C w - 3)) (s : Bool) :
    bigEndOfEnd C hDeg w ((endEquiv C w).symm ⟨k, hk⟩)
      ≠ (eEquiv C hDeg (Sum.inl x), s) := by
  intro h
  simp only [bigEndOfEnd] at h
  have hs := (eEquiv C hDeg).injective (congrArg Prod.fst h)
  simp at hs

theorem bigV_eq {w : Fin n} {a b : Fin (slotValence C w - 2)} (h : a.val = b.val) :
    (⟨w, a⟩ : BigV C) = ⟨w, b⟩ := congrArg (Sigma.mk w) (Fin.val_injective h)

theorem three_le_card_of_three_mem {α : Type} [DecidableEq α] {s : Finset α}
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  calc (3 : ℕ) = ({a, b, c} : Finset α).card := hcard.symm
    _ ≤ s.card := Finset.card_le_card hsub

include hDeg in
theorem three_le_valence (v : Fin (2 * (p - n))) :
    3 ≤ slotValence (data C hDeg).bigCore v := by
  classical
  obtain ⟨x, rfl⟩ := exists_vertex C hDeg v
  obtain ⟨w, i⟩ := x
  have hD := hDeg w
  have hi := i.isLt
  rw [slotValence]
  by_cases hD3 : slotValence C w = 3
  · have h0 : (0 : ℕ) < slotValence C w := by omega
    have h1 : (1 : ℕ) < slotValence C w := by omega
    have h2 : (2 : ℕ) < slotValence C w := by omega
    exact three_le_card_of_three_mem
      (legEnd_ne C hDeg w h0 h1 (by omega))
      (legEnd_ne C hDeg w h0 h2 (by omega))
      (legEnd_ne C hDeg w h1 h2 (by omega))
      (legEnd_mem C hDeg w i 0 h0 (by unfold legIndex; split_ifs <;> first | exact ‹False›.elim | omega))
      (legEnd_mem C hDeg w i 1 h1 (by unfold legIndex; split_ifs <;> first | exact ‹False›.elim | omega))
      (legEnd_mem C hDeg w i 2 h2 (by unfold legIndex; split_ifs <;> first | exact ‹False›.elim | omega))
  · by_cases hi0 : i.val = 0
    · have h0 : (0 : ℕ) < slotValence C w := by omega
      have h1 : (1 : ℕ) < slotValence C w := by omega
      have hc : (0 : ℕ) < slotValence C w - 3 := by omega
      refine three_le_card_of_three_mem
        (legEnd_ne C hDeg w h0 h1 (by omega))
        (legEnd_ne_contracted C hDeg w h0 ⟨w, ⟨0, hc⟩⟩ false)
        (legEnd_ne_contracted C hDeg w h1 ⟨w, ⟨0, hc⟩⟩ false)
        (legEnd_mem C hDeg w i 0 h0 (by unfold legIndex; split_ifs <;> first | exact ‹False›.elim | omega))
        (legEnd_mem C hDeg w i 1 h1 (by unfold legIndex; split_ifs <;> first | exact ‹False›.elim | omega))
        ?_
      refine mem_slotEnds_tail C hDeg (Sum.inl ⟨w, ⟨0, hc⟩⟩) ⟨w, i⟩ (bigV_eq C ?_)
      show (0 : ℕ) = i.val
      omega
    · by_cases hilast : i.val = slotValence C w - 3
      · have h0 : slotValence C w - 2 < slotValence C w := by omega
        have h1 : slotValence C w - 1 < slotValence C w := by omega
        have hc : i.val - 1 < slotValence C w - 3 := by omega
        refine three_le_card_of_three_mem
          (legEnd_ne C hDeg w h0 h1 (by omega))
          (legEnd_ne_contracted C hDeg w h0 ⟨w, ⟨i.val - 1, hc⟩⟩ true)
          (legEnd_ne_contracted C hDeg w h1 ⟨w, ⟨i.val - 1, hc⟩⟩ true)
          (legEnd_mem C hDeg w i (slotValence C w - 2) h0
            (by unfold legIndex; split_ifs <;> first | exact ‹False›.elim | omega))
          (legEnd_mem C hDeg w i (slotValence C w - 1) h1
            (by unfold legIndex; split_ifs <;> first | exact ‹False›.elim | omega))
          ?_
        refine mem_slotEnds_head C hDeg (Sum.inl ⟨w, ⟨i.val - 1, hc⟩⟩) ⟨w, i⟩ (bigV_eq C ?_)
        show i.val - 1 + 1 = i.val
        omega
      · have h0 : i.val + 1 < slotValence C w := by omega
        have hcl : i.val - 1 < slotValence C w - 3 := by omega
        have hcr : i.val < slotValence C w - 3 := by omega
        refine three_le_card_of_three_mem
          (legEnd_ne_contracted C hDeg w h0 ⟨w, ⟨i.val - 1, hcl⟩⟩ true)
          (legEnd_ne_contracted C hDeg w h0 ⟨w, ⟨i.val, hcr⟩⟩ false)
          (by simp) ?_ ?_ ?_
        · refine legEnd_mem C hDeg w i (i.val + 1) h0 ?_
          unfold legIndex
          split_ifs <;> first | exact ‹False›.elim | omega
        · refine mem_slotEnds_head C hDeg (Sum.inl ⟨w, ⟨i.val - 1, hcl⟩⟩) ⟨w, i⟩
            (bigV_eq C ?_)
          show i.val - 1 + 1 = i.val
          omega
        · refine mem_slotEnds_tail C hDeg (Sum.inl ⟨w, ⟨i.val, hcr⟩⟩) ⟨w, i⟩
            (bigV_eq C ?_)
          show i.val = i.val
          rfl

include hDeg in
theorem bigCore_cubic : (data C hDeg).bigCore.Cubic := by
  classical
  intro v
  have hall := three_le_valence C hDeg
  have hsum := sum_slotValence (data C hDeg).bigCore
  have hconst : ∑ _u : Fin (2 * (p - n)), 3 = 3 * (2 * (p - n)) := by
    simp [Finset.sum_const, mul_comm]
  have hval : slotValence (data C hDeg).bigCore v = 3 := by
    by_contra hne
    have hlt : 3 < slotValence (data C hDeg).bigCore v := by
      have := hall v; omega
    have hstrict :
        (∑ _u : Fin (2 * (p - n)), 3) <
          ∑ u : Fin (2 * (p - n)), slotValence (data C hDeg).bigCore u :=
      Finset.sum_lt_sum (fun u _ => hall u) ⟨v, Finset.mem_univ v, hlt⟩
    rw [hconst, hsum] at hstrict
    omega
  have hEq := slotValence_eq_natSum (data C hDeg).bigCore v
  rw [hval] at hEq
  exact hEq.symm

/-! ## The expanded core is connected -/

include hDeg in
theorem bigCore_connected (hConn : C.Connected) : (data C hDeg).bigCore.Connected := by
  classical
  intro S hS
  obtain ⟨v0, w0, hv0, hw0⟩ := hS
  by_cases hUnif : ∀ (w : Fin n) (i i' : Fin (slotValence C w - 2)),
      vEquiv C hDeg ⟨w, i⟩ ∈ S → vEquiv C hDeg ⟨w, i'⟩ ∈ S
  · have hzero : ∀ w : Fin n, 0 < slotValence C w - 2 := by
      intro w; have := hDeg w; omega
    set S' : Finset (Fin n) :=
      Finset.univ.filter fun w => vEquiv C hDeg ⟨w, ⟨0, hzero w⟩⟩ ∈ S with hS'
    have hmem : ∀ (w : Fin n) (i : Fin (slotValence C w - 2)),
        vEquiv C hDeg ⟨w, i⟩ ∈ S ↔ w ∈ S' := by
      intro w i
      simp only [hS', Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => hUnif w i _ h, fun h => hUnif w _ i h⟩
    obtain ⟨x0, rfl⟩ := exists_vertex C hDeg v0
    obtain ⟨y0, rfl⟩ := exists_vertex C hDeg w0
    obtain ⟨wv, iv⟩ := x0
    obtain ⟨ww, iw⟩ := y0
    obtain ⟨j, hj⟩ := hConn S' ⟨wv, ww, (hmem wv iv).mp hv0,
      fun hcon => hw0 ((hmem ww iw).mpr hcon)⟩
    refine ⟨eEquiv C hDeg (Sum.inr j), ?_⟩
    have htail : (data C hDeg).bigCore.tail (eEquiv C hDeg (Sum.inr j))
        = vEquiv C hDeg ⟨C.tail j, legOf C hDeg (C.tail j) (tailEnd C j)⟩ := by
      rw [data_tail]; rfl
    have hhead : (data C hDeg).bigCore.head (eEquiv C hDeg (Sum.inr j))
        = vEquiv C hDeg ⟨C.head j, legOf C hDeg (C.head j) (headEnd C j)⟩ := by
      rw [data_head]; rfl
    rw [htail, hhead, hmem, hmem]
    exact hj
  · push Not at hUnif
    obtain ⟨w, i, i', h1, h2⟩ := hUnif
    obtain ⟨e, _, _, hcross⟩ := fibre_crossing C hDeg S w i i' h1 h2
    exact ⟨e, hcross⟩

end Construction

/-! ## The genus-generic trivalent expansion theorem -/

/-- **Trivalent expansion.**  Every connected ordered loopless core of minimum
slot valence three is the target of an equal-genus topological contraction
from a *cubic* connected ordered loopless core, whose size is forced by
trivalence: `2 (g - 1)` vertices and `3 (g - 1)` slots, where `g = p - n + 1`
is the genus. -/
theorem exists_expansion {n p : ℕ} (C : Core n p)
    (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j)
    (hDeg : ∀ w : Fin n, 3 ≤ slotValence C w)
    (hConn : C.Connected) :
    ∃ D : ExpansionData n p (2 * (p - n)) (3 * (p - n)),
      D.Conditions C ∧ D.bigCore.Cubic ∧ D.bigCore.Connected :=
  ⟨data C hDeg, conditions C hDeg hLoop, bigCore_cubic C hDeg,
    bigCore_connected C hDeg hConn⟩
end Utilities.Subdivision.TrivalentExpansion
