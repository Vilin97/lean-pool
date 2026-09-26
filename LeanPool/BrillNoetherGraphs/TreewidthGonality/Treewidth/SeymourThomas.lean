/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.SeymourThomasInduction

/-!
# Seymour--Thomas duality

The Seymour--Thomas theorem ("brambles and tree width", J. Combin. Theory Ser. B
58 (1993)) says that the maximum order of a bramble of `H` equals
`treewidth H + 1`.  `TreewidthGonality/Gonality/TreewidthGonality.lean` consumes the
existence of a bramble whose order is exactly `treewidth H + 1`.

This module assembles that statement from
`TreewidthGonality/Treewidth/SeymourThomasInduction.lean`, which proves the hard half
(some bramble has order **at least** `treewidth H + 1`) following
Bellenbaum--Diestel, *Two short proofs concerning tree-decompositions*, §4.

## Why the easy half is not proved

Getting order *exactly* `treewidth H + 1` classically needs the other
inequality: every bramble is covered by some bag, so no bramble has order above
`treewidth H + 1`.  Its proof orients every edge of the decomposition tree
towards the side that covers the bramble and takes the end of a maximal directed
path — a second consumer of Bellenbaum--Diestel's Lemma 1.

It is avoidable.  The order of a bramble is monotone in its member family
(`Bramble.order_restrict_le`) and increases by at most one when a single member
is adjoined (`Bramble.order_le_succ_erase`: a hitting set of the smaller family
plus one vertex of the new member hits the larger one).  Peeling members off one
at a time therefore realizes **every** value between `0` and the order, so a
bramble of order `≥ treewidth H + 1` contains a sub-bramble of order exactly
`treewidth H + 1`.  That is `exists_subfamily_order_eq` below, and it is
strictly cheaper than the easy half of duality.
-/

@[expose] public section

namespace Utilities.Treewidth

open Finset

universe u

variable {V : Type u} [DecidableEq V] {H : SimpleGraph V}

namespace Bramble

/-- Restricting to the full member family changes nothing. -/
theorem order_restrict_self (𝔅 : Bramble H) :
    (𝔅.restrict 𝔅.members le_rfl).order = 𝔅.order := rfl

/-- The empty sub-bramble has order `0`: the empty set hits it vacuously. -/
theorem order_restrict_empty (𝔅 : Bramble H) (h : (∅ : Finset (Finset V)) ⊆ 𝔅.members) :
    (𝔅.restrict ∅ h).order = 0 := by
  have hhit : (𝔅.restrict ∅ h).IsHittingSet (∅ : Finset V) := by
    intro B hB
    rw [Bramble.restrict_members] at hB
    exact absurd hB (Finset.notMem_empty B)
  simpa using (𝔅.restrict ∅ h).order_le_card_of_isHittingSet hhit

/-- **Removing one member drops the order by at most one.**  A hitting set of
the smaller family together with one vertex of the removed member hits the
larger family. -/
theorem order_le_succ_erase [Fintype V] (𝔅 : Bramble H) {M : Finset (Finset V)}
    (hM : M ⊆ 𝔅.members) {B : Finset V} (hB : B ∈ M) :
    (𝔅.restrict M hM).order ≤
      (𝔅.restrict (M.erase B) ((Finset.erase_subset _ _).trans hM)).order + 1 := by
  classical
  obtain ⟨S, hS, hcard⟩ :=
    (𝔅.restrict (M.erase B) ((Finset.erase_subset _ _).trans hM)).exists_isHittingSet_card_eq_order
  obtain ⟨b, hb⟩ := 𝔅.nonempty_of_mem (hM hB)
  have hhit : (𝔅.restrict M hM).IsHittingSet (insert b S) := by
    intro A hA
    rw [Bramble.restrict_members] at hA
    by_cases hAB : A = B
    · subst hAB
      exact ⟨b, Finset.mem_inter.mpr ⟨hb, Finset.mem_insert_self b S⟩⟩
    · obtain ⟨x, hx⟩ := hS A (by
        rw [Bramble.restrict_members]
        exact Finset.mem_erase.mpr ⟨hAB, hA⟩)
      exact ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        Finset.mem_insert_of_mem (Finset.mem_inter.mp hx).2⟩⟩
  refine le_trans ((𝔅.restrict M hM).order_le_card_of_isHittingSet hhit) ?_
  rw [← hcard]
  exact Finset.card_insert_le b S

/-- **Discrete intermediate value for the order of sub-brambles.**  Every value
below the order of a family is attained by some subfamily.

Discharge plan: strong induction on `M`.  If `m = (restrict M).order` take
`M' := M`.  Otherwise `m < (restrict M).order`, so `M` is nonempty
(`order_restrict_empty`); pick `B ∈ M` and apply the induction hypothesis to
`M.erase B`, whose order is at least `m` by `order_le_succ_erase`. -/
theorem exists_subfamily_order_eq [Fintype V] (𝔅 : Bramble H) :
    ∀ (M : Finset (Finset V)) (hM : M ⊆ 𝔅.members) (m : ℕ),
      m ≤ (𝔅.restrict M hM).order →
      ∃ (M' : Finset (Finset V)) (hM' : M' ⊆ M),
        (𝔅.restrict M' (hM'.trans hM)).order = m := by
  classical
  intro M
  induction M using Finset.strongInduction with
  | _ M ihM =>
      intro hM m hm
      by_cases heq : m = (𝔅.restrict M hM).order
      · exact ⟨M, Finset.Subset.refl M, heq.symm⟩
      · have hlt : m < (𝔅.restrict M hM).order := lt_of_le_of_ne hm heq
        have hne : M.Nonempty := by
          rcases Finset.eq_empty_or_nonempty M with rfl | h
          · rw [Bramble.order_restrict_empty 𝔅 hM] at hlt
            omega
          · exact h
        obtain ⟨B, hB⟩ := hne
        have hle : m ≤
            (𝔅.restrict (M.erase B) ((Finset.erase_subset _ _).trans hM)).order := by
          have h2 := Bramble.order_le_succ_erase 𝔅 hM hB
          omega
        obtain ⟨M', hM'sub, hM'ord⟩ :=
          ihM (M.erase B) (Finset.erase_ssubset hB)
            ((Finset.erase_subset _ _).trans hM) m hle
        exact ⟨M', hM'sub.trans (Finset.erase_subset _ _), hM'ord⟩

end Bramble

omit [DecidableEq V] in
/-- **Seymour--Thomas duality, hard direction.**  Every graph carries a bramble
whose order is exactly `treewidth H + 1`.

`Nonempty V` is required: on the empty graph both `treewidth` and the order of
the empty bramble are `0`, and there is no bramble of order `1`.

Proved 2026-08-25 from `exists_bramble_treewidth_succ_le` (Bellenbaum--Diestel's
Theorem 5, forward direction, with Menger's theorem replaced by an explicit
separator) and `Bramble.exists_subfamily_order_eq` (which supplies exactness
without the easy half of duality). -/
theorem exists_bramble_of_treewidth [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) :
    ∃ 𝔅 : Bramble H, 𝔅.order = treewidth H + 1 := by
  obtain ⟨𝔅, h𝔅⟩ := exists_bramble_treewidth_succ_le H
  obtain ⟨M, hM, hord⟩ :=
    𝔅.exists_subfamily_order_eq 𝔅.members le_rfl (treewidth H + 1)
      (by simpa [Bramble.order_restrict_self] using h𝔅)
  exact ⟨𝔅.restrict M (hM.trans le_rfl), hord⟩

end Utilities.Treewidth
