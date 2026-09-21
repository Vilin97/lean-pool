/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.CantorBendixsonConvexCover
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# The Cantor–Bendixson convex cover has a nondegenerate model

The partition hypotheses require a nested well-ordered neighborhood base at zero consisting of
open convex subgroups. The real line does not satisfy them: its only convex subgroups are zero
and the whole line, and zero is not open. Any witness is therefore non-Archimedean, and this file
supplies one: real sequences indexed by the naturals under the lexicographic order, with the
subgroups of sequences vanishing below a given index.

Those subgroups are nested, convex, open, and coinitial, so the hypotheses are consistent and the
geometric part of the cofactor construction is not vacuous. The check also separates the openness
requirement from the trivial family: the zero subgroup alone satisfies every other condition.
-/

public noncomputable section

open Set

namespace Tests.CantorBendixsonConvexCover

/-- Real sequences under the lexicographic order: a non-Archimedean ordered abelian group. -/
abbrev LexSeq := Lex (ℕ → ℝ)

/-- The entries of a lexicographic sequence. -/
abbrev entry (x : LexSeq) (k : ℕ) : ℝ := ofLex x k

theorem entry_add (x y : LexSeq) (k : ℕ) :
    entry (x + y) k = entry x k + entry y k := (rfl)

theorem entry_neg (x : LexSeq) (k : ℕ) : entry (-x) k = -entry x k := (rfl)

theorem entry_zero (k : ℕ) : entry (0 : LexSeq) k = 0 := (rfl)

theorem entry_sub (x y : LexSeq) (k : ℕ) :
    entry (x - y) k = entry x k - entry y k := (rfl)

theorem lt_of_forall_eq_of_lt {x y : LexSeq} {m : ℕ}
    (h : ∀ j < m, entry x j = entry y j) (hm : entry x m < entry y m) : x < y :=
  ⟨m, h, hm⟩

instance : TopologicalSpace LexSeq := Preorder.topology LexSeq

instance : OrderTopology LexSeq := ⟨rfl⟩

/-- The subgroup of sequences vanishing below a given index. -/
def vanishingBelow (n : ℕ) : AddSubgroup LexSeq where
  carrier := {x : LexSeq | ∀ k < n, entry x k = 0}
  zero_mem' := fun _ _ ↦ rfl
  add_mem' hx hy := fun k hk ↦ by
    rw [entry_add, hx k hk, hy k hk, add_zero]
  neg_mem' hx := fun k hk ↦ by
    rw [entry_neg, hx k hk, neg_zero]

@[simp]
theorem mem_vanishingBelow {n : ℕ} {x : LexSeq} :
    x ∈ vanishingBelow n ↔ ∀ k < n, entry x k = 0 := (Iff.rfl)

/-- The witnessing family is nested and decreasing. -/
theorem vanishingBelow_mono {i j : ℕ} (hij : i ≤ j) :
    (vanishingBelow j : Set LexSeq) ⊆ (vanishingBelow i : Set LexSeq) :=
  fun _ hx k hk ↦ hx k (hk.trans_le hij)

/-- The least index at which a nonzero sequence does not vanish. -/
theorem exists_least_ne_zero {c : LexSeq} {k : ℕ} (hne : entry c k ≠ 0) :
    ∃ m, entry c m ≠ 0 ∧ ∀ j < m, entry c j = 0 := by
  classical
  have hex : ∃ m, entry c m ≠ 0 := ⟨k, hne⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj ↦ not_not.mp (Nat.find_min hex hj)⟩

/-- Each subgroup of the family is convex: a sequence between two vanishing ones has no earlier
nonzero entry, since a positive one would exceed the upper bound and a negative one would fall
below the lower bound. -/
theorem vanishingBelow_ordConnected (n : ℕ) :
    ((vanishingBelow n : AddSubgroup LexSeq) : Set LexSeq).OrdConnected := by
  constructor
  intro a ha b hb c hc k hk
  by_contra hne
  obtain ⟨m, hm, hmin⟩ := exists_least_ne_zero hne
  have hmn : m < n := by
    by_contra hmn
    exact hne (hmin k (lt_of_lt_of_le hk (not_lt.mp hmn)))
  rcases lt_trichotomy (entry c m) 0 with hneg | hzero | hpos
  · have hca : c < a :=
      lt_of_forall_eq_of_lt (fun j hj ↦ by
        rw [hmin j hj, ha j (hj.trans hmn)]) (by rw [ha m hmn]; exact hneg)
    exact absurd hc.1 (not_le.mpr hca)
  · exact hm hzero
  · have hbc : b < c :=
      lt_of_forall_eq_of_lt (fun j hj ↦ by
        rw [hb j (hj.trans hmn), hmin j hj]) (by rw [hb m hmn]; exact hpos)
    exact absurd hc.2 (not_le.mpr hbc)

/-- The indicator sequence with a single unit entry. -/
def unitAt (n : ℕ) : LexSeq := toLex (fun k ↦ if k = n then (1 : ℝ) else 0)

theorem entry_unitAt (n k : ℕ) : entry (unitAt n) k = if k = n then (1 : ℝ) else 0 := (rfl)

theorem unitAt_pos (n : ℕ) : 0 < unitAt n := by
  refine lt_of_forall_eq_of_lt (m := n) (fun j hj ↦ ?_) ?_
  · rw [entry_unitAt, ite_eq_right hj.ne]
    rfl
  · rw [entry_unitAt, ite_eq_left rfl]
    exact zero_lt_one

/-- Every sequence vanishing below an index lies strictly between the negative and positive unit
sequences at that index, so each subgroup of the family contains a neighborhood of zero and is
therefore open. -/
theorem vanishingBelow_subset_Ioo (n : ℕ) :
    ((vanishingBelow (n + 1) : AddSubgroup LexSeq) : Set LexSeq) ⊆
      Ioo (-unitAt n) (unitAt n) := by
  intro x hx
  constructor
  · refine lt_of_forall_eq_of_lt (m := n) (fun j hj ↦ ?_) ?_
    · rw [entry_neg, entry_unitAt, ite_eq_right hj.ne, neg_zero,
        hx j (hj.trans (Nat.lt_succ_self n))]
    · rw [entry_neg, entry_unitAt, ite_eq_left rfl, hx n (Nat.lt_succ_self n)]
      norm_num
  · refine lt_of_forall_eq_of_lt (m := n) (fun j hj ↦ ?_) ?_
    · rw [entry_unitAt, ite_eq_right hj.ne, hx j (hj.trans (Nat.lt_succ_self n))]
    · rw [entry_unitAt, ite_eq_left rfl, hx n (Nat.lt_succ_self n)]
      exact zero_lt_one

theorem vanishingBelow_isOpen (n : ℕ) :
    IsOpen ((vanishingBelow n : AddSubgroup LexSeq) : Set LexSeq) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hsub : Ioo (x - unitAt n) (x + unitAt n) ⊆
      ((vanishingBelow n : AddSubgroup LexSeq) : Set LexSeq) := by
    intro y hy
    have hmem : y - x ∈ Ioo (-unitAt n) (unitAt n) := by
      constructor
      · rw [lt_sub_iff_add_lt]
        have h1 := hy.1
        rw [sub_eq_neg_add] at h1
        exact h1
      · rw [sub_lt_iff_lt_add]
        have h2 := hy.2
        rw [add_comm] at h2
        exact h2
    -- Convexity of the subgroup transfers membership from `x` to `y`.
    have hyx : y = x + (y - x) := by abel
    rw [hyx]
    refine AddSubgroup.add_mem _ hx ?_
    intro k hk
    by_contra hne
    obtain ⟨m, hm, hmin⟩ := exists_least_ne_zero hne
    have hmn : m < n := by
      by_contra hmn
      exact hne (hmin k (lt_of_lt_of_le hk (not_lt.mp hmn)))
    rcases lt_trichotomy (entry (y - x) m) 0 with hneg | hzero | hpos
    · refine absurd hmem.1 (not_lt.mpr (le_of_lt (lt_of_forall_eq_of_lt (m := m)
        (fun j hj ↦ ?_) ?_)))
      · rw [hmin j hj, entry_neg, entry_unitAt, ite_eq_right (by omega), neg_zero]
      · rw [entry_neg, entry_unitAt, ite_eq_right (by omega), neg_zero]
        exact hneg
    · exact hm hzero
    · refine absurd hmem.2 (not_lt.mpr (le_of_lt (lt_of_forall_eq_of_lt (m := m)
        (fun j hj ↦ ?_) ?_)))
      · rw [entry_unitAt, ite_eq_right (by omega), hmin j hj]
      · rw [entry_unitAt, ite_eq_right (by omega)]
        exact hpos
  exact Filter.mem_of_superset
    (Ioo_mem_nhds (sub_lt_self x (unitAt_pos n)) (lt_add_of_pos_right x (unitAt_pos n))) hsub

/-- The family is coinitial: every strictly positive sequence dominates one of its members. -/
theorem exists_vanishingBelow_subset_Ioo {ε : LexSeq} (hε : 0 < ε) :
    ∃ n : ℕ, ((vanishingBelow n : AddSubgroup LexSeq) : Set LexSeq) ⊆ Ioo (-ε) ε := by
  obtain ⟨p, hpz, hpos⟩ := hε
  have hpz' : ∀ j < p, entry ε j = 0 := fun j hj ↦ (hpz j hj).symm
  have hpos' : (0 : ℝ) < entry ε p := hpos
  refine ⟨p + 1, fun x hx ↦ ⟨?_, ?_⟩⟩
  · refine lt_of_forall_eq_of_lt (m := p) (fun j hj ↦ ?_) ?_
    · rw [entry_neg, hpz' j hj, neg_zero, hx j (hj.trans (Nat.lt_succ_self p))]
    · rw [entry_neg, hx p (Nat.lt_succ_self p)]
      linarith
  · refine lt_of_forall_eq_of_lt (m := p) (fun j hj ↦ ?_) ?_
    · rw [hx j (hj.trans (Nat.lt_succ_self p)), hpz' j hj]
    · rw [hx p (Nat.lt_succ_self p)]
      exact hpos'

instance : NoMinOrder LexSeq :=
  ⟨fun x ↦ ⟨x - unitAt 0, sub_lt_self x (unitAt_pos 0)⟩⟩

instance : NoMaxOrder LexSeq :=
  ⟨fun x ↦ ⟨x + unitAt 0, lt_add_of_pos_right x (unitAt_pos 0)⟩⟩

/-- **The cover hypotheses are consistent.** Every hypothesis of the disjoint convex cover theorem
holds for the lexicographic sequence group with the vanishing-below family, so the result is not
vacuous. -/
theorem exists_disjoint_convex_cover_with_rank_lt_center_lexSeq
    (s : TopologicalSpace.Closeds LexSeq) (hs : (s : Set LexSeq).IsPWO) :
    ∃ (X : Set LexSeq) (C : X → Set LexSeq),
      X ⊆ (s : Set LexSeq) ∧
      (∀ x : X, (x : LexSeq) ∈ C x) ∧
      (∀ x : X, IsOpen (C x)) ∧
      (∀ x : X, (C x).OrdConnected) ∧
      (∀ x y : X, x ≠ y → Disjoint (C x) (C y)) ∧
      (∀ x y : X, (x : LexSeq) < (y : LexSeq) → ∀ a ∈ C x, ∀ b ∈ C y, a < b) ∧
      ((s : Set LexSeq) ⊆ ⋃ x : X, C x) ∧
      (∀ x : X, ∀ z ∈ (s : Set LexSeq) ∩ C x, z ≤ (x : LexSeq)) ∧
      (∀ x : X, ∀ z ∈ (s : Set LexSeq) ∩ C x, z ≠ (x : LexSeq) →
        s.cantorBendixsonRank hs z < s.cantorBendixsonRank hs (x : LexSeq)) ∧
      (∀ z : LexSeq, ¬ AccPt z (Filter.principal X)) :=
  TopologicalSpace.Closeds.exists_disjoint_convex_cover_with_rank_lt_center s hs vanishingBelow
    (fun hij ↦ vanishingBelow_mono hij) vanishingBelow_isOpen vanishingBelow_ordConnected
    (fun _ hε ↦ exists_vanishingBelow_subset_Ioo hε)

/-- The real line is not a witness: its only convex subgroups are zero and the whole line, and
zero is not open, so no family of open convex subgroups is a neighborhood base at zero. The
openness requirement is therefore doing real work. -/
theorem not_isOpen_bot_real : ¬ IsOpen ((⊥ : AddSubgroup ℝ) : Set ℝ) := by
  intro h
  have hmem : (0 : ℝ) ∈ ((⊥ : AddSubgroup ℝ) : Set ℝ) := (⊥ : AddSubgroup ℝ).zero_mem
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp h 0 hmem
  have hlt : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have hb : ε / 2 ∈ (⊥ : AddSubgroup ℝ) := hsub hlt
  rw [AddSubgroup.mem_bot] at hb
  linarith

end Tests.CantorBendixsonConvexCover
