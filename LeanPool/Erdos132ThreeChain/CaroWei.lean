/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Caro--Wei independence bound

`carowei` is the classical greedy/random-order bound: every finite graph has an independent set
of size at least `∑ v, 1 / (deg v + 1)`.  It is proved here by the standard induction that
deletes the closed neighbourhood of a minimum-degree vertex.

`exists_independent_five` specialises it to the shape the main theorem needs.  The tangent-line
estimate `1 / (d + 1) ≥ (5 - d) / 9`, valid because `(d - 2) ^ 2 ≥ 0`, converts a degree-sum
bound into a lower bound on the independence number, and integrality upgrades `n / 3 > 4` to an
independent set of size `5` once `n ≥ 13`.
-/

namespace Erdos132ThreeChain

open Finset

variable {α : Type*}

/-- The degree of `v` in the graph that `adj` induces on the vertex set `V`. -/
def degree (adj : α → α → Prop) [DecidableRel adj] (V : Finset α) (v : α) : ℕ :=
  (V.filter (adj v)).card

theorem degree_mono {adj : α → α → Prop} [DecidableRel adj] {V W : Finset α} (h : W ⊆ V)
    (v : α) : degree adj W v ≤ degree adj V v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **Caro--Wei.**  Every finite graph has an independent set of size at least the sum over its
vertices of the reciprocal of one more than the degree. -/
theorem carowei (adj : α → α → Prop) [DecidableRel adj] (hsymm : ∀ a b, adj a b → adj b a)
    (hirr : ∀ a, ¬ adj a a) (V : Finset α) :
    ∃ S ⊆ V, (∀ p ∈ S, ∀ q ∈ S, ¬ adj p q) ∧
      ∑ v ∈ V, (1 : ℝ) / (degree adj V v + 1) ≤ S.card := by
  classical
  induction V using Finset.strongInduction with
  | _ V ih =>
    rcases V.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image V (degree adj V) hne
    set N : Finset α := V.filter (adj v) with hN
    have hvN : v ∉ N := by simp [hN, hirr v]
    set NV : Finset α := insert v N with hNV
    have hNVsub : NV ⊆ V := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv
      · exact (Finset.mem_filter.mp hx).1
    set W : Finset α := V \ NV with hW
    have hWsub : W ⊆ V := Finset.sdiff_subset
    have hvW : v ∉ W := by simp [hW, hNV]
    have hWlt : W ⊂ V := ⟨hWsub, fun hc => hvW (hc hv)⟩
    obtain ⟨S', hS'W, hS'ind, hS'card⟩ := ih W hWlt
    have hvS' : v ∉ S' := fun hc => hvW (hS'W hc)
    refine ⟨insert v S', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv
      · exact hWsub (hS'W hx)
    · intro p hp q hq
      have hnadj : ∀ u ∈ S', ¬ adj v u := by
        intro u hu hadj
        exact (Finset.mem_sdiff.mp (hS'W hu)).2
          (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hWsub (hS'W hu), hadj⟩))
      rcases Finset.mem_insert.mp hp with hp' | hp'
      · rcases Finset.mem_insert.mp hq with hq' | hq'
        · rw [hp', hq']; exact hirr v
        · rw [hp']; exact hnadj q hq'
      · rcases Finset.mem_insert.mp hq with hq' | hq'
        · rw [hq']; exact fun hadj => hnadj p hp' (hsymm _ _ hadj)
        · exact hS'ind p hp' q hq'
    · have hcard : ((insert v S').card : ℝ) = (S'.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem hvS', Nat.cast_add, Nat.cast_one]
      rw [hcard]
      have hsplit : ∑ u ∈ W, (1 : ℝ) / (degree adj V u + 1)
          + ∑ u ∈ NV, (1 : ℝ) / (degree adj V u + 1)
          = ∑ u ∈ V, (1 : ℝ) / (degree adj V u + 1) := Finset.sum_sdiff hNVsub
      have hhead : ∑ u ∈ NV, (1 : ℝ) / (degree adj V u + 1) ≤ 1 := by
        have hbound : ∀ u ∈ NV, (1 : ℝ) / (degree adj V u + 1)
            ≤ 1 / (degree adj V v + 1) := by
          intro u hu
          have := hmin u (hNVsub hu)
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right this 1
        calc ∑ u ∈ NV, (1 : ℝ) / (degree adj V u + 1)
            ≤ NV.card • ((1 : ℝ) / (degree adj V v + 1)) :=
              Finset.sum_le_card_nsmul _ _ _ hbound
          _ = 1 := by
              rw [hNV, Finset.card_insert_of_notMem hvN, nsmul_eq_mul]
              have : degree adj V v = N.card := rfl
              rw [this]
              push_cast
              field_simp
      have htail : ∑ u ∈ W, (1 : ℝ) / (degree adj V u + 1)
          ≤ ∑ u ∈ W, (1 : ℝ) / (degree adj W u + 1) := by
        refine Finset.sum_le_sum fun u _ => ?_
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right (degree_mono hWsub u) 1
      linarith [hsplit, hhead, htail, hS'card]


/-- A graph on at least thirteen vertices whose degrees sum to at most twice the number of
vertices has an independent set of five vertices.  The degree sum is twice the number of edges,
so the hypothesis is the edge bound `#edges ≤ #vertices`. -/
theorem exists_independent_five (adj : α → α → Prop) [DecidableRel adj]
    (hsymm : ∀ a b, adj a b → adj b a) (hirr : ∀ a, ¬ adj a a) (V : Finset α)
    (hcard : 13 ≤ V.card) (hdeg : ∑ v ∈ V, degree adj V v ≤ 2 * V.card) :
    ∃ S ⊆ V, S.card = 5 ∧ ∀ p ∈ S, ∀ q ∈ S, ¬ adj p q := by
  obtain ⟨T, hTV, hTind, hTcard⟩ := carowei adj hsymm hirr V
  have hterm : ∀ v ∈ V, (5 - (degree adj V v : ℝ)) / 9 ≤ 1 / ((degree adj V v : ℝ) + 1) := by
    intro v _
    have hd : (0 : ℝ) ≤ (degree adj V v : ℝ) := Nat.cast_nonneg _
    have hpos : (0 : ℝ) < (degree adj V v : ℝ) + 1 := by linarith
    have key : 1 / ((degree adj V v : ℝ) + 1) - (5 - (degree adj V v : ℝ)) / 9
        = ((degree adj V v : ℝ) - 2) ^ 2 / (9 * ((degree adj V v : ℝ) + 1)) := by
      field_simp; ring
    have hnn : (0 : ℝ) ≤ ((degree adj V v : ℝ) - 2) ^ 2 / (9 * ((degree adj V v : ℝ) + 1)) := by
      positivity
    rw [← key] at hnn
    linarith
  have hsum : ∑ v ∈ V, (5 - (degree adj V v : ℝ)) / 9
      = (5 * (V.card : ℝ) - ((∑ v ∈ V, degree adj V v : ℕ) : ℝ)) / 9 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_sum]
    ring
  have hdegR : ((∑ v ∈ V, degree adj V v : ℕ) : ℝ) ≤ 2 * (V.card : ℝ) := by exact_mod_cast hdeg
  have hcardR : (13 : ℝ) ≤ (V.card : ℝ) := by exact_mod_cast hcard
  have hT5 : 5 ≤ T.card := by
    by_contra hcon
    rw [Nat.not_le] at hcon
    have hle : (T.card : ℝ) ≤ 4 := by exact_mod_cast Nat.lt_succ_iff.mp hcon
    have h1 := Finset.sum_le_sum hterm
    rw [hsum] at h1
    linarith
  obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hT5
  exact ⟨S, hST.trans hTV, hScard, fun p hp q hq => hTind p (hST hp) q (hST hq)⟩

end Erdos132ThreeChain
