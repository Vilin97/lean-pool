/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Tactic.Push

/-!
# A six-column three-group census

This file isolates the small arithmetic obstruction used at the order-15
endpoint of the shared-star moat.  Each column records how many of its three
incidences land in three two-vertex groups.  If too few pairs are repeated
inside the groups and across the first group, the six columns cannot exist.
-/

public section

namespace ACMax

open Finset

open Classical in
/-- Six triples with entries at most two and column sum three cannot have
first-coordinate sum six while all three indicated pair counts stay small.

The three indicator sums count repeated pairs within the groups.  The product
sums count pairs crossing the first group with the other two groups. -/
theorem six_triple_census_impossible {α : Type*}
    (B : Finset α) (a c d : α → ℕ)
    (hB : B.card = 6)
    (hcol : ∀ x ∈ B, a x ≤ 2 ∧ c x ≤ 2 ∧ d x ≤ 2 ∧ a x + c x + d x = 3)
    (ha : ∑ x ∈ B, a x = 6)
    (hwithin : ∑ x ∈ B,
        ((if a x = 2 then 1 else 0) + (if c x = 2 then 1 else 0) +
          (if d x = 2 then 1 else 0)) ≤ 3)
    (hac : ∑ x ∈ B, a x * c x ≤ 4)
    (had : ∑ x ∈ B, a x * d x ≤ 4) : False := by
  classical
  classical
  let rainbow : α → Prop := fun x => a x = 1 ∧ c x = 1 ∧ d x = 1
  let R := B.filter rainbow
  let Q := B.filter (fun x => ¬rainbow x)
  have hsplit : R.card + Q.card = B.card := by
    simpa [R, Q] using Finset.card_filter_add_card_filter_not (s := B) rainbow
  have hQterm : ∀ x ∈ Q,
      1 ≤ (if a x = 2 then 1 else 0) + (if c x = 2 then 1 else 0) +
        (if d x = 2 then 1 else 0) := by
    intro x hx
    change x ∈ B.filter (fun x => ¬rainbow x) at hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxB, hxnr⟩ := hx
    obtain ⟨ha2, hc2, hd2, hsum⟩ := hcol x hxB
    simp only [rainbow] at hxnr
    split_ifs <;> omega
  have hQ : Q.card ≤ 3 := by
    calc
      Q.card = ∑ _x ∈ Q, 1 := by simp
      _ ≤ ∑ x ∈ Q,
          ((if a x = 2 then 1 else 0) + (if c x = 2 then 1 else 0) +
            (if d x = 2 then 1 else 0)) := Finset.sum_le_sum hQterm
      _ ≤ ∑ x ∈ B,
          ((if a x = 2 then 1 else 0) + (if c x = 2 then 1 else 0) +
            (if d x = 2 then 1 else 0)) :=
        Finset.sum_le_sum_of_subset (by
          change B.filter (fun x => ¬rainbow x) ⊆ B
          exact Finset.filter_subset _ _)
      _ ≤ 3 := hwithin
  have hR3 : 3 ≤ R.card := by omega
  have hpointAC : ∀ x ∈ B,
      (if rainbow x then 1 else 0) + 2 * (if d x = 0 then 1 else 0) ≤ a x * c x := by
    intro x hx
    obtain ⟨ha2, hc2, hd2, hsum⟩ := hcol x hx
    by_cases hr : rainbow x
    · rw [ite_eq_left hr]
      obtain ⟨ha1, hc1, hd1⟩ := hr
      simp [ha1, hc1, hd1]
    · by_cases hd0' : d x = 0
      · have hacases : a x = 1 ∨ a x = 2 := by omega
        rcases hacases with ha1 | ha2'
        · have hc2' : c x = 2 := by omega
          simp [hr, hd0', ha1, hc2']
        · have hc1 : c x = 1 := by omega
          simp [hr, hd0', ha2', hc1]
      · simp [hr, hd0']
  have hACsum : R.card + 2 * (B.filter fun x => d x = 0).card ≤
      ∑ x ∈ B, a x * c x := by
    calc
      R.card + 2 * (B.filter fun x => d x = 0).card
          = ∑ x ∈ B,
              ((if rainbow x then 1 else 0) + 2 * (if d x = 0 then 1 else 0)) := by
            simp only [R, Finset.card_filter, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ x ∈ B, a x * c x := Finset.sum_le_sum hpointAC
  have hd0 : (B.filter fun x => d x = 0).card = 0 := by omega
  have hdpos : ∀ x ∈ B, 1 ≤ d x := by
    intro x hx
    have hnot : ¬d x = 0 := by
      intro hzero
      have hmem : x ∈ B.filter (fun y => d y = 0) := Finset.mem_filter.mpr ⟨hx, hzero⟩
      rw [Finset.card_eq_zero.mp hd0] at hmem
      simp at hmem
    omega
  have hpointAD : ∀ x ∈ B,
      (if rainbow x then 1 else 0) + 2 * (if c x = 0 then 1 else 0) ≤ a x * d x := by
    intro x hx
    obtain ⟨ha2, hc2, hd2, hsum⟩ := hcol x hx
    by_cases hr : rainbow x
    · rw [ite_eq_left hr]
      obtain ⟨ha1, hc1, hd1⟩ := hr
      simp [ha1, hc1, hd1]
    · by_cases hc0' : c x = 0
      · have hadcases : a x = 1 ∨ a x = 2 := by omega
        rcases hadcases with ha1 | ha2'
        · have hd2' : d x = 2 := by omega
          simp [hr, hc0', ha1, hd2']
        · have hd1 : d x = 1 := by omega
          simp [hr, hc0', ha2', hd1]
      · simp [hr, hc0']
  have hADsum : R.card + 2 * (B.filter fun x => c x = 0).card ≤
      ∑ x ∈ B, a x * d x := by
    calc
      R.card + 2 * (B.filter fun x => c x = 0).card
          = ∑ x ∈ B,
              ((if rainbow x then 1 else 0) + 2 * (if c x = 0 then 1 else 0)) := by
            simp only [R, Finset.card_filter, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ x ∈ B, a x * d x := Finset.sum_le_sum hpointAD
  have hc0 : (B.filter fun x => c x = 0).card = 0 := by omega
  have hcpos : ∀ x ∈ B, 1 ≤ c x := by
    intro x hx
    have hnot : ¬c x = 0 := by
      intro hzero
      have hmem : x ∈ B.filter (fun y => c y = 0) := Finset.mem_filter.mpr ⟨hx, hzero⟩
      rw [Finset.card_eq_zero.mp hc0] at hmem
      simp at hmem
    omega
  have ha_indicator : ∀ x ∈ B, a x ≤ if rainbow x then 1 else 0 := by
    intro x hx
    obtain ⟨ha2, hc2, hd2, hsum⟩ := hcol x hx
    have hc1 := hcpos x hx
    have hd1 := hdpos x hx
    by_cases hr : rainbow x
    · rw [ite_eq_left hr]
      exact (hr.1.le)
    · have ha0 : a x = 0 := by
        by_contra hne
        have ha1 : a x = 1 := by omega
        have hc1' : c x = 1 := by omega
        have hd1' : d x = 1 := by omega
        exact hr ⟨ha1, hc1', hd1'⟩
      simp [hr, ha0]
  have haR : ∑ x ∈ B, a x ≤ R.card := by
    calc
      ∑ x ∈ B, a x ≤ ∑ x ∈ B, (if rainbow x then 1 else 0) :=
        Finset.sum_le_sum ha_indicator
      _ = R.card := by simp only [R, Finset.card_filter]
  have hR6 : R.card = 6 := by
    have hRle : R.card ≤ B.card := Finset.card_le_card (by
      change B.filter rainbow ⊆ B
      exact Finset.filter_subset _ _)
    omega
  have hRac : R.card ≤ ∑ x ∈ B, a x * c x := by
    calc
      R.card = ∑ x ∈ B, (if rainbow x then 1 else 0) := by
        simp only [R, Finset.card_filter]
      _ ≤ ∑ x ∈ B, a x * c x := by
        refine Finset.sum_le_sum ?_
        intro x hx
        by_cases hr : rainbow x
        · rw [ite_eq_left hr]
          rw [hr.1, hr.2.1]
        · simp [hr]
  omega

open Classical in
/-- Binary incidence form of `six_triple_census_impossible`.  Six three-incidence
columns on three pairs of rows force a repeated pair either within one row-pair,
or between the first row-pair and one of the other two. -/
theorem six_binary_columns_force_repeated_pair {α : Type*}
    (B : Finset α) (a₁ a₂ c₁ c₂ d₁ d₂ : α → Prop)
    (hB : B.card = 6)
    (hcol : ∀ x ∈ B,
      (if a₁ x then 1 else 0) + (if a₂ x then 1 else 0) +
        (if c₁ x then 1 else 0) + (if c₂ x then 1 else 0) +
        (if d₁ x then 1 else 0) + (if d₂ x then 1 else 0) = 3)
    (ha₁ : (B.filter a₁).card = 3) (ha₂ : (B.filter a₂).card = 3) :
    2 ≤ (B.filter fun x => a₁ x ∧ a₂ x).card ∨
    2 ≤ (B.filter fun x => c₁ x ∧ c₂ x).card ∨
    2 ≤ (B.filter fun x => d₁ x ∧ d₂ x).card ∨
    2 ≤ (B.filter fun x => a₁ x ∧ c₁ x).card ∨
    2 ≤ (B.filter fun x => a₁ x ∧ c₂ x).card ∨
    2 ≤ (B.filter fun x => a₂ x ∧ c₁ x).card ∨
    2 ≤ (B.filter fun x => a₂ x ∧ c₂ x).card ∨
    2 ≤ (B.filter fun x => a₁ x ∧ d₁ x).card ∨
    2 ≤ (B.filter fun x => a₁ x ∧ d₂ x).card ∨
    2 ≤ (B.filter fun x => a₂ x ∧ d₁ x).card ∨
    2 ≤ (B.filter fun x => a₂ x ∧ d₂ x).card := by
  classical
  classical
  let bit : (α → Prop) → α → ℕ := fun p x => if p x then 1 else 0
  let a : α → ℕ := fun x => bit a₁ x + bit a₂ x
  let c : α → ℕ := fun x => bit c₁ x + bit c₂ x
  let d : α → ℕ := fun x => bit d₁ x + bit d₂ x
  have hpair (p q : α → Prop) :
      ∑ x ∈ B, (if bit p x + bit q x = 2 then 1 else 0) =
        (B.filter fun x => p x ∧ q x).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hp : p x <;> by_cases hq : q x <;> simp [bit, hp, hq]
  have hmul (p q : α → Prop) (x : α) :
      bit p x * bit q x = if p x ∧ q x then 1 else 0 := by
    by_cases hp : p x <;> by_cases hq : q x <;> simp [bit, hp, hq]
  have hcross (p₁ p₂ q₁ q₂ : α → Prop) :
      ∑ x ∈ B, (bit p₁ x + bit p₂ x) * (bit q₁ x + bit q₂ x) =
        (B.filter fun x => p₁ x ∧ q₁ x).card +
        (B.filter fun x => p₁ x ∧ q₂ x).card +
        (B.filter fun x => p₂ x ∧ q₁ x).card +
        (B.filter fun x => p₂ x ∧ q₂ x).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter]
    simp_rw [mul_add, add_mul, hmul, Finset.sum_add_distrib]
    omega
  have hbitcard (p : α → Prop) : ∑ x ∈ B, bit p x = (B.filter p).card := by
    rw [Finset.card_filter]
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨haa, hcc, hdd, hac11, hac12, hac21, hac22,
    had11, had12, had21, had22⟩
  have hcols : ∀ x ∈ B, a x ≤ 2 ∧ c x ≤ 2 ∧ d x ≤ 2 ∧ a x + c x + d x = 3 := by
    intro x hx
    have hc := hcol x hx
    simp only [a, c, d, bit]
    by_cases ha1x : a₁ x <;> by_cases ha2x : a₂ x <;>
      by_cases hc1x : c₁ x <;> by_cases hc2x : c₂ x <;>
      by_cases hd1x : d₁ x <;> by_cases hd2x : d₂ x <;>
      simp [ha1x, ha2x, hc1x, hc2x, hd1x, hd2x] at hc ⊢
  have hasum : ∑ x ∈ B, a x = 6 := by
    calc
      ∑ x ∈ B, a x = (∑ x ∈ B, bit a₁ x) + ∑ x ∈ B, bit a₂ x := by
        simp only [a, Finset.sum_add_distrib]
      _ = (B.filter a₁).card + (B.filter a₂).card := by
        rw [hbitcard, hbitcard]
      _ = 6 := by omega
  have hwithin : ∑ x ∈ B,
      ((if a x = 2 then 1 else 0) + (if c x = 2 then 1 else 0) +
        (if d x = 2 then 1 else 0)) ≤ 3 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [show (∑ x ∈ B, if a x = 2 then 1 else 0) =
        (B.filter fun x => a₁ x ∧ a₂ x).card by simpa [a] using hpair a₁ a₂]
    rw [show (∑ x ∈ B, if c x = 2 then 1 else 0) =
        (B.filter fun x => c₁ x ∧ c₂ x).card by simpa [c] using hpair c₁ c₂]
    rw [show (∑ x ∈ B, if d x = 2 then 1 else 0) =
        (B.filter fun x => d₁ x ∧ d₂ x).card by simpa [d] using hpair d₁ d₂]
    omega
  have hac : ∑ x ∈ B, a x * c x ≤ 4 := by
    rw [show (∑ x ∈ B, a x * c x) =
        (B.filter fun x => a₁ x ∧ c₁ x).card +
        (B.filter fun x => a₁ x ∧ c₂ x).card +
        (B.filter fun x => a₂ x ∧ c₁ x).card +
        (B.filter fun x => a₂ x ∧ c₂ x).card by simpa [a, c] using hcross a₁ a₂ c₁ c₂]
    omega
  have had : ∑ x ∈ B, a x * d x ≤ 4 := by
    rw [show (∑ x ∈ B, a x * d x) =
        (B.filter fun x => a₁ x ∧ d₁ x).card +
        (B.filter fun x => a₁ x ∧ d₂ x).card +
        (B.filter fun x => a₂ x ∧ d₁ x).card +
        (B.filter fun x => a₂ x ∧ d₂ x).card by simpa [a, d] using hcross a₁ a₂ d₁ d₂]
    omega
  exact six_triple_census_impossible B a c d hB hcols hasum hwithin hac had

end ACMax
