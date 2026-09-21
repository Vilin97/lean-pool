/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# Weighted shadow inequality

Blueprint node H02: for a divisor-closed set `S` of exponent vectors in `N` variables,
`(t + 1) h(t + 1) ≤ (t + N) h(t)`, counted in `ℕ` by double counting weighted covering relations
`α ↦ α + eᵢ`.
-/

namespace Nikodym.LowerBound

open Finset Function

variable {N : ℕ}

/-- Blueprint H02: the degree-`t` layer of `S`. -/
noncomputable def layer (S : Set (Fin N → ℕ)) (t : ℕ) : Finset (Fin N → ℕ) := by
  classical exact (Nat.antidiagonalTuple N t).filter (· ∈ S)

/-- Blueprint H02: the number of elements of `S` of total degree `t`. -/
noncomputable def layerCard (S : Set (Fin N → ℕ)) (t : ℕ) : ℕ := (layer S t).card

/-- Blueprint H02: membership in a degree layer. -/
theorem mem_layer {S : Set (Fin N → ℕ)} {t : ℕ} {α : Fin N → ℕ} :
    α ∈ layer S t ↔ ∑ i, α i = t ∧ α ∈ S := by
  classical
  simp [layer, Nat.mem_antidiagonalTuple]

/-- Parent of `γ` along coordinate `i`: decrease `γ i` by one. -/
private def parent (γ : Fin N → ℕ) (i : Fin N) : Fin N → ℕ :=
  update γ i (γ i - 1)

private lemma sum_parent (γ : Fin N → ℕ) (i : Fin N) (hi : 1 ≤ γ i) :
    ∑ j, parent γ i j + 1 = ∑ j, γ j := by
  simp only [parent]
  rw [sum_update_of_mem (mem_univ i), sdiff_singleton_eq_erase]
  rw [add_right_comm, Nat.sub_add_cancel hi, add_sum_erase _ _ (mem_univ i)]

private lemma parent_le (γ : Fin N → ℕ) (i : Fin N) (j : Fin N) :
    parent γ i j ≤ γ j := by
  unfold parent
  rw [update_apply]
  split_ifs with h
  · rw [h]
    exact Nat.sub_le _ _
  · exact Nat.le_refl _

private lemma parent_mem_layer {S : Set (Fin N → ℕ)}
    (hS : ∀ α ∈ S, ∀ β : Fin N → ℕ, (∀ i, β i ≤ α i) → β ∈ S)
    {t : ℕ} {γ : Fin N → ℕ} {i : Fin N} (hγ : γ ∈ layer S (t + 1)) (hi : 1 ≤ γ i) :
    parent γ i ∈ layer S t := by
  have hγ' := mem_layer.mp hγ
  refine mem_layer.mpr ⟨?_, hS γ hγ'.2 _ fun j ↦ parent_le γ i j⟩
  have := sum_parent γ i hi
  rw [hγ'.1] at this
  exact Nat.add_one_inj.mp this

private lemma update_parent (γ : Fin N → ℕ) (i : Fin N) (hi : 1 ≤ γ i) :
    update (parent γ i) i (parent γ i i + 1) = γ := by
  unfold parent
  simp [update_self, Nat.sub_add_cancel hi]

/-- Outgoing covering edges from the degree-`t` layer. -/
private noncomputable def outgoing (S : Set (Fin N → ℕ)) (t : ℕ) :
    Finset ((Fin N → ℕ) × Fin N) :=
  layer S t ×ˢ univ

/-- Incoming covering edges into the degree-`(t+1)` layer. -/
private noncomputable def incoming (S : Set (Fin N → ℕ)) (t : ℕ) :
    Finset ((Fin N → ℕ) × Fin N) := by
  classical exact (layer S (t + 1) ×ˢ univ).filter fun p ↦ 1 ≤ p.1 p.2

private lemma mem_outgoing {S : Set (Fin N → ℕ)} {t : ℕ} {p : (Fin N → ℕ) × Fin N} :
    p ∈ outgoing S t ↔ p.1 ∈ layer S t := by
  simp [outgoing]

private lemma mem_incoming {S : Set (Fin N → ℕ)} {t : ℕ} {p : (Fin N → ℕ) × Fin N} :
    p ∈ incoming S t ↔ p.1 ∈ layer S (t + 1) ∧ 1 ≤ p.1 p.2 := by
  classical
  simp [incoming]

/-- Map an incoming edge to the corresponding outgoing edge by stepping down. -/
private def toParent (p : (Fin N → ℕ) × Fin N) : (Fin N → ℕ) × Fin N :=
  (parent p.1 p.2, p.2)

private lemma toParent_mem_outgoing {S : Set (Fin N → ℕ)}
    (hS : ∀ α ∈ S, ∀ β : Fin N → ℕ, (∀ i, β i ≤ α i) → β ∈ S)
    {t : ℕ} {p : (Fin N → ℕ) × Fin N} (hp : p ∈ incoming S t) :
    toParent p ∈ outgoing S t := by
  rw [mem_outgoing, toParent]
  obtain ⟨hγ, hi⟩ := mem_incoming.mp hp
  exact parent_mem_layer hS hγ hi

private lemma injOn_toParent (S : Set (Fin N → ℕ)) (t : ℕ) :
    Set.InjOn (toParent (N := N)) (incoming S t) := by
  intro p hp q hq heq
  obtain ⟨_, hip⟩ := mem_incoming.mp hp
  obtain ⟨_, hiq⟩ := mem_incoming.mp hq
  simp only [toParent] at heq
  obtain ⟨hpar, hi⟩ := Prod.mk.inj heq
  refine Prod.ext ?_ hi
  rw [← update_parent p.1 p.2 hip, ← update_parent q.1 q.2 hiq, hpar, hi]

private lemma sum_outgoing (S : Set (Fin N → ℕ)) (t : ℕ) :
    ∑ p ∈ outgoing S t, (p.1 p.2 + 1) = (t + N) * layerCard S t := by
  classical
  unfold outgoing
  rw [sum_product]
  have hα : ∀ α ∈ layer S t, ∑ i : Fin N, (α i + 1) = t + N := by
    intro α hα
    rw [sum_add_distrib, (mem_layer.mp hα).1, ← card_eq_sum_ones, card_univ, Fintype.card_fin]
  rw [sum_congr rfl hα, sum_const_nat fun _ _ ↦ rfl, mul_comm, layerCard]

private lemma sum_incoming (S : Set (Fin N → ℕ)) (t : ℕ) :
    ∑ p ∈ incoming S t, p.1 p.2 = (t + 1) * layerCard S (t + 1) := by
  classical
  unfold incoming
  rw [sum_filter, sum_product]
  have hγ : ∀ γ ∈ layer S (t + 1),
      ∑ i : Fin N, (if 1 ≤ γ i then γ i else 0) = t + 1 := by
    intro γ hγ
    have hite : ∀ i, (if 1 ≤ γ i then γ i else 0) = γ i := fun i ↦ by
      split_ifs with hi
      · rfl
      · exact (Nat.lt_one_iff.mp (Nat.not_le.mp hi)).symm
    rw [sum_congr rfl fun i _ ↦ hite i, (mem_layer.mp hγ).1]
  rw [sum_congr rfl hγ, sum_const_nat fun _ _ ↦ rfl, mul_comm, layerCard]

private lemma weight_toParent {p : (Fin N → ℕ) × Fin N} (hp : 1 ≤ p.1 p.2) :
    p.1 p.2 = (toParent p).1 (toParent p).2 + 1 := by
  simp [toParent, parent, update_self, Nat.sub_add_cancel hp]

/-- Blueprint H02: weighted shadow inequality for a divisor-closed monomial set. -/
theorem weighted_shadow (S : Set (Fin N → ℕ))
    (hS : ∀ α ∈ S, ∀ β : Fin N → ℕ, (∀ i, β i ≤ α i) → β ∈ S) (t : ℕ) :
    (t + 1) * layerCard S (t + 1) ≤ (t + N) * layerCard S t := by
  classical
  have hsub : (incoming S t).image toParent ⊆ outgoing S t := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    exact toParent_mem_outgoing hS hp
  calc
    (t + 1) * layerCard S (t + 1) = ∑ p ∈ incoming S t, p.1 p.2 :=
      (sum_incoming S t).symm
    _ = ∑ p ∈ incoming S t, ((toParent p).1 (toParent p).2 + 1) :=
      sum_congr rfl fun p hp ↦ weight_toParent (mem_incoming.mp hp).2
    _ = ∑ q ∈ (incoming S t).image toParent, (q.1 q.2 + 1) :=
      (sum_image (f := fun q ↦ q.1 q.2 + 1) (injOn_toParent S t)).symm
    _ ≤ ∑ q ∈ outgoing S t, (q.1 q.2 + 1) :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Nat.zero_le _
    _ = (t + N) * layerCard S t := sum_outgoing S t

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
