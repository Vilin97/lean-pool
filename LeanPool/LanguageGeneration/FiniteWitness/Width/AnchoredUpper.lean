/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.AnchoredLower

/-!
# Witness assignments attaining the anchored lower bounds
-/

@[expose] public section

namespace GenLimit.FiniteWitness.Anchored

/-- The first half of the indices, rounded up. -/
def low (k : ℕ) : Finset ℕ := Finset.range ((k + 1) / 2)
/-- The remaining indices below the row and column count. -/
def high (k : ℕ) : Finset ℕ := Finset.range k \ low k

/-- Left-side anchor points assigned to a row. -/
noncomputable def rowWitness {k} (i : Fin k) : Finset Point :=
  (if i.val < (k + 1) / 2 then low k else high k).image Sum.inl

/-- Right-side anchor points assigned to a column. -/
noncomputable def colWitness {k} (j : Fin k) : Finset Point :=
  (if j.val < (k + 1) / 2 then high k else low k).image Sum.inr

private theorem high_card (k : ℕ) : (high k).card = k - (k + 1) / 2 := by
  have h : Finset.range ((k + 1) / 2) ⊆ Finset.range k := Finset.range_mono (by omega)
  simp [high, low, Finset.card_sdiff_of_subset h]

private theorem row_card {k} (i : Fin k) : (rowWitness i).card ≤ (k + 1) / 2 := by
  apply Finset.card_image_le.trans
  by_cases h : i.val < (k + 1) / 2
  · simp [h, low]
  · rw [ite_eq_right h, high_card]
    omega

private theorem col_card {k} (j : Fin k) : (colWitness j).card ≤ (k + 1) / 2 := by
  apply Finset.card_image_le.trans
  by_cases h : j.val < (k + 1) / 2
  · rw [ite_eq_left h, high_card]
    omega
  · simp [h, low]

private theorem row_anchor {k} (i j : Fin k) :
    Sum.inl j.val ∈ rowWitness i ↔ (j.val < (k + 1) / 2 ↔ i.val < (k + 1) / 2) := by
  by_cases h : i.val < (k + 1) / 2 <;> simp [rowWitness, h, low, high, j.isLt]

private theorem col_anchor {k} (i j : Fin k) :
    Sum.inr i.val ∈ colWitness j ↔ ¬ (j.val < (k + 1) / 2 ↔ i.val < (k + 1) / 2) := by
  by_cases hi : i.val < (k + 1) / 2 <;> by_cases hj : j.val < (k + 1) / 2 <;>
    simp [colWitness, hi, hj, low, high, i.isLt]
  omega

/-- Assign the row or column witness of an anchored target, using the empty set off the family. -/
noncomputable def upperAssignment {k : ℕ} (L : Set Point) : Finset Point := by
  classical
  exact if h : ∃ p : Fin k × Set ℕ, leftTarget p.1 p.2 = L then rowWitness h.choose.1
    else if h : ∃ p : Fin k × Set ℕ, rightTarget p.1 p.2 = L then colWitness h.choose.1
    else ∅

theorem upper_left {k} (i : Fin k) (D : Set ℕ) :
    upperAssignment (k := k) (leftTarget i D) = rowWitness i := by
  classical
  have h : ∃ p : Fin k × Set ℕ, leftTarget p.1 p.2 = leftTarget i D := ⟨(i, D), rfl⟩
  rw [upperAssignment, dite_eq_left h]
  have he : h.choose = (i, D) := left_injective h.choose_spec
  exact congrArg (fun p : Fin k × Set ℕ => rowWitness p.1) he

theorem upper_right {k} (j : Fin k) (E : Set ℕ) :
    upperAssignment (k := k) (rightTarget j E) = colWitness j := by
  classical
  have hn : ¬ ∃ p : Fin k × Set ℕ, leftTarget p.1 p.2 = rightTarget j E := by
    rintro ⟨⟨i, D⟩, he⟩
    exact left_ne_right i j D E he
  have h : ∃ p : Fin k × Set ℕ, rightTarget p.1 p.2 = rightTarget j E := ⟨(j, E), rfl⟩
  rw [upperAssignment, dite_eq_right hn, dite_eq_left h]
  have he : h.choose = (j, E) := right_injective h.choose_spec
  exact congrArg (fun p : Fin k × Set ℕ => colWitness p.1) he

theorem upper_valid (k : ℕ) : Valid (family k) (upperAssignment (k := k)) := by
  classical
  have hcross (i : Fin k) (D) (j : Fin k) (E) :
      ¬ ((↑(upperAssignment (k := k) (leftTarget i D)) : Set Point) ⊆ rightTarget j E ∧
        (↑(upperAssignment (k := k) (rightTarget j E)) : Set Point) ⊆ leftTarget i D) := by
    rintro ⟨hLR, hRL⟩
    by_cases h : j.val < (k + 1) / 2 ↔ i.val < (k + 1) / 2
    · have ha : Sum.inl j.val ∈ upperAssignment (k := k) (leftTarget i D) := by
        rw [upper_left, row_anchor]; exact h
      exact ((anchor_mem_right j j E).mp (hLR ha)) rfl
    · have ha : Sum.inr i.val ∈ upperAssignment (k := k) (rightTarget j E) := by
        rw [upper_right, col_anchor]; exact h
      exact ((anchor_mem_left i i D).mp (hRL ha)) rfl
  refine ⟨?_, ?_⟩
  · rintro L (⟨⟨i, D⟩, rfl⟩ | ⟨⟨j, E⟩, rfl⟩) x hx
    · rw [upper_left] at hx
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
      trivial
    · rw [upper_right] at hx
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
      trivial
  · intro S hS
    obtain ⟨L, hL⟩ := hS
    rcases hL.1 with ⟨⟨i, D⟩, rfl⟩ | ⟨⟨j, E⟩, rfl⟩
    · apply (Set.infinite_range_of_injective (Sum.inl_injective : Function.Injective
        (Sum.inl : ℕ → Point))).mono
      rintro _ ⟨n, rfl⟩ K hK
      rcases hK.1 with ⟨⟨j, E⟩, rfl⟩ | ⟨⟨j, E⟩, rfl⟩
      · trivial
      · exact (hcross i D j E ⟨fun x hx => hK.2.2 (hL.2.1 hx),
          fun x hx => hL.2.2 (hK.2.1 hx)⟩).elim
    · apply (Set.infinite_range_of_injective (Sum.inr_injective : Function.Injective
        (Sum.inr : ℕ → Point))).mono
      rintro _ ⟨n, rfl⟩ K hK
      rcases hK.1 with ⟨⟨i, D⟩, rfl⟩ | ⟨⟨i, D⟩, rfl⟩
      · exact (hcross i D j E ⟨fun x hx => hL.2.2 (hK.2.1 hx),
          fun x hx => hK.2.2 (hL.2.1 hx)⟩).elim
      · trivial

theorem upper_bound (k : ℕ) : HasBoundedWitnesses (family k) ((k + 1) / 2) := by
  refine ⟨upperAssignment (k := k), upper_valid k, ?_⟩
  rintro L (⟨⟨i, D⟩, rfl⟩ | ⟨⟨j, E⟩, rfl⟩)
  · rw [upper_left]; exact row_card i
  · rw [upper_right]; exact col_card j

/-- Every finite level, on the precise anchored family, including the empty k=0 case. -/
theorem exact_width (k : ℕ) : separationWidth (family k) = finiteValue ((k + 1) / 2) :=
  width_eq_finite_of_bounds (upper_bound k) (fun _ => lower_bound)

theorem realizes_every_finite (d : ℕ) : separationWidth (family (2 * d)) = finiteValue d := by
  rw [exact_width]
  congr 1
  omega

end GenLimit.FiniteWitness.Anchored
