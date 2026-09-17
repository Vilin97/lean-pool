/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
import LeanPool.LanguageGeneration.FiniteWitness.Width.Foundation
import Mathlib.Order.WithBot

/-! The ordered range 0,1,2,...,omega,omega+1, and its exact threshold. -/

namespace GenLimit.FiniteWitness

/-- The ordered width values 0, 1, 2, ..., omega, and omega+1. -/
abbrev SeparationValue := WithTop (WithTop ℕ)

/-- Embed a finite witness bound into the separation-width range. -/
def finiteValue (n : ℕ) : SeparationValue := ((n : WithTop ℕ) : SeparationValue)
/-- The width value for finite witnesses with no uniform finite bound. -/
def omegaValue : SeparationValue := ((⊤ : WithTop ℕ) : SeparationValue)

@[simp] theorem finiteValue_le_iff (m n : ℕ) : finiteValue m ≤ finiteValue n ↔ m ≤ n := by
  simp [finiteValue]

@[simp] theorem finiteValue_le_omega (n : ℕ) : finiteValue n ≤ omegaValue := by
  exact WithTop.coe_le_coe.mpr le_top

@[simp] theorem not_omega_le_finite (n : ℕ) : ¬ omegaValue ≤ finiteValue n := by
  exact not_le_of_gt (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n))

@[simp] theorem omega_ne_top : omegaValue ≠ ⊤ := WithTop.coe_ne_top

@[simp] theorem finiteValue_ne_top (n : ℕ) : finiteValue n ≠ ⊤ := WithTop.coe_ne_top

@[simp] theorem finiteValue_ne_omega (n : ℕ) : finiteValue n ≠ omegaValue := by
  exact ne_of_lt (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n))

/-- A convenient normal form for the optimized width. The accompanying
minimum theorem identifies it with the paper's assignment-cost definition. -/
noncomputable def separationWidth (H : Set (Set α)) : SeparationValue := by
  classical
  exact if h : ∃ d, HasBoundedWitnesses H d then finiteValue (Nat.find h)
    else if HasFiniteWitnesses H then omegaValue else ⊤

theorem HasBoundedWitnesses.hasFiniteWitnesses {H : Set (Set α)} {d : ℕ}
    (h : HasBoundedWitnesses H d) : HasFiniteWitnesses H := by
  obtain ⟨T, hT, _⟩ := h
  exact hT.hasFiniteWitnesses

theorem finiteWitnesses_mono {H K : Set (Set α)}
    (h : HasFiniteWitnesses H) (hKH : K ⊆ H) : HasFiniteWitnesses K := by
  obtain ⟨T, hT⟩ := h
  exact (Valid.mono hT hKH).hasFiniteWitnesses

theorem width_le_finite_iff (H : Set (Set α)) (d : ℕ) :
    separationWidth H ≤ finiteValue d ↔ HasBoundedWitnesses H d := by
  classical
  by_cases h : ∃ e, HasBoundedWitnesses H e
  · simp only [separationWidth, dite_eq_left h, finiteValue_le_iff]
    exact ⟨fun hn => (Nat.find_spec h).mono_bound hn, fun hd => Nat.find_min' h hd⟩
  · have hd : ¬ HasBoundedWitnesses H d := fun hd => h ⟨d, hd⟩
    simp [separationWidth, h, hd, apply_ite (fun w => w ≤ finiteValue d)]

theorem width_le_omega_iff (H : Set (Set α)) :
    separationWidth H ≤ omegaValue ↔ HasFiniteWitnesses H := by
  classical
  by_cases h : ∃ d, HasBoundedWitnesses H d
  · simp [separationWidth, h, (Nat.find_spec h).hasFiniteWitnesses]
  · by_cases hw : HasFiniteWitnesses H
    · simp [separationWidth, h, hw]
    · simp [separationWidth, h, hw, omegaValue]

theorem ordinary_iff_width [Countable α] [Infinite α] (H : Set (Set α))
    (hUUS : Generic.UUS H) :
    Generic.GeneratableInLimit H ↔ separationWidth H ≤ omegaValue :=
  (ordinary_iff_finiteWitnesses H hUUS).trans (width_le_omega_iff H).symm

theorem width_eq_omega_iff (H : Set (Set α)) :
    separationWidth H = omegaValue ↔
      HasFiniteWitnesses H ∧ ∀ d, ¬ HasBoundedWitnesses H d := by
  classical
  by_cases h : ∃ d, HasBoundedWitnesses H d
  · have hn : ¬ ∀ d, ¬ HasBoundedWitnesses H d := by simpa using h
    simp [separationWidth, h, hn]
  · have hall : ∀ d, ¬ HasBoundedWitnesses H d := by simpa using h
    by_cases hw : HasFiniteWitnesses H
    · simp [separationWidth, hw, hall]
    · simp [separationWidth, h, hw, omegaValue]

theorem width_eq_top_iff (H : Set (Set α)) :
    separationWidth H = ⊤ ↔ ¬ HasFiniteWitnesses H := by
  classical
  by_cases h : ∃ d, HasBoundedWitnesses H d
  · simp [separationWidth, h, (Nat.find_spec h).hasFiniteWitnesses]
  · by_cases hw : HasFiniteWitnesses H <;> simp [separationWidth, h, hw, omegaValue]

theorem width_mono {H K : Set (Set α)} (hHK : H ⊆ K) :
    separationWidth H ≤ separationWidth K := by
  classical
  by_cases h : ∃ d, HasBoundedWitnesses K d
  · rw [show separationWidth K = finiteValue (Nat.find h) by simp [separationWidth, h]]
    exact (width_le_finite_iff H _).mpr ((Nat.find_spec h).mono hHK)
  · by_cases hw : HasFiniteWitnesses K
    · rw [show separationWidth K = omegaValue by simp [separationWidth, h, hw]]
      exact (width_le_omega_iff H).mpr (finiteWitnesses_mono hw hHK)
    · simp [separationWidth, h, hw]

theorem bounded_zero_iff_core_infinite [Infinite α] (H : Set (Set α)) :
    HasBoundedWitnesses H 0 ↔ (⋂₀ H).Infinite := by
  classical
  constructor
  · rintro ⟨T, hT, hd⟩
    have he (L) (hL : L ∈ H) : T L = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hd L hL))
    by_cases hH : H.Nonempty
    · obtain ⟨L, hL⟩ := hH
      have ha : (active H T ∅).Nonempty := ⟨L, hL, by simp [he L hL]⟩
      apply (hT.2 ∅ ha).mono
      intro x hx K hK
      exact hx K ⟨hK, by simp [he K hK]⟩
    · have hh : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hH
      simpa [hh] using (Set.infinite_univ : (Set.univ : Set α).Infinite)
  · intro hcore
    refine ⟨fun _ => ∅, ⟨by simp [Positive], ?_⟩, by simp⟩
    intro S _
    apply hcore.mono
    intro x hx L hL
    exact hx L hL.1

theorem width_zero_iff [Infinite α] (H : Set (Set α)) :
    separationWidth H = finiteValue 0 ↔ (⋂₀ H).Infinite := by
  rw [← bounded_zero_iff_core_infinite, ← width_le_finite_iff]
  have hzero : finiteValue 0 = (⊥ : SeparationValue) := rfl
  rw [hzero, le_bot_iff]

end GenLimit.FiniteWitness
