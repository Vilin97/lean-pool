/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import LeanPool.Redhill.Common.PairwiseCoprime
import LeanPool.Redhill.Common.Quality
import LeanPool.Redhill.Common.SubsumCondition

/-!
# Definitions of the tuple sets and conjectures considered in the paper
-/


open Finset

/-- The **abc conjecture** itself, using `quality`. -/
def ABCConjecture : Prop :=
  quality {a : Fin 3 → ℤ | ∑ i, a i = 0 ∧ univ.gcd a = 1} = 1

/-- The tuples in Browkin and Brzeziński's `n`-conjecture. `A(n)` in the paper. -/
def nConjectureTuples (n : ℕ) : Set (Fin n → ℤ) :=
  {a | ∑ i, a i = 0 ∧ SSC a ∧ univ.gcd a = 1}

/-- Browkin and Brzeziński's **`n`-conjecture** for a fixed `n`.
The conjecture itself is `∀ n ≥ 3, NConjecture n`. -/
def NConjecture (n : ℕ) : Prop :=
  quality (nConjectureTuples n) = (2 * n - 5 : ℕ)

/-- The tuples in Browkin's strong `n`-conjecture. `B(n)` in the paper. -/
def strongNConjectureTuples (n : ℕ) : Set (Fin n → ℤ) :=
  {a | ∑ i, a i = 0 ∧ PairwiseCoprime a}

/-- Browkin's **strong `n`-conjecture** for a fixed `n`.
The conjecture itself is `∀ n ≥ 3, StrongNConjecture n`. -/
def StrongNConjecture (n : ℕ) : Prop :=
  quality (strongNConjectureTuples n) < ⊤

/-- The tuples in Ramaekers's conjecture. `R(n)` in the paper. -/
def ramaekersTuples (n : ℕ) : Set (Fin n → ℤ) :=
  {a | ∑ i, a i = 0 ∧ SSC a ∧ PairwiseCoprime a}

/-- **Ramaekers's conjecture** for a fixed `n`.
The conjecture itself is `∀ n ≥ 3, RamaekersConjecture n`. -/
def RamaekersConjecture (n : ℕ) : Prop :=
  quality (ramaekersTuples n) = 1

/-- `U(F,n)` in the paper. -/
def factorFreeTuples (F : Finset ℕ) (n : ℕ) : Set (Fin n → ℤ) :=
  {a | ∑ i, a i = 0 ∧ StrongSSC a ∧ PairwiseCoprime a ∧ ∀ f ∈ F, ∀ i, ¬↑f ∣ a i}

lemma nConjecture_3_iff_ABC : NConjecture 3 ↔ ABCConjecture := by
  norm_num [NConjecture, ABCConjecture, nConjectureTuples]
  suffices hf : {a : Fin 3 → ℤ | ¬SSC a ∧ ∑ i, a i = 0 ∧ univ.gcd a = 1}.Finite by
    have := quality_union_finite (A := {a : Fin 3 → ℤ | SSC a ∧ ∑ i, a i = 0 ∧ univ.gcd a = 1}) hf
    simp_rw [← Set.setOf_or, ← or_and_right, or_not, true_and] at this
    simp [this, and_left_comm]
  set E := {a : Fin 3 → ℤ | ¬SSC a ∧ ∑ i, a i = 0 ∧ univ.gcd a = 1}
  have r₀ {a} (ma : a ∈ E) : 0 ∈ Set.range a := by
    simp_rw [E, Set.mem_setOf, SSC] at ma
    push Not at ma
    obtain ⟨⟨q, nq, nqc, sq⟩, sqc, -⟩ := ma
    rw [← sum_add_sum_compl q, sq, zero_add] at sqc
    have cacq : #q + #qᶜ = 3 := by simp
    all_goals grind [card_eq_one]
  have sE : E ⊆ {a | ∀ i, a i ∈ Set.Icc (-1) 1} := fun a ma ↦ by
    obtain ⟨i₀, hi₀⟩ := r₀ ma
    obtain ⟨-, sa, ga⟩ := ma
    have ueq : (univ : Finset (Fin 3)) = {i₀, i₀ + 1, i₀ + 2} := by grind
    rw [ueq, sum_insert (by simp), hi₀, zero_add, sum_pair (by simp), add_eq_zero_iff_eq_neg] at sa
    rw [ueq, gcd_insert, ← Int.coe_gcd, hi₀, Int.gcd_zero_left, gcd_insert, gcd_singleton,
      ← Int.abs_eq_normalize, ← abs_neg, ← sa, Int.abs_eq_normalize, ← gcd_singleton, ← gcd_insert,
      pair_eq_singleton, gcd_singleton, ← Int.abs_eq_normalize, Nat.cast_eq_one,
      Int.natAbs_abs, Int.natAbs_eq_iff, Nat.cast_one] at ga
    have ga' : a (i₀ + 2) = 1 ∨ a (i₀ + 2) = -1 := by grind
    intro i
    have mi := ueq ▸ mem_univ i
    simp only [mem_insert, mem_singleton] at mi
    obtain rfl | rfl | rfl := mi
    all_goals grind
  exact (Set.Finite.pi' fun _ ↦ Set.finite_Icc ..).subset sE

variable {n : ℕ} {F F' : Finset ℕ}

lemma quality_factorFreeTuples_anti (hF : F ⊆ F') :
    quality (factorFreeTuples F' n) ≤ quality (factorFreeTuples F n) :=
  quality_mono fun _ ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, fun f mf ↦ h₄ f (hF mf)⟩

lemma quality_factorFreeTuples_le_nConjectureTuples (hn : 2 ≤ n) :
    quality (factorFreeTuples F n) ≤ quality (nConjectureTuples n) :=
  quality_mono fun _ ⟨h₁, h₂, h₃, _⟩ ↦ ⟨h₁, h₂.SSC, gcd_one_of_pairwiseCoprime hn h₃⟩

lemma quality_factorFreeTuples_le_ramaekersTuples :
    quality (factorFreeTuples F n) ≤ quality (ramaekersTuples n) :=
  quality_mono fun _ ⟨h₁, h₂, h₃, _⟩ ↦ ⟨h₁, h₂.SSC, h₃⟩

lemma quality_ramaekersTuples_le_strongNConjectureTuples :
    quality (ramaekersTuples n) ≤ quality (strongNConjectureTuples n) :=
  quality_mono fun _ ⟨h₁, _, h₃⟩ ↦ ⟨h₁, h₃⟩
