/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.AnchoredUpper
public import Mathlib.Tactic.Push

/-!
# An explicit family with finite witnesses of unbounded size
-/

@[expose] public section

namespace GenLimit.FiniteWitness.TwoCore

/-- The two-copy universe shared with the anchored hierarchy examples. -/
abbrev Point := Anchored.Point

/-- A language contains the entire left copy of the natural numbers. -/
def HasLeft (L : Set Point) : Prop := ∀ n, Sum.inl n ∈ L
/-- A language contains the entire right copy of the natural numbers. -/
def HasRight (L : Set Point) : Prop := ∀ n, Sum.inr n ∈ L
/-- The languages containing at least one of the two infinite copies. -/
def family : Set (Set Point) := {L | HasLeft L ∨ HasRight L}

/-- A full left copy together with an arbitrary subset of the right copy. -/
def leftTarget (D : Set ℕ) : Set Point := Sum.elim (fun _ => True) (fun n => n ∈ D)
/-- A full right copy together with an arbitrary subset of the left copy. -/
def rightTarget (E : Set ℕ) : Set Point := Sum.elim (fun n => n ∈ E) (fun _ => True)

@[simp] theorem inl_left (D : Set ℕ) (n : ℕ) : Sum.inl n ∈ leftTarget D := trivial
@[simp] theorem inr_right (E : Set ℕ) (n : ℕ) : Sum.inr n ∈ rightTarget E := trivial
@[simp] theorem inr_left (D : Set ℕ) (n : ℕ) : Sum.inr n ∈ leftTarget D ↔ n ∈ D := Iff.rfl
@[simp] theorem inl_right (E : Set ℕ) (n : ℕ) : Sum.inl n ∈ rightTarget E ↔ n ∈ E := Iff.rfl

theorem left_mem (D : Set ℕ) : leftTarget D ∈ family := Or.inl (fun _ => trivial)
theorem right_mem (E : Set ℕ) : rightTarget E ∈ family := Or.inr (fun _ => trivial)

theorem family_uus : Generic.UUS family := by
  intro L hL
  rcases hL with hL | hL
  · exact (Set.infinite_range_of_injective (Sum.inl_injective : Function.Injective
      (Sum.inl : ℕ → Point))).mono (by rintro _ ⟨n, rfl⟩; exact hL n)
  · exact (Set.infinite_range_of_injective (Sum.inr_injective : Function.Injective
      (Sum.inr : ℕ → Point))).mono (by rintro _ ⟨n, rfl⟩; exact hL n)

/-- Witness a missing point in one copy by a finite initial segment of the other copy. -/
noncomputable def assignment (L : Set Point) : Finset Point := by
  classical
  exact if h : ∃ n, Sum.inr n ∉ L then (Finset.range (Nat.find h + 1)).image Sum.inl
    else if h : ∃ n, Sum.inl n ∉ L then (Finset.range (Nat.find h + 1)).image Sum.inr
    else ∅

theorem assignment_positive : Positive family assignment := by
  classical
  intro L hL x hx
  by_cases hR : ∃ n, Sum.inr n ∉ L
  · rw [assignment, dite_eq_left hR] at hx
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
    rcases hL with hL | hL
    · exact hL n
    · exact (hR.choose_spec (hL hR.choose)).elim
  · by_cases hL' : ∃ n, Sum.inl n ∉ L
    · rw [assignment, dite_eq_right hR, dite_eq_left hL'] at hx
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
      by_contra hn
      exact hR ⟨n, hn⟩
    · simp [assignment, hR, hL'] at hx

theorem no_cross {L K : Set Point} (_ : HasLeft L) (hR : HasRight K)
    (hnR : ¬ HasRight L) (hnL : ¬ HasLeft K) :
    ¬ ((↑(assignment L) : Set Point) ⊆ K ∧ (↑(assignment K) : Set Point) ⊆ L) := by
  classical
  have hmR : ∃ n, Sum.inr n ∉ L := not_forall.mp hnR
  have hmL : ∃ n, Sum.inl n ∉ K := not_forall.mp hnL
  have hnK : ¬ ∃ n, Sum.inr n ∉ K := by rintro ⟨n, hn⟩; exact hn (hR n)
  rintro ⟨hLK, hKL⟩
  by_cases hle : Nat.find hmL ≤ Nat.find hmR
  · apply Nat.find_spec hmL
    apply hLK
    rw [assignment, dite_eq_left hmR]
    exact Finset.mem_image.mpr ⟨Nat.find hmL, Finset.mem_range.mpr (by omega), rfl⟩
  · apply Nat.find_spec hmR
    apply hKL
    rw [assignment, dite_eq_right hnK, dite_eq_left hmL]
    exact Finset.mem_image.mpr ⟨Nat.find hmR, Finset.mem_range.mpr (by omega), rfl⟩

theorem assignment_valid : Valid family assignment := by
  classical
  refine ⟨assignment_positive, ?_⟩
  intro S _
  by_cases hall : ∀ L ∈ active family assignment S, HasLeft L
  · apply (Set.infinite_range_of_injective (Sum.inl_injective : Function.Injective
      (Sum.inl : ℕ → Point))).mono
    rintro _ ⟨n, rfl⟩ L hL
    exact hall L hL n
  · push Not at hall
    obtain ⟨K, hK, hnK⟩ := hall
    have hrK : HasRight K := hK.1.resolve_left hnK
    apply (Set.infinite_range_of_injective (Sum.inr_injective : Function.Injective
      (Sum.inr : ℕ → Point))).mono
    rintro _ ⟨n, rfl⟩ L hL
    by_cases hrL : HasRight L
    · exact hrL n
    · have hlL : HasLeft L := hL.1.resolve_right hrL
      exact (no_cross hlL hrK hrL hnK ⟨fun x hx => hK.2.2 (hL.2.1 hx),
        fun x hx => hL.2.2 (hK.2.1 hx)⟩).elim

theorem anchored_subset (k : ℕ) : Anchored.family k ⊆ family := by
  rintro L (⟨⟨i, D⟩, rfl⟩ | ⟨⟨j, E⟩, rfl⟩)
  · exact Or.inl (fun _ => trivial)
  · exact Or.inr (fun _ => trivial)

theorem no_finite_bound (d : ℕ) : ¬ HasBoundedWitnesses family d := by
  intro h
  have hl := Anchored.lower_bound (h.mono (anchored_subset (2 * d + 1)))
  omega

theorem exact_width : separationWidth family = omegaValue :=
  (width_eq_omega_iff family).mpr ⟨assignment_valid.hasFiniteWitnesses, no_finite_bound⟩

theorem ordinary : Generic.GeneratableInLimit family :=
  (ordinary_iff_finiteWitnesses family family_uus).mpr assignment_valid.hasFiniteWitnesses

end GenLimit.FiniteWitness.TwoCore
