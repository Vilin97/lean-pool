/-
Copyright (c) 2026 Shuangping Li, Peng Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuangping Li, Peng Zhang
-/
module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Set.Basic

/-!
# Language generation in the limit: basic definitions

This file fixes a countable universe `ℕ` and an indexed family of languages.
The family is indexed, rather than represented as a set of sets, because the
Kleinberg--Mullainathan algorithm depends on the enumeration order and permits
repeated languages.
-/

public section

namespace GenLimit

/- These inherited definitions fix the universe as `ℕ`. The arbitrary-universe
interfaces used by this project are in `Core.GenericGeneration` and
`Core.ClassGeneration`; the width hierarchy is transported along equivalences
in `FiniteWitness.Width.Transport`. -/
/-- A language over the countable universe `ℕ`. -/
abbrev Language := Set ℕ

/-- An indexed family of languages. Repeated languages are permitted. -/
abbrev LanguageFamily := ℕ → Language

/-- A stream is an exact presentation of `L` when its range is exactly `L`. -/
def Presents (stream : ℕ → ℕ) (L : Language) : Prop :=
  Set.range stream = L

/-- The set of observations strictly before time `t`. -/
def sample (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).image stream

/-- Candidate `i` is consistent with all observations strictly before `t`. -/
def Consistent (C : LanguageFamily) (stream : ℕ → ℕ) (t i : ℕ) : Prop :=
  ↑(sample stream t) ⊆ C i

/-- A Boolean membership oracle, uniform in the language index and element. -/
structure MembershipOracle (C : LanguageFamily) where
  /-- Decide whether an element belongs to the language with the given index. -/
  query : ℕ → ℕ → Bool
  query_spec : query i u = true ↔ u ∈ C i

theorem mem_sample_iff {stream : ℕ → ℕ} {t u : ℕ} :
    u ∈ sample stream t ↔ ∃ s < t, stream s = u := by
  simp [sample]

theorem sample_mono {stream : ℕ → ℕ} {s t : ℕ} (hst : s ≤ t) :
    sample stream s ⊆ sample stream t := by
  intro u hu
  rw [mem_sample_iff] at hu ⊢
  obtain ⟨r, hrs, hru⟩ := hu
  exact ⟨r, lt_of_lt_of_le hrs hst, hru⟩

theorem value_mem_sample {stream : ℕ → ℕ} {s t : ℕ} (hst : s < t) :
    stream s ∈ sample stream t := by
  rw [mem_sample_iff]
  exact ⟨s, hst, rfl⟩

theorem mem_language_of_mem_sample_of_presents
    {stream : ℕ → ℕ} {L : Language} (hP : Presents stream L)
    {t u : ℕ} (hu : u ∈ sample stream t) : u ∈ L := by
  rw [← hP]
  rw [mem_sample_iff] at hu
  obtain ⟨s, -, rfl⟩ := hu
  exact ⟨s, rfl⟩

/-- Any candidate containing the presented target is consistent at every
time. -/
theorem consistent_of_target_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z i t : ℕ}
    (hP : Presents stream (C z)) (hsub : C z ⊆ C i) :
    Consistent C stream t i := by
  intro u hu
  exact hsub (mem_language_of_mem_sample_of_presents hP hu)

theorem eventually_mem_sample_of_presents
    {stream : ℕ → ℕ} {L : Language} (hP : Presents stream L)
    {u : ℕ} (hu : u ∈ L) : ∃ T, ∀ t, T ≤ t → u ∈ sample stream t := by
  rw [← hP] at hu
  obtain ⟨s, rfl⟩ := hu
  refine ⟨s + 1, ?_⟩
  intro t ht
  rw [mem_sample_iff]
  exact ⟨s, lt_of_lt_of_le (Nat.lt_succ_self s) ht, rfl⟩

theorem presents_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {z t : ℕ}
    (hP : Presents stream (C z)) : Consistent C stream t z := by
  exact consistent_of_target_subset hP Set.Subset.rfl

theorem eventually_not_consistent_of_not_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {z i : ℕ}
    (hP : Presents stream (C z)) (hbad : ¬ C z ⊆ C i) :
    ∃ T, ∀ t, T ≤ t → ¬ Consistent C stream t i := by
  obtain ⟨u, huz, hui⟩ := Set.not_subset.mp hbad
  obtain ⟨T, hT⟩ := eventually_mem_sample_of_presents hP huz
  refine ⟨T, ?_⟩
  intro t ht hcon
  exact hui (hcon (hT t ht))

end GenLimit
