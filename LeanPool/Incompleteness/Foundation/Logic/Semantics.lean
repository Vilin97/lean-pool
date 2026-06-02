/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.LogicSymbol

/-!
# Basic definitions and properties of semantics-related notions

This file defines the semantics of formulas based on Tarski's truth definitions.
Also provides 𝓜 characterization of compactness.

## Main Definitions
* `LO.Semantics`: The realization of 𝓜 formula.
* `LO.Compact`: The semantic compactness of Foundation.

## Notation
* `𝓜 ⊧ φ`: a proposition that states `𝓜` satisfies `φ`.
* `𝓜 ⊧* T`: a proposition that states that `𝓜` satisfies each formulae in a set `T`.

-/

namespace LO

/-- Imported declaration from the Incompleteness formalization. -/
class Semantics (F : outParam Type*) (M : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Realize : M → F → Prop

variable {M : Type*} {F : Type*} [𝓢 : Semantics F M]

namespace Semantics

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊧ " => Realize

section «lp_section_1»

variable [LogicalConnective F] (M)

/-- Imported declaration from the Incompleteness formalization. -/
protected class Top where
  realize_top (𝓜 : M) : 𝓜 ⊧ (⊤ : F)

/-- Imported declaration from the Incompleteness formalization. -/
protected class Bot where
  realize_bot (𝓜 : M) : ¬𝓜 ⊧ (⊥ : F)

/-- Imported declaration from the Incompleteness formalization. -/
protected class And where
  realize_and {𝓜 : M} {φ ψ : F} : 𝓜 ⊧ φ ⋏ ψ ↔ 𝓜 ⊧ φ ∧ 𝓜 ⊧ ψ

/-- Imported declaration from the Incompleteness formalization. -/
protected class Or where
  realize_or {𝓜 : M} {φ ψ : F} : 𝓜 ⊧ φ ⋎ ψ ↔ 𝓜 ⊧ φ ∨ 𝓜 ⊧ ψ

/-- Imported declaration from the Incompleteness formalization. -/
protected class Imp where
  realize_imp {𝓜 : M} {φ ψ : F} : 𝓜 ⊧ φ ==> ψ ↔ (𝓜 ⊧ φ → 𝓜 ⊧ ψ)

/-- Imported declaration from the Incompleteness formalization. -/
protected class Not where
  realize_not {𝓜 : M} {φ : F} : 𝓜 ⊧ ∼φ ↔ ¬𝓜 ⊧ φ

/-- Imported declaration from the Incompleteness formalization. -/
class Tarski extends
  Semantics.Top M,
  Semantics.Bot M,
  Semantics.And M,
  Semantics.Or M,
  Semantics.Imp M,
  Semantics.Not M
  where


attribute [simp]
  Top.realize_top
  Bot.realize_bot
  Not.realize_not
  And.realize_and
  Or.realize_or
  Imp.realize_imp

variable {M}

variable [Tarski M]

variable {𝓜 : M}

@[simp] lemma realize_iff {φ ψ : F} :
    𝓜 ⊧ φ <=> ψ ↔ ((𝓜 ⊧ φ) ↔ (𝓜 ⊧ ψ)) := by
  simp [LogicalConnective.iff, iff_iff_implies_and_implies]

@[simp] lemma realize_list_conj {l : List F} :
    𝓜 ⊧ l.conj ↔ ∀ φ ∈ l, 𝓜 ⊧ φ := by induction l <;> simp [*]

@[simp] lemma realize_finset_conj {s : Finset F} :
    𝓜 ⊧ s.conj ↔ ∀ φ ∈ s, 𝓜 ⊧ φ := by simp [Finset.conj]

@[simp] lemma realize_list_disj {l : List F} :
    𝓜 ⊧ l.disj ↔ ∃ φ ∈ l, 𝓜 ⊧ φ := by induction l <;> simp [*]

@[simp] lemma realize_finset_disj {s : Finset F} :
    𝓜 ⊧ s.disj ↔ ∃ φ ∈ s, 𝓜 ⊧ φ := by simp [Finset.disj]

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
class RealizeSet (𝓜 : M) (T : Set F) : Prop where
  all_realize : ∀ ⦃f⦄, f ∈ T → Realize 𝓜 f

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊧* " => RealizeSet

variable (M)

/-- Imported declaration from the Incompleteness formalization. -/
def Valid (f : F) : Prop := ∀ 𝓜 : M, 𝓜 ⊧ f

/-- Imported declaration from the Incompleteness formalization. -/
def Satisfiable (T : Set F) : Prop := ∃ 𝓜 : M, 𝓜 ⊧* T

/-- Imported declaration from the Incompleteness formalization. -/
def models (T : Set F) : Set M := {𝓜 | 𝓜 ⊧* T}

variable {M}

/-- Imported declaration from the Incompleteness formalization. -/
def theory (𝓜 : M) : Set F := {φ | 𝓜 ⊧ φ}

/-- Imported declaration from the Incompleteness formalization. -/
class Meaningful (𝓜 : M) : Prop where
  exists_unrealize : ∃ f, ¬𝓜 ⊧ f

instance [LogicalConnective F] [Semantics.Bot M] (𝓜 : M) : Meaningful 𝓜 := ⟨⟨⊥, by simp⟩⟩

lemma meaningful_iff {𝓜 : M} : Meaningful 𝓜 ↔ ∃ f, ¬𝓜 ⊧ f :=
  ⟨by rintro ⟨h⟩; exact h, fun h ↦ ⟨h⟩⟩

lemma not_meaningful_iff (𝓜 : M) : ¬Meaningful 𝓜 ↔ ∀ f, 𝓜 ⊧ f := by simp [meaningful_iff]

lemma realizeSet_iff {𝓜 : M} {T : Set F} : 𝓜 ⊧* T ↔ ∀ ⦃f⦄, f ∈ T → Realize 𝓜 f :=
  ⟨by rintro ⟨h⟩ f hf; exact h hf, by intro h; exact ⟨h⟩⟩

lemma not_satisfiable_finset [LogicalConnective F] [Tarski M] [DecidableEq F] (t : Finset F) :
    ¬Satisfiable M (t : Set F) ↔ Valid M (t.image (∼·)).disj := by
  simp [Satisfiable, realizeSet_iff, Valid]

lemma satisfiableSet_iff_models_nonempty {T : Set F} :
    Satisfiable M T ↔ (models M T).Nonempty :=
  ⟨by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩, by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩⟩

namespace RealizeSet

lemma realize {T : Set F} (𝓜 : M) [𝓜 ⊧* T] (hf : f ∈ T) : 𝓜 ⊧ f :=
  all_realize hf

lemma of_subset {T U : Set F} {𝓜 : M} (h : 𝓜 ⊧* U) (ss : T ⊆ U) : 𝓜 ⊧* T :=
  ⟨fun _ hf => h.all_realize (ss hf)⟩

lemma of_subset' {T U : Set F} {𝓜 : M} [𝓜 ⊧* U] (ss : T ⊆ U) : 𝓜 ⊧* T :=
  of_subset (𝓜 := 𝓜) inferInstance ss

instance empty' (𝓜 : M) : 𝓜 ⊧* (∅ : Set F) := ⟨by simp⟩

@[simp] lemma empty (𝓜 : M) : 𝓜 ⊧* (∅ : Set F) := ⟨by simp⟩

@[simp] lemma singleton_iff {f : F} {𝓜 : M} :
    𝓜 ⊧* {f} ↔ 𝓜 ⊧ f := by simp [realizeSet_iff]

@[simp] lemma insert_iff {T : Set F} {f : F} {𝓜 : M} :
    𝓜 ⊧* insert f T ↔ 𝓜 ⊧ f ∧ 𝓜 ⊧* T := by
  simp [realizeSet_iff]

@[simp] lemma union_iff {T U : Set F} {𝓜 : M} :
    𝓜 ⊧* T ∪ U ↔ 𝓜 ⊧* T ∧ 𝓜 ⊧* U := by
  simp only [realizeSet_iff, Set.mem_union, or_imp, forall_and]

@[simp] lemma image_iff {ι} {f : ι → F} {A : Set ι} {𝓜 : M} :
    𝓜 ⊧* f '' A ↔ ∀ i ∈ A, 𝓜 ⊧ (f i) := by simp [realizeSet_iff]

@[simp] lemma range_iff {ι} {f : ι → F} {𝓜 : M} :
    𝓜 ⊧* Set.range f ↔ ∀ i, 𝓜 ⊧ (f i) := by simp [realizeSet_iff]

@[simp] lemma setOf_iff {P : F → Prop} {𝓜 : M} :
    𝓜 ⊧* setOf P ↔ ∀ f, P f → 𝓜 ⊧ f := by simp [realizeSet_iff]

end RealizeSet

lemma valid_neg_iff [LogicalConnective F] [Tarski M] (f : F) :
    Valid M (∼f) ↔ ¬Satisfiable M {f} := by
  simp [Valid, Satisfiable]

lemma _root_.LO.Semantics.Satisfiable.of_subset {T U : Set F} (h : Satisfiable M U) (ss : T ⊆ U) :
    Satisfiable M T := by
  rcases h with ⟨𝓜, h⟩; exact ⟨𝓜, RealizeSet.of_subset h ss⟩

variable (M)

instance : Semantics F (Set M) := ⟨fun s f ↦ ∀ ⦃𝓜⦄, 𝓜 ∈ s → 𝓜 ⊧ f⟩

@[simp] lemma empty_models (f : F) : (∅ : Set M) ⊧ f := by rintro h; simp

/-- Imported declaration from the Incompleteness formalization. -/
def Consequence (T : Set F) (f : F) : Prop := models M T ⊧ f

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)
/-- Imported declaration from the Incompleteness formalization. -/
notation T:45 " ⊨[" M "] " φ:46 => Consequence M T φ

variable {M}

lemma set_models_iff {s : Set M} : s ⊧ f ↔ ∀ 𝓜 ∈ s, 𝓜 ⊧ f := iff_of_eq rfl

instance [LogicalConnective F] [Semantics.Top M] :
    Semantics.Top (Set M) :=
  ⟨fun s ↦ by simp [set_models_iff]⟩

lemma set_meaningful_iff_nonempty [LogicalConnective F] [∀ 𝓜 : M, Meaningful 𝓜] {s : Set M} :
    Meaningful s ↔ s.Nonempty :=
  ⟨by rintro ⟨f, hf⟩; by_contra A; rcases Set.not_nonempty_iff_eq_empty.mp A; simp at hf,
   by rintro ⟨𝓜, h𝓜⟩
      have hMeaningful : Meaningful (F := F) 𝓜 := inferInstance
      rcases hMeaningful.exists_unrealize with ⟨f, hf⟩
      exact ⟨f, fun hs => hf (set_models_iff.mp hs 𝓜 h𝓜)⟩⟩

lemma meaningful_iff_satisfiableSet [LogicalConnective F] [∀ 𝓜 : M, Meaningful 𝓜] :
    Satisfiable M T ↔ Meaningful (models M T) := by
  simp [set_meaningful_iff_nonempty, satisfiableSet_iff_models_nonempty]

lemma consequence_iff {T : Set F} {f} : T ⊨[M] f ↔ ∀ {𝓜 : M}, 𝓜 ⊧* T → 𝓜 ⊧ f := iff_of_eq rfl

lemma consequence_iff' {T : Set F} {f : F} : T ⊨[M] f ↔ (∀ (𝓜 : M) [𝓜 ⊧* T], 𝓜 ⊧ f) :=
  ⟨fun h _ _ => consequence_iff.mp h inferInstance, fun H 𝓜 hs => @H 𝓜 hs⟩

lemma consequence_iff_not_satisfiable [LogicalConnective F] [Tarski M] {f : F} :
    T ⊨[M] f ↔ ¬Satisfiable M (insert (∼f) T) := by
  rw [consequence_iff]
  unfold Satisfiable
  constructor
  · intro h hs
    rcases hs with ⟨𝓜, hs⟩
    have hparts : 𝓜 ⊧ ∼f ∧ 𝓜 ⊧* T := by simpa using hs
    have : 𝓜 ⊧ f := h hparts.2
    exact (Semantics.Not.realize_not.mp hparts.1) this
  · intro h 𝓜 hT
    by_contra hf
    exact h ⟨𝓜, by
      exact RealizeSet.insert_iff.mpr ⟨by simpa using hf, hT⟩⟩

lemma weakening {T U : Set F} {f} (h : T ⊨[M] f) (ss : T ⊆ U) : U ⊨[M] f :=
  consequence_iff.mpr fun hs => consequence_iff.mp h (RealizeSet.of_subset hs ss)

lemma of_mem {T : Set F} {f} (h : f ∈ T) : T ⊨[M] f := fun _ hs => hs.all_realize h

end Semantics

/-- Imported declaration from the Incompleteness formalization. -/
def Cumulative (T : ℕ → Set F) : Prop := ∀ s, T s ⊆ T (s + 1)

namespace Cumulative

lemma subset_of_le {T : ℕ → Set F} (H : Cumulative T)
    {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : T s₁ ⊆ T s₂ := by
  suffices ∀ s d, T s ⊆ T (s + d) by
    simpa[Nat.add_sub_of_le h] using this s₁ (s₂ - s₁)
  intro s d
  induction d with
  | zero => simp
  | succ d ih => simpa only [Nat.add_succ, add_zero] using subset_trans ih (H (s + d))

lemma finset_mem {T : ℕ → Set F}
    (H : Cumulative T) {u : Finset F} (hu : ↑u ⊆ ⋃ s, T s) : ∃ s, ↑u ⊆ T s := by
  haveI := Classical.decEq
  induction u using Finset.induction
  case empty => exact ⟨0, by simp⟩
  case insert f u _ ih =>
    simp only [Finset.coe_insert] at hu
    have : ∃ s, ↑u ⊆ T s := ih (subset_trans (Set.subset_insert _ _) hu)
    rcases this with ⟨s, hs⟩
    have : ∃ s', f ∈ T s' := by simpa using (Set.insert_subset_iff.mp hu).1
    rcases this with ⟨s', hs'⟩
    exact ⟨max s s', by
      simp only [Finset.coe_insert]
      exact Set.insert_subset
        (subset_of_le H (Nat.le_max_right s s') hs')
        (subset_trans hs (subset_of_le H <| Nat.le_max_left s s'))⟩

end Cumulative

variable (M)

/-- Imported declaration from the Incompleteness formalization. -/
class Compact : Prop where
  compact {T : Set F} :
    Semantics.Satisfiable M T ↔ (∀ u : Finset F, ↑u ⊆ T → Semantics.Satisfiable M (u : Set F))

variable {M}

namespace Compact

variable [Compact M]

variable {𝓜 : M}

lemma conseq_compact [LogicalConnective F] [Semantics.Tarski M] {f : F} :
    T ⊨[M] f ↔ ∃ u : Finset F, ↑u ⊆ T ∧ u ⊨[M] f := by
  classical
  simp only [Semantics.consequence_iff_not_satisfiable, compact (T := insert (∼f) T),
    not_forall]
  constructor
  · intro ⟨u, ss, hu⟩
    exact ⟨Finset.erase u (∼f), by simp [ss],
      by
        simp only [Finset.coe_erase, Set.insert_diff_singleton]
        intro h
        exact hu (Semantics.Satisfiable.of_subset h (by simp))⟩
  · intro ⟨u, ss, hu⟩
    exact ⟨insert (∼f) u,
      by simpa using Set.insert_subset_insert ss, by simpa using hu⟩

lemma compact_cumulative {T : ℕ → Set F} (hT : Cumulative T) :
    Semantics.Satisfiable M (⋃ s, T s) ↔ ∀ s, Semantics.Satisfiable M (T s) :=
  ⟨by intro H s
      exact H.of_subset (Set.subset_iUnion T s),
   by intro H
      apply compact.mpr
      intro u hu
      rcases hT.finset_mem hu with ⟨s, hs⟩
      exact (H s).of_subset hs ⟩

end Compact

end LO
