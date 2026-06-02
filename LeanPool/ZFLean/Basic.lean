/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/

import Mathlib.SetTheory.ZFC.Basic

/-!
# LeanPool.ZFLean.Basic

Imported Lean Pool material for `LeanPool.ZFLean.Basic`.
-/
noncomputable section

namespace ZFSet

theorem nonempty_exists_iff {n : ZFSet} : n ≠ ∅ ↔ ∃ m, m ∈ n := by
  simp [ZFSet.ext_iff]

@[simp] theorem not_nonempty_is_empty {x : ZFSet} : ¬x.Nonempty ↔ x = ∅ := by
  rw [nonempty_def, not_exists, eq_empty]

theorem subset_of_empty {x : ZFSet} (h : x ⊆ ∅) : x = ∅ := by
  ext1 z
  constructor
  · intro hz
    exact h hz
  · intro hz
    nomatch notMem_empty z hz

theorem sep_subset_self {P : ZFSet → Prop} {a : ZFSet} : a.sep P ⊆ a := by
  intros x hx
  rw [mem_sep] at hx
  exact hx.left

theorem sUnion_insert {x : ZFSet} : (⋃₀ (insert x x) : ZFSet) = x ∪ (⋃₀ x : ZFSet) := by
  ext1
  simp only [mem_sUnion, mem_insert_iff, exists_eq_or_imp, mem_union]

theorem singleton_subset_mem_iff {x y : ZFSet} : {x} ⊆ y ↔ x ∈ y := by
  simp [subset_def]

theorem insert_def {x y : ZFSet} : insert x y = {x} ∪ y := by
  ext1 z
  rw [mem_insert_iff, mem_union, mem_singleton]

theorem sInter_pair {a b : ZFSet} : ⋂₀ {a, b} = a ∩ b := by
  ext1 x
  constructor
  · intro h
    rw [mem_sInter (by simp only [nonempty_def, mem_insert_iff, exists_or_eq_left])] at h
    simp only [mem_insert_iff, mem_singleton, forall_eq_or_imp, forall_eq] at h
    rwa [← mem_inter] at h
  · intro h
    rw [mem_sInter (by simp only [nonempty_def, mem_insert_iff, exists_or_eq_left])]
    simp only [mem_insert_iff, mem_singleton, forall_eq_or_imp, forall_eq]
    rwa [← mem_inter]

@[simp]
theorem sep_empty_iff {A : ZFSet} {P : ZFSet → Prop} : A.sep P = ∅ ↔ (A = ∅ ∨ ∀ x ∈ A, ¬ P x) where
  mp h := by classical
    by_cases A_emp : A = ∅
    · left; assumption
    · right
      intros x mem_x_A
      by_contra contr
      have : x ∈ A.sep P := by
        rw [mem_sep]
        exact ⟨mem_x_A, contr⟩
      rw [h] at this
      nomatch this, notMem_empty _
  mpr h := by classical
    rcases h with rfl | h
    · exact sep_empty P
    · ext1 z
      constructor
      · intro hz
        rw [mem_sep] at hz
        nomatch h _ hz.left, hz.right
      · intro hz
        nomatch notMem_empty z, hz

theorem insert_prod {A B x : ZFSet} : (insert x A).prod B = A.prod B ∪ ({x} : ZFSet).prod B := by
  ext1 z
  simp only [mem_prod, mem_insert_iff, exists_eq_or_imp, mem_union, mem_singleton, exists_eq_left]
  constructor
  · rintro (⟨b, bB, rfl⟩ | ⟨a, aA, b, bB, rfl⟩)
    · simp only [pair_inj, exists_eq_right_right', true_and, exists_eq_right']
      right
      exact bB
    · simp only [pair_inj, exists_eq_right_right']
      left
      exact ⟨aA, bB⟩
  · rintro (⟨a, aA, b, bB, rfl⟩ | ⟨b, bB, rfl⟩)
    · simp only [pair_inj, exists_eq_right_right']
      right
      exact ⟨aA, bB⟩
    · simp only [pair_inj, true_and, exists_eq_right', exists_eq_right_right']
      left
      exact bB

theorem prod_insert {A B x : ZFSet} : A.prod (insert x B) = A.prod B ∪ A.prod {x} := by
  ext1 z
  simp only [mem_prod, mem_insert_iff, exists_eq_or_imp, mem_union, mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨a, aA, rfl | ⟨b, bB, rfl⟩⟩
    · simp only [pair_inj, exists_eq_right_right', and_true, exists_eq_right']
      right
      exact aA
    · simp only [pair_inj, exists_eq_right_right', existsAndEq, true_and]
      left
      exact ⟨aA, bB⟩
  · rintro (⟨a, aA, b, bB, rfl⟩ | ⟨a, aA, rfl⟩)
    · simp only [pair_inj, exists_eq_right_right']
      exists a, aA
      rw [eq_self, and_true, true_and]
      right
      exact bB
    · simp only [pair_inj, and_true, exists_eq_right_right']
      exists a, aA
      left
      rfl

lemma prod_nonempty {x y : ZFSet} : x ≠ ∅ → y ≠ ∅ → ZFSet.prod x y ≠ ∅ := by
  classical
  intro hx hy h'
  simp only [ZFSet.ext_iff, ZFSet.mem_prod, ZFSet.notMem_empty, iff_false, not_exists,
    not_and, not_forall] at h'
  obtain ⟨a, ha⟩ := nonempty_exists_iff.mp hx
  obtain ⟨b, hb⟩ := nonempty_exists_iff.mp hy
  obtain ⟨_, h'⟩ := h' (a.pair b) _ ha _ hb
  exact h' (Eq.to_iff rfl)

theorem union_empty {A : ZFSet} : A ∪ ∅ = A := by
  ext1
  simp_rw [mem_union, notMem_empty, or_false]

theorem inter_comm {A B : ZFSet} : A ∩ B = B ∩ A := by
  ext1
  simp_rw [mem_inter]
  exact and_comm

theorem union_comm {A B : ZFSet} : A ∪ B = B ∪ A := by
  ext1
  simp_rw [mem_union]
  exact or_comm

theorem empty_union {A : ZFSet} : ∅ ∪ A = A := by
  rw [union_comm]
  exact union_empty

theorem union_mono {x y z : ZFSet} : x ⊆ z → y ⊆ z → x ∪ y ⊆ z := by
  intro hx hy a ha
  rw [ZFSet.mem_union] at ha
  rcases ha with _ | _
  · exact hx ‹_›
  · exact hy ‹_›

theorem inter_mono {x y z : ZFSet} : x ⊆ z → y ⊆ z → x ∩ y ⊆ z := by
  intro hx _ a ha
  rw [ZFSet.mem_inter] at ha
  exact hx ha.1

theorem mem_powerset_self {x : ZFSet} : x ∈ x.powerset := mem_powerset.mpr fun _ => id

theorem inter_self {A : ZFSet} : A ∩ A = A := by
  ext1
  rw [mem_inter]
  exact and_iff_left_of_imp id
theorem inter_empty {A : ZFSet} : A ∩ ∅ = ∅ := by
  ext1
  simp
theorem empty_inter {A : ZFSet} : ∅ ∩ A = ∅ := by
  ext1
  simp
theorem union_self {A : ZFSet} : A ∪ A = A := by
  ext1
  rw [mem_union]
  exact or_iff_left_of_imp id
theorem sep_true {A : ZFSet} : A.sep (fun _ => True) = A := by
  ext1
  rw [mem_sep, and_true]

theorem powerset_mono {x y : ZFSet} : x ⊆ y → x.powerset ⊆ y.powerset := by
  intro hxy z hz
  rw [mem_powerset] at hz ⊢
  exact fun _ => (hxy <| hz ·)

@[simp]
theorem prod_empty_right {x : ZFSet} : x.prod ∅ = ∅ := by
  ext z; simp
@[simp]
theorem prod_empty_left {x : ZFSet} : ZFSet.prod ∅ x = ∅ := by
  ext z; simp

instance ZFSetSProdinst : SProd ZFSet ZFSet ZFSet := ⟨prod⟩

/-- Imported ZFLean declaration. -/
notation " ε " => (Classical.epsilon fun z ↦ z ∈ ·)

theorem epsilon_mem {y : ZFSet} (hy : y ≠ ∅) : ε y ∈ y := by
  exact Classical.epsilon_spec (nonempty_exists_iff.mp hy)

theorem insert_mem {x y : ZFSet} (h : x ∈ y) : insert x y = y := by
  ext1
  rw [mem_insert_iff, or_iff_right_iff_imp]
  rintro rfl
  trivial

theorem eq_of_subset_subset {A B : ZFSet} (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
  ext1 x
  constructor <;> intro h
  · exact hAB (hBA (hAB h))
  · exact hBA (hAB (hBA h))

theorem powerset_inj {A B : ZFSet} (h : A.powerset = B.powerset) : A = B := by
  have A_sub := @ZFSet.mem_powerset_self A
  have B_sub := @ZFSet.mem_powerset_self B
  rw [h, ZFSet.mem_powerset] at A_sub
  rw [←h, ZFSet.mem_powerset] at B_sub
  apply ZFSet.eq_of_subset_subset <;> assumption

theorem prod_inj {A B C D : ZFSet} (h : A.prod B = C.prod D) (hA : A ≠ ∅) (hB : B ≠ ∅) :
    A = C ∧ B = D := by
  obtain ⟨a, ha⟩ := nonempty_exists_iff.mp hA
  obtain ⟨b, hb⟩ := nonempty_exists_iff.mp hB
  obtain ⟨aC, bD⟩ : a ∈ C ∧ b ∈ D := by
    rw [←pair_mem_prod, ←h, pair_mem_prod]
    exact ⟨ha, hb⟩
  rw [ZFSet.ext_iff, ZFSet.ext_iff]
  suffices ∀ x y, (x ∈ A ↔ x ∈ C) ∧ (y ∈ B ↔ y ∈ D) by
    and_intros
    · intro z
      specialize this z b
      exact this.1
    · intro z
      specialize this a z
      exact this.2
  rw [ZFSet.ext_iff] at h
  simp only [mem_prod] at h
  intro x y
  and_intros
  · specialize h (x.pair b)
    simp only [pair_inj, exists_eq_right_right'] at h
    constructor <;> intro hx
    · exact (h.mp ⟨hx, hb⟩).1
    · exact (h.mpr ⟨hx, bD⟩).1
  · specialize h (a.pair y)
    simp only [pair_inj, exists_eq_right_right'] at h
    constructor <;> intro hy
    · exact (h.mp ⟨ha, hy⟩).2
    · exact (h.mpr ⟨aC, hy⟩).2

end ZFSet

end
