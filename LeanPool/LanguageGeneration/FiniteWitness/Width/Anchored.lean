/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
import LeanPool.LanguageGeneration.FiniteWitness.Width.Capture
import LeanPool.LanguageGeneration.FiniteWitness.Width.Cost
import Mathlib.Data.Finset.Preimage

/-!
# Anchored families and their positive witness geometry
-/

namespace GenLimit.FiniteWitness.Anchored

/-- Two disjoint copies of the natural numbers for the anchored hierarchy examples. -/
abbrev Point := ℕ ⊕ ℕ

/-- A full left copy, all right anchors except one, and an arbitrary right tail. -/
def leftTarget {k : ℕ} (i : Fin k) (D : Set ℕ) : Set Point :=
  Sum.elim (fun _ => True) (fun n => if n < k then n ≠ i.val else n - k ∈ D)

/-- A full right copy, all left anchors except one, and an arbitrary left tail. -/
def rightTarget {k : ℕ} (j : Fin k) (E : Set ℕ) : Set Point :=
  Sum.elim (fun n => if n < k then n ≠ j.val else n - k ∈ E) (fun _ => True)

/-- The union of the left and right anchored target families with k anchors. -/
def family (k : ℕ) : Set (Set Point) :=
  Set.range (fun p : Fin k × Set ℕ => leftTarget p.1 p.2) ∪
  Set.range (fun p : Fin k × Set ℕ => rightTarget p.1 p.2)

@[simp] theorem inl_mem_left {k} (i : Fin k) (D : Set ℕ) (n : ℕ) :
    Sum.inl n ∈ leftTarget i D := trivial

@[simp] theorem inr_mem_right {k} (j : Fin k) (E : Set ℕ) (n : ℕ) :
    Sum.inr n ∈ rightTarget j E := trivial

@[simp] theorem inr_mem_left_iff {k} (i : Fin k) (D : Set ℕ) (n : ℕ) :
    Sum.inr n ∈ leftTarget i D ↔ (if n < k then n ≠ i.val else n - k ∈ D) := Iff.rfl

@[simp] theorem inl_mem_right_iff {k} (j : Fin k) (E : Set ℕ) (n : ℕ) :
    Sum.inl n ∈ rightTarget j E ↔ (if n < k then n ≠ j.val else n - k ∈ E) := Iff.rfl

theorem anchor_mem_left {k} (i j : Fin k) (D : Set ℕ) :
    Sum.inr j.val ∈ leftTarget i D ↔ j ≠ i := by
  simp [j.isLt, Fin.val_inj]

theorem anchor_mem_right {k} (i j : Fin k) (E : Set ℕ) :
    Sum.inl i.val ∈ rightTarget j E ↔ i ≠ j := by
  simp [i.isLt, Fin.val_inj]

theorem tail_mem_left {k} (i : Fin k) (D : Set ℕ) (n : ℕ) :
    Sum.inr (k + n) ∈ leftTarget i D ↔ n ∈ D := by
  simp [show ¬ k + n < k by omega]

theorem tail_mem_right {k} (j : Fin k) (E : Set ℕ) (n : ℕ) :
    Sum.inl (k + n) ∈ rightTarget j E ↔ n ∈ E := by
  simp [show ¬ k + n < k by omega]

theorem left_mem_family {k} (i : Fin k) (D : Set ℕ) : leftTarget i D ∈ family k :=
  Or.inl ⟨(i, D), rfl⟩

theorem right_mem_family {k} (j : Fin k) (E : Set ℕ) : rightTarget j E ∈ family k :=
  Or.inr ⟨(j, E), rfl⟩

theorem family_uus (k : ℕ) : Generic.UUS (family k) := by
  rintro L (⟨⟨i, D⟩, rfl⟩ | ⟨⟨j, E⟩, rfl⟩)
  · exact (Set.infinite_range_of_injective (Sum.inl_injective : Function.Injective
      (Sum.inl : ℕ → Point))).mono (by rintro _ ⟨n, rfl⟩; trivial)
  · exact (Set.infinite_range_of_injective (Sum.inr_injective : Function.Injective
      (Sum.inr : ℕ → Point))).mono (by rintro _ ⟨n, rfl⟩; trivial)

theorem left_injective {k} : Function.Injective
    (fun p : Fin k × Set ℕ => leftTarget p.1 p.2) := by
  rintro ⟨i, D⟩ ⟨j, E⟩ he
  change leftTarget i D = leftTarget j E at he
  have hij : i = j := by
    by_contra hn
    have hh : Sum.inr i.val ∈ leftTarget j E := (anchor_mem_left j i E).mpr hn
    rw [← he] at hh
    simp at hh
  subst j
  have hDE : D = E := by
    ext n
    simpa [show ¬ k + n < k by omega] using congrArg (fun L : Set Point => Sum.inr (k + n) ∈ L) he
  subst E
  rfl

theorem right_injective {k} : Function.Injective
    (fun p : Fin k × Set ℕ => rightTarget p.1 p.2) := by
  rintro ⟨i, D⟩ ⟨j, E⟩ he
  change rightTarget i D = rightTarget j E at he
  have hij : i = j := by
    by_contra hn
    have hh : Sum.inl i.val ∈ rightTarget j E := (anchor_mem_right i j E).mpr hn
    rw [← he] at hh
    simp at hh
  subst j
  have hDE : D = E := by
    ext n
    simpa [show ¬ k + n < k by omega] using congrArg (fun L : Set Point => Sum.inl (k + n) ∈ L) he
  subst E
  rfl

theorem left_ne_right {k} (i j : Fin k) (D E : Set ℕ) :
    leftTarget i D ≠ rightTarget j E := by
  intro he
  have h : Sum.inl j.val ∈ leftTarget i D := trivial
  rw [he] at h
  simp at h

/-- The indices of observed right-copy elements beyond the first k anchors. -/
noncomputable def rightTail (k : ℕ) (S : Finset Point) : Finset ℕ :=
  S.preimage (fun n => Sum.inr (k + n)) (fun _ _ _ _ h => Nat.add_left_cancel (Sum.inr.inj h))

@[simp] theorem mem_rightTail (k : ℕ) (S : Finset Point) (n : ℕ) :
    n ∈ rightTail k S ↔ Sum.inr (k + n) ∈ S := Finset.mem_preimage

theorem card_rightTail_le (k : ℕ) (S : Finset Point) : (rightTail k S).card ≤ S.card := by
  classical
  exact (Finset.card_preimage _ _ _).trans_le (Finset.card_filter_le _ _)

/-- The left anchors present in a finite sample. -/
noncomputable def leftAnchors (k : ℕ) (S : Finset Point) : Finset (Fin k) :=
  S.preimage (fun i => Sum.inl i.val) (fun _ _ _ _ h => Fin.ext (Sum.inl.inj h))

/-- The right anchors present in a finite sample. -/
noncomputable def rightAnchors (k : ℕ) (S : Finset Point) : Finset (Fin k) :=
  S.preimage (fun i => Sum.inr i.val) (fun _ _ _ _ h => Fin.ext (Sum.inr.inj h))

@[simp] theorem mem_leftAnchors {k} (S : Finset Point) (i : Fin k) :
    i ∈ leftAnchors k S ↔ Sum.inl i.val ∈ S := Finset.mem_preimage

@[simp] theorem mem_rightAnchors {k} (S : Finset Point) (i : Fin k) :
    i ∈ rightAnchors k S ↔ Sum.inr i.val ∈ S := Finset.mem_preimage

theorem card_leftAnchors_le (k : ℕ) (S : Finset Point) : (leftAnchors k S).card ≤ S.card := by
  classical
  exact (Finset.card_preimage _ _ _).trans_le (Finset.card_filter_le _ _)

theorem card_rightAnchors_le (k : ℕ) (S : Finset Point) : (rightAnchors k S).card ≤ S.card := by
  classical
  exact (Finset.card_preimage _ _ _).trans_le (Finset.card_filter_le _ _)

/-- The common tail of all active left targets with a fixed missing anchor. -/
def leftCore {k} (T : Set Point → Finset Point) (i : Fin k) (S : Finset Point) : Set ℕ :=
  {n | ∀ D, leftTarget i D ∈ active (family k) T S → n ∈ D}

theorem shift_infinite {C : Set ℕ} (hC : C.Infinite) (k : ℕ) :
    {n | k + n ∈ C}.Infinite := by
  intro hf
  apply hC
  apply ((Finset.range k).finite_toSet.union (hf.image (fun n => k + n))).subset
  intro n hn
  by_cases hnk : n < k
  · exact Or.inl (Finset.mem_range.mpr hnk)
  · exact Or.inr ⟨n - k, by simpa [Nat.add_sub_of_le (by omega : k ≤ n)] using hn,
      Nat.add_sub_of_le (by omega)⟩

theorem right_part_infinite {J : Set Point} (hJ : J.Infinite)
    (hf : {n | Sum.inl n ∈ J}.Finite) : {n | Sum.inr n ∈ J}.Infinite := by
  intro hg
  apply hJ
  apply ((hf.image Sum.inl).union (hg.image Sum.inr)).subset
  rintro (n | n) hn
  · exact Or.inl ⟨n, hn, rfl⟩
  · exact Or.inr ⟨n, hn, rfl⟩

theorem right_target_left_finite {k} (j : Fin k) {E : Set ℕ} (hE : E.Finite) :
    {n | Sum.inl n ∈ rightTarget j E}.Finite := by
  apply ((Finset.range k).finite_toSet.union (hE.image (fun n => k + n))).subset
  intro n hn
  by_cases hnk : n < k
  · exact Or.inl (Finset.mem_range.mpr hnk)
  · exact Or.inr ⟨n - k, by simpa [hnk] using hn,
      Nat.add_sub_of_le (by omega)⟩

theorem leftCore_infinite_of_active_right {k} {T : Set Point → Finset Point}
    (hT : Valid (family k) T) {S : Finset Point} (hS : (active (family k) T S).Nonempty)
    (i j : Fin k) {E : Set ℕ} (hE : E.Finite)
    (hR : rightTarget j E ∈ active (family k) T S) : (leftCore T i S).Infinite := by
  have hJ := hT.2 S hS
  have hlfin : {n | Sum.inl n ∈ activeCore (family k) T S}.Finite :=
    (right_target_left_finite j hE).subset (fun n hn => hn _ hR)
  apply (shift_infinite (right_part_infinite hJ hlfin) k).mono
  intro n hn D hD
  exact (tail_mem_left i D n).mp (hn _ hD)

end GenLimit.FiniteWitness.Anchored
