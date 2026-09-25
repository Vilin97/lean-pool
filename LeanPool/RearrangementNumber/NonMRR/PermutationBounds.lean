/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import LeanPool.RearrangementNumber.NonMRR.Bounding

/-!
# A common sparse set ordered eventually by a small family of permutations

An eventually bounded family of permutation controls admits a common increasing
sequence whose tail is preserved in order by the inverse of each permutation.
-/

@[expose] public section

open Filter Finset Cardinal

namespace NonMRR

/-- A cutoff after which all inverse images exceed the inverse images of
`0, ..., n`. -/
def permutationControl (π : Equiv.Perm ℕ) (n : ℕ) : ℕ :=
  (range ((range (n + 1)).sup π.symm + 1)).sup π + 1

theorem permutationControl_separates (π : Equiv.Perm ℕ) {n x y : ℕ}
    (hx : x ≤ n) (hy : permutationControl π n ≤ y) : π.symm x < π.symm y := by
  have hx' : π.symm x ≤ (range (n + 1)).sup π.symm :=
    le_sup (f := π.symm) (mem_range.mpr (by omega))
  by_contra h
  have hy' : π.symm y < (range (n + 1)).sup π.symm + 1 := by omega
  have hy'' := le_sup (f := π) (mem_range.mpr hy')
  rw [π.apply_symm_apply] at hy''
  unfold permutationControl at hy
  omega

/-- Insert enough space after each point to pass the next cutoff. -/
def spacedSequence (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (spacedSequence g n + 1) (g (spacedSequence g n))

theorem spacedSequence_strictMono (g : ℕ → ℕ) : StrictMono (spacedSequence g) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

theorem id_le_spacedSequence (g : ℕ → ℕ) (n : ℕ) : n ≤ spacedSequence g n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n hn =>
    exact (Nat.add_le_add_right hn 1).trans (le_max_left _ _)

theorem spacedSequence_eventually_ordered (g : ℕ → ℕ) (π : Equiv.Perm ℕ)
    (hπ : EventuallyLE (permutationControl π) g) :
    ∀ᶠ n in atTop, ∀ m, n < m →
      π.symm (spacedSequence g n) < π.symm (spacedSequence g m) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hπ
  filter_upwards [eventually_ge_atTop N] with n hn m hnm
  apply permutationControl_separates π le_rfl
  calc
    permutationControl π (spacedSequence g n) ≤ g (spacedSequence g n) :=
      hN _ (hn.trans (id_le_spacedSequence g n))
    _ ≤ spacedSequence g (n + 1) := le_max_right _ _
    _ ≤ spacedSequence g m :=
      (spacedSequence_strictMono g).monotone (by omega)

/-- A family with cardinality below the bounding number has a common eventual
bound for all of its permutation controls. -/
theorem exists_bound_permutationControls (P : Set (Equiv.Perm ℕ))
    (hP : #P < boundingNumber) :
    ∃ g, ∀ π ∈ P, EventuallyLE (permutationControl π) g := by
  classical
  have hb : ∃ g, ∀ f ∈ permutationControl '' P, EventuallyLE f g := by
    by_contra h
    have hd := (dominating_boundingRelation_iff (permutationControl '' P)).2 h
    have hle : boundingNumber ≤ #(permutationControl '' P) :=
      boundingRelation.norm_le hd
    exact (not_le_of_gt hP) (hle.trans Cardinal.mk_image_le)
  obtain ⟨g, hg⟩ := hb
  exact ⟨g, fun π hπ => hg _ (Set.mem_image_of_mem _ hπ)⟩

/-- Every family of fewer than `boundingNumber` permutations has a common
infinite set on which the inverse of each permutation is eventually increasing. -/
theorem exists_common_eventually_ordered_subsequence (P : Set (Equiv.Perm ℕ))
    (hP : #P < boundingNumber) :
    ∃ l : ℕ → ℕ, StrictMono l ∧ ∀ π ∈ P,
      ∀ᶠ n in atTop, ∀ m, n < m → π.symm (l n) < π.symm (l m) := by
  obtain ⟨g, hg⟩ := exists_bound_permutationControls P hP
  exact ⟨spacedSequence g, spacedSequence_strictMono g,
    fun π hπ => spacedSequence_eventually_ordered g π (hg π hπ)⟩

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
