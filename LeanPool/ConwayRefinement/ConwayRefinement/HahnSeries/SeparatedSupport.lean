/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.RingTheory.HahnSeries.Addition

/-!
# Strictly separated supports of Hahn series

`HahnSeries.SupportBelow x y` means that every exponent in the support of `x` is strictly below
every exponent in the support of `y`. This is the support orientation used in LM24, Proposition
3.2.1 and Definition 3.3.2. The generic lemmas below show that such supports cannot cancel under
addition and propagate the relation through finite sums.

The generic declarations follow Mathlib's Hahn-series namespace and assumptions. Adjacent and
pairwise separation of finite lists are expressed with `List.IsChain` and `List.Pairwise.isChain`.
-/

universe u v

public noncomputable section

namespace HahnSeries

variable {R : Type v} {G : Type u} [PartialOrder G]

section Zero

variable [Zero R]

/-- Every exponent in the support of `x` is strictly below every exponent in the support of `y`. -/
def SupportBelow (x y : R⟦G⟧) : Prop :=
  ∀ i ∈ x.support, ∀ j ∈ y.support, i < j

/-- Elementwise characterization of strict support separation. -/
theorem supportBelow_iff {x y : R⟦G⟧} :
    SupportBelow x y ↔ ∀ i ∈ x.support, ∀ j ∈ y.support, i < j :=
  (Iff.rfl)

/-- Extract the strict inequality between two supported exponents. -/
theorem SupportBelow.lt {x y : R⟦G⟧} (h : SupportBelow x y) {i j : G}
    (hi : i ∈ x.support) (hj : j ∈ y.support) : i < j :=
  supportBelow_iff.mp h i hi j hj

/-- Strict support separation is transitive when the intermediate series is nonzero. -/
theorem supportBelow_trans_of_ne_zero {x y z : R⟦G⟧} (hy : y ≠ 0)
    (hxy : SupportBelow x y) (hyz : SupportBelow y z) : SupportBelow x z := by
  have hsupport : y.support.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h ↦ hy (support_eq_empty_iff.mp h)
  obtain ⟨j, hj⟩ := hsupport
  rw [supportBelow_iff]
  intro i hi k hk
  exact (hxy.lt hi hj).trans (hyz.lt hj hk)

/-- An adjacent chain of nonzero series with strictly separated supports is pairwise separated. -/
theorem pairwise_supportBelow_of_isChain {l : List R⟦G⟧}
    (hne : ∀ x ∈ l, x ≠ 0) (hchain : l.IsChain SupportBelow) :
    l.Pairwise SupportBelow := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
      cases l with
      | nil => exact List.Pairwise.cons (by simp) List.Pairwise.nil
      | cons b l =>
          have htail : (b :: l).IsChain SupportBelow := hchain.tail
          have hpair : (b :: l).Pairwise SupportBelow :=
            ih (fun x hx ↦ hne x (by simp [hx])) htail
          rw [List.pairwise_cons]
          refine ⟨?_, hpair⟩
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact hchain.rel_head
          · exact supportBelow_trans_of_ne_zero (hne b (by simp)) hchain.rel_head
              ((List.pairwise_cons.mp hpair).1 c hc)

end Zero

section AddMonoid

variable [AddMonoid R]

/-- Strict support separation prevents cancellation in the support of a sum. -/
theorem support_add_eq_union_of_supportBelow (x y : R⟦G⟧) (hxy : SupportBelow x y) :
    (x + y).support = x.support ∪ y.support := by
  have hdisjoint : Disjoint x.support y.support := by
    rw [Set.disjoint_left]
    intro i hi hj
    exact (hxy.lt hi hj).false
  apply Set.Subset.antisymm (support_add_subset x y)
  rintro i (hi | hi)
  · rw [mem_support, coeff_add]
    have hy : y.coeff i = 0 := by
      rw [← not_ne_iff, ← mem_support]
      exact Set.disjoint_left.mp hdisjoint hi
    simpa [hy] using (mem_support x i).mp hi
  · rw [mem_support, coeff_add]
    have hx : x.coeff i = 0 := by
      rw [← not_ne_iff, ← mem_support]
      exact Set.disjoint_left.mp hdisjoint.symm hi
    simpa [hx] using (mem_support y i).mp hi

/-- A series below every member of a list is below the sum of that list. -/
theorem supportBelow_list_sum {x : R⟦G⟧} {l : List R⟦G⟧}
    (h : ∀ y ∈ l, SupportBelow x y) : SupportBelow x l.sum := by
  rw [supportBelow_iff]
  intro i hi j hj
  induction l with
  | nil => simp at hj
  | cons y ys ih =>
      rw [List.sum_cons] at hj
      rcases support_add_subset y ys.sum hj with hj | hj
      · exact (h y (by simp)).lt hi hj
      · exact ih (fun z hz ↦ h z (by simp [hz])) hj

/-- A sum of series each below `y` is itself below `y`. -/
theorem list_sum_supportBelow {l : List R⟦G⟧} {y : R⟦G⟧}
    (h : ∀ x ∈ l, SupportBelow x y) : SupportBelow l.sum y := by
  rw [supportBelow_iff]
  intro i hi j hj
  induction l with
  | nil => simp at hi
  | cons x xs ih =>
      rw [List.sum_cons] at hi
      rcases support_add_subset x xs.sum hi with hi | hi
      · exact (h x (by simp)).lt hi hj
      · exact ih (fun z hz ↦ h z (by simp [hz])) hi

/-- In a pairwise support-separated list, every summand support is contained in the sum support. -/
theorem support_subset_list_sum_of_mem {x : R⟦G⟧} {l : List R⟦G⟧}
    (hpair : l.Pairwise SupportBelow) (hx : x ∈ l) : x.support ⊆ l.sum.support := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.pairwise_cons] at hpair
      have hbelow : SupportBelow y ys.sum := supportBelow_list_sum hpair.1
      rw [List.sum_cons, support_add_eq_union_of_supportBelow y ys.sum hbelow]
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Set.subset_union_left
      · exact (ih hpair.2 hx).trans Set.subset_union_right

end AddMonoid

end HahnSeries
