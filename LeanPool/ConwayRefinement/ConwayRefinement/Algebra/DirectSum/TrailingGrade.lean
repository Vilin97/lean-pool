/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Finset.Max

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.LeadingGrade

/-!
# Trailing grades in graded direct sums

The trailing grade of a finitely supported graded sum is the smallest grade at which its component
is nonzero, with value top at zero. It satisfies the min-form addition inequality.

For a graded ring whose nonzero homogeneous elements have nonzero product, trailing grade is
multiplicative. The proof isolates the unique contribution at the sum of the two trailing grades.
This is the minimum-grade counterpart of `DirectSum.leadingGrade`.
-/

universe u v

public noncomputable section

open scoped DirectSum

namespace DirectSum

section Additive

variable {ι : Type u} (A : ι → Type v)
  [LinearOrder ι] [∀ i, AddCommMonoid (A i)]

/-- The smallest grade at which a graded direct-sum element has nonzero component. -/
def trailingGrade (x : DirectSum ι A) : WithTop ι := by
  classical
  exact x.support.min

@[simp]
theorem trailingGrade_zero : trailingGrade A 0 = ⊤ := by
  classical
  simp [trailingGrade]

theorem trailingGrade_of {i : ι} {a : A i} (ha : a ≠ 0) :
    trailingGrade A (DirectSum.of A i a) = i := by
  classical
  rw [trailingGrade, DirectSum.support_of i a ha, Finset.min_singleton]

@[simp]
theorem trailingGrade_eq_top_iff (x : DirectSum ι A) :
    trailingGrade A x = ⊤ ↔ x = 0 := by
  classical
  simp only [trailingGrade, Finset.min_eq_top, DFinsupp.support_eq_empty]
  rfl

theorem trailingGrade_le_grade {x : DirectSum ι A} {i : ι} (hi : x i ≠ 0) :
    trailingGrade A x ≤ (i : WithTop ι) := by
  classical
  exact Finset.min_le (DFinsupp.mem_support_iff.mpr hi)

theorem trailingGrade_eq_coe_iff (x : DirectSum ι A) (m : ι) :
    trailingGrade A x = (m : WithTop ι) ↔
      x m ≠ 0 ∧ ∀ i, x i ≠ 0 → m ≤ i := by
  classical
  constructor
  · intro h
    have hm : m ∈ x.support := Finset.mem_of_min h
    refine ⟨DFinsupp.mem_support_iff.mp hm, ?_⟩
    intro i hi
    exact Finset.min_le_of_eq (DFinsupp.mem_support_iff.mpr hi) h
  · rintro ⟨hm, hmin⟩
    apply le_antisymm
    · exact Finset.min_le (DFinsupp.mem_support_iff.mpr hm)
    · rw [trailingGrade]
      apply Finset.le_min
      intro i hi
      exact WithTop.coe_le_coe.mpr (hmin i (DFinsupp.mem_support_iff.mp hi))

theorem min_le_trailingGrade_add (x y : DirectSum ι A) :
    min (trailingGrade A x) (trailingGrade A y) ≤ trailingGrade A (x + y) := by
  classical
  rw [trailingGrade, trailingGrade, trailingGrade, ← Finset.min_union]
  exact Finset.min_mono DFinsupp.support_add

theorem exists_grade_eq_trailingGrade {x : DirectSum ι A} (hx : x ≠ 0) :
    ∃ m : ι, trailingGrade A x = m ∧ x m ≠ 0 := by
  classical
  have hs : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs
    apply hx
    apply DirectSum.ext
    intro i
    apply DFinsupp.notMem_support_iff.mp
    rw [hs]
    simp
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hs
  exact ⟨m, hm, DFinsupp.mem_support_iff.mp (Finset.mem_of_min hm)⟩

end Additive

section Multiplicative

variable {ι : Type u} (A : ι → Type v)
  [LinearOrder ι] [AddCommMonoid ι] [IsOrderedCancelAddMonoid ι]
  [∀ i, AddCommMonoid (A i)] [DirectSum.GSemiring A]

theorem le_trailingGrade_mul (x y : DirectSum ι A) :
    trailingGrade A x + trailingGrade A y ≤ trailingGrade A (x * y) := by
  classical
  rw [trailingGrade]
  apply Finset.le_min
  intro k hk
  obtain ⟨i, j, hi, hj, rfl⟩ :=
    exists_grades_of_mul_apply_ne_zero A (DFinsupp.mem_support_iff.mp hk)
  rw [WithTop.coe_add]
  exact add_le_add (trailingGrade_le_grade A hi) (trailingGrade_le_grade A hj)

theorem mul_apply_add_eq_of_trailingGrade_eq {x y : DirectSum ι A} {m n : ι}
    (hm : trailingGrade A x = m) (hn : trailingGrade A y = n) :
    (x * y) (m + n) = GradedMonoid.GMul.mul (x m) (y n) := by
  classical
  rw [DirectSum.mul_eq_sum_support_ghas_mul, DirectSum.sum_apply]
  let term : ι × ι → A (m + n) := fun ij ↦
    (DirectSum.of A (ij.1 + ij.2)
      (GradedMonoid.GMul.mul (x ij.1) (y ij.2))) (m + n)
  change (∑ ij ∈ x.support ×ˢ y.support, term ij) = _
  rw [Finset.sum_eq_single (f := term) (m, n)]
  · simp [term]
  · intro ij hij hne
    by_cases hgrade : ij.1 + ij.2 = m + n
    · exfalso
      apply hne
      apply Prod.ext
      · change ij.1 = m
        apply le_antisymm
        · apply le_of_not_gt
          intro hmi
          have hnj : n ≤ ij.2 :=
            Finset.min_le_of_eq (Finset.mem_product.mp hij).2 hn
          exact (add_lt_add_of_lt_of_le hmi hnj).ne hgrade.symm
        · exact Finset.min_le_of_eq (Finset.mem_product.mp hij).1 hm
      · change ij.2 = n
        apply le_antisymm
        · apply le_of_not_gt
          intro hni
          have hmi : m ≤ ij.1 :=
            Finset.min_le_of_eq (Finset.mem_product.mp hij).1 hm
          exact (add_lt_add_of_le_of_lt hmi hni).ne hgrade.symm
        · exact Finset.min_le_of_eq (Finset.mem_product.mp hij).2 hn
    · simp [term, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hgrade)]
  · intro hnotmem
    simp only [Finset.mem_product, not_and_or] at hnotmem
    rcases hnotmem with hmnot | hnnot
    · dsimp [term]
      rw [DFinsupp.notMem_support_iff.mp hmnot]
      rw [DirectSum.GNonUnitalNonAssocSemiring.zero_mul (A := A)]
      simp
    · dsimp [term]
      rw [DFinsupp.notMem_support_iff.mp hnnot]
      rw [DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := A)]
      simp

/-- Trailing grade is multiplicative when nonzero homogeneous products remain nonzero. -/
theorem trailingGrade_mul
    (hmul : ∀ {i j} (a : A i) (b : A j), a ≠ 0 → b ≠ 0 →
      GradedMonoid.GMul.mul a b ≠ 0)
    (x y : DirectSum ι A) :
    trailingGrade A (x * y) = trailingGrade A x + trailingGrade A y := by
  by_cases hx : x = 0
  · subst x
    simp [trailingGrade_zero]
  by_cases hy : y = 0
  · subst y
    simp [trailingGrade_zero]
  obtain ⟨m, hm, hxm⟩ := exists_grade_eq_trailingGrade A hx
  obtain ⟨n, hn, hyn⟩ := exists_grade_eq_trailingGrade A hy
  apply le_antisymm
  · rw [hm, hn, ← WithTop.coe_add]
    apply trailingGrade_le_grade A
    rw [mul_apply_add_eq_of_trailingGrade_eq A hm hn]
    exact hmul (x m) (y n) hxm hyn
  · exact le_trailingGrade_mul A x y

end Multiplicative

end DirectSum
