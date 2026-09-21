/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Finset.Max

/-!
# Leading grades in graded direct sums

The leading grade of a finitely supported graded sum is the largest grade at which its component
is nonzero, with value bottom at zero. It satisfies the max-form addition inequality.

For a graded ring whose nonzero homogeneous elements have nonzero product, leading grade is
multiplicative. The proof isolates the unique contribution at the sum of the two leading grades;
all other pairs of support indices have strictly smaller sum.
-/

universe u v

public noncomputable section

open scoped DirectSum

namespace DirectSum

section Additive

variable {ι : Type u} (A : ι → Type v)
  [LinearOrder ι] [∀ i, AddCommMonoid (A i)]

/-- The largest grade at which a graded direct-sum element has nonzero component. -/
def leadingGrade (x : DirectSum ι A) : WithBot ι := by
  classical
  exact x.support.max

@[simp]
theorem leadingGrade_zero : leadingGrade A 0 = ⊥ := by
  classical
  simp [leadingGrade]

theorem leadingGrade_of {i : ι} {a : A i} (ha : a ≠ 0) :
    leadingGrade A (DirectSum.of A i a) = i := by
  classical
  rw [leadingGrade, DirectSum.support_of i a ha, Finset.max_singleton]

@[simp]
theorem leadingGrade_eq_bot_iff (x : DirectSum ι A) :
    leadingGrade A x = ⊥ ↔ x = 0 := by
  classical
  simp only [leadingGrade, Finset.max_eq_bot, DFinsupp.support_eq_empty]
  rfl

theorem grade_le_leadingGrade {x : DirectSum ι A} {i : ι} (hi : x i ≠ 0) :
    (i : WithBot ι) ≤ leadingGrade A x := by
  classical
  exact Finset.le_max (DFinsupp.mem_support_iff.mpr hi)

theorem leadingGrade_eq_coe_iff (x : DirectSum ι A) (m : ι) :
    leadingGrade A x = (m : WithBot ι) ↔
      x m ≠ 0 ∧ ∀ i, x i ≠ 0 → i ≤ m := by
  classical
  constructor
  · intro h
    have hm : m ∈ x.support := Finset.mem_of_max h
    refine ⟨DFinsupp.mem_support_iff.mp hm, ?_⟩
    intro i hi
    exact Finset.le_max_of_eq (DFinsupp.mem_support_iff.mpr hi) h
  · rintro ⟨hm, hmax⟩
    apply le_antisymm
    · rw [leadingGrade]
      apply Finset.max_le
      intro i hi
      exact WithBot.coe_le_coe.mpr (hmax i (DFinsupp.mem_support_iff.mp hi))
    · exact Finset.le_max (DFinsupp.mem_support_iff.mpr hm)

theorem leadingGrade_add_le_max (x y : DirectSum ι A) :
    leadingGrade A (x + y) ≤ max (leadingGrade A x) (leadingGrade A y) := by
  classical
  rw [leadingGrade, leadingGrade, leadingGrade, ← Finset.max_union]
  exact Finset.max_mono DFinsupp.support_add

theorem exists_grade_eq_leadingGrade {x : DirectSum ι A} (hx : x ≠ 0) :
    ∃ m : ι, leadingGrade A x = m ∧ x m ≠ 0 := by
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
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty hs
  exact ⟨m, hm, DFinsupp.mem_support_iff.mp (Finset.mem_of_max hm)⟩

end Additive

section Group

variable {ι : Type u} (A : ι → Type v)
  [LinearOrder ι] [∀ i, AddCommGroup (A i)]

@[simp]
theorem leadingGrade_neg (x : DirectSum ι A) : leadingGrade A (-x) = leadingGrade A x := by
  have hsupp : ∀ i, (-x) i ≠ 0 ↔ x i ≠ 0 := fun i ↦ by
    rw [← zero_sub, DirectSum.sub_apply, DirectSum.zero_apply, zero_sub]
    exact neg_ne_zero
  apply le_antisymm
  · by_cases h : -x = 0
    · rw [h, leadingGrade_zero]
      exact bot_le
    obtain ⟨m, hm, hxm⟩ := exists_grade_eq_leadingGrade A h
    rw [hm]
    exact grade_le_leadingGrade A ((hsupp m).mp hxm)
  · by_cases h : x = 0
    · rw [h, leadingGrade_zero]
      exact bot_le
    obtain ⟨m, hm, hxm⟩ := exists_grade_eq_leadingGrade A h
    rw [hm]
    exact grade_le_leadingGrade A ((hsupp m).mpr hxm)

end Group

section Multiplicative

variable {ι : Type u} (A : ι → Type v)
  [LinearOrder ι] [AddCommMonoid ι] [IsOrderedCancelAddMonoid ι]
  [∀ i, AddCommMonoid (A i)] [DirectSum.GSemiring A]

omit [IsOrderedCancelAddMonoid ι] in
theorem exists_grades_of_mul_apply_ne_zero {x y : DirectSum ι A} {k : ι}
    (hk : (x * y) k ≠ 0) :
    ∃ i j, x i ≠ 0 ∧ y j ≠ 0 ∧ i + j = k := by
  classical
  rw [DirectSum.mul_eq_sum_support_ghas_mul, DirectSum.sum_apply] at hk
  obtain ⟨ij, hij, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  refine ⟨ij.1, ij.2, ?_, ?_, ?_⟩
  · exact DFinsupp.mem_support_iff.mp (Finset.mem_product.mp hij).1
  · exact DFinsupp.mem_support_iff.mp (Finset.mem_product.mp hij).2
  · by_contra hgrade
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hgrade)] at hterm
    exact hterm rfl

theorem leadingGrade_mul_le (x y : DirectSum ι A) :
    leadingGrade A (x * y) ≤ leadingGrade A x + leadingGrade A y := by
  classical
  rw [leadingGrade]
  apply Finset.max_le
  intro k hk
  obtain ⟨i, j, hi, hj, rfl⟩ :=
    exists_grades_of_mul_apply_ne_zero A (DFinsupp.mem_support_iff.mp hk)
  rw [WithBot.coe_add]
  exact add_le_add (grade_le_leadingGrade A hi) (grade_le_leadingGrade A hj)

theorem mul_apply_add_eq_of_leadingGrade_eq {x y : DirectSum ι A} {m n : ι}
    (hm : leadingGrade A x = m) (hn : leadingGrade A y = n) :
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
        · exact Finset.le_max_of_eq (Finset.mem_product.mp hij).1 hm
        · apply le_of_not_gt
          intro hmi
          have hjn : ij.2 ≤ n :=
            Finset.le_max_of_eq (Finset.mem_product.mp hij).2 hn
          exact (add_lt_add_of_lt_of_le hmi hjn).ne hgrade
      · change ij.2 = n
        apply le_antisymm
        · exact Finset.le_max_of_eq (Finset.mem_product.mp hij).2 hn
        · apply le_of_not_gt
          intro hnj
          have him : ij.1 ≤ m :=
            Finset.le_max_of_eq (Finset.mem_product.mp hij).1 hm
          exact (add_lt_add_of_le_of_lt him hnj).ne hgrade
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

/-- Leading grade is multiplicative when nonzero homogeneous products remain nonzero. -/
theorem leadingGrade_mul
    (hmul : ∀ {i j} (a : A i) (b : A j), a ≠ 0 → b ≠ 0 →
      GradedMonoid.GMul.mul a b ≠ 0)
    (x y : DirectSum ι A) :
    leadingGrade A (x * y) = leadingGrade A x + leadingGrade A y := by
  by_cases hx : x = 0
  · subst x
    simp [leadingGrade_zero]
  by_cases hy : y = 0
  · subst y
    simp [leadingGrade_zero]
  obtain ⟨m, hm, hxm⟩ := exists_grade_eq_leadingGrade A hx
  obtain ⟨n, hn, hyn⟩ := exists_grade_eq_leadingGrade A hy
  apply le_antisymm
  · exact leadingGrade_mul_le A x y
  · rw [hm, hn, ← WithBot.coe_add]
    apply grade_le_leadingGrade A
    rw [mul_apply_add_eq_of_leadingGrade_eq A hm hn]
    exact hmul (x m) (y n) hxm hyn

end Multiplicative

end DirectSum
