/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Sign.Defs
import Mathlib.Order.CompletePartialOrder

/-!
# An auxiliary tri-partition of indices

This file contains a simple tri-partition of an index set that is used to form
the triangular decompositions of both the Virasoro algebra and the Heisenberg algebra.

## Main definitions

* `indexTri`: A partition of `Option ℤ` into three parts.

-/

namespace VirasoroProject

/-- The partition of `Option ℤ` into zero, positive, and negative parts. -/
def indexTri (ε : SignType) : Set (Option ℤ) := match ε with
  | SignType.zero => {none, some 0}
  | SignType.pos => some '' {n : ℤ | 0 < n}
  | SignType.neg => some '' {n : ℤ | n < 0}

lemma pairwise_disjoint_indexTri :
    Pairwise fun ε₁ ε₂ ↦ Disjoint (indexTri ε₁) (indexTri ε₂) := by
  intro ε₁ ε₂ h
  simp only [indexTri]
  cases ε₁
  · cases ε₂ <;> aesop
  · cases ε₂
    · aesop
    · aesop
    · apply Set.disjoint_image_image fun k hk l hl ↦ ?_
      by_contra con
      simp only [Set.mem_setOf_eq, Option.some.injEq] at hk hl con
      linarith
  · cases ε₂
    · aesop
    · apply Set.disjoint_image_image fun k hk l hl ↦ ?_
      by_contra con
      simp only [Set.mem_setOf_eq, Option.some.injEq] at hk hl con
      linarith
    · aesop

lemma iUnion_indexTri :
    ⋃ ε, indexTri ε = Set.univ := by
  simp only [indexTri, Set.iUnion_eq_univ_iff]
  intro i
  match i with
  | none => refine ⟨0, by decide⟩
  | some n =>
    by_cases hn0 : n = 0
    · refine ⟨0, by simp [hn0]⟩
    by_cases n_pos : 0 < n
    · refine ⟨1, by simp [n_pos]⟩
    · have n_neg : n < 0 := by grind
      refine ⟨-1, by simp [n_neg]⟩

end VirasoroProject
