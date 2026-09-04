/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.FiniteCombinatorics
import LeanPool.Wallace.UniformKronecker
import Mathlib.Data.Finset.Lattice.Basic

/-!
# One finite character-fusion stage

This module turns the bounded-deletion conclusion into the exact short-relation compatibility
required by the uniform Kronecker lemma.  It is the finite algebraic heart of one fusion stage.
-/

open scoped BigOperators

universe u

namespace Wallace

noncomputable section

open FiniteCombinatorics

variable {G : Type u} [AddCommGroup G] [DecidableEq G]

/-- A short-relation-free old/new pair is disjoint as soon as the height bound contains `1`. -/
theorem disjoint_of_mixedRelationFree {A Y : Finset G} {Q : ℕ} (hQ : 1 ≤ Q)
    (hfree : MixedRelationFree Q A Y) : Disjoint A Y := by
  classical
  rw [Finset.disjoint_left]
  intro x hxA hxY
  apply hfree
  let b : G → ℤ := fun z ↦ if z = x then 1 else 0
  let c : G → ℤ := fun z ↦ if z = x then -1 else 0
  refine ⟨b, c, ?_, ?_, ⟨x, hxA, by simp [b]⟩, ⟨x, hxY, by simp [c]⟩, ?_⟩
  · intro a _ha
    by_cases hax : a = x <;> simp [b, hax, hQ]
  · intro y _hy
    by_cases hyx : y = x <;> simp [c, hyx, hQ]
  · simp [b, c, hxA, hxY]

section Coefficients

variable (A Y : Finset G)

private abbrev unionEquiv : Fin (A ∪ Y).card ≃ (A ∪ Y : Finset G) :=
  (A ∪ Y).equivFin.symm

private def unionTuple : Fin (A ∪ Y).card → G :=
  fun i ↦ (unionEquiv A Y i : G)

private def unionCoefficient (a : Fin (A ∪ Y).card → ℤ) (x : G) : ℤ := by
  classical
  exact if hx : x ∈ A ∪ Y then a ((unionEquiv A Y).symm ⟨x, hx⟩) else 0

omit [AddCommGroup G] in
private theorem unionCoefficient_of_mem
    (a : Fin (A ∪ Y).card → ℤ) {x : G} (hx : x ∈ A ∪ Y) :
    unionCoefficient A Y a x = a ((unionEquiv A Y).symm ⟨x, hx⟩) := by
  classical
  simp only [unionCoefficient, dif_pos hx]

omit [AddCommGroup G] in
private theorem unionCoefficient_tuple
    (a : Fin (A ∪ Y).card → ℤ) (i : Fin (A ∪ Y).card) :
    unionCoefficient A Y a (unionTuple A Y i) = a i := by
  classical
  have hm : ((unionEquiv A Y i : (A ∪ Y : Finset G)) : G) ∈ A ∪ Y :=
    (unionEquiv A Y i).property
  unfold unionTuple
  rw [unionCoefficient_of_mem A Y a hm]
  simp

private theorem sum_unionCoefficient
    (a : Fin (A ∪ Y).card → ℤ) :
    ∑ i, a i • unionTuple A Y i =
      ∑ x ∈ A ∪ Y, unionCoefficient A Y a x • x := by
  classical
  calc
    ∑ i, a i • unionTuple A Y i =
        ∑ i, unionCoefficient A Y a (unionTuple A Y i) • unionTuple A Y i := by
          simp only [unionCoefficient_tuple]
    _ = ∑ x : (A ∪ Y : Finset G), unionCoefficient A Y a x • (x : G) := by
          exact (unionEquiv A Y).sum_comp
            (fun x : (A ∪ Y : Finset G) ↦ unionCoefficient A Y a x • (x : G))
    _ = ∑ x ∈ A ∪ Y, unionCoefficient A Y a x • x := by
          simpa only using Finset.sum_coe_sort (A ∪ Y)
            (fun x ↦ unionCoefficient A Y a x • x)

end Coefficients

/-- The target which keeps the old character on `A` and is zero on the new set `Y`. -/
private def stageTarget (A Y : Finset G) (old : G →+ UnitAddCircle) :
    Fin (A ∪ Y).card → UnitAddCircle := by
  classical
  exact fun i ↦ if unionTuple A Y i ∈ A then old (unionTuple A Y i) else 0

/-- Reindexing the target sum over `A ∪ Y` leaves only the contribution from `A`. -/
private theorem sum_stageTarget_eq_sum_old
    (A Y : Finset G) (old : G →+ UnitAddCircle) (hdisj : Disjoint A Y)
    (a : Fin (A ∪ Y).card → ℤ) :
    ∑ i, a i • stageTarget A Y old i =
      ∑ x ∈ A, unionCoefficient A Y a x • old x := by
  classical
  calc
    ∑ i, a i • stageTarget A Y old i =
        ∑ i, unionCoefficient A Y a (unionTuple A Y i) •
          (if unionTuple A Y i ∈ A then old (unionTuple A Y i) else 0) := by
            simp only [unionCoefficient_tuple, stageTarget]
    _ = ∑ x : (A ∪ Y : Finset G),
          unionCoefficient A Y a (x : G) •
            (if (x : G) ∈ A then old (x : G) else 0) := by
          exact (unionEquiv A Y).sum_comp
            (fun x : (A ∪ Y : Finset G) ↦
              unionCoefficient A Y a (x : G) •
                (if (x : G) ∈ A then old (x : G) else 0))
    _ = ∑ x ∈ A ∪ Y, unionCoefficient A Y a x •
          (if x ∈ A then old x else 0) := by
          simpa only using Finset.sum_coe_sort (A ∪ Y)
            (fun x ↦ unionCoefficient A Y a x •
              (if x ∈ A then old x else 0))
    _ = ∑ x ∈ A, unionCoefficient A Y a x • old x := by
          rw [Finset.sum_union hdisj]
          have hYA : ∀ y ∈ Y, y ∉ A := by
            intro y hyY hyA
            exact Finset.disjoint_left.mp hdisj hyA hyY
          have hsumA :
              (∑ x ∈ A, unionCoefficient A Y a x •
                (if x ∈ A then old x else 0)) =
                ∑ x ∈ A, unionCoefficient A Y a x • old x := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [if_pos hx]
          have hsumY :
              (∑ x ∈ Y, unionCoefficient A Y a x •
                (if x ∈ A then old x else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro y hy
            rw [if_neg (hYA y hy), smul_zero]
          rw [hsumA, hsumY, add_zero]

/-- Bounded deletion makes the finite fusion target compatible with every relation up to `Q`. -/
theorem stageTarget_respectsRelationsUpTo
    {A Y : Finset G} {Q : ℕ} (hQ : 1 ≤ Q)
    (hfree : MixedRelationFree Q A Y) (old : G →+ UnitAddCircle) :
    RespectsRelationsUpTo Q (unionTuple A Y) (stageTarget A Y old) := by
  classical
  have hdisj : Disjoint A Y := disjoint_of_mixedRelationFree hQ hfree
  intro a haQ hrel
  have hcoeffQ (x : G) (hx : x ∈ A ∪ Y) :
      Int.natAbs (unionCoefficient A Y a x) ≤ Q := by
    rw [unionCoefficient_of_mem A Y a hx]
    exact (natAbs_le_intVectorHeight a _).trans haQ
  have hsumUnion :
      (∑ x ∈ A, unionCoefficient A Y a x • x) +
        ∑ y ∈ Y, unionCoefficient A Y a y • y = 0 := by
    rw [← Finset.sum_union hdisj]
    rw [← sum_unionCoefficient A Y a]
    exact hrel
  by_cases hold : ∃ x ∈ A, unionCoefficient A Y a x ≠ 0
  · by_cases hnew : ∃ y ∈ Y, unionCoefficient A Y a y ≠ 0
    · exfalso
      apply hfree
      exact ⟨unionCoefficient A Y a, unionCoefficient A Y a,
        fun x hx ↦ hcoeffQ x (Finset.mem_union_left Y hx),
        fun y hy ↦ hcoeffQ y (Finset.mem_union_right A hy), hold, hnew, hsumUnion⟩
    · push Not at hnew
      have hsumY : ∑ y ∈ Y, unionCoefficient A Y a y • y = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        simp [hnew y hy]
      have hsumA : ∑ x ∈ A, unionCoefficient A Y a x • x = 0 := by
        simpa [hsumY] using hsumUnion
      change ∑ i, a i • stageTarget A Y old i = 0
      calc
        ∑ i, a i • stageTarget A Y old i =
            old (∑ x ∈ A, unionCoefficient A Y a x • x) := by
              rw [sum_stageTarget_eq_sum_old A Y old hdisj]
              rw [map_sum]
              simp_rw [map_zsmul]
        _ = 0 := by rw [hsumA, map_zero]
  · push Not at hold
    change ∑ i, a i • stageTarget A Y old i = 0
    rw [sum_stageTarget_eq_sum_old A Y old hdisj]
    apply Finset.sum_eq_zero
    intro x hx
    simp [hold x hx]

/-- One application of uniform Kronecker performs a finite fusion stage. -/
theorem exists_character_fusion_stage
    {A Y : Finset G} {Q : ℕ} (hQ : 1 ≤ Q)
    (hfree : MixedRelationFree Q A Y) (old : G →+ UnitAddCircle)
    {eps : ℝ} (hbound : IsUniformKroneckerBound.{u} (A ∪ Y).card eps Q) :
    ∃ next : G →+ UnitAddCircle,
      (∀ x ∈ A, ‖next x - old x‖ < eps) ∧
      (∀ y ∈ Y, ‖next y‖ < eps) := by
  classical
  obtain ⟨next, hnext⟩ := hbound (unionTuple A Y) (stageTarget A Y old)
    (stageTarget_respectsRelationsUpTo hQ hfree old)
  refine ⟨next, ?_, ?_⟩
  · intro x hxA
    have hxU : x ∈ A ∪ Y := Finset.mem_union_left Y hxA
    let i : Fin (A ∪ Y).card := (unionEquiv A Y).symm ⟨x, hxU⟩
    have hzi : unionTuple A Y i = x := by simp [i, unionTuple, unionEquiv]
    simpa [stageTarget, hzi, hxA] using hnext i
  · intro y hyY
    have hyU : y ∈ A ∪ Y := Finset.mem_union_right A hyY
    let i : Fin (A ∪ Y).card := (unionEquiv A Y).symm ⟨y, hyU⟩
    have hzi : unionTuple A Y i = y := by simp [i, unionTuple, unionEquiv]
    have hyA : y ∉ A := fun hyA ↦ Finset.disjoint_left.mp
      (disjoint_of_mixedRelationFree hQ hfree) hyA hyY
    simpa [stageTarget, hzi, hyA, norm_eq_zero] using hnext i

/-- **One fusion step** (the complete form used in Section 4 of the paper).

`Q` is a uniform Kronecker bound for every positive tuple length that can occur.  Bounded
deletion first produces `Y`, including the no-mixed-relation certificate, and one application
of the uniform Kronecker lemma then produces the next homomorphism.  The empty union is handled
directly, exactly as in the paper, so no artificial bound for zero-length tuples is required. -/
theorem exists_one_fusion_step
    [IsAddTorsionFree G]
    (r Q : ℕ) (hQ : 1 ≤ Q) (A X : Finset G) (hAr : A.card ≤ r)
    (hX : BoundedIndependent (deletionIndependenceBound r Q) X)
    (old : G →+ UnitAddCircle) {eps : ℝ}
    (hbound : ∀ m, 0 < m → m ≤ r + X.card →
      IsUniformKroneckerBound.{u} m eps Q) :
    ∃ (Y : Finset G) (next : G →+ UnitAddCircle),
      Y ⊆ X ∧
      (X \ Y).card ≤ A.card ∧
      MixedRelationFree Q A Y ∧
      (∀ a ∈ A, ‖next a - old a‖ < eps) ∧
      (∀ y ∈ Y, ‖next y‖ < eps) := by
  classical
  obtain ⟨Y, hYX, hdeleted, hfree⟩ := bounded_deletion r Q A X hAr hX
  by_cases hempty : A ∪ Y = ∅
  · have hA : A = ∅ := (Finset.union_eq_empty.mp hempty).1
    have hY : Y = ∅ := (Finset.union_eq_empty.mp hempty).2
    subst A
    subst Y
    exact ⟨∅, old, by simp, hdeleted, hfree, by simp, by simp⟩
  · have hcardPos : 0 < (A ∪ Y).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
    have hcardLe : (A ∪ Y).card ≤ r + X.card := by
      calc
        (A ∪ Y).card ≤ A.card + Y.card := Finset.card_union_le A Y
        _ ≤ r + X.card := Nat.add_le_add hAr (Finset.card_le_card hYX)
    obtain ⟨next, hold, hnew⟩ := exists_character_fusion_stage
      hQ hfree old (hbound (A ∪ Y).card hcardPos hcardLe)
    exact ⟨Y, next, hYX, hdeleted, hfree, hold, hnew⟩

end

end Wallace
