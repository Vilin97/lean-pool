/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.RecursionCardinal

/-!
# Closed initial segments as an open segment with a new top
-/

namespace ScottishBook155

universe u

variable {J : Type u} [LinearOrder J]

private noncomputable def initialSegmentToWithTop (j : J) :
    Set.Iic j → WithTop (Set.Iio j) := fun x ↦
  if hx : x.1 < j then ((⟨x.1, hx⟩ : Set.Iio j) : WithTop (Set.Iio j)) else ⊤

private def initialSegmentFromWithTop (j : J) :
    WithTop (Set.Iio j) → Set.Iic j := fun x ↦
  x.recTopCoe ⟨j, le_rfl⟩ (fun i ↦ ⟨i.1, i.2.le⟩)

private theorem initialSegment_leftInverse (j : J) :
    Function.LeftInverse (initialSegmentFromWithTop j)
      (initialSegmentToWithTop j) := by
  intro x
  by_cases hx : x.1 < j
  · apply Subtype.ext
    simp [initialSegmentToWithTop, initialSegmentFromWithTop, hx]
  · apply Subtype.ext
    have hxj : x.1 = j := le_antisymm x.2 (le_of_not_gt hx)
    simp [initialSegmentToWithTop, initialSegmentFromWithTop, hx, hxj]

private theorem initialSegment_rightInverse (j : J) :
    Function.RightInverse (initialSegmentFromWithTop j)
      (initialSegmentToWithTop j) := by
  intro x
  induction x using WithTop.recTopCoe with
  | top => simp [initialSegmentToWithTop, initialSegmentFromWithTop]
  | coe x =>
      change initialSegmentToWithTop j ⟨x.1, x.2.le⟩ = (x : WithTop (Set.Iio j))
      have hx : (⟨x.1, x.2.le⟩ : Set.Iic j).1 < j := x.2
      rw [initialSegmentToWithTop, dif_pos hx]

private theorem initialSegmentToWithTop_monotone (j : J) :
    Monotone (initialSegmentToWithTop j) := by
  intro x y hxy
  by_cases hy : y.1 < j
  · have hx : x.1 < j := lt_of_le_of_lt hxy hy
    simp only [initialSegmentToWithTop, hx, hy, ↓reduceDIte, WithTop.coe_le_coe]
    exact hxy
  · simp [initialSegmentToWithTop, hy]

private theorem initialSegmentFromWithTop_monotone (j : J) :
    Monotone (initialSegmentFromWithTop j) := by
  intro x y hxy
  induction y using WithTop.recTopCoe with
  | top =>
      change (initialSegmentFromWithTop j x).1 ≤ j
      exact (initialSegmentFromWithTop j x).2
  | coe y =>
      induction x using WithTop.recTopCoe with
      | top => exact False.elim (by simpa using hxy)
      | coe x =>
          change x.1 ≤ y.1
          have h : x ≤ y := WithTop.coe_le_coe.mp hxy
          exact h

/-- A closed initial segment is the corresponding open segment with one new
top point. -/
noncomputable def initialSegmentWithTop (j : J) :
    Set.Iic j ≃o WithTop (Set.Iio j) where
  toEquiv := {
    toFun := initialSegmentToWithTop j
    invFun := initialSegmentFromWithTop j
    left_inv := initialSegment_leftInverse j
    right_inv := initialSegment_rightInverse j }
  map_rel_iff' := by
    intro x y
    change initialSegmentToWithTop j x ≤ initialSegmentToWithTop j y ↔ x ≤ y
    constructor
    · intro h
      have h' := initialSegmentFromWithTop_monotone j h
      rw [initialSegment_leftInverse j x, initialSegment_leftInverse j y] at h'
      exact h'
    · intro h
      exact initialSegmentToWithTop_monotone j h

variable [SuccOrder J]

/-- The open segment below a successor is the closed segment below its
predecessor. -/
noncomputable def openSuccOrderIso (j : J) (hj : ¬ IsMax j) :
    Set.Iio (Order.succ j) ≃o Set.Iic j where
  toEquiv := {
    toFun := fun x ↦ ⟨x.1, (Order.lt_succ_iff_of_not_isMax hj).mp x.2⟩
    invFun := fun x ↦ ⟨x.1, (Order.lt_succ_iff_of_not_isMax hj).mpr x.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  map_rel_iff' := by intro _ _; rfl

/-- Decompose the closed segment at a successor into the previous closed
segment and a new top. -/
noncomputable def successorSegmentWithTop (j : J) (hj : ¬ IsMax j) :
    Set.Iic (Order.succ j) ≃o WithTop (Set.Iic j) :=
  (initialSegmentWithTop (Order.succ j)).trans
    (OrderIso.withTopCongr (openSuccOrderIso j hj))

@[simp]
theorem initialSegmentWithTop_apply_lt (j : J) (i : J) (hij : i < j) :
    initialSegmentWithTop j ⟨i, hij.le⟩ =
      (⟨i, hij⟩ : Set.Iio j) := by
  simp [initialSegmentWithTop, initialSegmentToWithTop, hij]

@[simp]
theorem successorSegmentWithTop_apply_old (j : J) (hj : ¬ IsMax j)
    (i : Set.Iic j) :
    successorSegmentWithTop j hj
        ⟨i.1, i.2.trans (Order.le_succ j)⟩ =
      (i : WithTop (Set.Iic j)) := by
  change WithTop.map (openSuccOrderIso j hj)
      (initialSegmentWithTop (Order.succ j)
        ⟨i.1, i.2.trans (Order.le_succ j)⟩) = i
  have hi : i.1 < Order.succ j :=
    (Order.lt_succ_iff_of_not_isMax hj).mpr i.2
  rw [initialSegmentWithTop_apply_lt (Order.succ j) i.1 hi]
  rfl

end ScottishBook155
