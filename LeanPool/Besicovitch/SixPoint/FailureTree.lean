/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.FourChildren
public import LeanPool.Besicovitch.SixPoint.RowColumnRescue

/-!
# The first stage of the six-point failure tree

For an admissible endpoint configuration, either a packing already has nonnegative score or one
of the two perfect matchings of the four children satisfies the exact matching obstruction.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

private theorem barC_four_children_gaps :
    0 < barC * (barC + 2) - 4 ∧ 1 < 2 * barC * (barC - 1) := by
  have hc : (69 : ℝ) / 50 < barC := by
    nlinarith [barC_mem_isolation_box.1]
  constructor <;> nlinarith [sq_nonneg (barC - 69 / 50)]

private theorem sibling_distance_mem_four_children_range
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (color : SixPointColor) :
    barC ≤ dist (configuration color .left) (configuration color .right) ∧
      dist (configuration color .left) (configuration color .right) ≤ 2 := by
  constructor
  · have hsibling := h.sibling_distance color
    rw [barS, show 2 * (barC / 2) = barC by ring] at hsibling
    exact hsibling
  · calc
      dist (configuration color .left) (configuration color .right) ≤
          dist (configuration color .left) (configuration color .root) +
            dist (configuration color .root) (configuration color .right) := dist_triangle _ _ _
      _ ≤ 1 + 1 := add_le_add
        (by simpa [dist_comm] using h.child_distance color .left (by simp))
        (h.child_distance color .right (by simp))
      _ = 2 := by norm_num

private theorem cross_child_distance_le_three {configuration : SixPointConfiguration}
    (h : configuration.IsAdmissibleAt barS) (redLabel blueLabel : SixPointLabel)
    (hred : redLabel ≠ .root) (hblue : blueLabel ≠ .root) :
    dist (configuration .red redLabel) (configuration .blue blueLabel) ≤ 3 := by
  calc
    _ ≤ dist (configuration .red redLabel) (configuration .red .root) +
        dist (configuration .red .root) (configuration .blue blueLabel) := dist_triangle _ _ _
    _ ≤ dist (configuration .red redLabel) (configuration .red .root) +
        (dist (configuration .red .root) (configuration .blue .root) +
          dist (configuration .blue .root) (configuration .blue blueLabel)) :=
      by
        gcongr
        exact dist_triangle _ _ _
    _ ≤ 1 + (1 + 1) := add_le_add
      (by simpa [dist_comm] using h.child_distance .red redLabel hred)
      (add_le_add h.root_distance.le (h.child_distance .blue blueLabel hblue))
    _ = 3 := by norm_num

private theorem exists_nonnegative_score_or_matching_obstruction_of_no_split
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hno : ¬ ∃ x y : ℝ,
      dist (configuration .red .left) (configuration .red .right) - 1 ≤ x ∧ x ≤ 1 ∧
      dist (configuration .blue .left) (configuration .blue .right) - 1 ≤ y ∧ y ≤ 1 ∧
      fourChildrenSplitDiameter
          (dist (configuration .red .left) (configuration .red .right))
          (dist (configuration .blue .left) (configuration .blue .right)) x y
          (dist (configuration .red .left) (configuration .blue .left))
          (dist (configuration .red .left) (configuration .blue .right))
          (dist (configuration .red .right) (configuration .blue .left))
          (dist (configuration .red .right) (configuration .blue .right)) ≤
        barC * (dist (configuration .red .left) (configuration .red .right) +
          dist (configuration .blue .left) (configuration .blue .right))) :
    (∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS) ∨
      (2 * barC - 1) *
          (dist (configuration .red .left) (configuration .red .right) +
            dist (configuration .blue .left) (configuration .blue .right)) ≤
        dist (configuration .red .left) (configuration .blue .left) +
          dist (configuration .red .right) (configuration .blue .right) ∨
      (2 * barC - 1) *
          (dist (configuration .red .left) (configuration .red .right) +
            dist (configuration .blue .left) (configuration .blue .right)) ≤
        dist (configuration .red .left) (configuration .blue .right) +
          dist (configuration .red .right) (configuration .blue .left) := by
  obtain ⟨hcL, hL⟩ := sibling_distance_mem_four_children_range h .red
  obtain ⟨hcM, hM⟩ := sibling_distance_mem_four_children_range h .blue
  have hfail : ∀ x y : ℝ,
      dist (configuration .red .left) (configuration .red .right) - 1 ≤ x → x ≤ 1 →
      dist (configuration .blue .left) (configuration .blue .right) - 1 ≤ y → y ≤ 1 →
      barC * (dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right)) <
      fourChildrenSplitDiameter
        (dist (configuration .red .left) (configuration .red .right))
        (dist (configuration .blue .left) (configuration .blue .right)) x y
        (dist (configuration .red .left) (configuration .blue .left))
        (dist (configuration .red .left) (configuration .blue .right))
        (dist (configuration .red .right) (configuration .blue .left))
        (dist (configuration .red .right) (configuration .blue .right)) := by
    intro x y hx_lower hx_upper hy_lower hy_upper
    exact lt_of_not_ge fun hdiameter ↦
      hno ⟨x, y, hx_lower, hx_upper, hy_lower, hy_upper, hdiameter⟩
  rcases fourChildren_row_column_or_matching one_lt_barC_and_barC_lt_two.1
      one_lt_barC_and_barC_lt_two.2.le hcL hcM hL hM barC_four_children_gaps.1
      barC_four_children_gaps.2 (cross_child_distance_le_three h .left .left (by simp)
        (by simp)) (cross_child_distance_le_three h .left .right (by simp) (by simp))
      (cross_child_distance_le_three h .right .left (by simp) (by simp))
      (cross_child_distance_le_three h .right .right (by simp) (by simp)) hfail with
    hrowLeft | hrowRight | hcolumnLeft | hcolumnRight | hdiagonal | hantiDiagonal
  · exact Or.inl ⟨redRootBlueTrianglePacking configuration
      (h.child_distance .blue .left (by simp)) (h.child_distance .blue .right (by simp)),
      red_root_blue_triangle_score_nonnegative_of_row_obstruction configuration h .left
        (by simp) hrowLeft⟩
  · exact Or.inl ⟨redRootBlueTrianglePacking configuration
      (h.child_distance .blue .left (by simp)) (h.child_distance .blue .right (by simp)),
      red_root_blue_triangle_score_nonnegative_of_row_obstruction configuration h .right
        (by simp) hrowRight⟩
  · exact Or.inl ⟨blueRootRedTrianglePacking configuration
      (h.child_distance .red .left (by simp)) (h.child_distance .red .right (by simp)),
      blue_root_red_triangle_score_nonnegative_of_column_obstruction configuration h .left
        (by simp) (by nlinarith [hcolumnLeft])⟩
  · exact Or.inl ⟨blueRootRedTrianglePacking configuration
      (h.child_distance .red .left (by simp)) (h.child_distance .red .right (by simp)),
      blue_root_red_triangle_score_nonnegative_of_column_obstruction configuration h .right
        (by simp) (by nlinarith [hcolumnRight])⟩
  · exact Or.inr (Or.inl hdiagonal)
  · exact Or.inr (Or.inr hantiDiagonal)

/-- Every admissible endpoint configuration has a nonnegative packing or an obstructing child
matching. -/
theorem exists_nonnegative_score_or_matching_obstruction
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS) :
    (∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS) ∨
      (2 * barC - 1) *
          (dist (configuration .red .left) (configuration .red .right) +
            dist (configuration .blue .left) (configuration .blue .right)) ≤
        dist (configuration .red .left) (configuration .blue .left) +
          dist (configuration .red .right) (configuration .blue .right) ∨
      (2 * barC - 1) *
          (dist (configuration .red .left) (configuration .red .right) +
            dist (configuration .blue .left) (configuration .blue .right)) ≤
        dist (configuration .red .left) (configuration .blue .right) +
          dist (configuration .red .right) (configuration .blue .left) := by
  by_cases hsplit : ∃ x y : ℝ,
    dist (configuration .red .left) (configuration .red .right) - 1 ≤ x ∧ x ≤ 1 ∧
    dist (configuration .blue .left) (configuration .blue .right) - 1 ≤ y ∧ y ≤ 1 ∧
    fourChildrenSplitDiameter
        (dist (configuration .red .left) (configuration .red .right))
        (dist (configuration .blue .left) (configuration .blue .right)) x y
        (dist (configuration .red .left) (configuration .blue .left))
        (dist (configuration .red .left) (configuration .blue .right))
        (dist (configuration .red .right) (configuration .blue .left))
        (dist (configuration .red .right) (configuration .blue .right)) ≤
      barC * (dist (configuration .red .left) (configuration .red .right) +
        dist (configuration .blue .left) (configuration .blue .right))
  · rcases hsplit with ⟨x, y, hx_lower, hx_upper, hy_lower, hy_upper, hdiameter⟩
    have hL := (one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_four_children_range h .red).1)
    have hM := (one_lt_barC_and_barC_lt_two.1.le.trans
      (sibling_distance_mem_four_children_range h .blue).1)
    refine Or.inl ⟨fourChildrenPacking configuration rfl rfl hL hx_lower hx_upper hM
      hy_lower hy_upper, ?_⟩
    simpa only [barS] using fourChildrenPacking_score_nonnegative configuration rfl rfl hL
      hx_lower hx_upper hM hy_lower hy_upper barC_pos hdiameter
  · exact exists_nonnegative_score_or_matching_obstruction_of_no_split configuration h hsplit

end LeanPool.Besicovitch
