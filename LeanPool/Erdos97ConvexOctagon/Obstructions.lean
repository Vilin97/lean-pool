/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CycleStrip
import LeanPool.Erdos97ConvexOctagon.EquidistantFour
import LeanPool.Erdos97ConvexOctagon.Pentagon
import LeanPool.Erdos97ConvexOctagon.Radius

/-! # Erdős 97 convex-octagon formalization: Obstructions -/

namespace Erdos97Octagon

open scoped InnerProductSpace RealInnerProductSpace

/-- A four-clique in one radius-labelled graph is impossible in the plane. -/
theorem no_labelled_k4
    {p : Vertex → Plane} (hp : Function.Injective p)
    {Q : OctagonIncidence} (hR : Realises p Q)
    {root a b c d : Vertex} (had : a ≠ d)
    (hab : Q.LabelledEdge root a b) (hac : Q.LabelledEdge root a c)
    (had' : Q.LabelledEdge root a d) (hbc : Q.LabelledEdge root b c)
    (hbd : Q.LabelledEdge root b d) (hcd : Q.LabelledEdge root c d) :
    False := by
  obtain ⟨radius, hpos, hdist⟩ := exists_positive_radii hp Q hR
  exact four_points_not_pairwise_equidistant (hp.ne had)
    (dist_eq_radius_of_labelledEdge hdist hab)
    (dist_eq_radius_of_labelledEdge hdist hac)
    (dist_eq_radius_of_labelledEdge hdist had')
    (dist_eq_radius_of_labelledEdge hdist hbc)
    (dist_eq_radius_of_labelledEdge hdist hbd)
    (dist_eq_radius_of_labelledEdge hdist hcd)

/-- A hub and a five-cycle in one radius-labelled graph are impossible. -/
theorem no_labelled_hub_pentagon
    {p : Vertex → Plane} (hp : Function.Injective p)
    {Q : OctagonIncidence} (hR : Realises p Q)
    {root o a b c d e : Vertex}
    (hoa : Q.LabelledEdge root o a) (hob : Q.LabelledEdge root o b)
    (hoc : Q.LabelledEdge root o c) (hod : Q.LabelledEdge root o d)
    (hoe : Q.LabelledEdge root o e) (hab : Q.LabelledEdge root a b)
    (hbc : Q.LabelledEdge root b c) (hcd : Q.LabelledEdge root c d)
    (hde : Q.LabelledEdge root d e) (hea : Q.LabelledEdge root e a) :
    False := by
  obtain ⟨radius, hpos, hdist⟩ := exists_positive_radii hp Q hR
  exact no_unit_pentagon_centre (hpos root)
    (dist_eq_radius_of_labelledEdge hdist hoa)
    (dist_eq_radius_of_labelledEdge hdist hob)
    (dist_eq_radius_of_labelledEdge hdist hoc)
    (dist_eq_radius_of_labelledEdge hdist hod)
    (dist_eq_radius_of_labelledEdge hdist hoe)
    (dist_eq_radius_of_labelledEdge hdist hab)
    (dist_eq_radius_of_labelledEdge hdist hbc)
    (dist_eq_radius_of_labelledEdge hdist hcd)
    (dist_eq_radius_of_labelledEdge hdist hde)
    (dist_eq_radius_of_labelledEdge hdist hea)

/-- A seven-vertex cycle-square strip in one radius-labelled graph is impossible. -/
theorem no_labelled_cycle_square_strip
    {p : Vertex → Plane} (hp : Function.Injective p)
    {Q : OctagonIncidence} (hR : Realises p Q)
    {root o x1 x2 x3 x4 x5 x6 : Vertex}
    (e01 : Q.LabelledEdge root o x1) (e02 : Q.LabelledEdge root o x2)
    (e06 : Q.LabelledEdge root o x6) (e12 : Q.LabelledEdge root x1 x2)
    (e13 : Q.LabelledEdge root x1 x3) (e23 : Q.LabelledEdge root x2 x3)
    (e24 : Q.LabelledEdge root x2 x4) (e34 : Q.LabelledEdge root x3 x4)
    (e35 : Q.LabelledEdge root x3 x5) (e45 : Q.LabelledEdge root x4 x5)
    (e46 : Q.LabelledEdge root x4 x6) (e56 : Q.LabelledEdge root x5 x6) :
    False := by
  obtain ⟨radius, hpos, hdist⟩ := exists_positive_radii hp Q hR
  exact no_unit_cycle_square_strip (hpos root)
    (dist_eq_radius_of_labelledEdge hdist e01)
    (dist_eq_radius_of_labelledEdge hdist e02)
    (dist_eq_radius_of_labelledEdge hdist e06)
    (dist_eq_radius_of_labelledEdge hdist e12)
    (dist_eq_radius_of_labelledEdge hdist e13)
    (dist_eq_radius_of_labelledEdge hdist e23)
    (dist_eq_radius_of_labelledEdge hdist e24)
    (dist_eq_radius_of_labelledEdge hdist e34)
    (dist_eq_radius_of_labelledEdge hdist e35)
    (dist_eq_radius_of_labelledEdge hdist e45)
    (dist_eq_radius_of_labelledEdge hdist e46)
    (dist_eq_radius_of_labelledEdge hdist e56)

private lemma common_circle_points_collinear
    {A B q1 q2 q3 : Plane} (hAB : A ≠ B)
    (hA12 : dist A q1 = dist A q2) (hA13 : dist A q1 = dist A q3)
    (hB12 : dist B q1 = dist B q2) (hB13 : dist B q1 = dist B q3) :
    Collinear ℝ ({q1, q2, q3} : Set Plane) := by
  have hne : B -ᵥ A ≠ 0 := fun h => hAB (vsub_eq_zero_iff_eq.mp h).symm
  have h12 : ⟪q2 -ᵥ q1, B -ᵥ A⟫ = (0 : ℝ) := by
    rw [real_inner_comm]
    exact EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
      (by simpa [dist_comm] using hA12) (by simpa [dist_comm] using hB12)
  have h13 : ⟪q3 -ᵥ q1, B -ᵥ A⟫ = (0 : ℝ) := by
    rw [real_inner_comm]
    exact EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
      (by simpa [dist_comm] using hA13) (by simpa [dist_comm] using hB13)
  have hfd : Module.finrank ℝ Plane = 1 + 1 := by
    rw [finrank_euclideanSpace]
    norm_num
  let : Fact (Module.finrank ℝ Plane = 1 + 1) := ⟨hfd⟩
  have hfo : Module.finrank ℝ ((ℝ ∙ (B -ᵥ A) : Submodule ℝ Plane))ᗮ = 1 :=
    Submodule.finrank_orthogonal_span_singleton hne
  have horth : vectorSpan ℝ ({q1, q2, q3} : Set Plane) ≤
      (ℝ ∙ (B -ᵥ A) : Submodule ℝ Plane)ᗮ := by
    rw [vectorSpan_eq_span_vsub_set_right_ne ℝ (Set.mem_insert q1 _)]
    rw [Submodule.span_le]
    intro w hw
    rw [Set.mem_image] at hw
    obtain ⟨q, hq, rfl⟩ := hw
    have hq_ne : q ≠ q1 := fun h => hq.2 (by simpa using h)
    have hq_cases : q = q2 ∨ q = q3 := by
      rcases hq.1 with hq | hq
      · exact absurd hq hq_ne
      rcases hq with hq | hq
      · exact Or.inl hq
      · simpa using Or.inr hq
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
    rcases hq_cases with rfl | rfl
    · exact h12
    · exact h13
  let : FiniteDimensional ℝ (vectorSpan ℝ ({q1, q2, q3} : Set Plane)) :=
    Submodule.finiteDimensional_of_le horth
  rw [collinear_iff_finrank_le_one]
  calc
    Module.finrank ℝ (vectorSpan ℝ ({q1, q2, q3} : Set Plane)) ≤
        Module.finrank ℝ ((ℝ ∙ (B -ᵥ A) : Submodule ℝ Plane)ᗮ) :=
      Submodule.finrank_mono horth
    _ = 1 := hfo

/-- Two distinct realised centres cannot share three distinct selected targets
in a convex-independent planar family. -/
theorem no_three_shared_targets
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p)
    {Q : OctagonIncidence} (hR : Realises p Q)
    {a b q1 q2 q3 : Vertex} (hab : a ≠ b)
    (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h23 : q2 ≠ q3)
    (ha1 : q1 ∈ Q.targets a) (ha2 : q2 ∈ Q.targets a)
    (ha3 : q3 ∈ Q.targets a) (hb1 : q1 ∈ Q.targets b)
    (hb2 : q2 ∈ Q.targets b) (hb3 : q3 ∈ Q.targets b) :
    False := by
  obtain ⟨ra, hra⟩ := hR a
  obtain ⟨rb, hrb⟩ := hR b
  have hcol : Collinear ℝ ({p q1, p q2, p q3} : Set Plane) :=
    common_circle_points_collinear (hC.injective.ne hab)
      ((hra q1 ha1).trans (hra q2 ha2).symm)
      ((hra q1 ha1).trans (hra q3 ha3).symm)
      ((hrb q1 hb1).trans (hrb q2 hb2).symm)
      ((hrb q1 hb1).trans (hrb q3 hb3).symm)
  exact three_collinear_not_convexIndependent hC h12 h13 h23 hcol

end Erdos97Octagon
