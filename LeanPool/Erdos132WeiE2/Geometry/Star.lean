/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132WeiE2.Geometry.Basic
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# The diameter star

The main target of this file is the standard orientation of the seven-cycle
formed by the unit diameter segments.
-/

namespace LeanPool.Erdos132WeiE2.Geometry

open Metric

/-- Two open line segments have a common point. -/
def OpenSegmentsMeet (a b c d : Plane) : Prop :=
  ∃ x, x ∈ openSegment ℝ a b ∧ x ∈ openSegment ℝ c d

private theorem orientedArea_affine_combo
    (a b c d : Plane) (r s : ℝ) (hrs : r + s = 1) :
    orientedArea a b (r • c + s • d) =
      r * orientedArea a b c + s * orientedArea a b d := by
  have hre :
      (toComplex (r • c + s • d) - toComplex a).re =
        r * (toComplex c - toComplex a).re +
          s * (toComplex d - toComplex a).re := by
    simp only [toComplex, map_add, map_smul, Complex.add_re, Complex.smul_re,
      Complex.sub_re]
    linear_combination (complexPlaneEquiv.symm a).re * hrs
  have him :
      (toComplex (r • c + s • d) - toComplex a).im =
        r * (toComplex c - toComplex a).im +
          s * (toComplex d - toComplex a).im := by
    simp only [toComplex, map_add, map_smul, Complex.add_im, Complex.smul_im,
      Complex.sub_im]
    linear_combination (complexPlaneEquiv.symm a).im * hrs
  simp only [orientedArea]
  rw [hre, him]
  ring

/-- A noncollinear triple has nonzero signed area in the chosen coordinates. -/
private theorem orientedArea_ne_zero_of_not_collinear
    {a b c : Plane} (hcol : ¬Collinear ℝ ({a, b, c} : Set Plane)) :
    orientedArea a b c ≠ 0 := by
  intro harea
  apply hcol
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  have hab : a ≠ b := by
    intro hab
    subst b
    exact hcol (by simpa [Set.pair_comm] using collinear_pair ℝ a c)
  let u : ℂ := toComplex b - toComplex a
  let v : ℂ := toComplex c - toComplex a
  have hu : u ≠ 0 := by
    intro hu
    have : toComplex b = toComplex a := sub_eq_zero.mp hu
    have hba : b = a := complexPlaneEquiv.symm.injective (by
      simpa [toComplex] using this)
    exact hab hba.symm
  have hcross : u.re * v.im - u.im * v.re = 0 := by
    simpa [orientedArea, u, v] using harea
  obtain ⟨r, hvr⟩ : ∃ r : ℝ, v = r • u := by
    by_cases hure : u.re = 0
    · have huim : u.im ≠ 0 := by
        intro huim
        apply hu
        apply Complex.ext <;> simp_all
      refine ⟨v.im / u.im, ?_⟩
      apply Complex.ext
      · simp only [Complex.smul_re]
        have hvre : v.re = 0 := by
          rw [hure, zero_mul, zero_sub] at hcross
          have hproduct : u.im * v.re = 0 := by linarith
          exact (mul_eq_zero.mp hproduct).resolve_left huim
        simp [hure, hvre]
      · simp only [Complex.smul_im]
        change v.im = (v.im / u.im) * u.im
        exact (div_mul_cancel₀ v.im huim).symm
    · refine ⟨v.re / u.re, ?_⟩
      apply Complex.ext
      · simp only [Complex.smul_re]
        change v.re = (v.re / u.re) * u.re
        exact (div_mul_cancel₀ v.re hure).symm
      · simp only [Complex.smul_im]
        change v.im = (v.re / u.re) * u.im
        field_simp
        nlinarith
  have hplane : c - a = r • (b - a) := by
    apply complexPlaneEquiv.symm.injective
    simpa [u, v, toComplex] using hvr
  refine ⟨a, b - a, ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨r, by simpa [vadd_eq_add] using (sub_eq_iff_eq_add.mp hplane)⟩

/-- A proper segment crossing gives alternating signed areas once one area
in each line direction is known to be nonzero. -/
theorem alternating_oriented_areas_of_open_segments_meet
    {a b c d : Plane} (hmeet : OpenSegmentsMeet a b c d)
    (habc : orientedArea a b c ≠ 0) (hcda : orientedArea c d a ≠ 0) :
    orientedArea a b c * orientedArea a b d < 0 ∧
      orientedArea c d a * orientedArea c d b < 0 := by
  obtain ⟨x, hxab, hxcd⟩ := hmeet
  obtain ⟨r, s, hr, hs, hrs, hxAB⟩ := hxab
  obtain ⟨u, v, hu, hv, huv, hxCD⟩ := hxcd
  have hareaAB : orientedArea a b x = 0 := by
    rw [← hxAB, orientedArea_affine_combo a b a b r s hrs]
    simp only [orientedArea, sub_self, Complex.zero_re, Complex.zero_im, mul_zero]
    ring
  have hrelationAB :
      u * orientedArea a b c + v * orientedArea a b d = 0 := by
    rw [← hxCD, orientedArea_affine_combo a b c d u v huv] at hareaAB
    exact hareaAB
  have hareaCD : orientedArea c d x = 0 := by
    rw [← hxCD, orientedArea_affine_combo c d c d u v huv]
    simp only [orientedArea, sub_self, Complex.zero_re, Complex.zero_im, mul_zero]
    ring
  have hrelationCD :
      r * orientedArea c d a + s * orientedArea c d b = 0 := by
    rw [← hxAB, orientedArea_affine_combo c d a b r s hrs] at hareaCD
    exact hareaCD
  constructor
  · have hscaled :
        u * (orientedArea a b c) ^ 2 +
          v * (orientedArea a b c * orientedArea a b d) = 0 := by
      linear_combination orientedArea a b c * hrelationAB
    have hpositive := mul_pos hu (sq_pos_of_ne_zero habc)
    nlinarith
  · have hscaled :
        r * (orientedArea c d a) ^ 2 +
          s * (orientedArea c d a * orientedArea c d b) = 0 := by
      linear_combination orientedArea c d a * hrelationCD
    have hpositive := mul_pos hr (sq_pos_of_ne_zero hcda)
    nlinarith

/-- With the endpoint order induced by two crossed edges, the two consecutive
turns have the same strict sign. -/
private theorem consecutive_turn_product_pos_of_open_segments_meet
    {a b c d : Plane} (hmeet : OpenSegmentsMeet a b c d)
    (habc : orientedArea a b c ≠ 0) (hcda : orientedArea c d a ≠ 0) :
    0 < orientedArea a b c * orientedArea b c d := by
  have hsigns :=
    alternating_oriented_areas_of_open_segments_meet hmeet habc hcda
  have hcyclicABC : orientedArea b c a = orientedArea a b c := by
    simp only [orientedArea, Complex.sub_re, Complex.sub_im]
    ring
  have hcyclicBCD : orientedArea c d b = orientedArea b c d := by
    simp only [orientedArea, Complex.sub_re, Complex.sub_im]
    ring
  have hbcd : orientedArea b c d ≠ 0 := by
    intro hbcd
    have hcdb : orientedArea c d b = 0 := by simpa [hcyclicBCD] using hbcd
    rw [hcdb, mul_zero] at hsigns
    linarith [hsigns.2]
  obtain ⟨x, hxab, hxcd⟩ := hmeet
  obtain ⟨r, s, hr, _hs, hrs, hxAB⟩ := hxab
  obtain ⟨u, v, _hu, hv, huv, hxCD⟩ := hxcd
  have hareaAB :
      orientedArea b c x = r * orientedArea a b c := by
    rw [← hxAB, orientedArea_affine_combo b c a b r s hrs, hcyclicABC]
    simp only [orientedArea, sub_self, Complex.zero_re, Complex.zero_im,
      mul_zero, add_zero]
  have hareaCD :
      orientedArea b c x = v * orientedArea b c d := by
    rw [← hxCD, orientedArea_affine_combo b c c d u v huv]
    simp only [orientedArea]
    ring
  have hrelation :
      r * orientedArea a b c = v * orientedArea b c d := hareaAB.symm.trans hareaCD
  have hscaled :
      r * (orientedArea a b c) ^ 2 =
        v * (orientedArea a b c * orientedArea b c d) := by
    linear_combination orientedArea a b c * hrelation
  have hpositive := mul_pos hr (sq_pos_of_ne_zero habc)
  have hproduct_ne := mul_ne_zero habc hbcd
  have hproduct_nonneg :
      0 ≤ orientedArea a b c * orientedArea b c d := by
    nlinarith
  exact lt_of_le_of_ne hproduct_nonneg hproduct_ne.symm

/-- The four endpoints of two diameter pairs are in convex position. -/
private theorem diameter_endpoints_convexIndependent
    {a b c d : Plane}
    (hab : dist a b = 1) (hcd : dist c d = 1)
    (hac : dist a c ≤ 1) (had : dist a d ≤ 1)
    (hbc : dist b c ≤ 1) (hbd : dist b d ≤ 1)
    (hacne : a ≠ c) (hadne : a ≠ d) (hbcne : b ≠ c) (hbdne : b ≠ d) :
    ConvexIndependent ℝ ![a, b, c, d] := by
  let f : Fin 4 → Plane := ![a, b, c, d]
  let center : Fin 4 → Plane := ![b, a, d, c]
  have habne : a ≠ b := by
    intro h
    have hzero : dist a b = 0 := dist_eq_zero.mpr h
    linarith
  have hcdne : c ≠ d := by
    intro h
    have hzero : dist c d = 0 := dist_eq_zero.mpr h
    linarith
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hall (i j : Fin 4) : dist (center i) (f j) ≤ 1 := by
    fin_cases i <;> fin_cases j <;>
      simp_all [center, f, dist_comm]
  have hsphere (i : Fin 4) : dist (center i) (f i) = 1 := by
    fin_cases i <;> simp_all [center, f, dist_comm]
  intro s i hi
  have hsubset : convexHull ℝ (f '' s) ⊆ closedBall (center i) 1 := by
    apply convexHull_min
    · rintro y ⟨j, hj, rfl⟩
      exact mem_closedBall.mpr (by simpa [dist_comm] using hall i j)
    · exact convex_closedBall _ _
  have hboundary : f i ∈ sphere (center i) 1 := by
    exact mem_sphere.mpr (by simpa [dist_comm] using hsphere i)
  have hextremeBall : f i ∈ (closedBall (center i) 1).extremePoints ℝ :=
    StrictConvexSpace.sphere_subset_extremePoints_closedBall
      (center i) one_ne_zero hboundary
  have hextremeHull : f i ∈ (convexHull ℝ (f '' s)).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset hsubset ⟨hi, hextremeBall⟩
  obtain ⟨j, hjs, hji⟩ := extremePoints_convexHull_subset hextremeHull
  simpa [hf hji] using hjs

/-- A proper point on one side of a noncollinear triangle gives a strict
triangle inequality through that point. -/
private theorem strict_triangle_through_open_segment
    {a b c x : Plane} (hx : x ∈ openSegment ℝ a c)
    (hncol : ¬Collinear ℝ ({a, b, c} : Set Plane)) :
    dist a b < dist a x + dist x b := by
  rw [dist_lt_dist_add_dist_iff]
  intro habx
  have hxne : x ≠ a := by
    intro h
    subst x
    have hac : a = c := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hx
    subst c
    apply hncol
    simpa [Set.pair_comm] using collinear_pair ℝ a b
  have hxlineAB : x ∈ line[ℝ, a, b] := habx.mem_affineSpan
  have hxlineAC : x ∈ line[ℝ, a, c] :=
    (mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ a c hx)).mem_affineSpan
  have hlineAB : line[ℝ, a, x] = line[ℝ, a, b] :=
    affineSpan_pair_eq_of_right_mem_of_ne hxlineAB hxne
  have hlineAC : line[ℝ, a, x] = line[ℝ, a, c] :=
    affineSpan_pair_eq_of_right_mem_of_ne hxlineAC hxne
  have hbline : b ∈ line[ℝ, a, c] := by
    rw [← hlineAC, hlineAB]
    exact right_mem_affineSpan_pair ℝ a b
  apply hncol
  simpa [Set.insert_comm] using collinear_insert_of_mem_affineSpan_pair hbline

/-- If one pairing crosses properly, its two side lengths have strictly
smaller sum than the crossed diagonal lengths. -/
private theorem side_sum_lt_of_open_segments_meet
    {a b c d : Plane}
    (habc : ¬Collinear ℝ ({a, b, c} : Set Plane))
    (hcda : ¬Collinear ℝ ({c, d, a} : Set Plane))
    (hmeet : OpenSegmentsMeet a c b d) :
    dist a b + dist c d < dist a c + dist b d := by
  obtain ⟨x, hxac, hxbd⟩ := hmeet
  have hab := strict_triangle_through_open_segment hxac habc
  have hcd := strict_triangle_through_open_segment
    (by simpa [openSegment_symm] using hxac) hcda
  have hac : dist a x + dist x c = dist a c :=
    dist_add_dist_eq_iff.mpr
      (mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ a c hxac))
  have hbd : dist b x + dist x d = dist b d :=
    dist_add_dist_eq_iff.mpr
      (mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ b d hxbd))
  calc
    dist a b + dist c d <
        (dist a x + dist x b) + (dist c x + dist x d) := add_lt_add hab hcd
    _ = (dist a x + dist x c) + (dist b x + dist x d) := by
      rw [dist_comm x b, dist_comm c x]
      ring
    _ = dist a c + dist b d := by rw [hac, hbd]

/-- Proper intersection depends only on the two unordered endpoint pairs. -/
private theorem openSegmentsMeet_congr_pairs
    {a b c d a' b' c' d' : Plane}
    (hab : ({a, b} : Set Plane) = {a', b'})
    (hcd : ({c, d} : Set Plane) = {c', d'})
    (hmeet : OpenSegmentsMeet a b c d) : OpenSegmentsMeet a' b' c' d' := by
  rcases Set.pair_eq_pair_iff.mp hab with hab | hab <;>
    rcases Set.pair_eq_pair_iff.mp hcd with hcd | hcd <;>
      simpa [OpenSegmentsMeet, hab.1, hab.2, hcd.1, hcd.2,
        openSegment_symm, and_comm] using hmeet

private theorem openSegmentsMeet_swap_pairs
    {a b c d : Plane} (hmeet : OpenSegmentsMeet a b c d) :
    OpenSegmentsMeet c d a b := by
  simpa [OpenSegmentsMeet, and_comm] using hmeet

/-- The three unordered two-two partitions of four labels. -/
private theorem fin_four_partition_cases
    (i j k l : Fin 4) (hji : j ≠ i)
    (hcomp : ({k, l} : Set (Fin 4)) = ({i, j} : Set (Fin 4))ᶜ) :
    ((({i, j} : Set (Fin 4)) = {0, 1} ∧ ({k, l} : Set (Fin 4)) = {2, 3}) ∨
      (({i, j} : Set (Fin 4)) = {2, 3} ∧ ({k, l} : Set (Fin 4)) = {0, 1})) ∨
    ((({i, j} : Set (Fin 4)) = {0, 2} ∧ ({k, l} : Set (Fin 4)) = {1, 3}) ∨
      (({i, j} : Set (Fin 4)) = {1, 3} ∧ ({k, l} : Set (Fin 4)) = {0, 2})) ∨
    (({i, j} : Set (Fin 4)) = {0, 3} ∧ ({k, l} : Set (Fin 4)) = {1, 2}) ∨
      (({i, j} : Set (Fin 4)) = {1, 2} ∧ ({k, l} : Set (Fin 4)) = {0, 3}) := by
  fin_cases i
  · fin_cases j
    · exact (hji rfl).elim
    · exact Or.inl (Or.inl ⟨rfl, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩)
    · exact Or.inr (Or.inl (Or.inl ⟨rfl, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨by simp, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩))
  · fin_cases j
    · exact Or.inl (Or.inl ⟨by exact Set.pair_comm _ _, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩)
    · exact (hji rfl).elim
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨by simp, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩))
  · fin_cases j
    · exact Or.inr (Or.inl (Or.inl ⟨by exact Set.pair_comm _ _, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by exact Set.pair_comm _ _, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩))
    · exact (hji rfl).elim
    · exact Or.inl (Or.inr ⟨by simp, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩)
  · fin_cases j
    · exact Or.inr (Or.inr (Or.inl ⟨by exact Set.pair_comm _ _, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨by exact Set.pair_comm _ _, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩))
    · exact Or.inl (Or.inr ⟨by exact Set.pair_comm _ _, hcomp.trans (by
        ext m
        fin_cases m <;> decide)⟩)
    · exact (hji rfl).elim

private theorem classify_fin_four_pairing
    (f : Fin 4 → Plane) (i j k l : Fin 4) (hji : j ≠ i)
    (hcomp : ({k, l} : Set (Fin 4)) = ({i, j} : Set (Fin 4))ᶜ)
    (hmeet : OpenSegmentsMeet (f i) (f j) (f k) (f l)) :
    OpenSegmentsMeet (f 0) (f 1) (f 2) (f 3) ∨
      OpenSegmentsMeet (f 0) (f 2) (f 1) (f 3) ∨
        OpenSegmentsMeet (f 0) (f 3) (f 1) (f 2) := by
  rcases fin_four_partition_cases i j k l hji hcomp with h12 | hrest
  · rcases h12 with h | h
    · exact Or.inl (openSegmentsMeet_congr_pairs
        (by simpa [Set.image_pair] using congrArg (f '' ·) h.1)
        (by simpa [Set.image_pair] using congrArg (f '' ·) h.2) hmeet)
    · exact Or.inl (openSegmentsMeet_congr_pairs
        (by simpa [Set.image_pair] using congrArg (f '' ·) h.2)
        (by simpa [Set.image_pair] using congrArg (f '' ·) h.1)
        (openSegmentsMeet_swap_pairs hmeet))
  · rcases hrest with h34 | hrest
    · rcases h34 with h | h
      · exact Or.inr (Or.inl (openSegmentsMeet_congr_pairs
          (by simpa [Set.image_pair] using congrArg (f '' ·) h.1)
          (by simpa [Set.image_pair] using congrArg (f '' ·) h.2) hmeet))
      · exact Or.inr (Or.inl (openSegmentsMeet_congr_pairs
          (by simpa [Set.image_pair] using congrArg (f '' ·) h.2)
          (by simpa [Set.image_pair] using congrArg (f '' ·) h.1)
          (openSegmentsMeet_swap_pairs hmeet)))
    · rcases hrest with h | h
      · exact Or.inr (Or.inr (openSegmentsMeet_congr_pairs
          (by simpa [Set.image_pair] using congrArg (f '' ·) h.1)
          (by simpa [Set.image_pair] using congrArg (f '' ·) h.2) hmeet))
      · exact Or.inr (Or.inr (openSegmentsMeet_congr_pairs
          (by simpa [Set.image_pair] using congrArg (f '' ·) h.2)
          (by simpa [Set.image_pair] using congrArg (f '' ·) h.1)
          (openSegmentsMeet_swap_pairs hmeet)))

/-- Radon's theorem gives one of the three pairings as the proper diagonals
of four convex-independent planar points. -/
private theorem one_pairing_open_segments_meet
    {a b c d : Plane} (hconv : ConvexIndependent ℝ ![a, b, c, d]) :
    OpenSegmentsMeet a b c d ∨ OpenSegmentsMeet a c b d ∨
      OpenSegmentsMeet a d b c := by
  let f : Fin 4 → Plane := ![a, b, c, d]
  have hf : ConvexIndependent ℝ f := by simpa [f] using hconv
  have hdep : ¬AffineIndependent ℝ f := by
    rw [← finrank_vectorSpan_le_iff_not_affineIndependent ℝ f (by decide : 4 = 2 + 2)]
    exact (Submodule.finrank_le _).trans_eq (by simp [Plane])
  obtain ⟨I, x, hxI, hxIc⟩ := Convex.radon_partition hdep
  have hInonempty : I.Nonempty := by
    have : (f '' I).Nonempty := convexHull_nonempty_iff.mp ⟨x, hxI⟩
    exact Set.image_nonempty.mp this
  have hIcNonempty : Iᶜ.Nonempty := by
    have : (f '' Iᶜ).Nonempty := convexHull_nonempty_iff.mp ⟨x, hxIc⟩
    exact Set.image_nonempty.mp this
  have hother (S : Set (Fin 4))
      (hxS : x ∈ convexHull ℝ (f '' S))
      (hxSc : x ∈ convexHull ℝ (f '' Sᶜ)) :
      ∀ i ∈ S, ∃ j ∈ S, j ≠ i := by
    intro i hi
    by_contra hnone
    push Not at hnone
    have hSeq : S = {i} := by
      ext j
      constructor
      · intro hj
        exact Set.mem_singleton_iff.mpr (hnone j hj)
      · intro hj
        have hji : j = i := by simpa using hj
        simpa [hji] using hi
    have hxi : x = f i := by
      simpa [hSeq] using hxS
    have hiSc : i ∈ Sᶜ := hf Sᶜ i (by simpa [← hxi] using hxSc)
    exact (by simpa using hiSc : i ∉ S) hi
  obtain ⟨i, hi⟩ := hInonempty
  obtain ⟨j, hj, hji⟩ := hother I hxI hxIc i hi
  obtain ⟨k, hk⟩ := hIcNonempty
  obtain ⟨l, hl, hlk⟩ := hother Iᶜ hxIc (by simpa using hxI) k hk
  let IF : Finset (Fin 4) := I.toFinite.toFinset
  have hiIF : i ∈ IF := by simpa [IF] using hi
  have hjIF : j ∈ IF := by simpa [IF] using hj
  have hkIFc : k ∈ IFᶜ := by simpa [IF] using hk
  have hlIFc : l ∈ IFᶜ := by simpa [IF] using hl
  have hIFcard : IF.card = 2 := by
    have hleft : 2 ≤ IF.card := by
      rw [show 2 ≤ IF.card ↔ 1 < IF.card by omega, Finset.one_lt_card_iff]
      exact ⟨i, j, hiIF, hjIF, hji.symm⟩
    have hright : 2 ≤ IFᶜ.card := by
      rw [show 2 ≤ IFᶜ.card ↔ 1 < IFᶜ.card by omega, Finset.one_lt_card_iff]
      exact ⟨k, l, hkIFc, hlIFc, hlk.symm⟩
    have htotal : IF.card + IFᶜ.card = 4 := by simp
    omega
  have hIFccard : IFᶜ.card = 2 := by
    have htotal : IF.card + IFᶜ.card = 4 := by simp
    omega
  have hIFeq : IF = {i, j} := by
    have hij : i ≠ j := hji.symm
    have hpaircard : ({i, j} : Finset (Fin 4)).card = 2 := by simp [hij]
    have hsubset : ({i, j} : Finset (Fin 4)) ⊆ IF := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> assumption
    have hcardle : IF.card ≤ ({i, j} : Finset (Fin 4)).card := by
      rw [hIFcard, hpaircard]
    exact (Finset.eq_of_subset_of_card_le hsubset hcardle).symm
  have hIFceq : IFᶜ = {k, l} := by
    have hkl : k ≠ l := hlk.symm
    have hpaircard : ({k, l} : Finset (Fin 4)).card = 2 := by simp [hkl]
    have hsubset : ({k, l} : Finset (Fin 4)) ⊆ IFᶜ := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> assumption
    have hcardle : IFᶜ.card ≤ ({k, l} : Finset (Fin 4)).card := by
      rw [hIFccard, hpaircard]
    exact (Finset.eq_of_subset_of_card_le hsubset hcardle).symm
  have hIeq : I = {i, j} := by
    ext m
    calc
      m ∈ I ↔ m ∈ IF := by simp [IF]
      _ ↔ m ∈ ({i, j} : Finset (Fin 4)) := by rw [hIFeq]
      _ ↔ m ∈ ({i, j} : Set (Fin 4)) := by simp
  have hIceq : Iᶜ = {k, l} := by
    ext m
    calc
      m ∈ Iᶜ ↔ m ∈ IFᶜ := by simp [IF]
      _ ↔ m ∈ ({k, l} : Finset (Fin 4)) := by rw [hIFceq]
      _ ↔ m ∈ ({k, l} : Set (Fin 4)) := by simp
  have hxne (m : Fin 4) : f m ≠ x := by
    intro hmx
    by_cases hm : m ∈ I
    · have : m ∈ Iᶜ := hf Iᶜ m (by simpa [hmx] using hxIc)
      exact this hm
    · have : m ∈ I := hf I m (by simpa [hmx] using hxI)
      exact hm this
  have hmeet : OpenSegmentsMeet (f i) (f j) (f k) (f l) := by
    refine ⟨x, ?_, ?_⟩
    · apply mem_openSegment_of_ne_left_right (hxne i) (hxne j)
      simpa [hIeq, Set.image_pair, convexHull_pair] using hxI
    · apply mem_openSegment_of_ne_left_right (hxne k) (hxne l)
      simpa [hIceq, Set.image_pair, convexHull_pair] using hxIc
  have hcomp : ({k, l} : Set (Fin 4)) = ({i, j} : Set (Fin 4))ᶜ := by
    rw [← hIceq, hIeq]
  simpa [f] using classify_fin_four_pairing f i j k l hji hcomp hmeet

/-- Three different members of a convex-independent family are not collinear. -/
private theorem convexIndependent_not_collinear
    {ι : Type*} {f : ι → Plane} (hconv : ConvexIndependent ℝ f)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬Collinear ℝ ({f i, f j, f k} : Set Plane) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · have hjmem : j ∈ ({i, k} : Set ι) := hconv {i, k} j (by
      simpa [Set.image_pair, convexHull_pair] using h.mem_segment)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hjmem
    exact hjmem.elim (fun h ↦ hij h.symm) hjk
  · have hkmem : k ∈ ({j, i} : Set ι) := hconv {j, i} k (by
      simpa [Set.image_pair, convexHull_pair] using h.mem_segment)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hkmem
    exact hkmem.elim (fun h ↦ hjk h.symm) (fun h ↦ hik h.symm)
  · have himem : i ∈ ({k, j} : Set ι) := hconv {k, j} i (by
      simpa [Set.image_pair, convexHull_pair] using h.mem_segment)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at himem
    exact himem.elim hik (fun h ↦ hij h)

/-- Two disjoint diameter pairs in a four-point set of diameter one cross properly. -/
theorem four_point_diameter_segments_meet
    {a b c d : Plane}
    (hab : dist a b = 1) (hcd : dist c d = 1)
    (hac : dist a c ≤ 1) (had : dist a d ≤ 1)
    (hbc : dist b c ≤ 1) (hbd : dist b d ≤ 1)
    (hacne : a ≠ c) (hadne : a ≠ d) (hbcne : b ≠ c) (hbdne : b ≠ d) :
    OpenSegmentsMeet a b c d := by
  have hconv := diameter_endpoints_convexIndependent hab hcd hac had hbc hbd
    hacne hadne hbcne hbdne
  have hpairing := one_pairing_open_segments_meet hconv
  rcases hpairing with hcross | hcross | hcross
  · exact hcross
  · have habc : ¬Collinear ℝ ({a, b, c} : Set Plane) := by
      simpa using convexIndependent_not_collinear hconv
        (i := (0 : Fin 4)) (j := 1) (k := 2) (by decide) (by decide) (by decide)
    have hcda : ¬Collinear ℝ ({c, d, a} : Set Plane) := by
      simpa using convexIndependent_not_collinear hconv
        (i := (2 : Fin 4)) (j := 3) (k := 0) (by decide) (by decide) (by decide)
    have hlt := side_sum_lt_of_open_segments_meet habc hcda hcross
    rw [hab, hcd] at hlt
    linarith
  · have habd : ¬Collinear ℝ ({a, b, d} : Set Plane) := by
      simpa using convexIndependent_not_collinear hconv
        (i := (0 : Fin 4)) (j := 1) (k := 3) (by decide) (by decide) (by decide)
    have hdca : ¬Collinear ℝ ({d, c, a} : Set Plane) := by
      simpa using convexIndependent_not_collinear hconv
        (i := (3 : Fin 4)) (j := 2) (k := 0) (by decide) (by decide) (by decide)
    have hlt := side_sum_lt_of_open_segments_meet habd hdca hcross
    rw [hab, dist_comm d c, hcd] at hlt
    linarith

/-- All nonincident edges of the labelled diameter cycle cross properly. -/
theorem all_diameter_edges_cross
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) :
    ∀ i j : Fin 7,
      i ≠ j → i ≠ j + 3 → i + 3 ≠ j → i + 3 ≠ j + 3 →
        OpenSegmentsMeet (p i) (p (i + 3)) (p j) (p (j + 3)) := by
  intro i j hij hij3 hi3j hi3j3
  have hinjective := pairwise_distinct_of_diameter_pattern h
  apply four_point_diameter_segments_meet
  · exact h.hdiam i
  · exact h.hdiam j
  · exact dist_le_one_of_diameter_pattern h i j
  · exact dist_le_one_of_diameter_pattern h i (j + 3)
  · exact dist_le_one_of_diameter_pattern h (i + 3) j
  · exact dist_le_one_of_diameter_pattern h (i + 3) (j + 3)
  · exact hinjective.ne hij
  · exact hinjective.ne hij3
  · exact hinjective.ne hi3j
  · exact hinjective.ne hi3j3

/-- Four successive vertices of the diameter walk form the convex quadrilateral
whose opposite diameter edges cross. -/
private theorem walk_four_convexIndependent
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (k : Fin 7) :
    ConvexIndependent ℝ
      ![p (walkIndex k), p (walkIndex (k + 1)),
        p (walkIndex (k + 2)), p (walkIndex (k + 3))] := by
  apply diameter_endpoints_convexIndependent
  · have hd := h.hdiam (walkIndex k)
    fin_cases k <;> simpa [walkIndex] using hd
  · have hd := h.hdiam (walkIndex (k + 2))
    fin_cases k <;> simpa [walkIndex] using hd
  · exact dist_le_one_of_diameter_pattern h _ _
  · exact dist_le_one_of_diameter_pattern h _ _
  · exact dist_le_one_of_diameter_pattern h _ _
  · exact dist_le_one_of_diameter_pattern h _ _
  · exact (pairwise_distinct_of_diameter_pattern h).ne (by
      fin_cases k <;> decide)
  · exact (pairwise_distinct_of_diameter_pattern h).ne (by
      fin_cases k <;> decide)
  · exact (pairwise_distinct_of_diameter_pattern h).ne (by
      fin_cases k <;> decide)
  · exact (pairwise_distinct_of_diameter_pattern h).ne (by
      fin_cases k <;> decide)

private theorem walk_turn_ne_zero
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (k : Fin 7) :
    orientedArea (p (walkIndex k)) (p (walkIndex (k + 1)))
      (p (walkIndex (k + 2))) ≠ 0 := by
  apply orientedArea_ne_zero_of_not_collinear
  simpa using convexIndependent_not_collinear (walk_four_convexIndependent h k)
    (i := (0 : Fin 4)) (j := 1) (k := 2) (by decide) (by decide) (by decide)

private theorem walk_cross_area_ne_zero
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (k : Fin 7) :
    orientedArea (p (walkIndex (k + 2))) (p (walkIndex (k + 3)))
      (p (walkIndex k)) ≠ 0 := by
  apply orientedArea_ne_zero_of_not_collinear
  simpa using convexIndependent_not_collinear (walk_four_convexIndependent h k)
    (i := (2 : Fin 4)) (j := 3) (k := 0) (by decide) (by decide) (by decide)

private theorem walk_edges_two_apart_cross
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (k : Fin 7) :
    OpenSegmentsMeet
      (p (walkIndex k)) (p (walkIndex (k + 1)))
      (p (walkIndex (k + 2))) (p (walkIndex (k + 3))) := by
  have hcross := all_diameter_edges_cross h (walkIndex k) (walkIndex (k + 2))
    (by fin_cases k <;> decide) (by fin_cases k <;> decide)
    (by fin_cases k <;> decide) (by fin_cases k <;> decide)
  fin_cases k <;> simpa [walkIndex] using hcross

private theorem consecutive_walk_turn_product_pos
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (k : Fin 7) :
    0 < orientedArea (p (walkIndex k)) (p (walkIndex (k + 1)))
        (p (walkIndex (k + 2))) *
      orientedArea (p (walkIndex (k + 1))) (p (walkIndex (k + 2)))
        (p (walkIndex (k + 3))) := by
  exact consecutive_turn_product_pos_of_open_segments_meet
    (walk_edges_two_apart_cross h k) (walk_turn_ne_zero h k)
    (walk_cross_area_ne_zero h k)

/-- Along the diameter-cycle walk, every turn has one common orientation. -/
def SameTurnStar (p : Fin 7 → Plane) : Prop :=
  ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
    ∀ k : Fin 7,
      0 < ε * orientedArea
        (p (walkIndex k)) (p (walkIndex (k + 1))) (p (walkIndex (k + 2)))

/-- The seven unit diameters have the standard star orientation, up to reflection. -/
theorem diameter_star_structure
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) : SameTurnStar p := by
  let turn : Fin 7 → ℝ := fun k ↦
    orientedArea (p (walkIndex k)) (p (walkIndex (k + 1)))
      (p (walkIndex (k + 2)))
  have hstep (k : Fin 7) : 0 < turn k * turn (k + 1) := by
    have hs := consecutive_walk_turn_product_pos h k
    fin_cases k <;> simpa [turn] using hs
  have hne : turn 0 ≠ 0 := by simpa [turn] using walk_turn_ne_zero h 0
  have next_negative {x y : ℝ} (hx : x < 0) (hxy : 0 < x * y) : y < 0 := by
    rcases mul_pos_iff.mp hxy with hpos | hneg
    · linarith [hpos.1]
    · exact hneg.2
  have next_positive {x y : ℝ} (hx : 0 < x) (hxy : 0 < x * y) : 0 < y := by
    rcases mul_pos_iff.mp hxy with hpos | hneg
    · exact hpos.2
    · linarith [hneg.1]
  rcases lt_or_gt_of_ne hne with hnegative | hpositive
  · have h1 : turn 1 < 0 := next_negative hnegative (by simpa using hstep 0)
    have h2 : turn 2 < 0 := next_negative h1 (by simpa using hstep 1)
    have h3 : turn 3 < 0 := next_negative h2 (by simpa using hstep 2)
    have h4 : turn 4 < 0 := next_negative h3 (by simpa using hstep 3)
    have h5 : turn 5 < 0 := next_negative h4 (by simpa using hstep 4)
    have h6 : turn 6 < 0 := next_negative h5 (by simpa using hstep 5)
    refine ⟨-1, Or.inr rfl, ?_⟩
    intro k
    have hk : turn k < 0 := by
      fin_cases k <;> assumption
    simpa [turn] using (show 0 < (-1 : ℝ) * turn k by linarith)
  · have h1 : 0 < turn 1 := next_positive hpositive (by simpa using hstep 0)
    have h2 : 0 < turn 2 := next_positive h1 (by simpa using hstep 1)
    have h3 : 0 < turn 3 := next_positive h2 (by simpa using hstep 2)
    have h4 : 0 < turn 4 := next_positive h3 (by simpa using hstep 3)
    have h5 : 0 < turn 5 := next_positive h4 (by simpa using hstep 4)
    have h6 : 0 < turn 6 := next_positive h5 (by simpa using hstep 5)
    refine ⟨1, Or.inl rfl, ?_⟩
    intro k
    have hk : 0 < turn k := by
      fin_cases k <;> assumption
    simpa [turn] using hk

end LeanPool.Erdos132WeiE2.Geometry
