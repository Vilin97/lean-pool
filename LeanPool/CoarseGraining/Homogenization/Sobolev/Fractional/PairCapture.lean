/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ShellGeometry

/-!
# Pair capture by overlapping centers (G3)

If two points of a triadic cube `Q` are at `sup`-distance at most the side
length of a depth-`(j+1)` cell, then some overlapping center cube at depth `j`
contains both points.  This is the geometric input G3 for the fractional
Sobolev versus Besov comparison.

The proof parametrizes the depth-`m` descendants of `Q` by the integer index
window of radius `halfRange m = (3 ^ m - 1) / 2` around `3 ^ m * Q.index`,
then clamps the cell of the first point one step towards the center of the
window so that the resulting overlapping cube both stays inside `Q` and
captures the second point.
-/

namespace Homogenization
namespace Gagliardo

variable {d : ℕ}

/-- Radius of the integer index window of the depth-`m` descendants:
`halfRange m = (3 ^ m - 1) / 2`. -/
def halfRange : ℕ → ℤ
  | 0 => 0
  | m + 1 => 3 * halfRange m + 1

theorem halfRange_zero : halfRange 0 = 0 := rfl

theorem halfRange_succ (m : ℕ) : halfRange (m + 1) = 3 * halfRange m + 1 := rfl

theorem two_mul_halfRange : ∀ m : ℕ, 2 * halfRange m = 3 ^ m - 1
  | 0 => by simp [halfRange]
  | m + 1 => by
      have ih := two_mul_halfRange m
      have h3 : (3 : ℤ) ^ (m + 1) = 3 * 3 ^ m := by ring
      rw [halfRange_succ]
      omega

theorem halfRange_nonneg : ∀ m : ℕ, 0 ≤ halfRange m
  | 0 => le_refl 0
  | m + 1 => by
      have ih := halfRange_nonneg m
      rw [halfRange_succ]
      omega

theorem one_le_halfRange_succ (m : ℕ) : 1 ≤ halfRange (m + 1) := by
  have := halfRange_nonneg m
  rw [halfRange_succ]
  omega

private theorem triadicCube_ext {T R : TriadicCube d} (hs : T.scale = R.scale)
    (hi : T.index = R.index) : T = R := by
  cases T
  cases R
  simp_all

/-- Rounding bound: clamped division by `3` shrinks the index window by a
factor of `3`. -/
private theorem div3_bound {a h t : ℤ}
    (h1 : 3 * a - (3 * h + 1) ≤ t) (h2 : t ≤ 3 * a + (3 * h + 1)) :
    a - h ≤ (t + 1) / 3 ∧ (t + 1) / 3 ≤ a + h := by
  omega

/-- Membership constructor for `childCubes`: a cube one scale below `P` whose
index is within the child window of `P` is a child of `P`. -/
theorem mem_childCubes_of_scale_eq_of_index_range {P T : TriadicCube d}
    (hsc : T.scale = P.scale - 1)
    (hidx : ∀ i, 0 ≤ T.index i - 3 * P.index i + 1 ∧
      T.index i - 3 * P.index i + 1 < 3) :
    T ∈ childCubes P := by
  have hlt : ∀ i, (T.index i - 3 * P.index i + 1).toNat < 3 := by
    intro i
    have h := hidx i
    omega
  apply mem_childCubes_iff.mpr
  refine ⟨fun i => ⟨(T.index i - 3 * P.index i + 1).toNat, hlt i⟩, ?_⟩
  apply triadicCube_ext hsc
  funext i
  have h := hidx i
  have hcast :
      ((⟨(T.index i - 3 * P.index i + 1).toNat, hlt i⟩ : Fin 3) : ℤ) =
        T.index i - 3 * P.index i + 1 := by
    simp [Int.toNat_of_nonneg h.1]
  show T.index i =
    3 * P.index i +
      ((⟨(T.index i - 3 * P.index i + 1).toNat, hlt i⟩ : Fin 3) : ℤ) - 1
  rw [hcast]
  ring

/-- The index of a depth-`m` descendant of `Q` lies in the window of radius
`halfRange m` around `3 ^ m * Q.index`. -/
theorem index_range_of_mem_descendantsAtDepth {Q : TriadicCube d} :
    ∀ {m : ℕ} {S : TriadicCube d}, S ∈ descendantsAtDepth Q m →
      ∀ i, 3 ^ m * Q.index i - halfRange m ≤ S.index i ∧
        S.index i ≤ 3 ^ m * Q.index i + halfRange m
  | 0, S, hS => by
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hS
      subst hS
      intro i
      simp only [pow_zero, one_mul, halfRange_zero]
      omega
  | m + 1, S, hS => by
      rcases mem_descendantsAtDepth_succ_iff.mp hS with ⟨R, hR, hSchild⟩
      rcases mem_childCubes_iff.mp hSchild with ⟨digits, rfl⟩
      intro i
      have ih := index_range_of_mem_descendantsAtDepth hR i
      have hd0 : (0 : ℤ) ≤ (digits i : ℤ) := by
        exact_mod_cast Nat.zero_le (digits i).val
      have hd2 : (digits i : ℤ) ≤ 2 := by
        exact_mod_cast Nat.le_of_lt_succ (digits i).isLt
      have hkey : (3 : ℤ) ^ (m + 1) * Q.index i = 3 * (3 ^ m * Q.index i) := by
        ring
      rw [halfRange_succ, hkey]
      show 3 * (3 ^ m * Q.index i) - (3 * halfRange m + 1) ≤
          3 * R.index i + (digits i : ℤ) - 1 ∧
        3 * R.index i + (digits i : ℤ) - 1 ≤
          3 * (3 ^ m * Q.index i) + (3 * halfRange m + 1)
      constructor
      · linarith [ih.1]
      · linarith [ih.2]

/-- Converse: a cube at scale `Q.scale - m` whose index lies in the window of
radius `halfRange m` around `3 ^ m * Q.index` is a depth-`m` descendant. -/
theorem mem_descendantsAtDepth_of_index_range {Q : TriadicCube d} :
    ∀ {m : ℕ} {T : TriadicCube d}, T.scale = Q.scale - (m : ℤ) →
      (∀ i, 3 ^ m * Q.index i - halfRange m ≤ T.index i ∧
        T.index i ≤ 3 ^ m * Q.index i + halfRange m) →
      T ∈ descendantsAtDepth Q m
  | 0, T, hscale, hbound => by
      rw [descendantsAtDepth_zero, Finset.mem_singleton]
      refine triadicCube_ext ?_ ?_
      · simpa using hscale
      · funext i
        have h := hbound i
        simp only [pow_zero, one_mul, halfRange_zero] at h
        omega
  | m + 1, T, hscale, hbound => by
      have hPmem :
          ({ scale := Q.scale - (m : ℤ),
             index := fun i => (T.index i + 1) / 3 } : TriadicCube d) ∈
            descendantsAtDepth Q m := by
        refine mem_descendantsAtDepth_of_index_range rfl ?_
        intro i
        have h := hbound i
        have hkey : (3 : ℤ) ^ (m + 1) * Q.index i = 3 * (3 ^ m * Q.index i) := by
          ring
        rw [hkey, halfRange_succ] at h
        exact div3_bound h.1 h.2
      have hchild :
          T ∈ childCubes
            ({ scale := Q.scale - (m : ℤ),
               index := fun i => (T.index i + 1) / 3 } : TriadicCube d) := by
        apply mem_childCubes_of_scale_eq_of_index_range
        · show T.scale = Q.scale - (m : ℤ) - 1
          rw [hscale]
          push_cast
          ring
        · intro i
          show 0 ≤ T.index i - 3 * ((T.index i + 1) / 3) + 1 ∧
            T.index i - 3 * ((T.index i + 1) / 3) + 1 < 3
          omega
      exact mem_descendantsAtDepth_succ_iff.mpr ⟨_, hPmem, hchild⟩

/-- Clamp `u` to the window `[A - N, A + N]`. -/
def clampIndex (A N u : ℤ) : ℤ := max (A - N) (min (A + N) u)

/-- The clamped index stays in the wide window of radius `h`. -/
theorem clampIndex_range_wide {A h u : ℤ} (hh : 1 ≤ h) :
    A - h ≤ clampIndex A (h - 1) u ∧ clampIndex A (h - 1) u ≤ A + h := by
  unfold clampIndex
  omega

/-- The clamped index lies in the strict window of radius `h - 1`. -/
theorem clampIndex_mem_range {A h u : ℤ} (hh : 1 ≤ h) :
    A - (h - 1) ≤ clampIndex A (h - 1) u ∧
      clampIndex A (h - 1) u ≤ A + (h - 1) := by
  unfold clampIndex
  omega

/-- The clamped index moves by at most one. -/
theorem clampIndex_near {A h u : ℤ} (hh : 1 ≤ h)
    (h1 : A - h ≤ u) (h2 : u ≤ A + h) :
    u - 1 ≤ clampIndex A (h - 1) u ∧ clampIndex A (h - 1) u ≤ u + 1 := by
  unfold clampIndex
  omega

/-- Trichotomy: clamping is the identity except at the two extremes of the
wide window, where it moves one step inward. -/
theorem clampIndex_cases {A h u : ℤ} (hh : 1 ≤ h)
    (h1 : A - h ≤ u) (h2 : u ≤ A + h) :
    clampIndex A (h - 1) u = u ∨
      (u = A - h ∧ clampIndex A (h - 1) u = u + 1) ∨
      (u = A + h ∧ clampIndex A (h - 1) u = u - 1) := by
  unfold clampIndex
  omega

/-- Coordinate arithmetic for the fit lemma: a strict-window cell coordinate
interval is contained in the corresponding parent coordinate interval. -/
private theorem coord_fit_real {qi ti p c xv : ℝ} (hc : 0 < c)
    (hlow : 2 * (p * qi) - p + 3 ≤ 2 * ti)
    (hhigh : 2 * ti ≤ 2 * (p * qi) + p - 3)
    (hx1 : (ti - 3 / 2) * c ≤ xv) (hx2 : xv < (ti + 3 / 2) * c) :
    (qi - 1 / 2) * (p * c) ≤ xv ∧ xv < (qi + 1 / 2) * (p * c) := by
  constructor
  · have h : (qi - 1 / 2) * p ≤ ti - 3 / 2 := by linarith
    have h2 : (qi - 1 / 2) * p * c ≤ (ti - 3 / 2) * c :=
      mul_le_mul_of_nonneg_right h hc.le
    calc (qi - 1 / 2) * (p * c) = (qi - 1 / 2) * p * c := by ring
      _ ≤ (ti - 3 / 2) * c := h2
      _ ≤ xv := hx1
  · have h : ti + 3 / 2 ≤ (qi + 1 / 2) * p := by linarith
    have h2 : (ti + 3 / 2) * c ≤ (qi + 1 / 2) * p * c :=
      mul_le_mul_of_nonneg_right h hc.le
    calc xv < (ti + 3 / 2) * c := hx2
      _ ≤ (qi + 1 / 2) * p * c := h2
      _ = (qi + 1 / 2) * (p * c) := by ring

/-- A point of a triadic cell lies in the overlapping cube of any center
within index distance one at the same scale. -/
private theorem coord_overlap_of_near {s u xi c : ℝ} (hc : 0 < c)
    (h1 : u - 1 ≤ s) (h2 : s ≤ u + 1)
    (hx1 : (u - 1 / 2) * c ≤ xi) (hx2 : xi < (u + 1 / 2) * c) :
    (s - 3 / 2) * c ≤ xi ∧ xi < (s + 3 / 2) * c := by
  constructor
  · have h : (s - 3 / 2) * c ≤ (u - 1 / 2) * c :=
      mul_le_mul_of_nonneg_right (by linarith) hc.le
    linarith
  · have h : (u + 1 / 2) * c ≤ (s + 3 / 2) * c :=
      mul_le_mul_of_nonneg_right (by linarith) hc.le
    linarith

/-- Fit lemma: an overlapping cube whose center index lies in the strict
window of radius `halfRange (m + 1) - 1` is contained in `Q`. -/
theorem overlap_cubeSet_subset_of_index_range {Q T : TriadicCube d} {m : ℕ}
    (hscale : T.scale = Q.scale - ((m + 1 : ℕ) : ℤ))
    (hbound : ∀ i,
      3 ^ (m + 1) * Q.index i - (halfRange (m + 1) - 1) ≤ T.index i ∧
        T.index i ≤ 3 ^ (m + 1) * Q.index i + (halfRange (m + 1) - 1)) :
    ScalarOverlap.cubeSet T ⊆ Homogenization.cubeSet Q := by
  have hcT : (0 : ℝ) < cubeScaleFactor T := cubeScaleFactor_pos' T
  have hp : ((3 : ℝ) ^ (m + 1)) ≠ 0 := by positivity
  have hCQ : cubeScaleFactor Q = (3 : ℝ) ^ (m + 1) * cubeScaleFactor T := by
    have h : cubeScaleFactor T = cubeScaleFactor Q / (3 : ℝ) ^ (m + 1) := by
      unfold cubeScaleFactor
      rw [hscale, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    rw [h, mul_comm, div_mul_cancel₀ _ hp]
  intro x hxmem i
  obtain ⟨hx1, hx2⟩ := hxmem i
  obtain ⟨hb1, hb2⟩ := hbound i
  have h2m := two_mul_halfRange (m + 1)
  have hZlow : 2 * ((3 : ℤ) ^ (m + 1) * Q.index i) - (3 : ℤ) ^ (m + 1) + 3 ≤
      2 * T.index i := by
    linarith
  have hZhigh : 2 * T.index i ≤
      2 * ((3 : ℤ) ^ (m + 1) * Q.index i) + (3 : ℤ) ^ (m + 1) - 3 := by
    linarith
  have hRlow : 2 * ((3 : ℝ) ^ (m + 1) * (Q.index i : ℝ)) - (3 : ℝ) ^ (m + 1) + 3 ≤
      2 * (T.index i : ℝ) := by
    exact_mod_cast hZlow
  have hRhigh : 2 * (T.index i : ℝ) ≤
      2 * ((3 : ℝ) ^ (m + 1) * (Q.index i : ℝ)) + (3 : ℝ) ^ (m + 1) - 3 := by
    exact_mod_cast hZhigh
  rw [hCQ]
  exact coord_fit_real hcT hRlow hRhigh hx1 hx2

/-- The candidate overlapping center: the depth-`(j + 1)` cell `U` of the
first point, clamped one step into the strict index window of `Q`. -/
def pairCenter (Q U : TriadicCube d) (j : ℕ) : TriadicCube d :=
  { scale := U.scale
    index := fun i =>
      clampIndex (3 ^ (j + 1) * Q.index i) (halfRange (j + 1) - 1) (U.index i) }

theorem pairCenter_scale (Q U : TriadicCube d) (j : ℕ) :
    (pairCenter Q U j).scale = U.scale := rfl

theorem pairCenter_index (Q U : TriadicCube d) (j : ℕ) (i : Fin d) :
    (pairCenter Q U j).index i =
      clampIndex (3 ^ (j + 1) * Q.index i) (halfRange (j + 1) - 1)
        (U.index i) := rfl

theorem cubeScaleFactor_pairCenter (Q U : TriadicCube d) (j : ℕ) :
    cubeScaleFactor (pairCenter Q U j) = cubeScaleFactor U := rfl

/-- G3 (pair capture): two points of `Q` at `sup`-distance at most the side
length of a depth-`(j + 1)` cell are both contained in some overlapping
center cube at depth `j`. -/
theorem exists_centersAtDepth_pair_mem {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    {x y : Vec d} (hx : x ∈ Homogenization.cubeSet Q)
    (hy : y ∈ Homogenization.cubeSet Q)
    (hxy : dist x y ≤ cubeScaleFactor Q / 3 ^ (j + 1)) :
    ∃ S ∈ ScalarOverlap.centersAtDepth Q j,
      x ∈ ScalarOverlap.cubeSet S ∧ y ∈ ScalarOverlap.cubeSet S := by
  obtain ⟨U, hU, hxU⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet (j + 1) hx
  have hUscale : U.scale = Q.scale - ((j + 1 : ℕ) : ℤ) :=
    scale_eq_sub_of_mem_descendantsAtDepth hU
  have hUb := index_range_of_mem_descendantsAtDepth hU
  have hh1 : 1 ≤ halfRange (j + 1) := one_le_halfRange_succ j
  have hc : (0 : ℝ) < cubeScaleFactor U := cubeScaleFactor_pos' U
  have hCQ : cubeScaleFactor Q = (3 : ℝ) ^ (j + 1) * cubeScaleFactor U := by
    rw [cubeScaleFactor_descendant_eq_div_pow hU, mul_comm,
      div_mul_cancel₀ _ (by positivity : ((3 : ℝ) ^ (j + 1)) ≠ 0)]
  have hxyc : dist x y ≤ cubeScaleFactor U := by
    rw [cubeScaleFactor_descendant_eq_div_pow hU]
    exact hxy
  refine ⟨pairCenter Q U j, ?_, ?_, ?_⟩
  · -- membership among the overlapping centers at depth `j`
    rw [ScalarOverlap.mem_centersAtDepth_iff]
    constructor
    · refine mem_descendantsAtDepth_of_index_range hUscale ?_
      intro i
      rw [pairCenter_index]
      exact clampIndex_range_wide hh1
    · refine overlap_cubeSet_subset_of_index_range hUscale ?_
      intro i
      rw [pairCenter_index]
      exact clampIndex_mem_range hh1
  · -- the first point lies in the overlapping cube
    intro i
    rw [pairCenter_index, cubeScaleFactor_pairCenter]
    obtain ⟨hn1, hn2⟩ := clampIndex_near hh1 (hUb i).1 (hUb i).2
    have hn1' := (Int.cast_le (R := ℝ)).mpr hn1
    have hn2' := (Int.cast_le (R := ℝ)).mpr hn2
    push_cast at hn1' hn2'
    exact coord_overlap_of_near hc hn1' hn2' (hxU i).1 (hxU i).2
  · -- the second point lies in the overlapping cube
    intro i
    rw [pairCenter_index, cubeScaleFactor_pairCenter]
    obtain ⟨hya, hyb⟩ := hy i
    obtain ⟨hxa, hxb⟩ := hxU i
    have hdist : |y i - x i| ≤ cubeScaleFactor U := by
      have h1 := dist_le_pi_dist y x i
      rw [Real.dist_eq, dist_comm y x] at h1
      exact h1.trans hxyc
    obtain ⟨hd1, hd2⟩ := abs_le.mp hdist
    have h2m := two_mul_halfRange (j + 1)
    rcases clampIndex_cases hh1 (hUb i).1 (hUb i).2 with
      hcase | ⟨hext, hcase⟩ | ⟨hext, hcase⟩
    · -- interior case: the center is the cell of `x` itself
      have hcaseR :
          ((clampIndex (3 ^ (j + 1) * Q.index i) (halfRange (j + 1) - 1)
            (U.index i) : ℤ) : ℝ) = (U.index i : ℝ) := by
        exact_mod_cast hcase
      rw [hcaseR]
      constructor
      · linarith
      · linarith
    · -- lower extreme: the cell boundary aligns with the boundary of `Q`
      have hcaseR :
          ((clampIndex (3 ^ (j + 1) * Q.index i) (halfRange (j + 1) - 1)
            (U.index i) : ℤ) : ℝ) = (U.index i : ℝ) + 1 := by
        exact_mod_cast hcase
      rw [hcaseR]
      have hZ : (2 : ℤ) * U.index i - 1 =
          2 * (3 ^ (j + 1) * Q.index i) - 3 ^ (j + 1) := by
        linarith
      have hZR : (2 : ℝ) * (U.index i : ℝ) - 1 =
          2 * ((3 : ℝ) ^ (j + 1) * (Q.index i : ℝ)) - (3 : ℝ) ^ (j + 1) := by
        exact_mod_cast hZ
      have halign : ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q =
          ((U.index i : ℝ) - 1 / 2) * cubeScaleFactor U := by
        rw [hCQ]
        linear_combination (-(cubeScaleFactor U) / 2) * hZR
      constructor
      · linarith
      · linarith
    · -- upper extreme: mirror image of the previous case
      have hcaseR :
          ((clampIndex (3 ^ (j + 1) * Q.index i) (halfRange (j + 1) - 1)
            (U.index i) : ℤ) : ℝ) = (U.index i : ℝ) - 1 := by
        exact_mod_cast hcase
      rw [hcaseR]
      have hZ : (2 : ℤ) * U.index i + 1 =
          2 * (3 ^ (j + 1) * Q.index i) + 3 ^ (j + 1) := by
        linarith
      have hZR : (2 : ℝ) * (U.index i : ℝ) + 1 =
          2 * ((3 : ℝ) ^ (j + 1) * (Q.index i : ℝ)) + (3 : ℝ) ^ (j + 1) := by
        exact_mod_cast hZ
      have halign : ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q =
          ((U.index i : ℝ) + 1 / 2) * cubeScaleFactor U := by
        rw [hCQ]
        linear_combination (-(cubeScaleFactor U) / 2) * hZR
      constructor
      · linarith
      · linarith

end Gagliardo
end Homogenization
