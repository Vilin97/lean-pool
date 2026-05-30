/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha and contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import LeanPool.Monsky.SimplexBasic
import LeanPool.Monsky.SegmentTriangle
import LeanPool.Monsky.BasicDefinitions
import LeanPool.Monsky.RainbowTriangles
import LeanPool.Monsky.Square

namespace LeanPool.Monsky


local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open BigOperators
open Finset


/- This rewriting is for convenience. -/
/-- `disjoint_set X f` states that `f` sends distinct elements of `X` to disjoint sets. -/
def disjoint_set {α β : Type} (X : Set α) (f : α → Set β) :=
  ∀ a₁ a₂, a₁ ∈ X → a₂ ∈ X → a₁ ≠ a₂ → Disjoint (f a₁) (f a₂)
/-- `covers X Y f` states that `Y` is the union of `f a` over `a ∈ X`. -/
def covers {α β} (X : Set α) (Y : Set β) (f : α → Set β) := Y = ⋃ a ∈ X, f a

lemma is_cover_iff (X : Set ℝ²) (S : Set Triangle)
    : is_disjoint_cover X S ↔ covers S X closed_hull ∧ disjoint_set S open_hull := by
  simp only [is_disjoint_cover, is_cover, is_disjoint_polygon_set, ne_eq, covers, disjoint_set,
    and_congr_right_iff]
  intro _
  constructor
  · intro h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq
    exact h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq
  · intro h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq
    exact h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq

lemma disjoint_aux {α β : Type} (S₁ S₂ : Set α) (f : α → Set β) (h₁ : disjoint_set S₁ f)
    (h₂ : disjoint_set S₂ f)
    (h₃ : ∀ a₁ a₂, a₁ ∈ S₁ → a₂ ∈ S₂ → Disjoint (f a₁) (f a₂)) :
    disjoint_set (S₁ ∪ S₂) f := by
  intro a₁ a₂ ha₁ ha₂ hneq
  obtain ha₁ | ha₁ := ha₁ <;> obtain ha₂ | ha₂ := ha₂
  · exact h₁ a₁ a₂ ha₁ ha₂ hneq
  · exact h₃ a₁ a₂ ha₁ ha₂
  · exact (h₃ a₂ a₁ ha₂ ha₁ ).symm
  · exact h₂ a₁ a₂ ha₁ ha₂ hneq


/-
  The square can be covered by an even number of triangles.
-/

/- These two triangles dissect the square and have equal area.-/
/-- The lower triangle of the standard two-triangle dissection of the unit square. -/
def Δ₀ : Triangle  := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
/-- The upper triangle of the standard two-triangle dissection of the unit square. -/
def Δ₀' : Triangle  := fun | 0 => (v 1 0) | 1 => (v 0 1) | 2 => (v 1 1)

lemma areaΔ₀ : triangle_area Δ₀ = 1 / 2 := by
  simp [triangle_area, det, Δ₀]

lemma areaΔ₀' : triangle_area Δ₀' = 1 / 2 := by
  simp [triangle_area, det, Δ₀']


/- Now we show how a cover of size two implies a cover of any even size.-/

/- Elementary stuff about scaling (only in the y direction).-/

/-- Scales the second coordinate of a plane vector by `a`. -/
def scale_vector (a : ℝ) (y : ℝ²) : ℝ² := !₂[y 0, a * y 1]

/-- Applies `scale_vector a` to every vertex of a triangle. -/
def scale_triangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ scale_vector a (T i)

lemma scale_triangle_det (a : ℝ) (T : Triangle) :
    det (scale_triangle a T) = a * det T := by
  simp [det, scale_triangle, scale_vector]
  ring

lemma scale_triangle_area (a : ℝ) (T : Triangle)
    : triangle_area (scale_triangle a T) = |a| * (triangle_area T) := by
  simp only [triangle_area, scale_triangle_det a T, abs_mul, mul_div_assoc]


/- Elementary stuff about translating (only in the y direction).-/

/-- Translates the second coordinate of a plane vector by `a`. -/
def translate_vector (a : ℝ) (x : ℝ²) : ℝ² := !₂[x 0, a + x 1]
/-- Applies `translate_vector a` to every vertex of a triangle. -/
def translate_triangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ translate_vector a (T i)

lemma translate_triangle_det (a : ℝ) (T : Triangle) :
    det (translate_triangle a T) = det T := by
  simp [det, translate_triangle, translate_vector]
  ring

lemma translate_triangle_area (a : ℝ) (T : Triangle)
    : triangle_area (translate_triangle a T) = (triangle_area T) := by
  simp only [triangle_area, translate_triangle_det]

lemma translate_injective {T : Triangle} :
    Function.Injective (fun (a : ℝ) ↦ translate_triangle a T) := by
  intro _ _ hsame
  have hsame := congrArg (fun Δ ↦ Δ 0 1) hsame
  simp [translate_triangle, translate_vector] at hsame
  assumption

-- Here a different try. Just give a very explicit cover.
/-- The `n` translated copies of the scaled lower triangle `Δ₀` covering the square. -/
noncomputable def zig_part_cover (n : ℕ)
  := Finset.image
    (fun (s : Fin n) ↦
      translate_triangle ((s : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀)) univ

/-- The `n` translated copies of the scaled upper triangle `Δ₀'` covering the square. -/
noncomputable def zag_part_cover (n : ℕ)
  := Finset.image
    (fun (s : Fin n) ↦
      translate_triangle ((s : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀')) univ

lemma zig_zag_cover_size_aux (n : ℕ) :
    (zig_part_cover n).card = n ∧ (zag_part_cover n).card = n := by
  rw [zig_part_cover, zag_part_cover]
  constructor <;> (
    rw [Finset.card_image_of_injective]
    · exact card_fin n
    · convert Function.Injective.comp translate_injective ?_
      intro s _ hsame
      have hn : (n : ℝ) ≠ 0 := fun h ↦ Fin.elim0 (Fin.cast ((Nat.cast_eq_zero).1 h) s)
      simp_all only [div_eq_div_iff hn hn, mul_eq_mul_right_iff, or_false, Nat.cast_inj]
      exact Fin.eq_of_val_eq hsame
    )

lemma zig_zag_cover_size (n : ℕ) : (zig_part_cover n ∪ zag_part_cover n).card = 2 * n := by
  have h : (zig_part_cover n ∩ zag_part_cover n).card = 0 := by
    rw [card_eq_zero, ←disjoint_iff_inter_eq_empty, disjoint_left]
    intro _ h₁ h₂
    simp only [zig_part_cover, one_div, mem_image, mem_univ, true_and, zag_part_cover] at h₁ h₂
    have ⟨s₁,hs₁⟩ := h₁
    have ⟨s₂,hs₂⟩ := h₂
    rw [←hs₂] at hs₁
    have hsame := congrArg (fun Δ ↦ Δ 0 0) hs₁
    simp [translate_triangle, translate_vector, scale_triangle, scale_vector, Δ₀, Δ₀'] at hsame
  simp_rw [card_union, zig_zag_cover_size_aux, h, tsub_zero, two_mul]


lemma zig_cover_area {n : ℕ} :
    ∀ {Δ : Triangle}, Δ ∈ zig_part_cover n → triangle_area Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp only [zig_part_cover, one_div, mem_image, mem_univ, true_and] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translate_triangle_area, scale_triangle_area, areaΔ₀]
  simp

lemma zag_cover_area {n : ℕ} :
    ∀ {Δ : Triangle}, Δ ∈ zag_part_cover n → triangle_area Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp only [zag_part_cover, one_div, mem_image, mem_univ, true_and] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translate_triangle_area, scale_triangle_area, areaΔ₀']
  simp

lemma fin_el_bound {n : ℕ} {x : ℝ} {s₁ s₂ : Fin n} (h₁l : x - 1 < s₁) (h₁u : s₁ < x)
    (h₂l : x - 1 < s₂) (h₂u : s₂ < x) : s₁ = s₂ := by
  wlog hl : s₁ ≤ s₂
  · refine (this h₂l h₂u h₁l h₁u (le_of_not_ge hl)).symm
  · refine Fin.le_antisymm_iff.mpr ⟨hl, ?_⟩
    by_contra hc
    rw [not_le, @Fin.lt_def, @Nat.lt_iff_add_one_le,
        ←Nat.cast_le (α := ℝ), @Nat.cast_add, @Nat.cast_one] at hc
    linarith

lemma zig_open_disjoint {n : ℕ} : disjoint_set ((zig_part_cover n) : Set Triangle) open_hull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp only [zig_part_cover, one_div, coe_image, coe_univ, Set.image_univ, Set.mem_range]
      at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff (by simp [det, translate_triangle, scale_triangle, Δ₀,
      translate_vector, scale_vector, Nat.ne_zero_of_lt nsign])] at hx₁
    rw [←hs₂, open_triangle_iff (by simp [det, translate_triangle, scale_triangle, Δ₀,
      translate_vector, scale_vector, Nat.ne_zero_of_lt nsign])] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    refine hΔneq ?_
    simp [Tco, sign_seg, det, scale_triangle, translate_triangle, scale_triangle,
      translate_vector, Tside, scale_vector, Δ₀] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    rw [←hs₁, ←hs₂, fin_el_bound (x := ↑n * x.ofLp 1) (s₁ := s₁) (s₂ := s₂)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  · simp [Nat.eq_zero_of_not_pos nsign, zig_part_cover, disjoint_set]

lemma zag_open_disjoint {n : ℕ} : disjoint_set ((zag_part_cover n) : Set Triangle) open_hull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp only [zag_part_cover, one_div, coe_image, coe_univ, Set.image_univ, Set.mem_range]
      at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff (by
      simp [det, translate_triangle, scale_triangle, Δ₀', translate_vector, scale_vector]
      field_simp [Nat.ne_zero_of_lt nsign]
      ring_nf; norm_num)] at hx₁
    rw [←hs₂, open_triangle_iff (by
      simp [det, translate_triangle, scale_triangle, Δ₀', translate_vector, scale_vector]
      field_simp [Nat.ne_zero_of_lt nsign]
      ring_nf; norm_num)] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    refine hΔneq ?_
    simp [Tco, sign_seg, det, scale_triangle, translate_triangle, scale_triangle,
      translate_vector, Tside, scale_vector, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    rw [←hs₁, ←hs₂, fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  · simp [Nat.eq_zero_of_not_pos nsign, zag_part_cover, disjoint_set]

lemma zig_zag_open_disjoint {n : ℕ}
    : ∀ a₁ a₂, a₁ ∈ (zig_part_cover n) → a₂ ∈ (zag_part_cover n) →
      Disjoint (open_hull a₁) (open_hull a₂) := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂
    simp only [zig_part_cover, one_div, mem_image, mem_univ, true_and, zag_part_cover] at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff (by simp [det, translate_triangle, scale_triangle, Δ₀,
      translate_vector, scale_vector, Nat.ne_zero_of_lt nsign])] at hx₁
    rw [←hs₂, open_triangle_iff (by
      simp [det, translate_triangle, scale_triangle, Δ₀', translate_vector, scale_vector]
      field_simp [Nat.ne_zero_of_lt nsign]
      ring_nf; norm_num)] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₁ := hx₂ 1
    have hx₂₂ := hx₂ 2
    simp [Tco, sign_seg, det, scale_triangle, translate_triangle, scale_triangle,
      translate_vector, Tside, scale_vector, Δ₀, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
    ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
    field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
    have l := fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂)
      (by linarith) (by linarith) (by linarith) (by linarith)
    rw [l] at hx₁₀ hx₁₂
    linarith
  · simp [Nat.eq_zero_of_not_pos nsign, zag_part_cover]


lemma zig_zag_covers_square {n : ℕ} (hn : n ≠ 0)
    : covers ((zig_part_cover n ∪ zag_part_cover n) : Set Triangle) (closed_hull unit_square)
      closed_hull := by
  ext x
  simp only [closed_unit_square_eq, Fin.forall_fin_two, Fin.isValue, Set.mem_setOf_eq,
    Set.mem_union, SetLike.mem_coe, Set.mem_iUnion, exists_prop]
  constructor
  · intro hx
    replace hx : ∀ i : Fin 2, 0 ≤ x i ∧ x i ≤ 1 :=
      fun i => by fin_cases i <;> exact ⟨by tauto, by tauto⟩
    -- Determine in which part of the cover x falls.
    -- Nat.floor (n * x 1) is not right unfortunately when x 1 = 1
    by_cases hx₁ : x 1 < 1
    · let j := Nat.floor (n * x 1)
      by_cases hj : (n * x 1 - j) + x 0 ≤ 1
      · use translate_triangle ((j : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀)
        constructor
        · left
          rw [zig_part_cover,mem_image]
          refine ⟨⟨j,?_⟩ ,by simp⟩
          rw [propext (Nat.floor_lt' hn)]
          convert (mul_lt_mul_iff_right₀ ?_).mpr hx₁
          · ring
          · rw [Nat.cast_pos]
            exact Nat.zero_lt_of_ne_zero hn
        · rw [closed_triangle_iff]
          · intro i
            fin_cases i <;> (
              simp [Tco, sign_seg, det, scale_triangle, translate_triangle, scale_triangle,
                translate_vector, Tside, scale_vector, Δ₀];
              field_simp [hn]
              ring_nf
              try linarith [hx 0 ]
            )
            rw [sub_nonneg, mul_comm]
            exact Nat.floor_le (Left.mul_nonneg (Nat.cast_nonneg' _) (hx 1).1)
          · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
            · simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, hn, not_false_eq_true]
            · simp [det, Δ₀]
      · use translate_triangle ((j : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀')
        constructor
        · right
          rw [zag_part_cover,mem_image]
          refine ⟨⟨j,?_⟩ ,by simp⟩
          rw [propext (Nat.floor_lt' hn)]
          convert (mul_lt_mul_iff_right₀ ?_).mpr hx₁
          · ring
          · rw [Nat.cast_pos]
            exact Nat.zero_lt_of_ne_zero hn
        · rw [closed_triangle_iff]
          · intro i
            fin_cases i <;> (
              simp [Tco, sign_seg, det, scale_triangle, translate_triangle, scale_triangle,
                translate_vector, Tside, scale_vector, Δ₀'];
              field_simp [hn]
              ring_nf
              try linarith [hx 0 ]
            )
            convert sub_nonneg.2 (le_of_lt (Nat.lt_floor_add_one (↑n * x 1))) using 1
            ring
          · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
            · simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, hn, not_false_eq_true]
            · simp [det, Δ₀']
    · have hx₁ : x 1 = 1 := by linarith [hx 1]
      · use translate_triangle (( n  - 1 ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀')
        constructor
        · right
          rw [zag_part_cover,mem_image]
          refine ⟨⟨n - 1, Nat.sub_one_lt hn⟩,?_⟩
          simp only [mem_univ, one_div, true_and]
          conv =>
            arg 1; arg 1; arg 1
            rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one]
        · rw [closed_triangle_iff]
          · intro i
            fin_cases i <;> (
              simp [Tco, sign_seg, det, scale_triangle, translate_triangle, scale_triangle,
                translate_vector, Tside, scale_vector, Δ₀', hx₁];
              field_simp [hn]
              ring_nf
              try linarith [hx 0]
            )
          · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
            · simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, hn, not_false_eq_true]
            · simp [det, Δ₀']
  · rintro ⟨S,(hzig | hzag),hS⟩
    · simp only [zig_part_cover, one_div, mem_image, mem_univ, true_and] at hzig
      have ⟨s, hs⟩ := hzig
      rw [←hs, closed_triangle_iff] at hS
      · have hs₀ := hS 0
        have hs₁ := hS 1
        have hs₂ := hS 2
        simp [Tco, sign_seg, det, scale_triangle, translate_triangle, scale_triangle,
          translate_vector, Tside, scale_vector, Δ₀] at hs₀ hs₁ hs₂
        field_simp [hn] at hs₀ hs₁ hs₂
        refine ⟨⟨hs₁, by linarith⟩, ?_, ?_⟩
        · have hnpos : (0 : ℝ) < ↑n := Nat.cast_pos'.mpr (Nat.zero_lt_of_ne_zero hn)
          have hmul : (0 : ℝ) ≤ ↑n * x.ofLp 1 := by
            have : (0 : ℝ) ≤ (s.1 : ℝ) := Nat.cast_nonneg' s.1
            linarith
          exact (mul_nonneg_iff_of_pos_left hnpos).mp hmul
        · have hnpos : (0 : ℝ) < ↑n := Nat.cast_pos'.mpr (Nat.zero_lt_of_ne_zero hn)
          rw [add_assoc, le_neg_add_iff_le] at hs₀
          have hthis := le_trans hs₁ hs₀
          rw [le_neg_add_iff_le] at hthis
          have hsn : (↑↑s + 1 : ℝ) ≤ ↑n := by exact_mod_cast Nat.add_one_le_of_lt s.2
          have hbound : ↑n * x.ofLp 1 ≤ ↑n * 1 := by rw [mul_one]; linarith
          exact le_of_mul_le_mul_left hbound hnpos
      · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
        · exact inv_ne_zero (Nat.cast_ne_zero.mpr hn)
        · simp [det, Δ₀]
    · simp only [zag_part_cover, one_div, mem_image, mem_univ, true_and] at hzag
      have ⟨s, hs⟩ := hzag
      rw [←hs, closed_triangle_iff] at hS
      · have hs₀ := hS 0
        have hs₁ := hS 1
        have hs₂ := hS 2
        simp [Tco, sign_seg, det, scale_triangle, translate_triangle, scale_triangle,
          translate_vector, Tside, scale_vector, Δ₀'] at hs₀ hs₁ hs₂
        field_simp [hn] at hs₀ hs₁ hs₂
        conv at hs₀ => ring_nf
        conv at hs₁ => ring_nf
        conv at hs₂ => ring_nf
        have hnpos : (0 : ℝ) < ↑n := Nat.cast_pos'.mpr (Nat.zero_lt_of_ne_zero hn)
        have hscast : (0 : ℝ) ≤ (s.1 : ℝ) := Nat.cast_nonneg' s.1
        refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
        · have hmul : (0 : ℝ) ≤ x.ofLp 1 * ↑n := by linarith
          exact (mul_nonneg_iff_of_pos_right hnpos).mp hmul
        · have hsn : (↑↑s + 1 : ℝ) ≤ ↑n := by exact_mod_cast Nat.add_one_le_of_lt s.2
          have hbound : x.ofLp 1 * ↑n ≤ 1 * ↑n := by rw [one_mul]; linarith
          exact le_of_mul_le_mul_right hbound hnpos
      · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
        · exact inv_ne_zero (Nat.cast_ne_zero.mpr hn)
        · simp [det, Δ₀']


theorem monsky_easy_direction' {n : ℕ} (hn : Even n) (hnneq : n ≠ 0)
    : (∃ (S : Finset Triangle), is_equal_area_cover (closed_hull unit_square) S ∧ S.card = n) := by
  have ⟨m,hm⟩ := hn
  use (zig_part_cover m ∪ zag_part_cover m)
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [is_cover_iff]
    refine ⟨?_,?_⟩
    · convert zig_zag_covers_square (n := m) ?_
      · simp only [coe_union]
      · intro h; apply hnneq
        rw [hm,h,add_zero]
    · convert disjoint_aux (S₁ := zig_part_cover m) (S₂ := (zag_part_cover m : Set Triangle))
        (f := open_hull) zig_open_disjoint zag_open_disjoint zig_zag_open_disjoint
      exact coe_union (zig_part_cover m) (zag_part_cover m)
  · use 1 / (2*m)
    intro Δ hΔ
    simp only [coe_union, Set.mem_union, SetLike.mem_coe] at hΔ
    obtain hΔ | hΔ := hΔ
    · exact zig_cover_area hΔ
    · exact zag_cover_area hΔ
  · convert zig_zag_cover_size m
    linarith

end Monsky
end LeanPool
