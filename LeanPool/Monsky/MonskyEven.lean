/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha, contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Abel
import LeanPool.Monsky.SimplexBasic
import LeanPool.Monsky.SegmentTriangle
import LeanPool.Monsky.BasicDefinitions
import LeanPool.Monsky.RainbowTriangles
import LeanPool.Monsky.Square

/-!
# LeanPool.Monsky.MonskyEven

Imported Lean Pool material for `LeanPool.Monsky.MonskyEven`.
-/

namespace LeanPool.Monsky


local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open BigOperators
open Finset


/- This rewriting is for convenience. -/
/-- `disjointSet X f` states that `f` sends distinct elements of `X` to disjoint sets. -/
def disjointSet {α β : Type} (X : Set α) (f : α → Set β) :=
  ∀ a₁ a₂, a₁ ∈ X → a₂ ∈ X → a₁ ≠ a₂ → Disjoint (f a₁) (f a₂)
/-- `covers X Y f` states that `Y` is the union of `f a` over `a ∈ X`. -/
def covers {α β} (X : Set α) (Y : Set β) (f : α → Set β) := Y = ⋃ a ∈ X, f a

lemma isCover_iff (X : Set ℝ²) (S : Set Triangle)
    : isDisjointCover X S ↔ covers S X closedHull ∧ disjointSet S openHull := by
  simp only [isDisjointCover, isCover, isDisjointPolygonSet, ne_eq, covers, disjointSet,
    and_congr_right_iff]
  intro _
  exact ⟨fun h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq ↦ h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq,
    fun h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq ↦ h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq⟩

lemma disjoint_aux {α β : Type} (S₁ S₂ : Set α) (f : α → Set β) (h₁ : disjointSet S₁ f)
    (h₂ : disjointSet S₂ f)
    (h₃ : ∀ a₁ a₂, a₁ ∈ S₁ → a₂ ∈ S₂ → Disjoint (f a₁) (f a₂)) :
    disjointSet (S₁ ∪ S₂) f := by
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

lemma areaΔ₀ : triangleArea Δ₀ = 1 / 2 := by
  simp [triangleArea, det, Δ₀]

lemma areaΔ₀' : triangleArea Δ₀' = 1 / 2 := by
  simp [triangleArea, det, Δ₀']


/- Now we show how a cover of size two implies a cover of any even size.-/

/- Elementary stuff about scaling (only in the y direction).-/

/-- Scales the second coordinate of a plane vector by `a`. -/
def scaleVector (a : ℝ) (y : ℝ²) : ℝ² := !₂[y 0, a * y 1]

/-- Applies `scaleVector a` to every vertex of a triangle. -/
def scaleTriangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ scaleVector a (T i)

lemma scaleTriangle_det (a : ℝ) (T : Triangle) :
    det (scaleTriangle a T) = a * det T := by
  simp [det, scaleTriangle, scaleVector]
  ring

lemma scaleTriangle_area (a : ℝ) (T : Triangle)
    : triangleArea (scaleTriangle a T) = |a| * (triangleArea T) := by
  simp only [triangleArea, scaleTriangle_det a T, abs_mul, mul_div_assoc]


/- Elementary stuff about translating (only in the y direction).-/

/-- Translates the second coordinate of a plane vector by `a`. -/
def translateVector (a : ℝ) (x : ℝ²) : ℝ² := !₂[x 0, a + x 1]
/-- Applies `translateVector a` to every vertex of a triangle. -/
def translateTriangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ translateVector a (T i)

lemma translateTriangle_det (a : ℝ) (T : Triangle) :
    det (translateTriangle a T) = det T := by
  simp [det, translateTriangle, translateVector]
  ring

lemma translateTriangle_area (a : ℝ) (T : Triangle)
    : triangleArea (translateTriangle a T) = (triangleArea T) := by
  simp only [triangleArea, translateTriangle_det]

lemma translate_injective {T : Triangle} :
    Function.Injective (fun (a : ℝ) ↦ translateTriangle a T) := by
  intro _ _ hsame
  have hsame := congrArg (fun Δ ↦ Δ 0 1) hsame
  simp [translateTriangle, translateVector] at hsame
  assumption

-- Here a different try. Just give a very explicit cover.
/-- The `n` translated copies of the scaled lower triangle `Δ₀` covering the square. -/
noncomputable def zigPartCover (n : ℕ)
  := Finset.image
    (fun (s : Fin n) ↦
      translateTriangle ((s : ℝ) / (n : ℝ)) (scaleTriangle (1 / (n : ℝ)) Δ₀)) univ

/-- The `n` translated copies of the scaled upper triangle `Δ₀'` covering the square. -/
noncomputable def zagPartCover (n : ℕ)
  := Finset.image
    (fun (s : Fin n) ↦
      translateTriangle ((s : ℝ) / (n : ℝ)) (scaleTriangle (1 / (n : ℝ)) Δ₀')) univ

lemma zig_zag_cover_size_aux (n : ℕ) :
    (zigPartCover n).card = n ∧ (zagPartCover n).card = n := by
  rw [zigPartCover, zagPartCover]
  constructor <;> (
    rw [Finset.card_image_of_injective]
    · exact card_fin n
    · intro s s' hsame
      have hn : (n : ℝ) ≠ 0 := fun h ↦ Fin.elim0 (Fin.cast ((Nat.cast_eq_zero).1 h) s)
      have hsame := translate_injective hsame
      simp_all only [div_eq_div_iff hn hn, mul_eq_mul_right_iff, or_false, Nat.cast_inj]
      exact Fin.eq_of_val_eq hsame
    )

lemma zig_zag_cover_size (n : ℕ) : (zigPartCover n ∪ zagPartCover n).card = 2 * n := by
  have h : (zigPartCover n ∩ zagPartCover n).card = 0 := by
    rw [card_eq_zero, ←disjoint_iff_inter_eq_empty, disjoint_left]
    intro _ h₁ h₂
    simp only [zigPartCover, one_div, mem_image, mem_univ, true_and, zagPartCover] at h₁ h₂
    have ⟨s₁,hs₁⟩ := h₁
    have ⟨s₂,hs₂⟩ := h₂
    rw [←hs₂] at hs₁
    have hsame := congrArg (fun Δ ↦ Δ 0 0) hs₁
    simp [translateTriangle, translateVector, scaleTriangle, scaleVector, Δ₀, Δ₀'] at hsame
  simp_rw [card_union, zig_zag_cover_size_aux, h, tsub_zero, two_mul]


lemma zig_cover_area {n : ℕ} :
    ∀ {Δ : Triangle}, Δ ∈ zigPartCover n → triangleArea Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp only [zigPartCover, one_div, mem_image, mem_univ, true_and] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translateTriangle_area, scaleTriangle_area, areaΔ₀]
  simp

lemma zag_cover_area {n : ℕ} :
    ∀ {Δ : Triangle}, Δ ∈ zagPartCover n → triangleArea Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp only [zagPartCover, one_div, mem_image, mem_univ, true_and] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translateTriangle_area, scaleTriangle_area, areaΔ₀']
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

lemma zig_open_disjoint {n : ℕ} : disjointSet ((zigPartCover n) : Set Triangle) openHull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp only [zigPartCover, one_div, coe_image, coe_univ, Set.image_univ, Set.mem_range]
      at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff (by simp [det, translateTriangle, scaleTriangle, Δ₀,
      translateVector, scaleVector, Nat.ne_zero_of_lt nsign])] at hx₁
    rw [←hs₂, open_triangle_iff (by simp [det, translateTriangle, scaleTriangle, Δ₀,
      translateVector, scaleVector, Nat.ne_zero_of_lt nsign])] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    refine hΔneq ?_
    simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
      translateVector, Tside, scaleVector, Δ₀] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    rw [←hs₁, ←hs₂, fin_el_bound (x := ↑n * x.ofLp 1) (s₁ := s₁) (s₂ := s₂)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  · simp [Nat.eq_zero_of_not_pos nsign, zigPartCover, disjointSet]

lemma zag_open_disjoint {n : ℕ} : disjointSet ((zagPartCover n) : Set Triangle) openHull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp only [zagPartCover, one_div, coe_image, coe_univ, Set.image_univ, Set.mem_range]
      at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff (by
      simp [det, translateTriangle, scaleTriangle, Δ₀', translateVector, scaleVector]
      field_simp [Nat.ne_zero_of_lt nsign]
      ring_nf; norm_num)] at hx₁
    rw [←hs₂, open_triangle_iff (by
      simp [det, translateTriangle, scaleTriangle, Δ₀', translateVector, scaleVector]
      field_simp [Nat.ne_zero_of_lt nsign]
      ring_nf; norm_num)] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    refine hΔneq ?_
    simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
      translateVector, Tside, scaleVector, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
    rw [←hs₁, ←hs₂, fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂)
      (by linarith) (by linarith) (by linarith) (by linarith)]
  · simp [Nat.eq_zero_of_not_pos nsign, zagPartCover, disjointSet]

lemma zig_zag_open_disjoint {n : ℕ}
    : ∀ a₁ a₂, a₁ ∈ (zigPartCover n) → a₂ ∈ (zagPartCover n) →
      Disjoint (openHull a₁) (openHull a₂) := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂
    simp only [zigPartCover, one_div, mem_image, mem_univ, true_and, zagPartCover] at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff (by simp [det, translateTriangle, scaleTriangle, Δ₀,
      translateVector, scaleVector, Nat.ne_zero_of_lt nsign])] at hx₁
    rw [←hs₂, open_triangle_iff (by
      simp [det, translateTriangle, scaleTriangle, Δ₀', translateVector, scaleVector]
      field_simp [Nat.ne_zero_of_lt nsign]
      ring_nf; norm_num)] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₁ := hx₂ 1
    have hx₂₂ := hx₂ 2
    simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
      translateVector, Tside, scaleVector, Δ₀, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
    ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
    field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
    have l := fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂)
      (by linarith) (by linarith) (by linarith) (by linarith)
    rw [l] at hx₁₀ hx₁₂
    linarith
  · simp [Nat.eq_zero_of_not_pos nsign, zagPartCover]


lemma zig_zag_covers_square {n : ℕ} (hn : n ≠ 0)
    : covers ((zigPartCover n ∪ zagPartCover n) : Set Triangle) (closedHull unitSquare)
      closedHull := by
  ext x
  simp only [closed_unitSquare_eq, Fin.forall_fin_two, Fin.isValue, Set.mem_ofPred_eq,
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
      · use translateTriangle ((j : ℝ) / (n : ℝ)) (scaleTriangle (1 / (n : ℝ)) Δ₀)
        constructor
        · left
          rw [zigPartCover,mem_image]
          refine ⟨⟨j,?_⟩ ,by simp⟩
          rw [propext (Nat.floor_lt' hn)]
          convert (mul_lt_mul_iff_right₀ ?_).mpr hx₁
          · ring
          · rw [Nat.cast_pos]
            exact Nat.zero_lt_of_ne_zero hn
        · rw [closed_triangle_iff]
          · intro i
            fin_cases i <;> (
              simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
                translateVector, Tside, scaleVector, Δ₀];
              field_simp [hn]
              ring_nf
              try linarith [hx 0 ]
            )
            rw [sub_nonneg, mul_comm]
            exact Nat.floor_le (Left.mul_nonneg (Nat.cast_nonneg' _) (hx 1).1)
          · rw [translateTriangle_det, scaleTriangle_det, mul_ne_zero_iff_right]
            · simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, hn, not_false_eq_true]
            · simp [det, Δ₀]
      · use translateTriangle ((j : ℝ) / (n : ℝ)) (scaleTriangle (1 / (n : ℝ)) Δ₀')
        constructor
        · right
          rw [zagPartCover,mem_image]
          refine ⟨⟨j,?_⟩ ,by simp⟩
          rw [propext (Nat.floor_lt' hn)]
          convert (mul_lt_mul_iff_right₀ ?_).mpr hx₁
          · ring
          · rw [Nat.cast_pos]
            exact Nat.zero_lt_of_ne_zero hn
        · rw [closed_triangle_iff]
          · intro i
            fin_cases i <;> (
              simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
                translateVector, Tside, scaleVector, Δ₀'];
              field_simp [hn]
              ring_nf
              try linarith [hx 0 ]
            )
            convert sub_nonneg.2 (le_of_lt (Nat.lt_floor_add_one (↑n * x 1))) using 1
            · rfl
            · ring
          · rw [translateTriangle_det, scaleTriangle_det, mul_ne_zero_iff_right]
            · simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, hn, not_false_eq_true]
            · simp [det, Δ₀']
    · have hx₁ : x 1 = 1 := by linarith [hx 1]
      · use translateTriangle (( n  - 1 ) / (n : ℝ)) (scaleTriangle (1 / (n : ℝ)) Δ₀')
        constructor
        · right
          rw [zagPartCover,mem_image]
          refine ⟨⟨n - 1, Nat.sub_one_lt hn⟩,?_⟩
          simp only [mem_univ, one_div, true_and]
          conv =>
            arg 1; arg 1; arg 1
            rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one]
        · rw [closed_triangle_iff]
          · intro i
            fin_cases i <;> (
              simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
                translateVector, Tside, scaleVector, Δ₀', hx₁];
              field_simp [hn]
              ring_nf
              try linarith [hx 0]
            )
          · rw [translateTriangle_det, scaleTriangle_det, mul_ne_zero_iff_right]
            · simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, hn, not_false_eq_true]
            · simp [det, Δ₀']
  · rintro ⟨S,(hzig | hzag),hS⟩
    · simp only [zigPartCover, one_div, mem_image, mem_univ, true_and] at hzig
      have ⟨s, hs⟩ := hzig
      rw [←hs, closed_triangle_iff] at hS
      · have hs₀ := hS 0
        have hs₁ := hS 1
        have hs₂ := hS 2
        simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
          translateVector, Tside, scaleVector, Δ₀] at hs₀ hs₁ hs₂
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
      · rw [translateTriangle_det, scaleTriangle_det, mul_ne_zero_iff_right]
        · exact inv_ne_zero (Nat.cast_ne_zero.mpr hn)
        · simp [det, Δ₀]
    · simp only [zagPartCover, one_div, mem_image, mem_univ, true_and] at hzag
      have ⟨s, hs⟩ := hzag
      rw [←hs, closed_triangle_iff] at hS
      · have hs₀ := hS 0
        have hs₁ := hS 1
        have hs₂ := hS 2
        simp [Tco, signSeg, det, scaleTriangle, translateTriangle, scaleTriangle,
          translateVector, Tside, scaleVector, Δ₀'] at hs₀ hs₁ hs₂
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
      · rw [translateTriangle_det, scaleTriangle_det, mul_ne_zero_iff_right]
        · exact inv_ne_zero (Nat.cast_ne_zero.mpr hn)
        · simp [det, Δ₀']


theorem monsky_easy_direction' {n : ℕ} (hn : Even n) (hnneq : n ≠ 0)
    : (∃ (S : Finset Triangle), isEqualAreaCover (closedHull unitSquare) S ∧ S.card = n) := by
  have ⟨m,hm⟩ := hn
  use (zigPartCover m ∪ zagPartCover m)
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [isCover_iff]
    refine ⟨?_,?_⟩
    · convert zig_zag_covers_square (n := m) ?_
      · simp only [coe_union]
      · simp_all
    · convert disjoint_aux (S₁ := zigPartCover m) (S₂ := (zagPartCover m : Set Triangle))
        (f := openHull) zig_open_disjoint zag_open_disjoint zig_zag_open_disjoint
      exact coe_union (zigPartCover m) (zagPartCover m)
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
