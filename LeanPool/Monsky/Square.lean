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
import LeanPool.Monsky.Miscellaneous
import LeanPool.Monsky.BasicDefinitions

/-!
# LeanPool.Monsky.Square

Imported Lean Pool material for `LeanPool.Monsky.Square`.
-/

namespace LeanPool.Monsky


local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open BigOperators
open Finset


/-
  Basic properties about the unit square, i.e. the square with vertices 00, 10, 11, 01.
-/

/-- The unit square as a four-vertex polygon. -/
def unitSquare : Fin 4 → ℝ² := (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1)


lemma closed_unitSquare_eq : closedHull unitSquare = {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
  ext x
  constructor
  · intro ⟨α, hα, hxα⟩ i
    rw [←hxα, ←hα.2]
    have hs : α 1 + α 2 ≤ α 0 + α 1 + α 2 + α 3 := by linarith [hα.1 0, hα.1 3]
    fin_cases i <;> simp [unitSquare, Fin.sum_univ_four, Left.add_nonneg, v, hα.1, hs]
  · intro hx
    use fun
          | 0 => (1 - x 0 ) * (1 - x 1)
          | 1 => x 0 * (1 - x 1)
          | 2 => x 0 * x 1
          | 3 => (1 - x 0) * x 1
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun i ↦ by fin_cases i <;> simp [hx 0, hx 1,  Left.mul_nonneg]
    · rw [Fin.sum_univ_four]; ring
    · ext i; fin_cases i <;> (simp [Fin.sum_univ_four, unitSquare, v]; ring)



-- The open unit square is more or less the same
lemma open_unitSquare_eq : openHull unitSquare = {x | ∀ i, 0 < x i ∧ x i < 1} := by
  ext x
  constructor
  · intro ⟨α, hα, hxα⟩ i
    rw [←hxα]
    constructor
    · fin_cases i <;> simp [unitSquare, Fin.sum_univ_four, Left.add_pos,v , hα.1]
    · rw [←hα.2]
      fin_cases i <;>
      ( simp [unitSquare, Fin.sum_univ_four, v]
        linarith [hα.1 0, hα.1 1, hα.1 2, hα.1 3])
  · intro hx
    use fun
          | 0 => (1 - x 0 ) * (1 - x 1)
          | 1 => x 0 * (1 - x 1)
          | 2 => x 0 * x 1
          | 3 => (1 - x 0) * x 1
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun i ↦ by fin_cases i <;> simp [hx 0, hx 1]
    · rw [Fin.sum_univ_four]; ring
    · ext i; fin_cases i <;> (simp [Fin.sum_univ_four, unitSquare, v]; ring)


lemma element_in_boundary_square {x : ℝ²} (hx : x ∈ boundary unitSquare) :
    ∃ i, x i = 0 ∨ x i = 1 := by
  by_contra hc; push Not at hc
  rw [boundary, closed_unitSquare_eq, open_unitSquare_eq, @Set.mem_sdiff] at hx
  apply hx.2
  exact fun i ↦ ⟨lt_of_le_of_ne (hx.1 i).1 (hc i).1.symm, lt_of_le_of_ne (hx.1 i).2 (hc i).2⟩


lemma boundary_unitSquare_eq :
    boundary unitSquare = { x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∃ i, x i = 0 ∨ x i = 1)} := by
  rw [Set.setOf_and, ←closed_unitSquare_eq]
  ext
  refine ⟨fun hx ↦ ⟨boundary_sub_closed _ hx, element_in_boundary_square hx⟩,
          fun ⟨hc, ⟨i, hno⟩⟩ ↦ (Set.mem_sdiff _).mpr ⟨hc, ?_⟩⟩
  rw [open_unitSquare_eq]
  exact fun hco ↦ by rcases hno <;> linarith [hco i]



lemma segment_in_boundary_square {x : ℝ²} (hx : x ∈ boundary unitSquare)
    : ∃ i, ∀ L, x ∈ openHull L → closedHull L ⊆ closedHull unitSquare → (segVec L) i = 0 := by
  by_contra hNonzero
  push Not at hNonzero
  have ⟨i, hxi⟩ := element_in_boundary_square hx
  have ⟨L,hxL,hL, hvec⟩ := hNonzero i
  have ⟨δ,hδ, hδx⟩ := seg_dir_sub hxL
  rcases hxi with hxi | hxi
  · specialize hδx (δ * (- Real.sign ((segVec L) i))) (by
      simp only [mul_neg, abs_neg, abs_mul, abs_of_pos hδ]
      nth_rewrite 2 [←mul_one δ]
      gcongr
      exact real_sign_abs_le
      )
    have ht := hL (open_sub_closed _ hδx)
    rw [closed_unitSquare_eq] at ht
    have ht₂ := (ht i).1
    simp [hxi] at ht₂
    linarith [mul_pos hδ (real_sign_mul_self hvec)]
  · specialize hδx (δ * (Real.sign ((segVec L) i))) (by
      simp only [abs_mul, abs_of_pos hδ]
      nth_rewrite 2 [←mul_one δ]
      gcongr
      exact real_sign_abs_le
      )
    have ht := hL (open_sub_closed _ hδx)
    rw [closed_unitSquare_eq] at ht
    have ht₂ := (ht i).2
    simp [hxi] at ht₂
    linarith [mul_pos hδ (real_sign_mul_self hvec)]


/- A version that states that the open_unitSquare is open. -/
--The proof below is not as difficult as it seems, but I just needed a lot of
--explicit bounds because simp was not cooperating
lemma open_unitSquare_open_dir {x : ℝ²} (y : ℝ²) (hx : x ∈ openHull unitSquare) :
    ∃ (ε : ℝ), ε > 0 ∧ ∀ (n : ℕ), x + (1 / (n : ℝ)) • (ε • y) ∈ openHull unitSquare := by
  simp_rw [open_unitSquare_eq] at *
  -- The constant we will choose is of order 1/ y, so we have to make an exception for y =0
  by_cases h : ∀ i, (y i = 0) -- this formulation was slightly easier for me
  · use 1
    have h1: y = 0 := by
      ext i
      exact h i
    rw[h1]
    refine ⟨by norm_num, fun n => ?_⟩
    simpa using hx
  -- I would prefer to define the epsilon with an infinum over i, rather than doing it explicitly,
  -- but I could not find the right api to show this infinum is bigger than zero
  -- (as it is only a infinum over a finite index)
  · use ((1/(max |y 0| |y 1|))*(1/2) )* min (min (x 0) (1- x 0)) (min (x 1) (1 - x 1))
    have h2 : (max |y 0| |y 1|) > 0 := by
      push Not at h
      rcases h with ⟨ i, h2⟩
      fin_cases i
      · exact lt_sup_of_lt_left (abs_pos.mpr (h2))
      · exact lt_sup_of_lt_right (abs_pos.mpr h2)
    have h1: ∀ (i: Fin 2), 0 < (1- x i) := (fun i ↦  by linarith [hx i] )
    have h8: 0 <  (2* (|y 0| ⊔ |y 1|)) :=  (mul_pos (by norm_num) h2)
    have hxbound :  0 < x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1)) := by
      apply lt_min <;> apply lt_min
      · exact (hx 0).1
      · exact h1 0
      · exact (hx 1).1
      · exact h1 1
    constructor
    · exact mul_pos (by simp[h2]) hxbound
    · have h3: ∀ i, |-y i| <  (2*(max |y 0| |y 1|)) := by
        intro i
        have hle : |-y i| ≤ max |y 0| |y 1| := by fin_cases i <;> simp
        linarith [hle, h2]
      have h4: ∀ i, x i ≥  (x 0 ⊓ (1 - x 0)) ⊓ (x 1 ⊓ (1 - x 1)) := by
        intro i; fin_cases i
        · apply inf_le_of_left_le; apply inf_le_of_left_le; rfl
        · apply inf_le_of_right_le; apply inf_le_of_left_le; rfl
      have h5 : ∀ i, 1 - x i ≥  (x 0 ⊓ (1 - x 0)) ⊓ (x 1 ⊓ (1 - x 1)) := by
        intro i; fin_cases i
        · apply inf_le_of_left_le; apply inf_le_of_right_le; rfl
        · apply inf_le_of_right_le; apply inf_le_of_right_le; rfl
      intro n i; simp only [one_div, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      -- mathematically, n should be at least 1, but because 1/ 0 = 0, the
      -- statement still holds for n = 0, but just requires a different proof
      by_cases hn : ( n= 0)
      · rw[hn]; simp[hx i]
      --for n≥ 1, the proof is as follows
      have hn4 : (n : ℝ ) ≥ 1 :=  Nat.one_le_cast.mpr ( Nat.one_le_iff_ne_zero.mpr hn)
      have h7: (1/(n: ℝ )) ≤  1 := by
        exact (div_le_one₀ (lt_of_le_of_lt' hn4 (by norm_num))).mpr hn4
      constructor
      · apply neg_lt_iff_pos_add.mp
        have h6: -((↑n)⁻¹ * ((|y 0| ⊔ |y 1|)⁻¹ * 2⁻¹ *
            (x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1))) * y i)) =
            ((-y i) / (2*(|y 0| ⊔ |y 1|))) * (1/n)*
            (x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1))) := by ring
        rw[h6]
        refine lt_of_lt_of_le (mul_lt_of_lt_one_left hxbound ?_) (h4 i)
        refine lt_of_lt_of_le
          (mul_lt_of_lt_one_left (one_div_pos.mpr (lt_of_le_of_lt' hn4 (by norm_num))) ?_) (h7)
        apply Bound.div_lt_one_of_pos_of_lt h8 (lt_of_abs_lt (h3 i))
      · apply lt_tsub_iff_left.mp
        have h6: ((↑n)⁻¹ * ((|y 0| ⊔ |y 1|)⁻¹ * 2⁻¹ *
            (x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1))) * y i)) =
            ((y i) / (2*(|y 0| ⊔ |y 1|))) * (1/n)*
            (x 0 ⊓ (1 - x 0) ⊓ (x 1 ⊓ (1 - x 1))) := by ring
        rw[h6]
        refine lt_of_lt_of_le (mul_lt_of_lt_one_left hxbound ?_) (h5 i)
        refine lt_of_lt_of_le
          (mul_lt_of_lt_one_left (one_div_pos.mpr (lt_of_le_of_lt' hn4 (by norm_num))) ?_) (h7)
        simp_rw[abs_neg] at h3
        apply Bound.div_lt_one_of_pos_of_lt h8 (lt_of_abs_lt (h3 i))






lemma el_boundary_square_triangle_dir {x : ℝ²} (hx : x ∈ boundary unitSquare) :
    ∃ σ ∈ ({-1,1} : Finset ℝ), ∀ (Δ : Triangle), (det Δ ≠ 0) →
    (closedHull Δ ⊆ closedHull unitSquare) → (∃ i, x ∈ openHull (Tside Δ i))
    → (∃ εΔ > 0, ∀ y, 0 < y → y ≤ εΔ → x + (σ * y) • (v 1 1) ∈ openHull Δ) := by
    -- First we produce such triangle
    by_cases hΔ : ∃ Δ, (det Δ ≠ 0) ∧ (closedHull Δ ⊆ closedHull unitSquare) ∧
        (∃ i, x ∈ openHull (Tside Δ i))
    · have ⟨Δ, hArea, hΔP, ⟨j,hSide⟩⟩ := hΔ
      have ⟨σ, hσ, ⟨δ,hδ, hδx⟩,_⟩  := seg_inter_open (y := v 1 1) hSide hArea ?_
      · use σ, hσ
        intro Δ' hArea' hΔ'P ⟨j',hSide'⟩
        have ⟨σ', hσ', ⟨δ',hδ', hδx'⟩, _⟩  := seg_inter_open (y := v 1 1) hSide' hArea' ?_
        · use δ', hδ'
          convert hδx' using 5
          rw [mul_smul, smul_comm]
          congr
          simp only [mem_insert, mem_singleton] at hσ hσ'
          have hσσ' : σ' = σ ∨ σ' = - σ := by
            obtain hσ | hσ := hσ <;> obtain hσ' | hσ' := hσ' <;> (rw [hσ, hσ']; simp)
          rcases hσσ' with hσσ' | hσσ'
          · exact hσσ'.symm
          · exfalso
            specialize hδx (min δ δ') (lt_min hδ hδ') (min_le_left δ δ')
            specialize hδx' (min δ δ') (lt_min hδ hδ') (min_le_right δ δ')
            rw [hσσ'] at hδx'
            have ⟨i, hL⟩ := segment_in_boundary_square hx
            specialize hL
              (fun | 0 => x + (δ ⊓ δ') • σ • v 1 1 | 1 => x + (δ ⊓ δ') • -σ • v 1 1) ?_ ?_
            · use fun | 0 => 1/2 | 1 => 1/2
              refine ⟨⟨?_,?_⟩,?_⟩
              · intro i
                fin_cases i <;> simp
              · simp; ring
              · ext i
                fin_cases i <;> (simp; ring)
            · apply closedHull_convex
              intro i
              fin_cases i
              · exact hΔP (open_sub_closed _ hδx)
              · exact hΔ'P (open_sub_closed _ hδx')
            · unfold segVec at hL
              fin_cases i <;>(
                obtain hσ | hσ := hσ <;>(
                  simp [hσ] at hL
                  ring_nf at hL
                  try simp [neg_eq_zero] at hL
                  linarith [lt_min hδ hδ']
                  ))
        · apply aux_det₂
          · intro this
            rw [segVec_zero_iff] at this
            exact (nondegen_triangle_imp_nondegen_side j' hArea') this
          · have ⟨i,hi⟩ := segment_in_boundary_square hx
            exact ⟨i, hi _ hSide' (subset_trans closed_side_sub' hΔ'P)⟩
      · apply aux_det₂
        · intro this
          rw [segVec_zero_iff] at this
          exact (nondegen_triangle_imp_nondegen_side j hArea) this
        · have ⟨i,hi⟩ := segment_in_boundary_square hx
          exact ⟨i, hi _ hSide (subset_trans closed_side_sub' hΔP)⟩
    · push Not at hΔ
      use (1 : ℝ), by simp
      intro Δ hArea hΔP ⟨i,hSide⟩
      exact False.elim (hΔ Δ hArea hΔP i hSide)

lemma boundary_leave_dir {x : ℝ²} (hx : x ∈ boundary unitSquare) :
    ∃ σ ∈ ({1, -1} : Finset ℝ), ∀ ε > 0, x + (σ * ε) • (v 1 1) ∉ closedHull unitSquare := by
  by_contra h_contra
  push Not at h_contra
  have ⟨ε₁, hε₁pos, hx₁⟩ := h_contra 1 (by simp)
  have ⟨ε₂, hε₂pos, hx₂⟩ := h_contra (-1) (by simp)
  have ⟨i, hi⟩ := segment_in_boundary_square hx
  specialize hi (segmentAroundX x (v 1 1) ε₁ ε₂) ?_ ?_
  · exact openHull_segment_around hε₁pos hε₂pos
  · apply closedHull_convex
    intro i
    fin_cases i <;> simpa only [toSegment]
  · simp [segmentAroundX, segVec, toSegment, v] at hi
    fin_cases i <;> (simp_all; linarith)

open Classical in
lemma segment_triangle_pairing_int
    (S : Finset Triangle)
    (hCover : isDisjointCover (closedHull unitSquare) (S : Set Triangle))
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0)
    (L : Segment)
    (hInt : ∀ Δ ∈ S, (openHull Δ) ∩ (closedHull L) = ∅)
    (hLunit : openHull L ⊆ openHull unitSquare)
    (hv : ∀ Δ ∈ S, ∀ i, Δ i ∉ openHull L)
  : (S.filter (fun Δ ↦ closedHull L ⊆ boundary Δ)).card = 2 := by
  -- We first take an element from openHull L
  have ⟨x, hLx⟩ := open_seg_nonempty L
  -- A useful statement:
  have hU : ∀ Δ ∈ S, x ∉ openHull Δ := by
    intro Δ hΔ hxΔ
    have this := Set.mem_inter hxΔ (open_sub_closed _ hLx )
    rw [hInt Δ hΔ] at this
    exact this
  -- This x is a member of side i of some triangle Δ.
  have ⟨Δ, hΔ, i, hxi⟩ := cover_mem_side hCover hArea (open_sub_closed _ (hLunit hLx)) hU ?_
  · -- Now it should follow that the closed hull of L is contained in the closed hull of Tside Δ i
    have hLΔ := seg_sub_side (hArea Δ hΔ) hLx hxi (hInt Δ hΔ) (hv Δ hΔ)
    -- We take a vector y that is not in the direction of any side.
    have ⟨y,hy⟩ := perp_vec_exists (Finset.biUnion S (fun Δ ↦ image (fun i ↦ Tside Δ i) (univ))) ?_
    · -- Specialize to the Δᵢ
      have yΔi := hy (Tside Δ i)
        (by rw [mem_biUnion]; exact ⟨Δ,hΔ,by rw [mem_image]; exact ⟨i, mem_univ _,rfl⟩⟩)
      -- Use this to show that there is a direction of y to move in which does not intersect Δ
      have ⟨σ, hσ, ⟨δ, hδ, hain⟩, haout⟩ := seg_inter_open hxi (hArea Δ hΔ) yΔi
      -- We have an epsilon such that x + (1/n) ε • - σ • y lies inside the open
      -- triangle for all n ∈ ℕ
      have ⟨ε,hεPos, hn⟩ := open_unitSquare_open_dir (- σ • y) (hLunit hLx)
      -- This gives a map from ℕ to S assigning to each such ℕ a triangle that contains it.
      have hfS : ∀ n : ℕ, ∃ T ∈ S, x + (1 / (n : ℝ)) • ε • -σ • y ∈ closedHull T := by
        intro n
        have this := (open_sub_closed _ (hn n))
        rw [hCover.1, Set.mem_iUnion₂] at this
        have ⟨T,hT,hT'⟩ := this
        exact ⟨T,hT,hT'⟩
      choose f hfS hfCl using hfS
      -- This means that there is a triangle with infinitely many vectors of the
      -- form x + (1 / (n : ℝ)) • ε • -σ • y
      have ⟨Δ', hΔ', hΔ'Inf⟩ := finset_infinite_pigeonhole hfS
      -- First we prove that Δ' ≠ Δ
      have ⟨l,hl,hlZ⟩ := infinite_distinct_el hΔ'Inf 0
      have hMemΔ' := hfCl l
      rw [hl] at hMemΔ'
      have hΔneq : Δ' ≠ Δ := by
        by_contra hΔeq
        rw [hΔeq] at hMemΔ'
        apply haout ((1/ (l : ℝ) * ε))
          (mul_pos (one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hlZ)) hεPos)
        convert hMemΔ' using 2
        simp [mul_smul]
      -- Then we prove that x ∈ closedHull Δ'
      have hxΔ' := closed_triangle_is_closed_dir (x := x) (y := ε • -σ • y) (hArea Δ' hΔ') (by
        refine Set.Infinite.mono ?_ hΔ'Inf
        intro m _
        have _ := hfCl m
        simp_all
        )
      -- This means that x lies in some side of Δ'
      have ⟨i',hi'⟩ := el_in_boundary_imp_side (hArea Δ' hΔ')
        (Set.mem_sdiff_of_mem hxΔ' (fun d ↦ hU Δ' hΔ' d)) (fun i ht ↦ hv Δ' hΔ' i (by rwa [←ht]))
      -- This again means that L lies completely in Tside Δ' i
      have hLΔ' := seg_sub_side (hArea Δ' hΔ') hLx hi' (hInt Δ' hΔ') (hv Δ' hΔ')
      -- We now have our two elements that should give the cardinality 2.
      rw [card_eq_two]
      use Δ', Δ, hΔneq
      ext Δ''
      constructor
      · -- The hard part of the proof continues here.
        -- We have to show that if there is a third triangle that it intersects
        -- one of the triangles.
        intro hΔ''
        rw [mem_filter] at hΔ''
        have ⟨hΔ'', hLΔ''⟩ := hΔ''
        have ⟨i'',hi''⟩ := el_in_boundary_imp_side (hArea Δ'' hΔ'')
          (hLΔ'' (open_sub_closed _ hLx)) (fun i ht ↦ hv Δ'' hΔ'' i (by rwa [←ht]))
        -- We define σ' and σ''
        have yΔi' := hy (Tside Δ' i')
          (by rw [mem_biUnion]; exact ⟨Δ',hΔ',by rw [mem_image]; exact ⟨i', mem_univ _,rfl⟩⟩)
        have ⟨σ', hσ', ⟨δ',hδ', hain'⟩, haout'⟩ := seg_inter_open hi' (hArea Δ' hΔ') yΔi'
        have yΔi'' := hy (Tside Δ'' i'')
          (by rw [mem_biUnion]; exact ⟨Δ'',hΔ'',by rw [mem_image]; exact ⟨i'', mem_univ _,rfl⟩⟩)
        have ⟨σ'', hσ'', ⟨δ'',hδ'', hain''⟩, haout''⟩ := seg_inter_open hi'' (hArea Δ'' hΔ'') yΔi''
        -- First we show that σ ≠ σ' The following argument is repeated
        -- three times and could use its own lemma
        have σneq : σ ≠ σ' := by
          intro σeq
          rw [σeq] at hain
          specialize hain (min δ δ') (lt_min hδ hδ') (min_le_left δ δ')
          specialize hain' (min δ δ') (lt_min hδ hδ') (min_le_right δ δ')
          exact hΔneq (isCover_open_el_imp_eq hCover.2 hΔ' hΔ hain' hain)
        have σ''mem : σ'' = σ ∨ σ'' = σ' := by
          simp only [mem_insert, mem_singleton] at hσ hσ' hσ''
          obtain t | t := hσ <;> obtain t' | t' := hσ' <;> obtain t'' | t'' := hσ'' <;> (
            rw [t,t',t'']
            rw [t,t'] at σneq
            tauto)
        rcases σ''mem with h | h
        · have hl : Δ'' = Δ := by
            by_contra hneq
            rw [h] at hain''
            specialize hain (min δ δ'') (lt_min hδ hδ'') (min_le_left δ δ'')
            specialize hain'' (min δ δ'') (lt_min hδ hδ'') (min_le_right δ δ'')
            exact hneq (isCover_open_el_imp_eq hCover.2 hΔ'' hΔ hain'' hain)
          simp only [hl, mem_insert, mem_singleton, or_true]
        · have hl : Δ'' = Δ' := by
            by_contra hneq
            rw [h] at hain''
            specialize hain' (min δ' δ'') (lt_min hδ' hδ'') (min_le_left δ' δ'')
            specialize hain'' (min δ' δ'') (lt_min hδ' hδ'') (min_le_right δ' δ'')
            exact hneq (isCover_open_el_imp_eq hCover.2 hΔ'' hΔ' hain'' hain')
          simp only [hl, mem_insert, mem_singleton, true_or]
      · intro hΔ''; simp only [mem_insert, mem_singleton] at hΔ''
        obtain hΔ'' | hΔ'' := hΔ'' <;> (rw [hΔ'']; simp only [mem_filter])
        · exact ⟨hΔ', fun _ a ↦ (side_in_boundary (hArea Δ' hΔ') i') (hLΔ' a)⟩
        · exact ⟨hΔ, fun _ a ↦ (side_in_boundary (hArea Δ hΔ) i) (hLΔ a)⟩
    · intro L hL
      simp_rw [mem_biUnion, mem_image] at hL
      have ⟨T,TS,i',_,hTL⟩ := hL
      rw [←hTL]
      exact nondegen_triangle_imp_nondegen_side _ (hArea T TS)
  · intro i Δ hΔ hxΔ
    rw [hxΔ] at hLx
    exact hv Δ hΔ i hLx


open Classical in
lemma segment_triangle_pairing_boundary (S : Finset Triangle)
    (hCover : isDisjointCover (closedHull unitSquare) (S : Set Triangle))
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) (L : Segment) (hL : L 0 ≠ L 1)
    (hInt : ∀ Δ ∈ S, (openHull Δ) ∩ (closedHull L) = ∅)
    (hLunit : openHull L ⊆ boundary unitSquare) (hv : ∀ Δ ∈ S, ∀ i, Δ i ∉ openHull L)
  : (S.filter (fun Δ ↦ closedHull L ⊆ boundary Δ)).card = 1 := by
  -- We first take an element from openHull L
  have ⟨x, hLx⟩ := open_seg_nonempty L
  -- The point x is not in any open triangle:
  have hU : ∀ Δ ∈ S, x ∉ openHull Δ := by
    intro Δ hΔ hxΔ
    have this := Set.mem_inter hxΔ (open_sub_closed _ hLx )
    rw [hInt Δ hΔ] at this
    exact this
  -- The point x is also not a vertex of any triangle
  have hxNvtx : ∀ (i : Fin 3), ∀ Δ ∈ S, x ≠ Δ i := by
    intro i Δ hΔ hxΔ
    rw [hxΔ] at hLx
    exact hv Δ hΔ i hLx
  -- This x is a member of side i of some triangle Δ.
  have ⟨Δ, hΔ, i, hxi⟩ :=
    cover_mem_side hCover hArea (boundary_sub_closed unitSquare (hLunit hLx)) hU hxNvtx
  -- The closed hull of L is contained in the closed hull of Tside Δ i
  have hLΔ := seg_sub_side (hArea Δ hΔ) hLx hxi (hInt Δ hΔ) (hv Δ hΔ)
  -- We will prove that Δ is the only triangle containing L in its boundary
  refine card_eq_one.mpr ⟨Δ,?_⟩
  simp_rw [eq_singleton_iff_unique_mem, mem_filter]
  constructor
  · exact ⟨hΔ, subset_trans hLΔ (side_in_boundary (hArea Δ hΔ) i)⟩
  · intro Δ' ⟨hΔ',hΔ'sub⟩
    -- There is a side i' such that
    have ⟨i',hi'⟩ := segment_in_boundary_imp_in_side (hArea Δ' hΔ') hΔ'sub
    -- Pick the direction for which the vector (1,1) points into the square
    have ⟨σ, hσval, hσ⟩ := el_boundary_square_triangle_dir (hLunit hLx)
    -- Specialize to the triangles Δ and Δ'
    have ⟨ε, hε, hεΔ⟩ := hσ Δ (hArea Δ hΔ) (isCover_sub hCover.1 Δ hΔ) ⟨i,hxi⟩
    have ⟨ε', hε', hεΔ'⟩ :=
      hσ Δ' (hArea Δ' hΔ') (isCover_sub hCover.1 Δ' hΔ') ⟨i',open_segment_sub' hi' hL hLx⟩
    specialize hεΔ (min ε ε') (lt_min hε hε') (min_le_left ε ε')
    specialize hεΔ' (min ε ε') (lt_min hε hε') (min_le_right ε ε')
    exact isCover_open_el_imp_eq hCover.2 hΔ' hΔ hεΔ' hεΔ


-- Lemmas and Theorems about the square boundary

/-- The `i`-th side of the unit square, as a segment. -/
def squareBoundaryBig : Fin 4 → Segment := fun
  | 0 => (fun | 0 => v 0 0 | 1 => v 1 0)
  | 1 => (fun | 0 => v 1 0 | 1 => v 1 1)
  | 2 => (fun | 0 => v 1 1 | 1 => v 0 1)
  | 3 => (fun | 0 => v 0 1 | 1 => v 0 0)

/-- The four sides of the unit square, as a set of segments. -/
noncomputable def squareBoundaryBigSet : Finset Segment :=
   @Finset.biUnion (Fin 4) Segment _ ⊤ (fun i ↦ {squareBoundaryBig i})


-- noncomputable def squareBoundaryBigSet₂ : Finset Segment :=
--   Finset.image squareBoundaryBig (univ : Finset (Fin 4))


lemma squareBoundaryBig_corners : ∀ i, ∀ j, ∃ k,
    squareBoundaryBig i j = unitSquare k :=
  fun i j ↦ ⟨i + (if j = 0 then 0 else 1), by fin_cases i <;> fin_cases j <;> rfl⟩

lemma squareBoundaryBig_injective : squareBoundaryBig.Injective := by
  intro i j hij
  have h₀ := congrFun hij 0
  have h₁ := congrFun hij 1
  fin_cases i <;> fin_cases j <;> simp_all [squareBoundaryBig, v]

lemma square_boundary_sides_nonDegen (i : Fin 4) :
    squareBoundaryBig i 0 ≠ squareBoundaryBig i 1 := by
  intro h_contra
  fin_cases i <;> simp_all [squareBoundaryBig, v]


/-- The index of the coordinate that is constant along side `i` of the square. -/
def boundaryLine : Fin 4 → Fin 2 := fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1
/-- The constant coordinate value along side `i` of the unit square. -/
def bc : Fin 4 → ℝ := fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0

@[simp]
lemma boundaryLine_rw {i : Fin 4}
  : boundaryLine i = (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1) i := rfl

@[simp]
lemma boundary_constant_rw {i : Fin 4}
  : bc i = (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0) i := rfl


lemma squareBoundaryBig_eq (i : Fin 4) :
    closedHull (squareBoundaryBig i)
    = {x | 0 ≤ x (boundaryLine i) ∧ x (boundaryLine i) ≤ 1 ∧ x (boundaryLine i + 1) = bc i} := by
  ext x; constructor
  · intro ⟨_, hα, hαx⟩
    simp_rw [Fin.sum_univ_two, simplex_closed_sub_fin2 hα 1] at hαx
    fin_cases i <;>
    simp [←hαx, squareBoundaryBig, simplex_co_leq_1 hα, hα.1]
  · intro ⟨hx₀, hx₁, hxr⟩
    fin_cases i
    · rw [←reverseSegment_closedHull]
      convert linear_co_closed _ (real_to_fin_2_closed hx₀ hx₁)
      ext k; fin_cases k <;>
      all_goals simp_all [linearCombination, real_to_fin_2, reverseSegment,
        squareBoundaryBig, toSegment, v]
    · rw [←reverseSegment_closedHull]
      convert linear_co_closed _ (real_to_fin_2_closed hx₀ hx₁)
      ext k; fin_cases k <;>
      all_goals simp_all [linearCombination, real_to_fin_2, reverseSegment,
        squareBoundaryBig, toSegment, v]
    · convert linear_co_closed _ (real_to_fin_2_closed hx₀ hx₁)
      ext k; fin_cases k <;>
      all_goals simp_all [linearCombination, real_to_fin_2, squareBoundaryBig, v]
    · convert linear_co_closed _ (real_to_fin_2_closed hx₀ hx₁)
      ext k; fin_cases k <;>
      all_goals simp_all [linearCombination, real_to_fin_2, squareBoundaryBig, v]


lemma square_boundary_in_boundary (i : Fin 4) :
    closedHull (squareBoundaryBig i) ⊆ boundary unitSquare := by
  rw [squareBoundaryBig_eq, boundary_unitSquare_eq]
  exact fun _ ⟨_, _, _⟩ ↦
    ⟨fun j ↦ by fin_cases i <;> fin_cases j <;> simp_all,
      ⟨boundaryLine i + 1, by fin_cases i <;> simp_all⟩⟩

lemma square_boundary_segments_in_boundary : ∀ i : Fin 4, closedHull (squareBoundaryBig i) ⊆
    boundary unitSquare := by
  intro i
  fin_cases i <;> simp_all [square_boundary_in_boundary]

lemma boundary_in_square_boundary {x : ℝ²} (hx : x ∈ boundary unitSquare) :
    ∃ i, x ∈ closedHull (squareBoundaryBig i) := by
  rw [boundary_unitSquare_eq] at hx
  have ⟨j, hj⟩ := hx.2
  fin_cases j <;> obtain hj | hj := hj
  · use 3
    simp_all [squareBoundaryBig_eq]
  · use 1
    simp_all [squareBoundaryBig_eq]
  · use 0
    simp_all [squareBoundaryBig_eq]
  · use 2
    simp_all [squareBoundaryBig_eq]


lemma square_boundary_is_union_sides
    : boundary unitSquare = ⋃ i, closedHull (squareBoundaryBig i) := by
  ext x
  refine ⟨fun hx ↦ Set.mem_iUnion.mpr (boundary_in_square_boundary hx), ?_⟩
  intro ⟨S, ⟨i, hi⟩ , hxS⟩
  rw [←hi] at hxS
  exact square_boundary_in_boundary _ hxS


lemma squareBoundaryBig_inter_seg_aux₁ {a b c d : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c)
    (hd : 0 ≤ d) (habcd : a * b + c * d = 0) : b = 0 ∧ d = 0 := by
  rw [add_eq_zero_iff_of_nonneg
      ((mul_nonneg_iff_of_pos_left ha).mpr hb) ((mul_nonneg_iff_of_pos_left hc).mpr hd)] at habcd
  exact ⟨
    (mul_eq_zero_iff_left (ne_of_lt ha).symm).mp habcd.1,
    (mul_eq_zero_iff_left (ne_of_lt hc).symm).mp habcd.2⟩


lemma squareBoundaryBig_inter_seg_aux₂ {a b c d : ℝ} (hac : a + c = 1) (ha : 0 < a) (hb : b ≤ 1)
    (hc : 0 < c) (hd : d ≤ 1) (habcd : a * b + c * d = 1) : b = 1 ∧ d = 1 := by
  rw [←(sub_eq_zero), ←(sub_eq_zero (a := d)), ←neg_eq_zero, ←neg_eq_zero (a := d -1)]
  refine squareBoundaryBig_inter_seg_aux₁ (a := a) (c := c) ha ?_ hc ?_ ?_  <;>
  linarith


lemma squareBoundaryBig_inter_seg {S : Segment} {x : ℝ²} {i : Fin 4} (hx : x ∈ openHull S)
    (hxi : x ∈ closedHull (squareBoundaryBig i)) (hS : closedHull S ⊆ closedHull unitSquare) :
    closedHull S ⊆ closedHull (squareBoundaryBig i) := by
  apply closedHull_convex
  intro j
  have hS := fun k ↦ hS (corner_in_closedHull (P := S) (i := k))
  have hS₀ := hS 0; have hS₁ := hS 1;
  rw [squareBoundaryBig_eq, closed_unitSquare_eq] at *
  have ⟨α, hα, hαx⟩ := hx
  simp_rw [←hαx, Fin.sum_univ_two] at hxi
  have hαsum : α 0 + α 1 = 1 := by convert hα.2; exact (Fin.sum_univ_two α).symm
  clear hαx
  -- Unfortunately I couldn't get the simp to close it all, so there is a nonterminating simp here.
  fin_cases i <;> fin_cases j <;>
    simp_all only [Fin.forall_fin_two, Fin.isValue, Set.mem_setOf_eq, and_self, Fin.mk_one,
      boundaryLine_rw, Fin.reduceAdd, boundary_constant_rw, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, Fin.zero_eta, true_and, Fin.reduceFinMk, zero_add]
  · exact (squareBoundaryBig_inter_seg_aux₁ (hα.1 0) hS.1.2.1 (hα.1 1) hS.2.2.1 hxi.2.2).1
  · exact (squareBoundaryBig_inter_seg_aux₁ (hα.1 0) hS.1.2.1 (hα.1 1) hS.2.2.1 hxi.2.2).2
  · exact (squareBoundaryBig_inter_seg_aux₂ hαsum (hα.1 0) hS.1.1.2 (hα.1 1) hS.2.1.2 hxi.2.2).1
  · exact (squareBoundaryBig_inter_seg_aux₂ hαsum (hα.1 0) hS.1.1.2 (hα.1 1) hS.2.1.2 hxi.2.2).2
  · exact (squareBoundaryBig_inter_seg_aux₂ hαsum (hα.1 0) hS.1.2.2 (hα.1 1) hS.2.2.2 hxi.2.2).1
  · exact (squareBoundaryBig_inter_seg_aux₂ hαsum (hα.1 0) hS.1.2.2 (hα.1 1) hS.2.2.2 hxi.2.2).2
  · exact (squareBoundaryBig_inter_seg_aux₁ (hα.1 0) hS.1.1.1 (hα.1 1) hS.2.1.1 hxi.2.2).1
  · exact (squareBoundaryBig_inter_seg_aux₁ (hα.1 0) hS.1.1.1 (hα.1 1) hS.2.1.1 hxi.2.2).2

lemma convex_faces {x y p : ℝ²} (i : Fin 4) (hpiface : p ∈ closedHull (squareBoundaryBig i))
(hp : p ∈ openHull (toSegment x y)) (hx : x ∈ closedHull unitSquare)
(hy : y ∈ closedHull unitSquare) :
x ∈ closedHull (squareBoundaryBig i) ∧ y ∈ closedHull (squareBoundaryBig i) := by
  have h_inter := squareBoundaryBig_inter_seg hp hpiface
    (closedHull_convex (by intro i; fin_cases i <;> assumption))
  refine ⟨?_,?_⟩
  · convert h_inter (corner_in_closedHull (i := 0)) using 2; rfl
  · convert h_inter (corner_in_closedHull (i := 1)) using 2; rfl

lemma convex_faces'' {p : ℝ²} {L : Segment} (i : Fin 4)
(hpiface : p ∈ closedHull (squareBoundaryBig i))
(hp : p ∈ openHull L) (hx : L 0 ∈ closedHull unitSquare) (hy : L 1 ∈ closedHull unitSquare) :
closedHull L ⊆ closedHull (squareBoundaryBig i) := by
  apply closedHull_convex
  intro j
  fin_cases j
  · exact (convex_faces i hpiface hp hx hy).1
  · exact (convex_faces i hpiface hp hx hy).2


lemma square_boundary_pairwise_inter {i : Fin 4} :
    closedHull (squareBoundaryBig (i - 1)) ∩ closedHull (squareBoundaryBig i)
      = {unitSquare i} := by
  rw [squareBoundaryBig_eq, squareBoundaryBig_eq]
  have hprev : i - 1 = i + 3 := by
    fin_cases i <;> rfl
  rw [hprev]
  ext x; rw [Set.mem_singleton_iff]
  constructor
  · intro _; ext j
    fin_cases i <;> fin_cases j <;> simp_all [unitSquare]
  · exact fun h ↦ by fin_cases i <;> simp [h, unitSquare]


lemma square_corner_in_boundary {i : Fin 4} :
    unitSquare i ∈ closedHull (squareBoundaryBig i):= by
  rw [←Set.singleton_subset_iff, ←square_boundary_pairwise_inter]
  exact Set.inter_subset_right

lemma square_corner_in_boundary' {i : Fin 4} :
    unitSquare i ∈ closedHull (squareBoundaryBig (i-1)):= by
  rw [←Set.singleton_subset_iff, ←square_boundary_pairwise_inter]
  exact Set.inter_subset_left

lemma segment_through_corner {S : Segment} {i : Fin 4} (hx : unitSquare i ∈ openHull S)
    (hS : closedHull S ⊆ closedHull unitSquare) : closedHull S = {unitSquare i} := by
  rw [Set.Subset.antisymm_iff]
  constructor
  · rw [←square_boundary_pairwise_inter, Set.subset_inter_iff]
    exact ⟨ squareBoundaryBig_inter_seg hx square_corner_in_boundary' hS ,
            squareBoundaryBig_inter_seg hx square_corner_in_boundary hS⟩
  · rw [Set.singleton_subset_iff]
    exact open_sub_closed _ hx


lemma cover_imples_corner_in_triangle
    {S : Finset Triangle}
    (hCover : isCover (closedHull unitSquare) (↑S : Set Triangle)) :
    ∀ i, ∃ T ∈ S, ∃ j, unitSquare i = T j := by
  by_contra h_contra; push Not at h_contra
  have ⟨c, hc⟩ := h_contra
  have ⟨T, hTsub, hT⟩ := isCover_includes hCover (corner_in_closedHull (i := c))
  specialize hc T hTsub
  have ⟨L, hLnTtriv, hOpen, hCsub⟩ := triangle_direction_sub hT hc
  apply hLnTtriv
  have hS := segment_through_corner hOpen (fun _ y ↦ (isCover_sub hCover _ hTsub) (hCsub y))
  rw [closedHull_constant_rev hS 0, closedHull_constant_rev hS 1]


lemma line_in_boundary {x : ℝ²} {L : Segment} (hL : closedHull L ⊆ closedHull unitSquare)
(hboundary : x ∈ openHull L ∩ boundary unitSquare) : closedHull L ⊆ boundary unitSquare := by
  rw [square_boundary_is_union_sides] at hboundary
  simp only [Set.mem_inter_iff, Set.mem_iUnion] at hboundary
  rcases hboundary with ⟨hx, ⟨i, h1⟩⟩
  have : closedHull L ⊆ closedHull (squareBoundaryBig i) := by
    apply squareBoundaryBig_inter_seg hx h1 hL
  exact subset_trans this (square_boundary_in_boundary i)


lemma unitSquare_is_convex {x y : ℝ²} (hx : x ∈ closedHull unitSquare) (hy : y ∈ closedHull
unitSquare) : closedHull (toSegment x y) ⊆ closedHull unitSquare := by
  have h: ∀ i, toSegment x y i ∈ closedHull unitSquare := by
    intro i; fin_cases i
    · exact hx
    · exact hy
  apply closedHull_convex h

lemma unitSquare_is_convex' {S : Segment} (hS : closedHull S ⊆ boundary unitSquare) :
    ∃ i : Fin 4, closedHull S ⊆ closedHull (squareBoundaryBig i) := by
  have hSi : ∀ i, S i ∈ closedHull unitSquare :=
    (fun i↦ boundary_in_closed (hS corner_in_closedHull))
  rw[square_boundary_is_union_sides] at hS
  rcases open_seg_nonempty S with ⟨ x, h⟩
  rcases hS (open_sub_closed S h) with ⟨ y, ⟨⟨i,h1 ⟩ , h2  ⟩⟩
  rw[← h1] at h2
  exact ⟨ i, convex_faces'' i h2 h (hSi 0) (hSi 1)⟩

lemma unitSquare_is_convex_open {S : Segment} (hS : closedHull S ⊆ boundary unitSquare)
    (hNondegen : S 0 ≠ S 1) :
    ∃ i : Fin 4, openHull S ⊆ openHull (squareBoundaryBig i) := by
  apply unitSquare_is_convex' at hS
  rcases hS with ⟨ i, hS⟩
  exact ⟨ i, open_segment_sub' hS hNondegen⟩


lemma openHull_segment_in_boundary {S : Segment}
    (hS : openHull S ⊆ boundary unitSquare)
    (hcS : closedHull S ⊆ closedHull unitSquare)
  : ∃ i, closedHull S ⊆ closedHull (squareBoundaryBig i) := by
  have ⟨x, hx⟩ := open_pol_nonempty (by norm_num) S
  have ⟨i, hi⟩ := boundary_in_square_boundary (hS hx)
  use i
  apply squareBoundaryBig_inter_seg hx hi hcS

end Monsky
end LeanPool
