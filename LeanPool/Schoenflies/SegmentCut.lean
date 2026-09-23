/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Plane

/-!
# Cutting a segment

Mathlib has no lemma splitting a segment at an interior point, and the polygonal subdivision
of Layer 6 is built entirely out of one: cutting loses nothing (`segment_split`) and cutting
is permanent (`openSegment_left_subset`, `openSegment_right_subset` — each half's interior
stays inside the whole's, so nothing later can put a removed point back into an interior).

Everything here is an identity between convex combinations. The `⊇` half of the split is
convexity; the `⊆` half rescales the parameter, and the only case analysis is on whether the
far coefficient vanishes.

## Blueprint

* `segment_split` — cutting at a point of the segment loses nothing; underneath
  `subdivide_covers`.
* `openSegment_left_subset`, `openSegment_right_subset` — a cut is permanent; underneath
  `subdivide_inside`.
-/

@[expose] public section

open Set

namespace Schoenflies

variable {a b p : Plane}

/-- Cutting a segment at one of its points loses nothing: the two halves cover it. -/
theorem segment_split (hp : p ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a p ∪ segment ℝ p b := by
  refine subset_antisymm ?_ (union_subset
    ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hp)
    ((convex_segment a b).segment_subset hp (right_mem_segment ℝ a b)))
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  rcases le_or_gt v β with hvβ | hvβ
  · -- `x` lies on the near half. Rescale `v` by `β`, unless `β = 0`, when the cut is at `a`.
    left
    rcases eq_or_lt_of_le hβ with rfl | hβpos
    · have hv0 : v = 0 := le_antisymm hvβ hv
      have hu1 : u = 1 := by linarith
      subst hv0; subst hu1
      simp only [zero_smul, add_zero, one_smul]
      exact left_mem_segment ℝ a _
    · refine ⟨1 - v / β, v / β, by
        rw [sub_nonneg]
        exact div_le_one_of_le₀ hvβ hβpos.le, by positivity, by ring, ?_⟩
      have hβne : β ≠ 0 := ne_of_gt hβpos
      have hvβ' : v / β * β = v := div_mul_cancel₀ v hβne
      have hcoef : (1 - v / β) + (v / β) * α = u := by
        have hα' : α = 1 - β := by linarith
        calc (1 - v / β) + (v / β) * α
            = (1 - v / β) + (v / β) * (1 - β) := by rw [hα']
          _ = 1 - v / β * β := by ring
          _ = 1 - v := by rw [hvβ']
          _ = u := by linarith
      rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, hcoef, hvβ']
  · -- `x` lies on the far half. Rescale `u` by `α`, which is positive because `v > β`.
    right
    have hαpos : 0 < α := by linarith
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have huα : u ≤ α := by linarith
    refine ⟨u / α, 1 - u / α, by positivity, by
      rw [sub_nonneg]
      exact div_le_one_of_le₀ huα hαpos.le, by ring, ?_⟩
    have huα' : u / α * α = u := div_mul_cancel₀ u hαne
    have hcoef : (u / α) * β + (1 - u / α) = v := by
      have hβ' : β = 1 - α := by linarith
      calc (u / α) * β + (1 - u / α)
          = (u / α) * (1 - α) + (1 - u / α) := by rw [hβ']
        _ = 1 - u / α * α := by ring
        _ = 1 - u := by rw [huα']
        _ = v := by linarith
    rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul, hcoef, huα']

/-- Cutting is permanent, near half: the interior of the near piece stays inside the
interior of the whole. -/
theorem openSegment_left_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ a p ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s + t * α, t * β, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]

/-- Cutting is permanent, far half. -/
theorem openSegment_right_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ p b ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s * α, s * β + t, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]

end Schoenflies
