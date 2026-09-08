/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.DyadicLevels
import LeanPool.RareDistanceFields.DyadicSize

/-!
# Logarithmically many rare distances for integer planar sets

See the project entry module for the exact coordinate restrictions and source roles.
Each occurring dyadic level contributes its numerically largest squared
distance. Their multiplicities are at most n, and n is at most two to the
number of selected levels. This proves both assertions for integer coordinates.
-/

namespace LeanPool.RareDistanceFields.IntegerDivergence

open IntegerPlane DyadicCoordinates DyadicLevels DyadicSize
noncomputable section

variable {V : Type*} [Fintype V]

open Classical in
/-- All squared distances realized between distinct integer-point labels. -/
def palette (x : V → Point) : Finset ℤ :=
  OrderedColors.palette (fun a b => sqDist (x a) (x b))

open Classical in
/-- Occurring squared distances whose unordered multiplicities are at most the label count. -/
def rareSquared (x : V → Point) : Finset ℤ :=
  (palette x).filter fun r => (graph x r).edgeFinset.card ≤ Fintype.card V

open Classical in
theorem mem_palette (x : V → Point) (a b : V) (hab : a ≠ b) :
    sqDist (x a) (x b) ∈ palette x := by
  exact Finset.mem_image.mpr ⟨(a, b), by simp [hab], rfl⟩

open Classical in
theorem exists_pair_of_mem_palette (x : V → Point) {r : ℤ} (hr : r ∈ palette x) :
    ∃ a b, a ≠ b ∧ sqDist (x a) (x b) = r := by
  obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp hr
  exact ⟨a, b, (Finset.mem_offDiag.mp hab).2.2, he⟩

open Classical in
theorem palette_positive (x : V → Point) (hx : Function.Injective x)
    {r : ℤ} (hr : r ∈ palette x) : 0 < r := by
  obtain ⟨a, b, hab, rfl⟩ := exists_pair_of_mem_palette x hr
  exact DyadicCoordinates.sqDist_pos _ _ (hx.ne hab)

open Classical in
theorem rare_at_level (x : V → Point) (hx : Function.Injective x)
    {v : ℕ} (hv : v ∈ levels x) : ∃ r ∈ rareSquared x, padicValInt 2 r = v := by
  classical
  let s := (palette x).filter fun r => padicValInt 2 r = v
  have hs : s.Nonempty := by
    obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp hv
    exact ⟨sqDist (x a) (x b), Finset.mem_filter.mpr
      ⟨mem_palette x a b (Finset.mem_offDiag.mp hab).2.2, he⟩⟩
  let r := s.max' hs
  have hr : r ∈ s := Finset.max'_mem s hs
  have hrP : r ∈ palette x := (Finset.mem_filter.mp hr).1
  have hrv : padicValInt 2 r = v := (Finset.mem_filter.mp hr).2
  have hpos := palette_positive x hx hrP
  have hcast : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hpos.le
  have hmax (a b : V) (hab : a ≠ b)
      (he : padicValInt 2 (sqDist (x a) (x b)) = padicValInt 2 (r.toNat : ℤ)) :
      sqDist (x a) (x b) ≤ (r.toNat : ℤ) := by
    rw [hcast]
    apply Finset.le_max'
    apply Finset.mem_filter.mpr
    refine ⟨mem_palette x a b hab, ?_⟩
    rwa [hcast, hrv] at he
  have hm := level_max_multiplicity_le x hx r.toNat (by omega) hmax
  rw [hcast] at hm
  exact ⟨r, Finset.mem_filter.mpr ⟨hrP, hm⟩, hrv⟩

open Classical in
theorem levels_card_le_rare (x : V → Point) (hx : Function.Injective x) :
    (levels x).card ≤ (rareSquared x).card := by
  have hs : levels x ⊆ (rareSquared x).image (padicValInt 2) := by
    intro v hv
    obtain ⟨r, hr, he⟩ := rare_at_level x hx hv
    exact Finset.mem_image.mpr ⟨r, hr, he⟩
  exact (Finset.card_le_card hs).trans Finset.card_image_le

open Classical in
theorem card_le_pow_rare (x : V → Point) (hx : Function.Injective x) :
    Fintype.card V ≤ 2 ^ (rareSquared x).card :=
  (card_le_pow_levels x hx).trans (Nat.pow_le_pow_right (by decide) (levels_card_le_rare x hx))

open Classical in
theorem uniform_divergence (k : ℕ) : ∃ N : ℕ, ∀ {V : Type*} [Fintype V]
    (x : V → Point), Function.Injective x → N ≤ Fintype.card V →
      k ≤ (rareSquared x).card := by
  refine ⟨2 ^ k, ?_⟩
  intro V inst x hx hn
  have hh := card_le_pow_rare x hx
  by_contra h
  have hp : 2 ^ (rareSquared x).card < 2 ^ k := Nat.pow_lt_pow_right (by decide) (by omega)
  omega

end
end LeanPool.RareDistanceFields.IntegerDivergence
