/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.GlueCore
public import LeanPool.OneManifold.OneMfld.Normalize


/-! # Gluing two charts into an `ℝ≥0`-valued chart

The shared assembly for the O-H and O-O (connected overlap) cases. Chart `a` is
normalized so its target is `Ioo 0 1` and the overlap image is the full lower
end-segment `Ioo 0 r`; chart `b` sees the overlap as an upper end-segment `Ioo q 1` of
its target. Pick a split value `μ ∈ Ioo q 1`, let `m := b.symm μ` be the split point and
`ρ := a m` its `a`-coordinate; glue `b` (kept as-is on the `b`-side `s`, where
`b ≤ μ`) with the rescaled chart `(μ/ρ) • a` (which agrees with `b` at `m`) using
`OpenPartialHomeomorph.piecewise` along `s := b.source ∩ b⁻¹' (Iic μ)`, `t := Iic μ`.
All the frontier conditions come from `IsImage.frontier` and `frontier_Iic`.
-/

@[expose] public section

namespace OneMfld

open Set

/-- **NNReal gluing.** Given charts `a` (target `Ioo 0 1`, overlap image the lower
end-segment `Ioo 0 r`) and `b` (target inside `Iio 1`, overlap image the upper
end-segment `Ioo q 1` with `q` interior), there is a chart on `a.source ∪ b.source`
whose target is `(b.target ∩ Iic μ) ∪ Ioo μ (μ/ρ)` for some split values
`q < μ < 1`, `0 < ρ < 1`. -/
theorem glue_nnreal {M : Type*} [TopologicalSpace M] [T2Space M]
    (a b : OpenPartialHomeomorph M NNReal)
    (hat : a.target = Ioo 0 1)
    (hbt : b.target ⊆ Iio 1)
    {r q : NNReal}
    (ha : a '' (a.source ∩ b.source) = Ioo 0 r) (hr0 : 0 < r) (hr1 : r < 1)
    (hb : b '' (a.source ∩ b.source) = Ioo q 1)
    (hq : q ∈ b.target) :
    ∃ f : OpenPartialHomeomorph M NNReal, f.source = a.source ∪ b.source ∧
      ∃ μ ρ : NNReal, q < μ ∧ μ < 1 ∧ 0 < ρ ∧ ρ < 1 ∧
        f.target = (b.target ∩ Iic μ) ∪ Ioo μ (μ/ρ) := by
  classical
  -- The overlap is nonempty, so `q < 1`.
  have hSne : (a.source ∩ b.source).Nonempty := by
    have h : (a '' (a.source ∩ b.source)).Nonempty := by
      rw [ha]; exact nonempty_Ioo.2 hr0
    exact h.of_image
  have hq1 : q < 1 := by
    have h : (b '' (a.source ∩ b.source)).Nonempty := hSne.image _
    rw [hb] at h
    exact nonempty_Ioo.1 h
  -- Pick the split value `μ` and the split point `m`.
  obtain ⟨μ, hqμ, hμ1⟩ := exists_between hq1
  have hμ0 : 0 < μ := lt_of_le_of_lt (zero_le : (0 : NNReal) ≤ q) hqμ
  obtain ⟨m, hmS, hbm⟩ : ∃ m ∈ a.source ∩ b.source, b m = μ := by
    have h : μ ∈ b '' (a.source ∩ b.source) := by rw [hb]; exact ⟨hqμ, hμ1⟩
    obtain ⟨m, hm, hbm⟩ := h
    exact ⟨m, hm, hbm⟩
  have hρmem : a m ∈ Ioo 0 r := by rw [← ha]; exact mem_image_of_mem _ hmS
  have hρ0 : 0 < a m := hρmem.1
  have hρr : a m < r := hρmem.2
  have hρ1 : a m < 1 := hρr.trans hr1
  have hc : (0 : NNReal) < μ / a m := div_pos hμ0 hρ0
  have hcρ : μ / a m * a m = μ := div_mul_cancel₀ μ hρ0.ne'
  -- The rescaled chart `e' = (μ/ρ) • a`.
  set e' := a.transHomeomorph (NNReal.mulHomeomorph (μ / a m) hc) with he'def
  have he's : e'.source = a.source := rfl
  have he'app : ∀ x, e' x = μ / a m * a x := fun _ => rfl
  have he't : e'.target = Ioo 0 (μ / a m) := by
    rw [he'def, OpenPartialHomeomorph.transHomeomorph_target, hat]
    ext y
    simp only [mem_preimage, NNReal.mulHomeomorph_symm_apply, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le (zero_le : (0 : NNReal) ≤ y) with h | h
        · rw [← h, mul_zero] at h1; exact absurd h1 (lt_irrefl 0)
        · exact h
      · have h3 := mul_lt_mul_of_pos_left h2 hc
        rwa [mul_inv_cancel_left₀ hc.ne', mul_one] at h3
    · rintro ⟨h1, h2⟩
      refine ⟨mul_pos (inv_pos.2 hc) h1, ?_⟩
      have h3 := mul_lt_mul_of_pos_left h2 (inv_pos.2 hc)
      rwa [inv_mul_cancel₀ hc.ne'] at h3
  -- The transition map is increasing.
  have hr' : r ∈ a.target := by rw [hat]; exact ⟨hr0, hr1⟩
  have mono := overlap_mono a b ha hb hr' hq
  -- Membership in the overlap via the image descriptions.
  have hmem_of_a : ∀ x ∈ a.source, a x < r → x ∈ a.source ∩ b.source := by
    intro x hx hxr
    have h0 : 0 < a x := by
      have h := a.map_source hx
      rw [hat] at h
      exact h.1
    have h : a x ∈ a '' (a.source ∩ b.source) := by rw [ha]; exact ⟨h0, hxr⟩
    obtain ⟨x', hx', hax'⟩ := h
    have hxx : x' = x := a.injOn hx'.1 hx hax'
    rwa [hxx] at hx'
  have hmem_of_b : ∀ x ∈ b.source, q < b x → x ∈ a.source ∩ b.source := by
    intro x hx hqx
    have h1 : b x < 1 := hbt (b.map_source hx)
    have h : b x ∈ b '' (a.source ∩ b.source) := by rw [hb]; exact ⟨hqx, h1⟩
    obtain ⟨x', hx', hbx'⟩ := h
    have hxx : x' = x := b.injOn hx'.2 hx hbx'
    rwa [hxx] at hx'
  -- The side sets for the piecewise gluing.
  set s := b.source ∩ b ⁻¹' (Iic μ) with hsdef
  -- Key correspondence between the two descriptions of the `b`-side.
  have key : ∀ x ∈ a.source, (a x ≤ a m ↔ x ∈ s) := by
    intro x hx
    constructor
    · intro hle
      have hxS : x ∈ a.source ∩ b.source := hmem_of_a x hx (lt_of_le_of_lt hle hρr)
      refine ⟨hxS.2, ?_⟩
      simp only [mem_preimage, mem_Iic]
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact le_of_lt (hbm ▸ mono x hxS m hmS hlt)
      · have hxm : x = m := a.injOn hx hmS.1 heq
        rw [hxm, hbm]
    · rintro ⟨hxb, hxμ⟩
      simp only [mem_preimage, mem_Iic] at hxμ
      have hxS : x ∈ a.source ∩ b.source := ⟨hx, hxb⟩
      by_contra hgt
      rw [not_le] at hgt
      have h := mono m hmS x hxS hgt
      rw [hbm] at h
      exact absurd hxμ (not_le.2 h)
  -- `Iic μ` is the image of `s` under both charts.
  have H : b.IsImage s (Iic μ) := by
    intro x hx
    simp only [hsdef, mem_inter_iff, mem_preimage]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  have H' : e'.IsImage s (Iic μ) := by
    intro x hx
    rw [he's] at hx
    rw [he'app x, ← key x hx, mem_Iic]
    constructor
    · intro h
      have h2 : μ / a m * a x ≤ μ / a m * a m := by rw [hcρ]; exact h
      exact le_of_mul_le_mul_left h2 hc
    · intro h
      calc μ / a m * a x ≤ μ / a m * a m := mul_le_mul_of_nonneg_left h (le_of_lt hc)
        _ = μ := hcρ
  -- Both frontier intersections are the singleton `{m}`.
  have hft : frontier (Iic μ) = {μ} := frontier_Iic
  have hbfront : b.source ∩ frontier s = {m} := by
    have h1 := H.frontier.preimage_eq
    rw [hft] at h1
    rw [← h1]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hxb, hbx⟩
      exact b.injOn hxb hmS.2 (hbx.trans hbm.symm)
    · rintro rfl
      exact ⟨hmS.2, hbm⟩
  have he'front : e'.source ∩ frontier s = {m} := by
    have h1 := H'.frontier.preimage_eq
    rw [hft] at h1
    rw [← h1]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, he's]
    constructor
    · rintro ⟨hxa, hex⟩
      rw [he'app x] at hex
      have h2 : μ / a m * a x = μ / a m * a m := by rw [hcρ]; exact hex
      have h3 : a x = a m := mul_left_cancel₀ hc.ne' h2
      exact a.injOn hxa hmS.1 h3
    · rintro rfl
      exact ⟨hmS.1, by rw [he'app, hcρ]⟩
  have Hs : b.source ∩ frontier s = e'.source ∩ frontier s := by
    rw [hbfront, he'front]
  have Heq : EqOn b e' (b.source ∩ frontier s) := by
    rw [hbfront]
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    rw [hbm, he'app, hcρ]
  -- Glue.
  refine ⟨b.piecewise e' s (Iic μ) H H' Hs Heq, ?_, μ, a m, hqμ, hμ1, hρ0, hρ1, ?_⟩
  · change Set.ite s b.source e'.source = a.source ∪ b.source
    have hite : Set.ite s b.source e'.source = (b.source ∩ s) ∪ (e'.source \ s) := rfl
    rw [hite, he's]
    apply Subset.antisymm
    · rintro x (⟨hxb, -⟩ | ⟨hxa, -⟩)
      · exact Or.inr hxb
      · exact Or.inl hxa
    · rintro x hx
      by_cases hxs : x ∈ s
      · exact Or.inl ⟨hxs.1, hxs⟩
      · rcases hx with hxa | hxb
        · exact Or.inr ⟨hxa, hxs⟩
        · have hμx : μ < b x := by
            by_contra hle
            rw [not_lt] at hle
            exact hxs ⟨hxb, hle⟩
          have hxS := hmem_of_b x hxb (hqμ.trans hμx)
          exact Or.inr ⟨hxS.1, hxs⟩
  · change Set.ite (Iic μ) b.target e'.target = (b.target ∩ Iic μ) ∪ Ioo μ (μ / a m)
    have hite : Set.ite (Iic μ) b.target e'.target
        = (b.target ∩ Iic μ) ∪ (e'.target \ Iic μ) := rfl
    rw [hite, he't]
    congr 1
    ext y
    simp only [mem_sdiff, mem_Ioo, mem_Iic, not_le]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨lt_of_le_of_lt (zero_le : (0 : NNReal) ≤ μ) h1, h2⟩, h1⟩

end OneMfld
