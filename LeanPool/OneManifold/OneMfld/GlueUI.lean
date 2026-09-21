/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib
import LeanPool.OneManifold.OneMfld.GlueCore
import LeanPool.OneManifold.OneMfld.GlueBlocks

/-! # Gluing two boundary charts onto the unit interval

The H-H assembly. Both charts are normalized to target `Iio 1`; each sees the overlap
as an upper end-segment (`Ioo p 1` in `a`, `Ioo q 1` in `b`), and the transition is
decreasing (`overlap_anti`). Embed `b` into the lower half of the unit interval via
`halfOPH` (`x ↦ x/2`) and `a` into the upper piece via a decreasing Möbius map
`mobiusOPH k` (`x ↦ k/(x+k)`), with `k` chosen so the two embeddings agree at the split
point `m := b.symm μ` (that is, `k/(ρ+k) = μ/2` where `ρ := a m`). Glue with
`OpenPartialHomeomorph.piecewise` along `t := {y ≤ μ/2}`; the two targets
`[0, μ/2]` and `(μ/2, 1]` unite to the whole interval.
-/

open Set

/-- **Unit-interval gluing.** Two boundary charts (targets `Iio 1`) whose overlap is an
upper end-segment in each glue to a chart of `M` onto the whole unit interval, with
source `a.source ∪ b.source`. -/
theorem glue_hh_ui {M : Type*} [TopologicalSpace M] [T2Space M]
    (a b : OpenPartialHomeomorph M NNReal)
    (hat : a.target = Iio 1) (hbt : b.target = Iio 1)
    {p q : NNReal}
    (ha : a '' (a.source ∩ b.source) = Ioo p 1) (hp : p < 1)
    (hb : b '' (a.source ∩ b.source) = Ioo q 1) :
    ∃ f : OpenPartialHomeomorph M UnitInterval,
      f.source = a.source ∪ b.source ∧ f.target = univ := by
  classical
  -- the overlap is nonempty, so `q < 1`
  have hS : (a.source ∩ b.source).Nonempty := by
    have h1 : (Ioo p (1 : NNReal)).Nonempty := nonempty_Ioo.2 hp
    rw [← ha] at h1
    exact h1.of_image
  have hq1 : q < 1 := nonempty_Ioo.1 (hb ▸ hS.image b)
  -- choose the split level `μ` and its preimage `m`
  obtain ⟨μ, hqμ, hμ1⟩ := exists_between hq1
  have hμpos : 0 < μ := lt_of_le_of_lt zero_le hqμ
  have hμS : μ ∈ b '' (a.source ∩ b.source) := by rw [hb]; exact ⟨hqμ, hμ1⟩
  obtain ⟨m, hmS, hbm⟩ := hμS
  have hma : m ∈ a.source := hmS.1
  have hme : m ∈ b.source := hmS.2
  set ρ := a m with hρdef
  have hρmem : ρ ∈ Ioo p 1 := by rw [← ha]; exact mem_image_of_mem a hmS
  have hρp : p < ρ := hρmem.1
  have hρ1 : ρ < 1 := hρmem.2
  have hρpos : 0 < ρ := lt_of_le_of_lt zero_le hρp
  -- the Möbius parameter `k` and its key identity `k/(ρ+k) = μ/2`
  have h2μ : μ < 2 := hμ1.trans one_lt_two
  have h2μpos : 0 < 2 - μ := tsub_pos_of_lt h2μ
  set k : NNReal := μ * ρ / (2 - μ) with hkdef
  have hkpos : 0 < k := div_pos (mul_pos hμpos hρpos) h2μpos
  have hkey2 : 2 * k = μ * (ρ + k) := by
    have h1 : k * (2 - μ) = μ * ρ := by
      rw [hkdef]; exact div_mul_cancel₀ _ h2μpos.ne'
    calc 2 * k = ((2 - μ) + μ) * k := by rw [tsub_add_cancel_of_le h2μ.le]
      _ = (2 - μ) * k + μ * k := add_mul _ _ _
      _ = μ * ρ + μ * k := by rw [mul_comm (2 - μ) k, h1]
      _ = μ * (ρ + k) := (mul_add μ ρ k).symm
  -- real-number versions of the positivity facts and the key identity
  have hkR : (0 : ℝ) < (k : ℝ) := NNReal.coe_pos.2 hkpos
  have hμR : (0 : ℝ) < (μ : ℝ) := NNReal.coe_pos.2 hμpos
  have hρR : (0 : ℝ) < (ρ : ℝ) := NNReal.coe_pos.2 hρpos
  have hμ1R : (μ : ℝ) < 1 := by exact_mod_cast hμ1
  have hρ1R : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  have hρkR : (0 : ℝ) < (ρ : ℝ) + (k : ℝ) := by linarith
  have hkeyR : (k : ℝ) / ((ρ : ℝ) + (k : ℝ)) = (μ : ℝ) / 2 := by
    have h := congrArg (fun x : NNReal => (x : ℝ)) hkey2
    push_cast at h
    rw [div_eq_div_iff hρkR.ne' (two_ne_zero)]
    linarith
  -- the two building blocks
  obtain ⟨eb, hbs, hbt', hbf⟩ := halfOPH
  obtain ⟨ea, has, hat', haf, hanti⟩ := mobiusOPH k hkpos
  set e := b.trans eb with hedef
  set e' := a.trans ea with he'def
  have hbmem : ∀ x, x ∈ b.source → b x ∈ Iio (1 : NNReal) := fun x hx =>
    hbt ▸ b.map_source hx
  have hesrc : e.source = b.source := by
    rw [hedef, OpenPartialHomeomorph.trans_source, hbs, inter_eq_left]
    intro x hx
    exact hbmem x hx
  have he'src : e'.source = a.source := by
    rw [he'def, OpenPartialHomeomorph.trans_source, has, preimage_univ, inter_univ]
  have hef : ∀ x ∈ b.source, (e x : ℝ) = (b x : ℝ) / 2 := by
    intro x hx
    rw [hedef, OpenPartialHomeomorph.trans_apply]
    exact hbf (b x) (hbmem x hx)
  have he'f : ∀ x : M, (e' x : ℝ) = (k : ℝ) / ((a x : ℝ) + (k : ℝ)) := by
    intro x
    rw [he'def, OpenPartialHomeomorph.trans_apply]
    exact haf (a x)
  -- the gluing sets
  set tset : Set UnitInterval := {y : UnitInterval | (y : ℝ) ≤ (μ : ℝ) / 2} with htdef
  set sset : Set M := b.source ∩ b ⁻¹' (Iic μ) with hsdef
  -- the anti correspondence between the two coordinates on the overlap
  have hpa : p ∈ a.target := by rw [hat]; exact hp
  have hqb : q ∈ b.target := by rw [hbt]; exact hq1
  have anti := overlap_anti a b ha hb hpa hqb
  -- `ρ ≤ a x` on `a.source` characterizes `sset`
  have hcorr : ∀ x, x ∈ a.source → (ρ ≤ a x ↔ x ∈ sset) := by
    intro x hxa
    constructor
    · intro hle
      have hax1 : a x < 1 := by
        have h := a.map_source hxa
        rwa [hat] at h
      have haxS : a x ∈ Ioo p 1 := ⟨hρp.trans_le hle, hax1⟩
      rw [← ha] at haxS
      obtain ⟨z, hzS, hz⟩ := haxS
      have hzx : z = x := a.injOn hzS.1 hxa hz
      subst hzx
      rw [hsdef]
      refine ⟨hzS.2, ?_⟩
      rcases eq_or_lt_of_le hle with heq | hlt
      · have hxm : z = m := a.injOn hxa hma (heq.symm.trans hρdef)
        rw [mem_preimage, hxm, hbm]
        exact mem_Iic.2 le_rfl
      · have h := anti m hmS z hzS (by rw [← hρdef]; exact hlt)
        rw [hbm] at h
        exact mem_Iic.2 h.le
    · intro hxs
      rw [hsdef] at hxs
      obtain ⟨hxb, hxμ⟩ := hxs
      have hxS : x ∈ a.source ∩ b.source := ⟨hxa, hxb⟩
      by_contra hlt
      push Not at hlt
      have h := anti x hxS m hmS (by rw [← hρdef]; exact hlt)
      rw [hbm] at h
      rw [mem_preimage, mem_Iic] at hxμ
      exact absurd hxμ (not_le.mpr h)
  -- `IsImage` for the lower embedding
  have H : e.IsImage sset tset := by
    intro x hx
    rw [hesrc] at hx
    have h1 : e x ∈ tset ↔ (b x : ℝ) ≤ (μ : ℝ) := by
      rw [htdef, mem_ofPred_eq, hef x hx]
      constructor <;> intro h <;> linarith
    have h2 : x ∈ sset ↔ b x ≤ μ := by
      rw [hsdef]
      exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    rw [h1, h2, NNReal.coe_le_coe]
  -- `IsImage` for the upper embedding
  have H' : e'.IsImage sset tset := by
    intro x hx
    rw [he'src] at hx
    have haxk : (0 : ℝ) < (a x : ℝ) + (k : ℝ) :=
      add_pos_of_nonneg_of_pos (a x).coe_nonneg hkR
    have h1 : e' x ∈ tset ↔ (k : ℝ) / ((a x : ℝ) + (k : ℝ)) ≤ (μ : ℝ) / 2 := by
      rw [htdef, mem_ofPred_eq, he'f x]
    have h2 : ((k : ℝ) / ((a x : ℝ) + (k : ℝ)) ≤ (μ : ℝ) / 2) ↔ ρ ≤ a x := by
      rw [← hkeyR]
      constructor
      · intro h
        rw [div_le_div_iff₀ haxk hρkR] at h
        have h3 : (ρ : ℝ) + (k : ℝ) ≤ (a x : ℝ) + (k : ℝ) :=
          le_of_mul_le_mul_left h hkR
        have h4 : (ρ : ℝ) ≤ (a x : ℝ) := by linarith
        exact_mod_cast h4
      · intro h
        have h3 : (ρ : ℝ) ≤ (a x : ℝ) := NNReal.coe_le_coe.2 h
        rw [div_le_div_iff₀ haxk hρkR]
        nlinarith
    rw [h1, h2]
    exact hcorr x hx
  -- the frontier of `tset` is the level `{μ/2}`
  have hfront_t : frontier tset = {y : UnitInterval | (y : ℝ) = (μ : ℝ) / 2} := by
    rw [htdef]
    exact frontier_UIIic (half_pos hμR) (by linarith)
  -- both sources meet the frontier of `sset` exactly at `m`
  have hfr_e : e.source ∩ frontier sset = {m} := by
    rw [← H.frontier.preimage_eq, hfront_t, hesrc]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hxb, hx2⟩
      rw [hef x hxb] at hx2
      have hbx : b x = μ := by
        have h : (b x : ℝ) = (μ : ℝ) := by linarith
        exact_mod_cast h
      exact b.injOn hxb hme (hbx.trans hbm.symm)
    · intro hxm
      rw [hxm]
      exact ⟨hme, by rw [hef m hme, hbm]⟩
  have hfr_e' : e'.source ∩ frontier sset = {m} := by
    rw [← H'.frontier.preimage_eq, hfront_t, he'src]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hxa, hx2⟩
      rw [he'f x, ← hkeyR] at hx2
      have haxk : (0 : ℝ) < (a x : ℝ) + (k : ℝ) :=
        add_pos_of_nonneg_of_pos (a x).coe_nonneg hkR
      rw [div_eq_div_iff haxk.ne' hρkR.ne'] at hx2
      have h4 : (ρ : ℝ) + (k : ℝ) = (a x : ℝ) + (k : ℝ) :=
        mul_left_cancel₀ hkR.ne' hx2
      have h5 : a x = ρ := by
        have h : (a x : ℝ) = (ρ : ℝ) := by linarith
        exact_mod_cast h
      exact a.injOn hxa hma (by rw [h5, hρdef])
    · intro hxm
      rw [hxm]
      refine ⟨hma, ?_⟩
      rw [he'f m, ← hρdef]
      exact hkeyR
  have Hs : e.source ∩ frontier sset = e'.source ∩ frontier sset :=
    hfr_e.trans hfr_e'.symm
  -- the two embeddings agree at the frontier point `m`
  have Heq : Set.EqOn e e' (e.source ∩ frontier sset) := by
    rw [hfr_e]
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    apply Subtype.ext
    rw [hef x hme, hbm, he'f x, ← hρdef, hkeyR]
  -- glue
  set f := e.piecewise e' sset tset H H' Hs Heq with hfdef
  refine ⟨f, ?_, ?_⟩
  · -- source computation
    have hfs : f.source = e.source ∩ sset ∪ e'.source \ sset := rfl
    rw [hfs, hesrc, he'src]
    apply subset_antisymm
    · rintro x (⟨hxb, _⟩ | ⟨hxa, _⟩)
      · exact Or.inr hxb
      · exact Or.inl hxa
    · intro x hx
      by_cases hxs : x ∈ sset
      · have hxb : x ∈ b.source := by
          rw [hsdef] at hxs
          exact hxs.1
        exact Or.inl ⟨hxb, hxs⟩
      · rcases hx with hxa | hxb
        · exact Or.inr ⟨hxa, hxs⟩
        · -- `x ∈ b.source \ sset` implies `x` lies in the overlap
          have hμbx : μ < b x := by
            by_contra hle
            push Not at hle
            exact hxs (by rw [hsdef]; exact ⟨hxb, mem_Iic.2 hle⟩)
          have hbx1 : b x < 1 := hbmem x hxb
          have hbIoo : b x ∈ Ioo q 1 := ⟨hqμ.trans hμbx, hbx1⟩
          rw [← hb] at hbIoo
          obtain ⟨z, hzS, hz⟩ := hbIoo
          have hzx : z = x := b.injOn hzS.2 hxb hz
          subst hzx
          exact Or.inr ⟨hzS.1, hxs⟩
  · -- target computation
    have hft : f.target = e.target ∩ tset ∪ e'.target \ tset := rfl
    rw [hft]
    apply eq_univ_of_forall
    intro y
    by_cases hy : (y : ℝ) ≤ (μ : ℝ) / 2
    · -- lower piece
      left
      have hyt : y ∈ eb.target := by
        rw [hbt']
        show (y : ℝ) < 1 / 2
        linarith
      refine ⟨?_, hy⟩
      rw [hedef, OpenPartialHomeomorph.trans_target]
      refine ⟨hyt, ?_⟩
      rw [mem_preimage, hbt, ← hbs]
      exact eb.map_target hyt
    · -- upper piece
      right
      push Not at hy
      refine ⟨?_, fun h => absurd h (not_le.2 hy)⟩
      have hy0 : (0 : ℝ) < (y : ℝ) := lt_trans (half_pos hμR) hy
      have hy1 : (y : ℝ) ≤ 1 := y.2.2
      -- the point `w := k/y - k` of `a.target` mapping to `y`
      have hknn : (k : ℝ) ≤ (k : ℝ) / (y : ℝ) := by
        rw [le_div_iff₀ hy0]
        nlinarith
      have hnn : (0 : ℝ) ≤ (k : ℝ) / (y : ℝ) - (k : ℝ) := by linarith
      have h1k : (0 : ℝ) < 1 + (k : ℝ) := by linarith
      have hge : (k : ℝ) / (1 + (k : ℝ)) ≤ (k : ℝ) / ((ρ : ℝ) + (k : ℝ)) := by
        rw [div_le_div_iff₀ h1k hρkR]
        nlinarith
      have hygt : (k : ℝ) / (1 + (k : ℝ)) < (y : ℝ) :=
        lt_of_le_of_lt (hge.trans (le_of_eq hkeyR)) hy
      have hlt1 : (k : ℝ) / (y : ℝ) - (k : ℝ) < 1 := by
        rw [div_lt_iff₀ h1k] at hygt
        rw [sub_lt_iff_lt_add]
        rw [div_lt_iff₀ hy0]
        nlinarith
      set w : NNReal := Real.toNNReal ((k : ℝ) / (y : ℝ) - (k : ℝ)) with hwdef
      have hwcoe : (w : ℝ) = (k : ℝ) / (y : ℝ) - (k : ℝ) := Real.coe_toNNReal _ hnn
      have hwtarget : w ∈ a.target := by
        rw [hat, mem_Iio, ← NNReal.coe_lt_coe, NNReal.coe_one, hwcoe]
        exact hlt1
      set x₀ := a.symm w with hx0def
      have hx0src : x₀ ∈ a.source := a.map_target hwtarget
      have hax0 : a x₀ = w := a.right_inv hwtarget
      have hkne : (k : ℝ) ≠ 0 := hkR.ne'
      have hyne : (y : ℝ) ≠ 0 := hy0.ne'
      have he'x0 : (e' x₀ : ℝ) = (y : ℝ) := by
        rw [he'f x₀, hax0, hwcoe, sub_add_cancel]
        rw [div_div_eq_mul_div, mul_comm (k : ℝ) (y : ℝ), mul_div_assoc,
          div_self hkne, mul_one]
      have hexy : e' x₀ = y := Subtype.ext he'x0
      have hx0src' : x₀ ∈ e'.source := by rw [he'src]; exact hx0src
      have := e'.map_source hx0src'
      rwa [hexy] at this
