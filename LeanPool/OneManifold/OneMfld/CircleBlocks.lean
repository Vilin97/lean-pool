/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib

/-! # Building blocks for the circle case

* `mobiusFun c` — the Möbius reparametrization `x ↦ x / (x + c(1-x))` of the unit
  interval in `ℝ≥0`, packaged as an `OpenPartialHomeomorph` with its image lemmas: it
  lets us shrink the lower overlap component of a chart to sit below any `ε > 0` while
  preserving the end-segment structure of images.
* `affineNNRealOPH k d` — the affine chart `x ↦ k·x + d` from `Ioo 0 1 ⊆ ℝ≥0` onto
  `Ioo d (d + k) ⊆ ℝ`.
* Arithmetic for arcs in `AddCircle 1`: injectivity of the quotient map on short
  windows, period-shift identities, the frontier of a closed arc, and the covering of
  the circle by a closed arc and its complementary open arc.
-/

open Set

noncomputable section

/-- The Möbius reparametrization of the unit interval of `ℝ≥0`. -/
def mobiusFun (c x : NNReal) : NNReal := x / (x + c * (1 - x))

/-- `mobiusFun c` can push any interior point below any positive level, for large `c`. -/
lemma exists_mobiusFun_lt {r ε : NNReal} (hr0 : 0 < r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ c : NNReal, 0 < c ∧ mobiusFun c r < ε := by
  have h1r : 0 < 1 - r := tsub_pos_of_lt hr1
  have hden : 0 < ε * (1 - r) := mul_pos hε h1r
  refine ⟨r / (ε * (1 - r)), div_pos hr0 hden, ?_⟩
  rw [mobiusFun, div_lt_iff₀ (lt_of_lt_of_le hr0 le_self_add)]
  have hkey : r / (ε * (1 - r)) * (1 - r) = r / ε := by
    rw [div_mul_eq_mul_div, mul_comm ε (1 - r), ← div_div,
      mul_div_cancel_right₀ _ h1r.ne']
  rw [mul_add, hkey, ← mul_div_assoc, mul_div_cancel_left₀ _ hε.ne']
  exact lt_add_of_pos_left r (mul_pos hε hr0)

lemma mobiusFun_strictMonoOn (c : NNReal) (hc : 0 < c) :
    StrictMonoOn (mobiusFun c) (Ioo 0 1) := by
  intro x hx y hy hxy
  have hdx : 0 < x + c * (1 - x) := lt_of_lt_of_le hx.1 le_self_add
  have hdy : 0 < y + c * (1 - y) := lt_of_lt_of_le hy.1 le_self_add
  rw [mobiusFun, mobiusFun, div_lt_div_iff₀ hdx hdy]
  rw [← NNReal.coe_lt_coe]
  push_cast [NNReal.coe_sub hx.2.le, NNReal.coe_sub hy.2.le]
  have hc' : (0:ℝ) < c := hc
  have hxy' : (x:ℝ) < y := hxy
  nlinarith [mul_pos hc' (sub_pos.mpr hxy')]

lemma mobiusFun_mem (c : NNReal) (hc : 0 < c) {t : NNReal} (ht : t ∈ Ioo (0:NNReal) 1) :
    mobiusFun c t ∈ Ioo (0:NNReal) 1 := by
  have hden : 0 < t + c * (1 - t) := lt_of_lt_of_le ht.1 le_self_add
  refine ⟨div_pos ht.1 hden, ?_⟩
  rw [mobiusFun, div_lt_one hden]
  exact lt_add_of_pos_right t (mul_pos hc (tsub_pos_of_lt ht.2))

/-- The Möbius reparametrization as a partial homeomorphism of `Ioo 0 1 ⊆ ℝ≥0`, with
its action on lower and upper end-segments. -/
def mobiusOPH' (c : NNReal) (hc : 0 < c) :
    { e : OpenPartialHomeomorph NNReal NNReal //
      e.source = Ioo 0 1 ∧ e.target = Ioo 0 1 ∧
      (∀ x : NNReal, e.toFun x = mobiusFun c x) ∧
      (∀ t ∈ Ioo (0:NNReal) 1, e.toFun '' (Ioo 0 t) = Ioo 0 (mobiusFun c t)) ∧
      (∀ t ∈ Ioo (0:NNReal) 1, e.toFun '' (Ioo t 1) = Ioo (mobiusFun c t) 1) } := by
  have hc' : (0:ℝ) < c := hc
  -- the inverse function
  have hgmem : ∀ y ∈ Ioo (0:NNReal) 1, c * y / ((1 - y) + c * y) ∈ Ioo (0:NNReal) 1 := by
    intro y hy
    have hden : 0 < (1 - y) + c * y :=
      lt_of_lt_of_le (tsub_pos_of_lt hy.2) le_self_add
    exact ⟨div_pos (mul_pos hc hy.1) hden,
      (div_lt_one hden).mpr (lt_add_of_pos_left _ (tsub_pos_of_lt hy.2))⟩
  have hcoe_mobius : ∀ x : NNReal, x ≤ 1 →
      ((mobiusFun c x : NNReal) : ℝ) = (x:ℝ) / ((x:ℝ) + c * (1 - (x:ℝ))) := by
    intro x hx1
    rw [mobiusFun]
    push_cast [NNReal.coe_sub hx1]
    ring
  have hleft : ∀ x ∈ Ioo (0:NNReal) 1,
      c * mobiusFun c x / ((1 - mobiusFun c x) + c * mobiusFun c x) = x := by
    intro x hx
    have hfx := mobiusFun_mem c hc hx
    have hX0 : (0:ℝ) < x := hx.1
    have hX1 : (x:ℝ) < 1 := hx.2
    have hD : (0:ℝ) < (x:ℝ) + c * (1 - (x:ℝ)) := by nlinarith
    apply NNReal.coe_injective
    push_cast [NNReal.coe_sub hfx.2.le, hcoe_mobius x hx.2.le]
    have hkey : (1 - (x:ℝ) / ((x:ℝ) + c * (1 - (x:ℝ))))
        + c * ((x:ℝ) / ((x:ℝ) + c * (1 - (x:ℝ)))) = c / ((x:ℝ) + c * (1 - (x:ℝ))) := by
      field_simp
      ring
    rw [hkey]
    field_simp
  have hright : ∀ y ∈ Ioo (0:NNReal) 1,
      mobiusFun c (c * y / ((1 - y) + c * y)) = y := by
    intro y hy
    have hgy := hgmem y hy
    have hY0 : (0:ℝ) < y := hy.1
    have hY1 : (y:ℝ) < 1 := hy.2
    have hE : (0:ℝ) < (1 - (y:ℝ)) + c * (y:ℝ) := by nlinarith
    have hgy_coe : ((c * y / ((1 - y) + c * y) : NNReal) : ℝ)
        = c * (y:ℝ) / ((1 - (y:ℝ)) + c * (y:ℝ)) := by
      push_cast [NNReal.coe_sub hy.2.le]
      ring
    apply NNReal.coe_injective
    rw [hcoe_mobius _ hgy.2.le, hgy_coe]
    have hkey : c * (y:ℝ) / ((1 - (y:ℝ)) + c * (y:ℝ))
        + c * (1 - c * (y:ℝ) / ((1 - (y:ℝ)) + c * (y:ℝ)))
        = c / ((1 - (y:ℝ)) + c * (y:ℝ)) := by
      field_simp
      ring
    rw [hkey]
    field_simp
  refine ⟨{ toFun := mobiusFun c
            invFun := fun y => c * y / ((1 - y) + c * y)
            source := Ioo 0 1
            target := Ioo 0 1
            map_source' := fun x hx => mobiusFun_mem c hc hx
            map_target' := hgmem
            left_inv' := fun x hx => hleft x hx
            right_inv' := fun y hy => hright y hy
            open_source := isOpen_Ioo
            open_target := isOpen_Ioo
            continuousOn_toFun := ?_
            continuousOn_invFun := ?_ },
    rfl, rfl, fun x => rfl, ?_, ?_⟩
  · show ContinuousOn (fun x : NNReal => x / (x + c * (1 - x))) (Ioo 0 1)
    exact ContinuousOn.div continuousOn_id
      ((continuous_id.add (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn)
      (fun x hx => (lt_of_lt_of_le hx.1 le_self_add).ne')
  · exact ContinuousOn.div (continuous_const.mul continuous_id).continuousOn
      (((continuous_const.sub continuous_id).add
        (continuous_const.mul continuous_id)).continuousOn)
      (fun y hy => (lt_of_lt_of_le (tsub_pos_of_lt hy.2) le_self_add).ne')
  · -- lower end-segment
    intro t ht
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : x ∈ Ioo (0:NNReal) 1 := ⟨hx.1, hx.2.trans ht.2⟩
      exact ⟨(mobiusFun_mem c hc hx1).1, mobiusFun_strictMonoOn c hc hx1 ht hx.2⟩
    · intro hz
      have hz1 : z ∈ Ioo (0:NNReal) 1 := ⟨hz.1, hz.2.trans (mobiusFun_mem c hc ht).2⟩
      have hmem := hgmem z hz1
      refine ⟨c * z / ((1 - z) + c * z), ⟨hmem.1, ?_⟩, hright z hz1⟩
      by_contra hcon
      rw [not_lt] at hcon
      have := (mobiusFun_strictMonoOn c hc).monotoneOn ht hmem hcon
      rw [hright z hz1] at this
      exact absurd hz.2 (not_lt.mpr this)
  · -- upper end-segment
    intro t ht
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : x ∈ Ioo (0:NNReal) 1 := ⟨ht.1.trans hx.1, hx.2⟩
      exact ⟨mobiusFun_strictMonoOn c hc ht hx1 hx.1, (mobiusFun_mem c hc hx1).2⟩
    · intro hz
      have hz1 : z ∈ Ioo (0:NNReal) 1 := ⟨lt_trans (mobiusFun_mem c hc ht).1 hz.1, hz.2⟩
      have hmem := hgmem z hz1
      refine ⟨c * z / ((1 - z) + c * z), ⟨?_, hmem.2⟩, hright z hz1⟩
      by_contra hcon
      rw [not_lt] at hcon
      have := (mobiusFun_strictMonoOn c hc).monotoneOn hmem ht hcon
      rw [hright z hz1] at this
      exact absurd hz.1 (not_lt.mpr this)

/-- The affine map `x ↦ k·x + d` as a chart from `Ioo 0 1 ⊆ ℝ≥0` onto
`Ioo d (d + k) ⊆ ℝ`. -/
def affineNNRealOPH (k d : ℝ) (hk : 0 < k) :
    { e : OpenPartialHomeomorph NNReal ℝ //
      e.source = Ioo 0 1 ∧ e.target = Ioo d (d + k) ∧
      ∀ x : NNReal, e.toFun x = k * (x : ℝ) + d } := by
  refine ⟨{ toFun := fun x => k * (x : ℝ) + d
            invFun := fun y => Real.toNNReal ((y - d) / k)
            source := Ioo 0 1
            target := Ioo d (d + k)
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := isOpen_Ioo
            open_target := isOpen_Ioo
            continuousOn_toFun :=
              ((continuous_const.mul NNReal.continuous_coe).add continuous_const).continuousOn
            continuousOn_invFun :=
              (continuous_real_toNNReal.comp
                ((continuous_id.sub continuous_const).div_const k)).continuousOn },
    rfl, rfl, fun x => rfl⟩
  · intro x hx
    have hx0 : (0:ℝ) < x := hx.1
    have hx1 : (x:ℝ) < 1 := hx.2
    constructor
    · nlinarith
    · nlinarith
  · intro y hy
    exact ⟨Real.toNNReal_pos.mpr (div_pos (sub_pos.mpr hy.1) hk),
      Real.toNNReal_lt_one.mpr ((div_lt_one hk).mpr (by linarith [hy.2]))⟩
  · intro x _
    show Real.toNNReal ((k * (x:ℝ) + d - d) / k) = x
    have h : (k * (x:ℝ) + d - d) / k = (x:ℝ) := by
      field_simp
      ring
    rw [h, Real.toNNReal_coe]
  · intro y hy
    show k * ((Real.toNNReal ((y - d) / k) : NNReal) : ℝ) + d = y
    rw [Real.coe_toNNReal _ (div_nonneg (sub_nonneg.mpr hy.1.le) hk.le)]
    field_simp
    ring

section AddCircleArith

/-- Two reals with the same image in `AddCircle 1` and distance less than `1` are
equal. -/
lemma addCircle_coe_inj {x y : ℝ} (h : (x : AddCircle (1:ℝ)) = (y : AddCircle (1:ℝ)))
    (hxy : |x - y| < 1) : x = y := by
  have h0 : ((x - y : ℝ) : AddCircle (1:ℝ)) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).mp h0
  rw [zsmul_one] at hn
  have h1 : |(n:ℝ)| < 1 := by rw [hn]; exact hxy
  have h2 : |n| < 1 := by exact_mod_cast h1
  have h3 : n = 0 := Int.abs_lt_one_iff.mp h2
  rw [h3] at hn
  simp only [Int.cast_zero] at hn
  linarith

/-- Shifting a real by the period `1` does not change its image in `AddCircle 1`. -/
lemma addCircle_coe_add_one (x : ℝ) :
    ((x + 1 : ℝ) : AddCircle (1:ℝ)) = (x : AddCircle (1:ℝ)) :=
  AddCircle.coe_add_period 1 x

/-- The closed arc `coe '' Icc c d` is closed in `AddCircle 1`. -/
lemma addCircle_arc_isClosed (c d : ℝ) :
    IsClosed (((↑) : ℝ → AddCircle (1:ℝ)) '' Icc c d) := by
  have : Fact ((0:ℝ) < 1) := ⟨one_pos⟩
  exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed

/-- The open arc `coe '' Ioo c d` is open in `AddCircle 1`. -/
lemma addCircle_arc_isOpen (c d : ℝ) :
    IsOpen (((↑) : ℝ → AddCircle (1:ℝ)) '' Ioo c d) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- The frontier of a closed arc is contained in its two endpoints. -/
lemma addCircle_frontier_arc_subset {c d : ℝ} (hcd : c ≤ d) :
    frontier (((↑) : ℝ → AddCircle (1:ℝ)) '' Icc c d) ⊆
      {((c : ℝ) : AddCircle (1:ℝ)), ((d : ℝ) : AddCircle (1:ℝ))} := by
  have hclosed := addCircle_arc_isClosed c d
  have hopen := addCircle_arc_isOpen c d
  have hint : ((↑) : ℝ → AddCircle (1:ℝ)) '' Ioo c d ⊆
      interior (((↑) : ℝ → AddCircle (1:ℝ)) '' Icc c d) :=
    interior_maximal (image_mono Ioo_subset_Icc_self) hopen
  intro z hz
  rw [hclosed.frontier_eq] at hz
  obtain ⟨⟨y, hy, rfl⟩, hz2⟩ := hz
  have hnot : y ∉ Ioo c d := fun hy' => hz2 (hint ⟨y, hy', rfl⟩)
  have hy' : y = c ∨ y = d := by
    rcases lt_or_eq_of_le hy.1 with h1 | h1
    · rcases lt_or_eq_of_le hy.2 with h2 | h2
      · exact absurd ⟨h1, h2⟩ hnot
      · exact Or.inr h2
    · exact Or.inl h1.symm
  rcases hy' with rfl | rfl
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ (mem_singleton _)

/-- A closed arc and the complementary open arc cover the circle. -/
lemma addCircle_arc_union_covers {c d : ℝ} (hcd : c ≤ d) (hlen : d < c + 1) :
    (((↑) : ℝ → AddCircle (1:ℝ)) '' Icc c d) ∪
      (((↑) : ℝ → AddCircle (1:ℝ)) '' Ioo d (c + 1)) = univ := by
  have : Fact ((0:ℝ) < 1) := ⟨one_pos⟩
  rw [← image_union]
  have hsets : Icc c d ∪ Ioo d (c + 1) = Ico c (c + 1) := by
    ext x
    simp only [mem_union, mem_Icc, mem_Ioo, mem_Ico]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, lt_of_le_of_lt h2 hlen⟩
      · exact ⟨hcd.trans h1.le, h2⟩
    · rintro ⟨h1, h2⟩
      rcases le_or_gt x d with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h, h2⟩
  rw [hsets]
  exact AddCircle.coe_image_Ico_eq 1 c

end AddCircleArith

end
