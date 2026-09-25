/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.Charts
public import LeanPool.OneManifold.OneMfld.Normalize
public import LeanPool.OneManifold.OneMfld.GlueBlocks
public import LeanPool.OneManifold.OneMfld.TwoComponents
public import LeanPool.OneManifold.OneMfld.CircleBlocks


/-! # The circle chart

Two interior charts whose overlap is disconnected wrap around and close `M` into a
circle: after normalizing, the overlap has exactly two components, one at each end of
each chart. We shrink the charts' coordinates (Möbius) into a controlled numeric regime,
choose a split point in each component, and glue the two charts — each embedded as an
arc of `AddCircle 1` — with `OpenPartialHomeomorph.piecewise` along a closed sub-arc
whose frontier is the two split points. The result is a chart of `M` onto the whole of
`AddCircle 1` with source `a.source ∪ b.source`.
-/

@[expose] public section

namespace OneMfld

open Set

/-! ### Small helpers -/

/-- Two reals with the same image in `AddCircle 1` differ by an integer. -/
private lemma addCircle_coe_eq_iff_int {x y : ℝ} :
    (x : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) ↔ ∃ n : ℤ, x - y = (n : ℝ) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp h
    exact ⟨n, by rw [← hn, zsmul_eq_mul, mul_one]⟩
  · rintro ⟨n, hn⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by rw [zsmul_eq_mul, mul_one, hn]⟩

/-- Window analysis: two reals with the same circle image and difference in `(-1, 2)`
are equal or differ by exactly one period. -/
private lemma addCircle_eq_or_eq_add_one {x y : ℝ}
    (h : (x : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)))
    (h1 : -1 < x - y) (h2 : x - y < 2) : x = y ∨ x = y + 1 := by
  obtain ⟨n, hn⟩ := addCircle_coe_eq_iff_int.mp h
  have hn1 : (-1 : ℝ) < (n : ℝ) := hn ▸ h1
  have hn2 : ((n : ℤ) : ℝ) < 2 := hn ▸ h2
  have hn1' : (-1 : ℤ) < n := by exact_mod_cast hn1
  have hn2' : n < 2 := by exact_mod_cast hn2
  interval_cases n
  · left
    have : x - y = 0 := by rw [hn]; norm_num
    linarith
  · right
    have : x - y = 1 := by rw [hn]; norm_num
    linarith

/-- Pull membership in a chart image back to membership in the set, using injectivity. -/
private lemma mem_of_image_mem {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M NNReal) {W : Set M} {I : Set NNReal}
    (hW : W ⊆ e.source) (himg : e '' W = I) {x : M} (hx : x ∈ e.source)
    (hval : e x ∈ I) : x ∈ W := by
  rw [← himg] at hval
  obtain ⟨w, hw, hvw⟩ := hval
  rwa [← e.injOn (hW hw) hx hvw]

/-- A strictly increasing correspondence on `W` matches lower cuts at a point of `W`. -/
private lemma mono_key_le {M : Type*} [TopologicalSpace M]
    (A B : OpenPartialHomeomorph M NNReal)
    {W : Set M} (hWA : W ⊆ A.source)
    (mono : ∀ x ∈ W, ∀ y ∈ W, A x < A y → B x < B y)
    {m : M} (hm : m ∈ W) :
    ∀ x ∈ W, (A m ≤ A x ↔ B m ≤ B x) := by
  intro x hx
  constructor
  · intro hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [A.injOn (hWA hm) (hWA hx) heq]
    · exact (mono m hm x hx hlt).le
  · intro hle
    by_contra hgt
    rw [not_le] at hgt
    exact absurd hle (not_le.2 (mono x hx m hm hgt))

/-- A strictly increasing correspondence on `W` matches upper cuts at a point of `W`. -/
private lemma mono_key_ge {M : Type*} [TopologicalSpace M]
    (A B : OpenPartialHomeomorph M NNReal)
    {W : Set M} (hWA : W ⊆ A.source)
    (mono : ∀ x ∈ W, ∀ y ∈ W, A x < A y → B x < B y)
    {m : M} (hm : m ∈ W) :
    ∀ x ∈ W, (A x ≤ A m ↔ B x ≤ B m) := by
  intro x hx
  constructor
  · intro hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [A.injOn (hWA hx) (hWA hm) heq]
    · exact (mono x hx m hm hlt).le
  · intro hle
    by_contra hgt
    rw [not_le] at hgt
    exact absurd hle (not_le.2 (mono m hm x hx hgt))

/-- The real parameters of the circle gluing: slopes `kα`, `kg` and offset `g0` with the
matching identities and strict separation inequalities. -/
private lemma circle_params {ρ ν σ μ : ℝ}
    (hρ0 : 0 < ρ) (hρ4 : ρ < 1 / 4) (hν3 : 3 / 4 < ν) (hν1 : ν < 1)
    (hσ0 : 0 < σ) (hσ4 : σ < 1 / 4) (hμ3 : 3 / 4 < μ) (hμ1 : μ < 1) :
    ∃ kα kg g0 : ℝ, 0 < kα ∧ kα < 1 ∧ 0 < kg ∧ kg < 1 ∧
      kg * σ + g0 = kα * ν ∧
      kg * μ + g0 = 1 + kα * ρ ∧
      kα * ρ < g0 ∧
      g0 < kα * ν ∧
      1 + kα * ρ < g0 + kg ∧
      g0 + kg < 1 + kα * ν := by
  have hνρ : 1/2 < ν - ρ := by linarith
  have hμσ0 : 0 < μ - σ := by linarith
  have hd1 : (1 - μ + σ)/(ν - ρ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have h23 : (2/3 : ℝ) < 1 := by norm_num
  obtain ⟨kα, hkα1, hkα2⟩ := exists_between (max_lt hd1 h23)
  have hkα23 : (2/3 : ℝ) < kα := lt_of_le_of_lt (le_max_right _ _) hkα1
  have hkαd : (1 - μ + σ)/(ν - ρ) < kα := lt_of_le_of_lt (le_max_left _ _) hkα1
  have hkα0 : (0:ℝ) < kα := by linarith
  have hnum : 0 < 1 - kα * (ν - ρ) := by
    nlinarith [mul_pos (show (0:ℝ) < 1 - kα by linarith) (show (0:ℝ) < ν - ρ by linarith)]
  set kg := (1 - kα * (ν - ρ)) / (μ - σ) with hkgdef
  have hkg0 : 0 < kg := div_pos hnum hμσ0
  have hkgden : kg * (μ - σ) = 1 - kα * (ν - ρ) := div_mul_cancel₀ _ hμσ0.ne'
  have hkg1 : kg < 1 := by
    rw [hkgdef, div_lt_one hμσ0]
    have := (div_lt_iff₀ (show (0:ℝ) < ν - ρ by linarith)).mp hkαd
    linarith
  set g0 := kα * ν - kg * σ with hg0def
  have hid1 : kg * σ + g0 = kα * ν := by rw [hg0def]; ring
  have hid2 : kg * μ + g0 = 1 + kα * ρ := by
    rw [hg0def]; linear_combination hkgden
  have hP1 : (1/3 : ℝ) < kα * (ν - ρ) := by nlinarith
  have hP2 : (1 / 4 : ℝ) < kα * (ν - ρ) * μ := by nlinarith
  have hkey : σ < kα * (ν - ρ) * μ := by linarith
  have hc₁g0 : kα * ρ < g0 := by
    have h2 : kg * σ * (μ - σ) = σ * (1 - kα * (ν - ρ)) := by
      rw [← hkgden]; ring
    have h3 : kg * σ * (μ - σ) < kα * (ν - ρ) * (μ - σ) := by
      rw [h2]; nlinarith
    have h4 : kg * σ < kα * (ν - ρ) := lt_of_mul_lt_mul_right h3 hμσ0.le
    rw [hg0def]; nlinarith
  have hg0d : g0 < kα * ν := by
    rw [hg0def]
    nlinarith [mul_pos hkg0 hσ0]
  have h1c : 1 + kα * ρ < g0 + kg := by
    nlinarith [hid2, mul_pos hkg0 (show (0:ℝ) < 1 - μ by linarith)]
  have hg1d : g0 + kg < 1 + kα * ν := by
    nlinarith [hid1, mul_pos hkg0 hσ0]
  exact ⟨kα, kg, g0, hkα0, hkα2, hkg0, hkg1, hid1, hid2, hc₁g0, hg0d, h1c, hg1d⟩

/-- The target of a chart of the form `x ↦ coe (k * X x + d)` (with `X` landing onto
`Ioo 0 1`) is the arc `coe '' Ioo d (d + k)`. -/
private lemma affine_circle_target {M : Type*} [TopologicalSpace M]
    (X : OpenPartialHomeomorph M NNReal) (hXt : X.target = Ioo 0 1)
    (E : OpenPartialHomeomorph M (AddCircle (1 : ℝ)))
    (hEs : E.source = X.source) {k d : ℝ} (hk : 0 < k)
    (hEval : ∀ x ∈ X.source, E x = ((k * ((X x : NNReal) : ℝ) + d : ℝ) : AddCircle (1 : ℝ))) :
    E.target = ((↑) : ℝ → AddCircle (1 : ℝ)) '' (Ioo d (d + k)) := by
  rw [← E.image_source_eq_target, hEs]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hEval x hx]
    have hXx : X x ∈ Ioo (0:NNReal) 1 := hXt ▸ X.map_source hx
    have h0 : (0:ℝ) < ((X x : NNReal) : ℝ) := by exact_mod_cast hXx.1
    have h1 : ((X x : NNReal) : ℝ) < 1 := by exact_mod_cast hXx.2
    exact mem_image_of_mem _ ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨u, hu, rfl⟩
    have h0 : 0 < (u - d)/k := div_pos (by linarith [hu.1]) hk
    have h1 : (u - d)/k < 1 := (div_lt_one hk).mpr (by linarith [hu.2])
    set t := Real.toNNReal ((u - d)/k) with htdef
    have htc : (t : ℝ) = (u - d)/k := Real.coe_toNNReal _ h0.le
    have ht : t ∈ Ioo (0:NNReal) 1 := by
      constructor
      · rw [← NNReal.coe_lt_coe, NNReal.coe_zero, htc]; exact h0
      · rw [← NNReal.coe_lt_coe, NNReal.coe_one, htc]; exact h1
    have htT : t ∈ X.target := hXt ▸ ht
    refine ⟨X.symm t, X.map_target htT, ?_⟩
    rw [hEval _ (X.map_target htT), X.right_inv htT, htc]
    congr 1
    field_simp
    ring

/-- Normalize both charts to target `Ioo 0 1`, split the overlap into its two
components, orient the second chart so the component lower in `a` is upper in `b`, and
Möbius-shrink both charts so the lower end-segments sit below `1 / 4`. -/
private lemma exists_normalized_charts {M : Type*} [TopologicalSpace M] [T2Space M]
    (a b : OChart M) (h : Overlap a.source b.source)
    (hdisc : ¬ IsConnected (a.source ∩ b.source)) :
    ∃ (A B : OpenPartialHomeomorph M NNReal) (W₀ W₁ : Set M) (r p s q : NNReal),
      A.source = a.source ∧ B.source = b.source ∧
      A.target = Ioo 0 1 ∧ B.target = Ioo 0 1 ∧
      A.source ∩ B.source = W₀ ∪ W₁ ∧
      A '' W₀ = Ioo 0 r ∧ A '' W₁ = Ioo p 1 ∧
      B '' W₀ = Ioo q 1 ∧ B '' W₁ = Ioo 0 s ∧
      0 < r ∧ r ≤ p ∧ p < 1 ∧ r < 1 / 4 ∧
      0 < s ∧ s ≤ q ∧ q < 1 ∧ s < 1 / 4 := by
  have hane : a.source.Nonempty := h.1.mono inter_subset_left
  have hbne : b.source.Nonempty := h.1.mono inter_subset_right
  obtain ⟨a₀, ha₀s, ha₀t, -⟩ := a.rescale hane
  obtain ⟨b₀, hb₀s, hb₀t, -⟩ := b.rescale hbne
  have hab : (a₀.source \ b₀.source).Nonempty := by rw [ha₀s, hb₀s]; exact h.2.1
  have hba : (b₀.source \ a₀.source).Nonempty := by rw [ha₀s, hb₀s]; exact h.2.2
  have hne : (a₀.source ∩ b₀.source).Nonempty := by rw [ha₀s, hb₀s]; exact h.1
  have hdisc' : ¬ IsConnected (a₀.source ∩ b₀.source) := by rw [ha₀s, hb₀s]; exact hdisc
  have hbconn : IsConnected b₀.source := b₀.connected_source (hb₀s ▸ hbne)
  obtain ⟨W₀, W₁, r₀, p₁, hunion, hcomp₀, hcomp₁, hdisj, himgA₀, himgA₁, hr₀0, hr₀p, hp₁1⟩ :=
    two_components_structure a₀.toOpenPartialHomeomorph b₀.toOpenPartialHomeomorph
      ha₀t hbconn hab hba hne hdisc'
  have hW₀S : W₀ ⊆ a₀.source ∩ b₀.source := by rw [hunion]; exact subset_union_left
  have hW₁S : W₁ ⊆ a₀.source ∩ b₀.source := by rw [hunion]; exact subset_union_right
  have hne₀ : W₀.Nonempty := by
    have himg : (a₀.toOpenPartialHomeomorph '' W₀).Nonempty := by
      rw [himgA₀]; exact nonempty_Ioo.2 hr₀0
    exact himg.of_image
  have hne₁ : W₁.Nonempty := by
    have himg : (a₀.toOpenPartialHomeomorph '' W₁).Nonempty := by
      rw [himgA₁]; exact nonempty_Ioo.2 hp₁1
    exact himg.of_image
  have haconn : IsConnected a₀.source := a₀.connected_source (ha₀s ▸ hane)
  obtain ⟨s₁, q₀, hs₁0, hs₁q₀, hq₀1, harr⟩ :=
    two_components_other_chart a₀.toOpenPartialHomeomorph b₀.toOpenPartialHomeomorph
      hb₀t haconn hab hcomp₀ hcomp₁ hne₀ hne₁ hdisj
  -- Orient the `b`-side chart so that `W₀` is upper and `W₁` is lower.
  have hBpick : ∃ B₁ : OpenPartialHomeomorph M NNReal,
      B₁.source = b.source ∧ B₁.target = Ioo 0 1 ∧
      ∃ s₂ q₂ : NNReal, 0 < s₂ ∧ s₂ ≤ q₂ ∧ q₂ < 1 ∧
        B₁ '' W₀ = Ioo q₂ 1 ∧ B₁ '' W₁ = Ioo 0 s₂ := by
    rcases harr with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · exact ⟨b₀.toOpenPartialHomeomorph, hb₀s, hb₀t, s₁, q₀, hs₁0, hs₁q₀, hq₀1, h₀, h₁⟩
    · obtain ⟨b₁, hb₁s, hb₁t, hb₁f⟩ := b₀.flip hb₀t
      have himg₀ : b₁.toOpenPartialHomeomorph '' W₀
          = (fun y => 1 - y) '' (b₀.toOpenPartialHomeomorph '' W₀) := by
        rw [← image_comp]
        exact image_congr (fun x hx => hb₁f x (hW₀S hx).2)
      have himg₁ : b₁.toOpenPartialHomeomorph '' W₁
          = (fun y => 1 - y) '' (b₀.toOpenPartialHomeomorph '' W₁) := by
        rw [← image_comp]
        exact image_congr (fun x hx => hb₁f x (hW₁S hx).2)
      rw [h₀, reflect_image_Ioo_lower hs₁0 (hs₁q₀.trans hq₀1.le)] at himg₀
      rw [h₁, reflect_image_Ioo_upper hq₀1] at himg₁
      exact ⟨b₁.toOpenPartialHomeomorph, hb₁s.trans hb₀s, hb₁t, 1 - q₀, 1 - s₁,
        tsub_pos_of_lt hq₀1, tsub_le_tsub_left hs₁q₀ 1, tsub_lt_self one_pos hs₁0,
        himg₀, himg₁⟩
  obtain ⟨B₁, hB₁s, hB₁t, s₂, q₂, hs₂0, hs₂q, hq₂1, himgB₀, himgB₁⟩ := hBpick
  -- Möbius-shrink the `a`-side chart.
  have hr₀1 : r₀ < 1 := lt_of_le_of_lt hr₀p hp₁1
  have hquarter : (0:NNReal) < 1 / 4 := by norm_num
  obtain ⟨cA, hcA0, hcA⟩ := exists_mobiusFun_lt hr₀0 hr₀1 hquarter
  obtain ⟨mA, hmAs, hmAt, hmAf, hmAlo, hmAhi⟩ := mobiusOPH' cA hcA0
  set A := a₀.toOpenPartialHomeomorph.trans mA with hAdef
  have hAs : A.source = a.source := by
    rw [hAdef, OpenPartialHomeomorph.trans_source, hmAs, ← ha₀s]
    refine inter_eq_left.mpr fun x hx => ?_
    rw [mem_preimage, ← ha₀t]
    exact a₀.toOpenPartialHomeomorph.map_source hx
  have hAt : A.target = Ioo 0 1 := by
    rw [hAdef, OpenPartialHomeomorph.trans_target, hmAt]
    refine inter_eq_left.mpr fun y hy => ?_
    rw [mem_preimage, ha₀t, ← hmAs]
    exact mA.map_target (by rw [hmAt]; exact hy)
  have hr₀mem : r₀ ∈ Ioo (0:NNReal) 1 := ⟨hr₀0, hr₀1⟩
  have hp₁mem : p₁ ∈ Ioo (0:NNReal) 1 := ⟨lt_of_lt_of_le hr₀0 hr₀p, hp₁1⟩
  have himA₀ : A '' W₀ = Ioo 0 (mobiusFun cA r₀) := by
    rw [hAdef, OpenPartialHomeomorph.coe_trans, image_comp, himgA₀]
    exact hmAlo r₀ hr₀mem
  have himA₁ : A '' W₁ = Ioo (mobiusFun cA p₁) 1 := by
    rw [hAdef, OpenPartialHomeomorph.coe_trans, image_comp, himgA₁]
    exact hmAhi p₁ hp₁mem
  have hmonoA := mobiusFun_strictMonoOn cA hcA0
  have hrp' : mobiusFun cA r₀ ≤ mobiusFun cA p₁ := by
    rcases eq_or_lt_of_le hr₀p with heq | hlt
    · rw [heq]
    · exact (hmonoA hr₀mem hp₁mem hlt).le
  have hr'mem := mobiusFun_mem cA hcA0 hr₀mem
  have hp'mem := mobiusFun_mem cA hcA0 hp₁mem
  -- Möbius-shrink the `b`-side chart.
  have hs₂1 : s₂ < 1 := lt_of_le_of_lt hs₂q hq₂1
  obtain ⟨cB, hcB0, hcB⟩ := exists_mobiusFun_lt hs₂0 hs₂1 hquarter
  obtain ⟨mB, hmBs, hmBt, hmBf, hmBlo, hmBhi⟩ := mobiusOPH' cB hcB0
  set B := B₁.trans mB with hBdef
  have hBs : B.source = b.source := by
    rw [hBdef, OpenPartialHomeomorph.trans_source, hmBs, ← hB₁s]
    refine inter_eq_left.mpr fun x hx => ?_
    rw [mem_preimage, ← hB₁t]
    exact B₁.map_source hx
  have hBt : B.target = Ioo 0 1 := by
    rw [hBdef, OpenPartialHomeomorph.trans_target, hmBt]
    refine inter_eq_left.mpr fun y hy => ?_
    rw [mem_preimage, hB₁t, ← hmBs]
    exact mB.map_target (by rw [hmBt]; exact hy)
  have hs₂mem : s₂ ∈ Ioo (0:NNReal) 1 := ⟨hs₂0, hs₂1⟩
  have hq₂mem : q₂ ∈ Ioo (0:NNReal) 1 := ⟨lt_of_lt_of_le hs₂0 hs₂q, hq₂1⟩
  have himB₀ : B '' W₀ = Ioo (mobiusFun cB q₂) 1 := by
    rw [hBdef, OpenPartialHomeomorph.coe_trans, image_comp, himgB₀]
    exact hmBhi q₂ hq₂mem
  have himB₁ : B '' W₁ = Ioo 0 (mobiusFun cB s₂) := by
    rw [hBdef, OpenPartialHomeomorph.coe_trans, image_comp, himgB₁]
    exact hmBlo s₂ hs₂mem
  have hmonoB := mobiusFun_strictMonoOn cB hcB0
  have hsq' : mobiusFun cB s₂ ≤ mobiusFun cB q₂ := by
    rcases eq_or_lt_of_le hs₂q with heq | hlt
    · rw [heq]
    · exact (hmonoB hs₂mem hq₂mem hlt).le
  have hs'mem := mobiusFun_mem cB hcB0 hs₂mem
  have hq'mem := mobiusFun_mem cB hcB0 hq₂mem
  have hunion' : A.source ∩ B.source = W₀ ∪ W₁ := by
    rw [hAs, hBs, ← ha₀s, ← hb₀s]
    exact hunion
  exact ⟨A, B, W₀, W₁, mobiusFun cA r₀, mobiusFun cA p₁, mobiusFun cB s₂, mobiusFun cB q₂,
    hAs, hBs, hAt, hBt, hunion', himA₀, himA₁, himB₀, himB₁,
    hr'mem.1, hrp', hp'mem.2, hcA, hs'mem.1, hsq', hq'mem.2, hcB⟩

private theorem circle_overlap_membership
    {M : Type*}
    [TopologicalSpace M]
    (A B : OpenPartialHomeomorph M NNReal)
    (W₀ W₁ : Set M)
    (r p s q : NNReal)
    (hBt : B.target = Ioo 0 1)
    (hunion : A.source ∩ B.source = W₀ ∪ W₁)
    (himgA₀ : A '' W₀ = Ioo 0 r)
    (himgA₁ : A '' W₁ = Ioo p 1)
    (himgB₀ : B '' W₀ = Ioo q 1)
    (himgB₁ : B '' W₁ = Ioo 0 s)
    (hrp : r ≤ p)
    (hsq : s ≤ q)
    (hW₀A : W₀ ⊆ A.source)
    (hW₀B : W₀ ⊆ B.source)
    (hW₁A : W₁ ⊆ A.source)
    (hW₁B : W₁ ⊆ B.source)
    (ν : NNReal)
    (hpν : p < ν)
    (m₁ : M)
    (hm₁ν : A m₁ = ν)
    (μ : NNReal)
    (hqμ : q < μ)
    (m₀ : M)
    (hm₀μ : B m₀ = μ)
    (hρmem : A m₀ ∈ Ioo 0 r)
    (hσmem : B m₁ ∈ Ioo 0 s)
    (K₀ : ∀ x ∈ W₀, A m₀ ≤ A x ↔ B m₀ ≤ B x)
    (K₁ : ∀ x ∈ W₁, A x ≤ A m₁ ↔ B x ≤ B m₁)
    (sset : Set M)
    (hssetdef : sset = A.source ∩ A ⁻¹' Icc (A m₀) ν) :
    ∀ y ∈ B.source, B y ≤ B m₁ ∨ B m₀ ≤ B y ↔ y ∈ sset := by
  classical
  intro y hy
  rw [hssetdef]
  by_cases hyA : y ∈ A.source
  · have hyS : y ∈ W₀ ∪ W₁ := by rw [← hunion]; exact ⟨hyA, hy⟩
    rcases hyS with hyW | hyW
    · have hAy : A y ∈ Ioo 0 r := by rw [← himgA₀]; exact mem_image_of_mem _ hyW
      have hBy : B y ∈ Ioo q 1 := by rw [← himgB₀]; exact mem_image_of_mem _ hyW
      have hnots : ¬ (B y ≤ B m₁) := by
        rw [not_le]
        exact lt_trans (lt_of_lt_of_le hσmem.2 hsq) hBy.1
      have hK := K₀ y hyW
      constructor
      · rintro (hc | hc)
        · exact absurd hc hnots
        · refine ⟨hyA, ?_⟩
          rw [mem_preimage]
          exact ⟨hK.mpr hc, le_of_lt (lt_of_lt_of_le hAy.2 (hrp.trans hpν.le))⟩
      · rintro ⟨-, hmem⟩
        rw [mem_preimage] at hmem
        exact Or.inr (hK.mp hmem.1)
    · have hAy : A y ∈ Ioo p 1 := by rw [← himgA₁]; exact mem_image_of_mem _ hyW
      have hBy : B y ∈ Ioo 0 s := by rw [← himgB₁]; exact mem_image_of_mem _ hyW
      have hnots : ¬ (B m₀ ≤ B y) := by
        rw [not_le, hm₀μ]
        exact lt_trans (lt_of_lt_of_le hBy.2 hsq) hqμ
      have hK := K₁ y hyW
      constructor
      · rintro (hc | hc)
        · refine ⟨hyA, ?_⟩
          rw [mem_preimage]
          refine ⟨le_of_lt (lt_trans (lt_of_lt_of_le hρmem.2 hrp) hAy.1), ?_⟩
          rw [← hm₁ν]
          exact hK.mpr hc
        · exact absurd hc hnots
      · rintro ⟨-, hmem⟩
        rw [mem_preimage] at hmem
        refine Or.inl (hK.mp ?_)
        rw [hm₁ν]
        exact hmem.2
  · constructor
    · rintro (hc | hc)
      · exfalso
        have hBy0 : (0:NNReal) < B y := by
          have hmem := B.map_source hy
          rw [hBt] at hmem
          exact hmem.1
        have hmem : B y ∈ Ioo 0 s := ⟨hBy0, lt_of_le_of_lt hc hσmem.2⟩
        have hyW : y ∈ W₁ := mem_of_image_mem B hW₁B himgB₁ hy hmem
        exact hyA (hW₁A hyW)
      · exfalso
        have hBy1 : B y < 1 := by
          have hmem := B.map_source hy
          rw [hBt] at hmem
          exact hmem.2
        rw [hm₀μ] at hc
        have hmem : B y ∈ Ioo q 1 := ⟨lt_of_lt_of_le hqμ hc, hBy1⟩
        have hyW : y ∈ W₀ := mem_of_image_mem B hW₀B himgB₀ hy hmem
        exact hyA (hW₀A hyW)
    · rintro ⟨hyA', -⟩
      exact absurd hyA' hyA

private theorem glue_circle_arcs
    {M : Type*}
    [TopologicalSpace M]
    (A B : OpenPartialHomeomorph M NNReal)
    (W₀ W₁ : Set M)
    (r p : NNReal)
    (hAt : A.target = Ioo 0 1)
    (himgA₀ : A '' W₀ = Ioo 0 r)
    (himgA₁ : A '' W₁ = Ioo p 1)
    (hW₀A : W₀ ⊆ A.source)
    (hW₀B : W₀ ⊆ B.source)
    (hW₁A : W₁ ⊆ A.source)
    (hW₁B : W₁ ⊆ B.source)
    (ν : NNReal)
    (hpν : p < ν)
    (m₁ : M)
    (hm₁ν : A m₁ = ν)
    (μ : NNReal)
    (m₀ : M)
    (hm₀μ : B m₀ = μ)
    (hm₀A : m₀ ∈ A.source)
    (hm₀B : m₀ ∈ B.source)
    (hm₁A : m₁ ∈ A.source)
    (hm₁B : m₁ ∈ B.source)
    (hρmem : A m₀ ∈ Ioo 0 r)
    (kα kg g0 : ℝ)
    (hkα1 : kα < 1)
    (hkg1 : kg < 1)
    (hid1 : kg * ↑(B m₁) + g0 = kα * ↑ν)
    (hid2 : kg * ↑μ + g0 = 1 + kα * ↑(A m₀))
    (hcg0 : kα * ↑(A m₀) < g0)
    (hg0d : g0 < kα * ↑ν)
    (h1c : 1 + kα * ↑(A m₀) < g0 + kg)
    (hc₁0 : 0 < kα * ↑(A m₀))
    (hd₁kα : kα * ↑ν < kα)
    (hc₁1 : kα * ↑(A m₀) < 1)
    (hc₁d₁ : kα * ↑(A m₀) ≤ kα * ↑ν)
    (e e' : OpenPartialHomeomorph M (AddCircle 1))
    (heval : ∀ (x : M), e x = ↑(kα * ↑(A x)))
    (he'val : ∀ (x : M), e' x = ↑(kg * ↑(B x) + g0))
    (hes : e.source = A.source)
    (he's : e'.source = B.source)
    (htargetE : e.target = QuotientAddGroup.mk '' Ioo 0 kα)
    (htargetE' : e'.target = QuotientAddGroup.mk '' Ioo g0 (g0 + kg))
    (sset : Set M)
    (tset : Set (ℝ ⧸ AddSubgroup.zmultiples 1))
    (hssub : sset ⊆ A.source)
    (H : e.IsImage sset tset)
    (claim1 :
      ∀ v ∈ Ioo g0 (g0 + kg), ↑v ∈ tset ↔ v ∈ Icc (kα * ↑(A m₀)) (kα * ↑ν) ∨ v ∈ Icc (1 +
      kα * ↑(A m₀)) (1 + kα * ↑ν))
    (H' : e'.IsImage sset tset)
    (hfrontier : frontier tset ⊆ {↑(kα * ↑(A m₀)), ↑(kα * ↑ν)})
    (hssetdef : sset = A.source ∩ A ⁻¹' Icc (A m₀) ν)
    (htsetdef : tset = ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc (kα * (A m₀ : ℝ)) (kα * (ν : ℝ))) :
  ∃ f : OpenPartialHomeomorph M (AddCircle (1 : ℝ)),
    f.source = A.source ∪ B.source ∧ f.target = univ := by
  classical
  -- Injectivity of each chart identifies the split-point fibers.
  have he₀ : e m₀ = ((kα * ((A m₀ : NNReal) : ℝ) : ℝ) : AddCircle (1 : ℝ)) :=
    heval m₀
  have he₁ : e m₁ = ((kα * ((ν : NNReal) : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [heval m₁, hm₁ν]
  have he'₀ : e' m₀ = e m₀ := by
    rw [he'val m₀, hm₀μ, hid2, heval m₀, add_comm 1]
    exact addCircle_coe_add_one _
  have he'₁ : e' m₁ = e m₁ := by
    rw [he'val m₁, hid1, heval m₁, hm₁ν]
  have Pce : ∀ x ∈ A.source,
      (e x = ((kα * ((A m₀ : NNReal):ℝ) : ℝ) : AddCircle (1 : ℝ)) ↔ x = m₀) := by
    intro x hx
    rw [← he₀]
    exact ⟨fun h => e.injOn (hes.symm ▸ hx) (hes.symm ▸ hm₀A) h, congrArg e⟩
  have Pde : ∀ x ∈ A.source,
      (e x = ((kα * ((ν : NNReal):ℝ) : ℝ) : AddCircle (1 : ℝ)) ↔ x = m₁) := by
    intro x hx
    rw [← he₁]
    exact ⟨fun h => e.injOn (hes.symm ▸ hx) (hes.symm ▸ hm₁A) h, congrArg e⟩
  have Pce' : ∀ y ∈ B.source,
      (e' y = ((kα * ((A m₀ : NNReal):ℝ) : ℝ) : AddCircle (1 : ℝ)) ↔ y = m₀) := by
    intro y hy
    rw [← he₀, ← he'₀]
    exact ⟨fun h => e'.injOn (he's.symm ▸ hy) (he's.symm ▸ hm₀B) h, congrArg e'⟩
  have Pde' : ∀ y ∈ B.source,
      (e' y = ((kα * ((ν : NNReal):ℝ) : ℝ) : AddCircle (1 : ℝ)) ↔ y = m₁) := by
    intro y hy
    rw [← he₁, ← he'₁]
    exact ⟨fun h => e'.injOn (he's.symm ▸ hy) (he's.symm ▸ hm₁B) h, congrArg e'⟩
  -- Frontier agreement and equality on the frontier.
  have hpre := H.frontier.preimage_eq
  have hpre' := H'.frontier.preimage_eq
  have Hs : e.source ∩ frontier sset = e'.source ∩ frontier sset := by
    rw [← hpre, ← hpre']
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hx, hfx⟩
      have hx' : x ∈ A.source := by rwa [hes] at hx
      have hex := hfrontier hfx
      simp only [mem_insert_iff, mem_singleton_iff] at hex
      rcases hex with hcx | hdx
      · have hxm : x = m₀ := (Pce x hx').mp hcx
        subst hxm
        refine ⟨by rw [he's]; exact hm₀B, ?_⟩
        rw [(Pce' x hm₀B).mpr rfl, ← hcx]
        exact hfx
      · have hxm : x = m₁ := (Pde x hx').mp hdx
        subst hxm
        refine ⟨by rw [he's]; exact hm₁B, ?_⟩
        rw [(Pde' x hm₁B).mpr rfl, ← hdx]
        exact hfx
    · rintro ⟨hx, hfx⟩
      have hx' : x ∈ B.source := by rwa [he's] at hx
      have hex := hfrontier hfx
      simp only [mem_insert_iff, mem_singleton_iff] at hex
      rcases hex with hcx | hdx
      · have hxm : x = m₀ := (Pce' x hx').mp hcx
        subst hxm
        refine ⟨by rw [hes]; exact hm₀A, ?_⟩
        rw [(Pce x hm₀A).mpr rfl, ← hcx]
        exact hfx
      · have hxm : x = m₁ := (Pde' x hx').mp hdx
        subst hxm
        refine ⟨by rw [hes]; exact hm₁A, ?_⟩
        rw [(Pde x hm₁A).mpr rfl, ← hdx]
        exact hfx
  have Heq : Set.EqOn e e' (e.source ∩ frontier sset) := by
    rw [← hpre]
    rintro x ⟨hx, hfx⟩
    rw [mem_preimage] at hfx
    have hx' : x ∈ A.source := by rwa [hes] at hx
    have hex := hfrontier hfx
    simp only [mem_insert_iff, mem_singleton_iff] at hex
    rcases hex with hcx | hdx
    · have hxm : x = m₀ := (Pce x hx').mp hcx
      subst hxm
      rw [hcx, (Pce' x hm₀B).mpr rfl]
    · have hxm : x = m₁ := (Pde x hx').mp hdx
      subst hxm
      rw [hdx, (Pde' x hm₁B).mpr rfl]
  -- Glue.
  refine ⟨e.piecewise e' sset tset H H' Hs Heq, ?_, ?_⟩
  · change Set.ite sset e.source e'.source = A.source ∪ B.source
    have hite : Set.ite sset e.source e'.source
        = (e.source ∩ sset) ∪ (e'.source \ sset) := rfl
    rw [hite, hes, he's]
    apply Subset.antisymm
    · rintro x (⟨hx, -⟩ | ⟨hx, -⟩)
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro x hx
      by_cases hxs : x ∈ sset
      · exact Or.inl ⟨hssub hxs, hxs⟩
      · rcases hx with hxa | hxb
        · have hxB : x ∈ B.source := by
            have hAx : A x ∈ Ioo (0:NNReal) 1 := hAt ▸ A.map_source hxa
            have hnot : A x ∉ Icc (A m₀) ν := by
              intro hmem
              exact hxs (by rw [hssetdef]; exact ⟨hxa, hmem⟩)
            rcases lt_or_ge (A x) (A m₀) with hlt | hge
            · have hmem : A x ∈ Ioo 0 r := ⟨hAx.1, lt_trans hlt hρmem.2⟩
              exact hW₀B (mem_of_image_mem A hW₀A himgA₀ hxa hmem)
            · rcases le_or_gt (A x) ν with hle | hgt
              · exact absurd ⟨hge, hle⟩ hnot
              · have hmem : A x ∈ Ioo p 1 := ⟨lt_trans hpν hgt, hAx.2⟩
                exact hW₁B (mem_of_image_mem A hW₁A himgA₁ hxa hmem)
          exact Or.inr ⟨hxB, hxs⟩
        · exact Or.inr ⟨hxb, hxs⟩
  · change Set.ite tset e.target e'.target = univ
    have hite : Set.ite tset e.target e'.target
        = (e.target ∩ tset) ∪ (e'.target \ tset) := rfl
    rw [hite]
    have h1 : e.target ∩ tset = tset := by
      apply inter_eq_right.mpr
      rw [htargetE, htsetdef]
      exact image_mono
        (fun u hu => ⟨lt_of_lt_of_le hc₁0 hu.1, lt_of_le_of_lt hu.2 hd₁kα⟩)
    have h2 : e'.target \ tset = ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        (Ioo (kα * ((ν : NNReal):ℝ)) (kα * ((A m₀ : NNReal):ℝ) + 1)) := by
      rw [htargetE']
      ext z
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hnt⟩
        have hnor : ¬(v ∈ Icc (kα * ((A m₀ : NNReal):ℝ)) (kα * ((ν : NNReal):ℝ)) ∨
            v ∈ Icc (1 + kα * ((A m₀ : NNReal):ℝ)) (1 + kα * ((ν : NNReal):ℝ))) :=
          fun hor => hnt ((claim1 v hv).mpr hor)
        push Not at hnor
        obtain ⟨hn1, hn2⟩ := hnor
        rw [mem_Icc] at hn1 hn2
        push Not at hn1 hn2
        refine mem_image_of_mem _ ⟨?_, ?_⟩
        · exact hn1 (by linarith [hv.1])
        · by_contra hge
          push Not at hge
          have := hn2 (by linarith)
          linarith [hv.2]
      · rintro ⟨u, hu, rfl⟩
        have huv : u ∈ Ioo g0 (g0 + kg) :=
          ⟨lt_trans hg0d hu.1, by linarith [hu.2]⟩
        refine ⟨mem_image_of_mem _ huv, ?_⟩
        intro ht
        rcases (claim1 u huv).mp ht with hin | hin
        · rw [mem_Icc] at hin
          linarith [hu.1, hin.2]
        · rw [mem_Icc] at hin
          linarith [hu.2, hin.1]
    rw [h1, h2, htsetdef]
    exact addCircle_arc_union_covers hc₁d₁ (by linarith)

private theorem circle_coordinate_H
    {M : Type*}
    [TopologicalSpace M]
    (A : OpenPartialHomeomorph M NNReal)
    (ν : NNReal)
    (m₀ : M)
    (kα : ℝ)
    (hkα0 : 0 < kα)
    (hkα1 : kα < 1)
    (hc₁0 : 0 < kα * ↑(A m₀))
    (hd₁kα : kα * ↑ν < kα)
    (e : OpenPartialHomeomorph M (AddCircle 1))
    (heval : ∀ (x : M), e x = ↑(kα * ↑(A x)))
    (hbounds : ∀ x ∈ A.source, 0 < kα * ↑(A x) ∧ kα * ↑(A x) < kα)
    (hes : e.source = A.source)
    (sset : Set M)
    (hssetdef : sset = A.source ∩ A ⁻¹' Icc (A m₀) ν)
    (tset : Set (ℝ ⧸ AddSubgroup.zmultiples 1))
    (htsetdef : tset = QuotientAddGroup.mk '' Icc (kα * ↑(A m₀)) (kα * ↑ν)) :
  e.IsImage sset tset := by
  classical
  intro x hx
  rw [hes] at hx
  rw [heval x]
  obtain ⟨hb0, hb1⟩ := hbounds x hx
  constructor
  · intro hy
    rw [htsetdef] at hy
    rcases hy with ⟨y, hy, hye⟩
    have hyeq : y = kα * ((A x : NNReal):ℝ) := by
      apply addCircle_coe_inj hye
      rw [abs_lt]
      constructor
      · linarith [hy.1]
      · linarith [hy.2]
    rw [hyeq] at hy
    have hxle : ((A m₀ : NNReal):ℝ) ≤ ((A x : NNReal):ℝ) := le_of_mul_le_mul_left hy.1 hkα0
    have hxge : ((A x : NNReal):ℝ) ≤ ((ν : NNReal):ℝ) := le_of_mul_le_mul_left hy.2 hkα0
    rw [hssetdef]
    refine ⟨hx, ?_⟩
    rw [mem_preimage]
    exact ⟨by exact_mod_cast hxle, by exact_mod_cast hxge⟩
  · intro hmem
    rw [hssetdef] at hmem
    obtain ⟨-, hmem2⟩ := hmem
    rw [mem_preimage] at hmem2
    have h1' : ((A m₀ : NNReal):ℝ) ≤ ((A x : NNReal):ℝ) := by exact_mod_cast hmem2.1
    have h2' : ((A x : NNReal):ℝ) ≤ ((ν : NNReal):ℝ) := by exact_mod_cast hmem2.2
    rw [htsetdef]
    exact mem_image_of_mem _ ⟨mul_le_mul_of_nonneg_left h1' hkα0.le,
      mul_le_mul_of_nonneg_left h2' hkα0.le⟩

private theorem circle_coordinate_claim1
    {M : Type*}
    [TopologicalSpace M]
    (A : OpenPartialHomeomorph M NNReal)
    (ν : NNReal)
    (m₀ : M)
    (kα kg g0 : ℝ)
    (hkα1 : kα < 1)
    (hkg1 : kg < 1)
    (hg0d : g0 < kα * ↑ν)
    (h1c : 1 + kα * ↑(A m₀) < g0 + kg)
    (hc₁0 : 0 < kα * ↑(A m₀))
    (hd₁kα : kα * ↑ν < kα)
    (tset : Set (ℝ ⧸ AddSubgroup.zmultiples 1))
    (htsetdef : tset = QuotientAddGroup.mk '' Icc (kα * ↑(A m₀)) (kα * ↑ν)) :
  ∀ v ∈ Ioo g0 (g0 + kg),
    ↑v ∈ tset ↔ v ∈ Icc (kα * ↑(A m₀)) (kα * ↑ν) ∨ v ∈ Icc (1 + kα * ↑(A m₀)) (1 + kα * ↑ν) := by
  classical
  intro v hv
  rw [htsetdef]
  constructor
  · rintro ⟨z, hz, hze⟩
    have h1 : -1 < v - z := by linarith [hz.2, hv.1]
    have h2 : v - z < 2 := by linarith [hz.1, hv.2]
    rcases addCircle_eq_or_eq_add_one hze.symm h1 h2 with heq | heq
    · left; rw [heq]; exact hz
    · right; rw [heq]; exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  · rintro (hv1 | hv2)
    · exact mem_image_of_mem _ hv1
    · refine ⟨v - 1, ⟨by linarith [hv2.1], by linarith [hv2.2]⟩, ?_⟩
      rw [← addCircle_coe_add_one (v - 1), sub_add_cancel]

private theorem circle_coordinate_claim2
    {M : Type*}
    [TopologicalSpace M]
    (A B : OpenPartialHomeomorph M NNReal)
    (ν : NNReal)
    (m₁ : M)
    (μ : NNReal)
    (m₀ : M)
    (hm₀μ : B m₀ = μ)
    (kα kg g0 : ℝ)
    (hkg0 : 0 < kg)
    (hkg1 : kg < 1)
    (hid1 : kg * ↑(B m₁) + g0 = kα * ↑ν)
    (hid2 : kg * ↑μ + g0 = 1 + kα * ↑(A m₀))
    (hg0d : g0 < kα * ↑ν)
    (h1c : 1 + kα * ↑(A m₀) < g0 + kg)
    (hb'bounds : ∀ x ∈ B.source, g0 < kg * ↑(B x) + g0 ∧ kg * ↑(B x) + g0 < g0 + kg) :
  ∀ y ∈ B.source,
    kg * ↑(B y) + g0 ∈ Icc (kα * ↑(A m₀)) (kα * ↑ν) ∨ kg * ↑(B y) + g0 ∈ Icc (1 + kα * ↑(A m₀))
        (1 + kα * ↑ν) ↔
      B y ≤ B m₁ ∨ B m₀ ≤ B y := by
  classical
  intro y hy
  obtain ⟨hb0, hb1⟩ := hb'bounds y hy
  constructor
  · rintro (hc | hc)
    · left
      have h' : kg * ((B y : NNReal):ℝ) + g0 ≤ kg * ((B m₁ : NNReal):ℝ) + g0 := by
        rw [hid1]; exact hc.2
      have hby : ((B y : NNReal):ℝ) ≤ ((B m₁ : NNReal):ℝ) :=
        le_of_mul_le_mul_left (by linarith) hkg0
      exact_mod_cast hby
    · right
      have h' : kg * ((μ : NNReal):ℝ) + g0 ≤ kg * ((B y : NNReal):ℝ) + g0 := by
        rw [hid2]; exact hc.1
      have hby : ((μ : NNReal):ℝ) ≤ ((B y : NNReal):ℝ) :=
        le_of_mul_le_mul_left (by linarith) hkg0
      rw [hm₀μ]
      exact_mod_cast hby
  · rintro (hc | hc)
    · left
      have hby : ((B y : NNReal):ℝ) ≤ ((B m₁ : NNReal):ℝ) := by exact_mod_cast hc
      constructor
      · linarith
      · rw [← hid1]
        have := mul_le_mul_of_nonneg_left hby hkg0.le
        linarith
    · right
      rw [hm₀μ] at hc
      have hby : ((μ : NNReal):ℝ) ≤ ((B y : NNReal):ℝ) := by exact_mod_cast hc
      constructor
      · rw [← hid2]
        have := mul_le_mul_of_nonneg_left hby hkg0.le
        linarith
      · linarith

/-- Assemble the circle chart from the normalized data: embed each chart as an arc of
`AddCircle 1` and glue along a closed sub-arc via `piecewise`. -/
private lemma circle_chart_of_normalized {M : Type*} [TopologicalSpace M] [T2Space M]
    (A B : OpenPartialHomeomorph M NNReal) (W₀ W₁ : Set M) (r p s q : NNReal)
    (hAt : A.target = Ioo 0 1) (hBt : B.target = Ioo 0 1)
    (hunion : A.source ∩ B.source = W₀ ∪ W₁)
    (himgA₀ : A '' W₀ = Ioo 0 r) (himgA₁ : A '' W₁ = Ioo p 1)
    (himgB₀ : B '' W₀ = Ioo q 1) (himgB₁ : B '' W₁ = Ioo 0 s)
    (hr0 : 0 < r) (hrp : r ≤ p) (hp1 : p < 1) (hr4 : r < 1 / 4)
    (hs0 : 0 < s) (hsq : s ≤ q) (hq1 : q < 1) (hs4 : s < 1 / 4) :
    ∃ f : OpenPartialHomeomorph M (AddCircle (1 : ℝ)),
      f.source = A.source ∪ B.source ∧ f.target = univ := by
  classical
  have hfact : Fact ((0:ℝ) < 1) := ⟨one_pos⟩
  -- Subset bookkeeping.
  have hW₀S : W₀ ⊆ A.source ∩ B.source := by rw [hunion]; exact subset_union_left
  have hW₁S : W₁ ⊆ A.source ∩ B.source := by rw [hunion]; exact subset_union_right
  have hW₀A : W₀ ⊆ A.source := fun z hz => (hW₀S hz).1
  have hW₀B : W₀ ⊆ B.source := fun z hz => (hW₀S hz).2
  have hW₁A : W₁ ⊆ A.source := fun z hz => (hW₁S hz).1
  have hW₁B : W₁ ⊆ B.source := fun z hz => (hW₁S hz).2
  -- Numeric NNReal facts.
  have hp0 : (0:NNReal) < p := lt_of_lt_of_le hr0 hrp
  have hq0 : (0:NNReal) < q := lt_of_lt_of_le hs0 hsq
  have hr1 : r < 1 := hr4.trans (by norm_num)
  have hs1 : s < 1 := hs4.trans (by norm_num)
  -- Image of the full overlap.
  have himgS : A '' (A.source ∩ B.source) = Ioo 0 r ∪ Ioo p 1 := by
    rw [hunion, image_union, himgA₀, himgA₁]
  -- Monotone correspondences on both components.
  have mono₀ : ∀ x ∈ W₀, ∀ y ∈ W₀, A x < A y → B x < B y := by
    apply overlap_mono_on A B hW₀S himgA₀ himgB₀
    · rw [hAt]; exact ⟨hr0, hr1⟩
    · rw [hBt]; exact ⟨hq0, hq1⟩
    · rw [himgS]
      rintro (⟨-, h2⟩ | ⟨h1, -⟩)
      · exact absurd h2 (lt_irrefl r)
      · exact absurd h1 (not_lt.2 hrp)
  have mono₁ : ∀ x ∈ W₁, ∀ y ∈ W₁, A x < A y → B x < B y := by
    apply overlap_mono_on' A B hW₁S himgA₁ himgB₁
    · rw [hAt]; exact ⟨hp0, hp1⟩
    · rw [hBt]; exact ⟨hs0, hs1⟩
    · rw [himgS]
      rintro (⟨-, h2⟩ | ⟨h1, -⟩)
      · exact absurd h2 (not_lt.2 hrp)
      · exact absurd h1 (lt_irrefl p)
  -- Split points.
  have h34lt1 : (3 / 4 : NNReal) < 1 := by norm_num
  obtain ⟨ν, hν1', hν2⟩ := exists_between (max_lt hp1 h34lt1)
  have hpν : p < ν := lt_of_le_of_lt (le_max_left _ _) hν1'
  have h34ν : (3 / 4:NNReal) < ν := lt_of_le_of_lt (le_max_right _ _) hν1'
  obtain ⟨m₁, hm₁W, hm₁ν⟩ : ∃ m₁ ∈ W₁, A m₁ = ν := by
    have hmem : ν ∈ A '' W₁ := by rw [himgA₁]; exact ⟨hpν, hν2⟩
    obtain ⟨m₁, hm₁, he⟩ := hmem
    exact ⟨m₁, hm₁, he⟩
  obtain ⟨μ, hμ1', hμ2⟩ := exists_between (max_lt hq1 h34lt1)
  have hqμ : q < μ := lt_of_le_of_lt (le_max_left _ _) hμ1'
  have h34μ : (3 / 4:NNReal) < μ := lt_of_le_of_lt (le_max_right _ _) hμ1'
  obtain ⟨m₀, hm₀W, hm₀μ⟩ : ∃ m₀ ∈ W₀, B m₀ = μ := by
    have hmem : μ ∈ B '' W₀ := by rw [himgB₀]; exact ⟨hqμ, hμ2⟩
    obtain ⟨m₀, hm₀, he⟩ := hmem
    exact ⟨m₀, hm₀, he⟩
  have hm₀A : m₀ ∈ A.source := hW₀A hm₀W
  have hm₀B : m₀ ∈ B.source := hW₀B hm₀W
  have hm₁A : m₁ ∈ A.source := hW₁A hm₁W
  have hm₁B : m₁ ∈ B.source := hW₁B hm₁W
  have hρmem : A m₀ ∈ Ioo 0 r := by rw [← himgA₀]; exact mem_image_of_mem _ hm₀W
  have hσmem : B m₁ ∈ Ioo 0 s := by rw [← himgB₁]; exact mem_image_of_mem _ hm₁W
  -- Key monotone-correspondence facts.
  have K₀ := mono_key_le A B hW₀A mono₀ hm₀W
  have K₁ := mono_key_ge A B hW₁A mono₁ hm₁W
  -- Real versions of the split data.
  have hρ'0 : (0:ℝ) < ((A m₀ : NNReal) : ℝ) := by exact_mod_cast hρmem.1
  have hρ'4 : ((A m₀ : NNReal) : ℝ) < 1 / 4 := by exact_mod_cast hρmem.2.trans hr4
  have hν'3 : (3 / 4:ℝ) < ((ν : NNReal) : ℝ) := by exact_mod_cast h34ν
  have hν'1 : ((ν : NNReal) : ℝ) < 1 := by exact_mod_cast hν2
  have hσ'0 : (0:ℝ) < ((B m₁ : NNReal) : ℝ) := by exact_mod_cast hσmem.1
  have hσ'4 : ((B m₁ : NNReal) : ℝ) < 1 / 4 := by exact_mod_cast hσmem.2.trans hs4
  have hμ'3 : (3 / 4:ℝ) < ((μ : NNReal) : ℝ) := by exact_mod_cast h34μ
  have hμ'1 : ((μ : NNReal) : ℝ) < 1 := by exact_mod_cast hμ2
  obtain ⟨kα, kg, g0, hkα0, hkα1, hkg0, hkg1, hid1, hid2, hcg0, hg0d, h1c, hg1d⟩ :=
    circle_params hρ'0 hρ'4 hν'3 hν'1 hσ'0 hσ'4 hμ'3 hμ'1
  -- Derived real facts.
  have hc₁0 : (0:ℝ) < kα * ((A m₀ : NNReal) : ℝ) := mul_pos hkα0 hρ'0
  have hd₁kα : kα * ((ν : NNReal) : ℝ) < kα := by
    have hh : kα * ((ν : NNReal) : ℝ) < kα * 1 := mul_lt_mul_of_pos_left hν'1 hkα0
    rwa [mul_one] at hh
  have hd₁1 : kα * ((ν : NNReal) : ℝ) < 1 := hd₁kα.trans hkα1
  have hc₁1 : kα * ((A m₀ : NNReal) : ℝ) < 1 := by linarith
  have hg00 : (0:ℝ) < g0 := lt_trans hc₁0 hcg0
  have hc₁d₁ : kα * ((A m₀ : NNReal) : ℝ) ≤ kα * ((ν : NNReal) : ℝ) := by linarith
  -- The circle charts.
  obtain ⟨eA, heAs, heAt, heAf⟩ := affineNNRealOPH kα 0 hkα0
  obtain ⟨eB, heBs, heBt, heBf⟩ := affineNNRealOPH kg g0 hkg0
  have heAf' : ∀ x : NNReal, eA x = kα * (x:ℝ) + 0 := heAf
  have heBf' : ∀ x : NNReal, eB x = kg * (x:ℝ) + g0 := heBf
  set CA := AddCircle.openPartialHomeomorphCoe (1 : ℝ) (0:ℝ) with hCAdef
  set CB := AddCircle.openPartialHomeomorphCoe (1 : ℝ) (g0 + kg - 1) with hCBdef
  have hCAs : CA.source = Ioo (0:ℝ) (0+1) := rfl
  have hCBs : CB.source = Ioo (g0 + kg - 1) (g0 + kg - 1 + 1) := rfl
  set e := (A.trans eA).trans CA with hedef
  set e' := (B.trans eB).trans CB with he'def
  -- Sources and pointwise formulas.
  have hAeAs : (A.trans eA).source = A.source := by
    rw [OpenPartialHomeomorph.trans_source, heAs]
    refine inter_eq_left.mpr fun x hx => ?_
    rw [mem_preimage, ← hAt]
    exact A.map_source hx
  have hBeBs : (B.trans eB).source = B.source := by
    rw [OpenPartialHomeomorph.trans_source, heBs]
    refine inter_eq_left.mpr fun x hx => ?_
    rw [mem_preimage, ← hBt]
    exact B.map_source hx
  have hAeAval : ∀ x, (A.trans eA) x = kα * ((A x : NNReal):ℝ) + 0 := fun x => by
    rw [OpenPartialHomeomorph.trans_apply, heAf']
  have hBeBval : ∀ x, (B.trans eB) x = kg * ((B x : NNReal):ℝ) + g0 := fun x => by
    rw [OpenPartialHomeomorph.trans_apply, heBf']
  have heval : ∀ x, e x = ((kα * ((A x : NNReal) : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
    intro x
    rw [hedef, OpenPartialHomeomorph.trans_apply, hAeAval, add_zero]
    rfl
  have he'val : ∀ x, e' x = ((kg * ((B x : NNReal) : ℝ) + g0 : ℝ) : AddCircle (1 : ℝ)) := by
    intro x
    rw [he'def, OpenPartialHomeomorph.trans_apply, hBeBval]
    rfl
  have hbounds : ∀ x ∈ A.source,
      0 < kα * ((A x : NNReal):ℝ) ∧ kα * ((A x : NNReal):ℝ) < kα := by
    intro x hx
    have hAx : A x ∈ Ioo (0:NNReal) 1 := hAt ▸ A.map_source hx
    have h0 : (0:ℝ) < ((A x : NNReal):ℝ) := by exact_mod_cast hAx.1
    have h1 : ((A x : NNReal):ℝ) < 1 := by exact_mod_cast hAx.2
    have hh : kα * ((A x : NNReal):ℝ) < kα * 1 := mul_lt_mul_of_pos_left h1 hkα0
    rw [mul_one] at hh
    exact ⟨mul_pos hkα0 h0, hh⟩
  have hb'bounds : ∀ x ∈ B.source,
      g0 < kg * ((B x : NNReal):ℝ) + g0 ∧ kg * ((B x : NNReal):ℝ) + g0 < g0 + kg := by
    intro x hx
    have hBx : B x ∈ Ioo (0:NNReal) 1 := hBt ▸ B.map_source hx
    have h0 : (0:ℝ) < ((B x : NNReal):ℝ) := by exact_mod_cast hBx.1
    have h1 : ((B x : NNReal):ℝ) < 1 := by exact_mod_cast hBx.2
    have hh : kg * ((B x : NNReal):ℝ) < kg * 1 := mul_lt_mul_of_pos_left h1 hkg0
    rw [mul_one] at hh
    exact ⟨by linarith [mul_pos hkg0 h0], by linarith⟩
  have hes : e.source = A.source := by
    rw [hedef, OpenPartialHomeomorph.trans_source, hAeAs]
    refine inter_eq_left.mpr fun x hx => ?_
    rw [mem_preimage, hAeAval, hCAs]
    obtain ⟨hb0, hb1⟩ := hbounds x hx
    exact ⟨by linarith, by linarith⟩
  have he's : e'.source = B.source := by
    rw [he'def, OpenPartialHomeomorph.trans_source, hBeBs]
    refine inter_eq_left.mpr fun x hx => ?_
    rw [mem_preimage, hBeBval, hCBs]
    obtain ⟨hb0, hb1⟩ := hb'bounds x hx
    exact ⟨by linarith, by linarith⟩
  -- Targets.
  have htargetE : e.target = ((↑) : ℝ → AddCircle (1 : ℝ)) '' (Ioo 0 kα) := by
    have hgen := affine_circle_target A hAt e hes hkα0
      (fun x _ => by rw [heval x, add_zero])
    rw [hgen, zero_add]
  have htargetE' : e'.target = ((↑) : ℝ → AddCircle (1 : ℝ)) '' (Ioo g0 (g0 + kg)) :=
    affine_circle_target B hBt e' he's hkg0 (fun x _ => he'val x)
  -- The gluing sets.
  set sset := A.source ∩ A ⁻¹' (Icc (A m₀) ν) with hssetdef
  set tset := ((↑) : ℝ → AddCircle (1 : ℝ)) ''
    (Icc (kα * ((A m₀ : NNReal):ℝ)) (kα * ((ν : NNReal):ℝ))) with htsetdef
  have hssub : sset ⊆ A.source := by rw [hssetdef]; exact inter_subset_left
  -- `e` maps `sset` to `tset`.
  have H : e.IsImage sset tset :=
    circle_coordinate_H A ν m₀ kα hkα0 hkα1 hc₁0 hd₁kα e heval hbounds hes sset hssetdef tset
        htsetdef
  -- Windows: membership of a point of the `e'`-arc in `tset`.
  have claim1 : ∀ v : ℝ, v ∈ Ioo g0 (g0 + kg) →
      (((v : ℝ) : AddCircle (1 : ℝ)) ∈ tset ↔
        v ∈ Icc (kα * ((A m₀ : NNReal):ℝ)) (kα * ((ν : NNReal):ℝ)) ∨
        v ∈ Icc (1 + kα * ((A m₀ : NNReal):ℝ)) (1 + kα * ((ν : NNReal):ℝ))) :=
    circle_coordinate_claim1 A ν m₀ kα kg g0 hkα1 hkg1 hg0d h1c hc₁0 hd₁kα tset htsetdef
  -- Translation of the window membership into `B`-coordinate inequalities.
  have claim2 : ∀ y ∈ B.source,
      ((kg * ((B y : NNReal):ℝ) + g0 ∈
          Icc (kα * ((A m₀ : NNReal):ℝ)) (kα * ((ν : NNReal):ℝ)) ∨
        kg * ((B y : NNReal):ℝ) + g0 ∈
          Icc (1 + kα * ((A m₀ : NNReal):ℝ)) (1 + kα * ((ν : NNReal):ℝ)))
        ↔ (B y ≤ B m₁ ∨ B m₀ ≤ B y)) :=
    circle_coordinate_claim2 A B ν m₁ μ m₀ hm₀μ kα kg g0 hkg0 hkg1 hid1 hid2 hg0d h1c hb'bounds
  -- The `B`-coordinate inequalities describe exactly `sset`.
  have claim3 : ∀ y ∈ B.source, ((B y ≤ B m₁ ∨ B m₀ ≤ B y) ↔ y ∈ sset) :=
    circle_overlap_membership A B W₀ W₁ r p s q hBt hunion himgA₀ himgA₁ himgB₀ himgB₁
      hrp hsq hW₀A hW₀B hW₁A hW₁B ν hpν m₁ hm₁ν μ hqμ m₀ hm₀μ hρmem hσmem K₀ K₁ sset hssetdef
  -- `e'` also maps `sset` to `tset`.
  have H' : e'.IsImage sset tset := by
    intro y hy
    rw [he's] at hy
    rw [he'val y]
    obtain ⟨hb0, hb1⟩ := hb'bounds y hy
    rw [claim1 _ ⟨hb0, hb1⟩, claim2 y hy]
    exact claim3 y hy
  -- The frontier of the closed arc consists of at most the two endpoint classes.
  have hfrontier : frontier tset ⊆
      {((kα * ((A m₀ : NNReal):ℝ) : ℝ) : AddCircle (1 : ℝ)),
       ((kα * ((ν : NNReal):ℝ) : ℝ) : AddCircle (1 : ℝ))} := by
    rw [htsetdef]
    exact addCircle_frontier_arc_subset hc₁d₁
  exact glue_circle_arcs A B W₀ W₁ r p hAt himgA₀ himgA₁ hW₀A hW₀B hW₁A hW₁B ν hpν m₁ hm₁ν μ m₀
      hm₀μ hm₀A hm₀B hm₁A hm₁B hρmem kα kg g0 hkα1 hkg1 hid1 hid2 hcg0 hg0d h1c hc₁0 hd₁kα hc₁1
      hc₁d₁ e e' heval he'val hes he's htargetE htargetE' sset tset hssub H claim1 H' hfrontier
      hssetdef htsetdef

/-- **The circle chart.** Two O-charts with `Overlap` and a disconnected overlap glue to
a chart of `M` onto the whole of `AddCircle 1`. -/
theorem exists_circle_chart {M : Type*} [TopologicalSpace M] [T2Space M]
    (a b : OChart M) (h : Overlap a.source b.source)
    (hdisc : ¬ IsConnected (a.source ∩ b.source)) :
    ∃ f : OpenPartialHomeomorph M (AddCircle (1 : ℝ)),
      f.source = a.source ∪ b.source ∧ f.target = univ := by
  obtain ⟨A, B, W₀, W₁, r, p, s, q, hAs, hBs, hAt, hBt, hunion,
    himgA₀, himgA₁, himgB₀, himgB₁, hr0, hrp, hp1, hr4, hs0, hsq, hq1, hs4⟩ :=
    exists_normalized_charts a b h hdisc
  obtain ⟨f, hfs, hft⟩ := circle_chart_of_normalized A B W₀ W₁ r p s q hAt hBt hunion
    himgA₀ himgA₁ himgB₀ himgB₁ hr0 hrp hp1 hr4 hs0 hsq hq1 hs4
  exact ⟨f, by rw [hfs, hAs, hBs], hft⟩

end OneMfld
