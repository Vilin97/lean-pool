/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.Outer
public import LeanPool.OneManifold.OneMfld.TransitionMono
public import LeanPool.OneManifold.OneMfld.GlueCore


/-! # The two-component structure of a disconnected overlap

When two interior charts overlap disconnectedly, the overlap has exactly two connected
components, one at each end of each chart (outer-overlap lemma + two end-segments at the
same end must intersect). We also generalize the end-matching theorems of `GlueCore` from
the full overlap to a single component `W`: the extra hypothesis is that the relevant
interior endpoint is not in the image of the *full* overlap.
-/

@[expose] public section

namespace OneMfld

open Set Filter Topology

/-- A strictly antitone map of `Ioo p v` onto `Ioo q w` tends to `w` at the bottom end. -/
theorem tendsto_bot_of_strictAntiOn_image {p v q w : NNReal} (hpv : p < v)
    {f : NNReal → NNReal} (hm : StrictAntiOn f (Ioo p v))
    (himg : f '' Ioo p v = Ioo q w) :
    Tendsto f (𝓝[>] p) (𝓝 w) := by
  have hne : (Ioo p v).Nonempty := nonempty_Ioo.2 hpv
  have hqw : q < w := nonempty_Ioo.1 (himg ▸ hne.image f)
  have hbdd : BddAbove (f '' Ioo p v) := himg ▸ bddAbove_Ioo
  have h := AntitoneOn.tendsto_nhdsWithin_Ioo_right hne hm.antitoneOn hbdd
  rwa [himg, csSup_Ioo hqw] at h

variable {M : Type*} [TopologicalSpace M]

/-- Component version of `overlap_mono`: on a subset `W` of the overlap whose images are
`Ioo p r` and `Ioo q w`, with the `r`-end interior to `a.target`, the `q`-end interior to
`b.target`, and `r` not in the image of the full overlap, the transition is increasing. -/
theorem overlap_mono_on [T2Space M] (a b : OpenPartialHomeomorph M NNReal)
    {W : Set M} (hW : W ⊆ a.source ∩ b.source)
    {p r q w : NNReal}
    (ha : a '' W = Ioo p r)
    (hb : b '' W = Ioo q w)
    (hr : r ∈ a.target) (hq : q ∈ b.target)
    (hrS : r ∉ a '' (a.source ∩ b.source)) :
    ∀ x ∈ W, ∀ y ∈ W, a x < a y → b x < b y := by
  have hWa : W ⊆ a.source := hW.trans inter_subset_left
  have hWb : W ⊆ b.source := hW.trans inter_subset_right
  have hacoord : ∀ x ∈ W, a x ∈ Ioo p r := fun x hx => ha ▸ mem_image_of_mem a hx
  by_cases hpr : p < r
  swap
  · intro x hx y hy hxy
    exact absurd ((hacoord x hx).1.trans (hacoord x hx).2) hpr
  set τ : NNReal → NNReal := fun t => b (a.symm t) with hτdef
  have hsymm : ∀ t ∈ Ioo p r, a.symm t ∈ W ∧ a (a.symm t) = t := by
    intro t ht
    rw [← ha] at ht
    obtain ⟨x, hxW, rfl⟩ := ht
    rw [a.left_inv (hWa hxW)]
    exact ⟨hxW, rfl⟩
  have hkey : ∀ x ∈ W, τ (a x) = b x := by
    intro x hx
    simp only [hτdef]
    rw [a.left_inv (hWa hx)]
  have hτmaps : ∀ t ∈ Ioo p r, τ t ∈ Ioo q w := by
    intro t ht
    have hb' : b (a.symm t) ∈ b '' W := mem_image_of_mem b (hsymm t ht).1
    exact hb ▸ hb'
  have hIoo_target : Ioo p r ⊆ a.target := by
    rw [← ha]
    rintro y ⟨z, hz, rfl⟩
    exact a.map_source (hWa hz)
  have hqw_target : Ioo q w ⊆ b.target := by
    rw [← hb]
    rintro y ⟨z, hz, rfl⟩
    exact b.map_source (hWb hz)
  have hcont : ContinuousOn τ (Ioo p r) :=
    b.continuousOn.comp (a.symm.continuousOn.mono hIoo_target)
      (fun t ht => hWb (hsymm t ht).1)
  have hinj : InjOn τ (Ioo p r) := by
    intro t1 ht1 t2 ht2 heq
    obtain ⟨h1W, h1e⟩ := hsymm t1 ht1
    obtain ⟨h2W, h2e⟩ := hsymm t2 ht2
    have h12 : a.symm t1 = a.symm t2 := b.injOn (hWb h1W) (hWb h2W) heq
    rw [← h1e, ← h2e, h12]
  rcases strictMonoOn_or_strictAntiOn_of_injOn_Ioo hcont hinj with hmono | hanti
  · intro x hx y hy hxy
    have h := hmono (hacoord x hx) (hacoord y hy) hxy
    rwa [hkey x hx, hkey y hy] at h
  · exfalso
    have himg : τ '' Ioo p r = Ioo q w := by
      apply subset_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        exact hτmaps t ht
      · intro y hy
        rw [← hb] at hy
        obtain ⟨x, hxW, rfl⟩ := hy
        exact ⟨a x, hacoord x hxW, hkey x hxW⟩
    have hτlim : Tendsto τ (𝓝[<] r) (𝓝 q) :=
      tendsto_top_of_strictAntiOn_image hpr hanti himg
    have hF : 𝓝[Ioo p r] r = 𝓝[<] r := nhdsWithin_Ioo_eq_nhdsLT hpr
    have hFne : (𝓝[Ioo p r] r).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      rw [closure_Ioo hpr.ne]
      exact ⟨hpr.le, le_refl r⟩
    have hlim1 : Tendsto a.symm (𝓝[Ioo p r] r) (𝓝 (a.symm r)) :=
      (a.symm.continuousOn r hr).mono hIoo_target
    have hτq : Tendsto τ (𝓝[Ioo p r] r) (𝓝 q) := hF ▸ hτlim
    have hτq' : Tendsto τ (𝓝[Ioo p r] r) (𝓝[b.target] q) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hτq, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hqw_target (hτmaps t ht)
    have hlim2 : Tendsto (b.symm ∘ τ) (𝓝[Ioo p r] r) (𝓝 (b.symm q)) :=
      Tendsto.comp (b.symm.continuousOn q hq) hτq'
    have hlim2' : Tendsto a.symm (𝓝[Ioo p r] r) (𝓝 (b.symm q)) := by
      apply Tendsto.congr' _ hlim2
      filter_upwards [self_mem_nhdsWithin] with t ht
      change b.symm (τ t) = a.symm t
      simp only [hτdef]
      exact b.left_inv (hWb (hsymm t ht).1)
    have hz : a.symm r = b.symm q := tendsto_nhds_unique' hFne hlim1 hlim2'
    have hzS : a.symm r ∈ a.source ∩ b.source := by
      refine ⟨a.map_target hr, ?_⟩
      rw [hz]
      exact b.map_target hq
    exact hrS ⟨a.symm r, hzS, a.right_inv hr⟩

/-- Mirror component version: with the `p`-end interior to `a.target`, the `w`-end
interior to `b.target`, and `p` not in the image of the full overlap, the transition is
again increasing. -/
theorem overlap_mono_on' [T2Space M] (a b : OpenPartialHomeomorph M NNReal)
    {W : Set M} (hW : W ⊆ a.source ∩ b.source)
    {p r q w : NNReal}
    (ha : a '' W = Ioo p r)
    (hb : b '' W = Ioo q w)
    (hp : p ∈ a.target) (hw : w ∈ b.target)
    (hpS : p ∉ a '' (a.source ∩ b.source)) :
    ∀ x ∈ W, ∀ y ∈ W, a x < a y → b x < b y := by
  have hWa : W ⊆ a.source := hW.trans inter_subset_left
  have hWb : W ⊆ b.source := hW.trans inter_subset_right
  have hacoord : ∀ x ∈ W, a x ∈ Ioo p r := fun x hx => ha ▸ mem_image_of_mem a hx
  by_cases hpr : p < r
  swap
  · intro x hx y hy hxy
    exact absurd ((hacoord x hx).1.trans (hacoord x hx).2) hpr
  set τ : NNReal → NNReal := fun t => b (a.symm t) with hτdef
  have hsymm : ∀ t ∈ Ioo p r, a.symm t ∈ W ∧ a (a.symm t) = t := by
    intro t ht
    rw [← ha] at ht
    obtain ⟨x, hxW, rfl⟩ := ht
    rw [a.left_inv (hWa hxW)]
    exact ⟨hxW, rfl⟩
  have hkey : ∀ x ∈ W, τ (a x) = b x := by
    intro x hx
    simp only [hτdef]
    rw [a.left_inv (hWa hx)]
  have hτmaps : ∀ t ∈ Ioo p r, τ t ∈ Ioo q w := by
    intro t ht
    have hb' : b (a.symm t) ∈ b '' W := mem_image_of_mem b (hsymm t ht).1
    exact hb ▸ hb'
  have hIoo_target : Ioo p r ⊆ a.target := by
    rw [← ha]
    rintro y ⟨z, hz, rfl⟩
    exact a.map_source (hWa hz)
  have hqw_target : Ioo q w ⊆ b.target := by
    rw [← hb]
    rintro y ⟨z, hz, rfl⟩
    exact b.map_source (hWb hz)
  have hcont : ContinuousOn τ (Ioo p r) :=
    b.continuousOn.comp (a.symm.continuousOn.mono hIoo_target)
      (fun t ht => hWb (hsymm t ht).1)
  have hinj : InjOn τ (Ioo p r) := by
    intro t1 ht1 t2 ht2 heq
    obtain ⟨h1W, h1e⟩ := hsymm t1 ht1
    obtain ⟨h2W, h2e⟩ := hsymm t2 ht2
    have h12 : a.symm t1 = a.symm t2 := b.injOn (hWb h1W) (hWb h2W) heq
    rw [← h1e, ← h2e, h12]
  rcases strictMonoOn_or_strictAntiOn_of_injOn_Ioo hcont hinj with hmono | hanti
  · intro x hx y hy hxy
    have h := hmono (hacoord x hx) (hacoord y hy) hxy
    rwa [hkey x hx, hkey y hy] at h
  · exfalso
    have himg : τ '' Ioo p r = Ioo q w := by
      apply subset_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        exact hτmaps t ht
      · intro y hy
        rw [← hb] at hy
        obtain ⟨x, hxW, rfl⟩ := hy
        exact ⟨a x, hacoord x hxW, hkey x hxW⟩
    have hτlim : Tendsto τ (𝓝[>] p) (𝓝 w) :=
      tendsto_bot_of_strictAntiOn_image hpr hanti himg
    have hF : 𝓝[Ioo p r] p = 𝓝[>] p := nhdsWithin_Ioo_eq_nhdsGT hpr
    have hFne : (𝓝[Ioo p r] p).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      rw [closure_Ioo hpr.ne]
      exact ⟨le_refl p, hpr.le⟩
    have hlim1 : Tendsto a.symm (𝓝[Ioo p r] p) (𝓝 (a.symm p)) :=
      (a.symm.continuousOn p hp).mono hIoo_target
    have hτw : Tendsto τ (𝓝[Ioo p r] p) (𝓝 w) := hF ▸ hτlim
    have hτw' : Tendsto τ (𝓝[Ioo p r] p) (𝓝[b.target] w) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hτw, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hqw_target (hτmaps t ht)
    have hlim2 : Tendsto (b.symm ∘ τ) (𝓝[Ioo p r] p) (𝓝 (b.symm w)) :=
      Tendsto.comp (b.symm.continuousOn w hw) hτw'
    have hlim2' : Tendsto a.symm (𝓝[Ioo p r] p) (𝓝 (b.symm w)) := by
      apply Tendsto.congr' _ hlim2
      filter_upwards [self_mem_nhdsWithin] with t ht
      change b.symm (τ t) = a.symm t
      simp only [hτdef]
      exact b.left_inv (hWb (hsymm t ht).1)
    have hz : a.symm p = b.symm w := tendsto_nhds_unique' hFne hlim1 hlim2'
    have hzS : a.symm p ∈ a.source ∩ b.source := by
      refine ⟨a.map_target hp, ?_⟩
      rw [hz]
      exact b.map_target hw
    exact hpS ⟨a.symm p, hzS, a.right_inv hp⟩

/-- **Two-component structure.** A disconnected overlap of a chart with target `Ioo 0 1`
and a connected-source chart has exactly two components: one whose image is a lower
end-segment `Ioo 0 r` and one whose image is an upper end-segment `Ioo p 1`, with
`r ≤ p`. -/
theorem two_components_structure [T2Space M] (a b : OpenPartialHomeomorph M NNReal)
    (hat : a.target = Ioo 0 1)
    (hb : IsConnected b.source)
    (_hab : (a.source \ b.source).Nonempty)
    (hba : (b.source \ a.source).Nonempty)
    (hne : (a.source ∩ b.source).Nonempty)
    (hdisc : ¬ IsConnected (a.source ∩ b.source)) :
    ∃ (W₀ W₁ : Set M) (r p : NNReal),
      a.source ∩ b.source = W₀ ∪ W₁ ∧
      (∀ z ∈ W₀, connectedComponentIn (a.source ∩ b.source) z = W₀) ∧
      (∀ z ∈ W₁, connectedComponentIn (a.source ∩ b.source) z = W₁) ∧
      Disjoint W₀ W₁ ∧
      a '' W₀ = Ioo 0 r ∧ a '' W₁ = Ioo p 1 ∧
      0 < r ∧ r ≤ p ∧ p < 1 := by
  set S := a.source ∩ b.source with hSdef
  have hSa : S ⊆ a.source := inter_subset_left
  have outer : ∀ x ∈ S,
      (∃ p, 0 ≤ p ∧ p < 1 ∧ a '' connectedComponentIn S x = Ioo p 1) ∨
      (∃ q, 0 < q ∧ q ≤ 1 ∧ a '' connectedComponentIn S x = Ioo 0 q) :=
    fun x hx => overlap_component_outer_Ioo a b hat hb hba hx
  -- Two components whose images are both lower end-segments coincide.
  have hlow : ∀ x y : M, ∀ r r' : NNReal, 0 < r → 0 < r' →
      a '' connectedComponentIn S x = Ioo 0 r →
      a '' connectedComponentIn S y = Ioo 0 r' →
      connectedComponentIn S x = connectedComponentIn S y := by
    intro x y r r' hr hr' hix hiy
    obtain ⟨z, hz1, hz2⟩ := exists_between (lt_min hr hr')
    have hzx : z ∈ a '' connectedComponentIn S x :=
      hix ▸ mem_Ioo.mpr ⟨hz1, hz2.trans_le (min_le_left _ _)⟩
    have hzy : z ∈ a '' connectedComponentIn S y :=
      hiy ▸ mem_Ioo.mpr ⟨hz1, hz2.trans_le (min_le_right _ _)⟩
    obtain ⟨w1, hw1, hw1z⟩ := hzx
    obtain ⟨w2, hw2, hw2z⟩ := hzy
    have hw12 : w1 = w2 :=
      a.injOn (hSa (connectedComponentIn_subset _ _ hw1))
        (hSa (connectedComponentIn_subset _ _ hw2)) (hw1z.trans hw2z.symm)
    calc connectedComponentIn S x
        = connectedComponentIn S w1 := connectedComponentIn_eq hw1
      _ = connectedComponentIn S w2 := by rw [hw12]
      _ = connectedComponentIn S y := (connectedComponentIn_eq hw2).symm
  -- Two components whose images are both upper end-segments coincide.
  have hup : ∀ x y : M, ∀ p p' : NNReal, p < 1 → p' < 1 →
      a '' connectedComponentIn S x = Ioo p 1 →
      a '' connectedComponentIn S y = Ioo p' 1 →
      connectedComponentIn S x = connectedComponentIn S y := by
    intro x y p p' hp hp' hix hiy
    obtain ⟨z, hz1, hz2⟩ := exists_between (max_lt hp hp')
    have hzx : z ∈ a '' connectedComponentIn S x :=
      hix ▸ mem_Ioo.mpr ⟨(le_max_left _ _).trans_lt hz1, hz2⟩
    have hzy : z ∈ a '' connectedComponentIn S y :=
      hiy ▸ mem_Ioo.mpr ⟨(le_max_right _ _).trans_lt hz1, hz2⟩
    obtain ⟨w1, hw1, hw1z⟩ := hzx
    obtain ⟨w2, hw2, hw2z⟩ := hzy
    have hw12 : w1 = w2 :=
      a.injOn (hSa (connectedComponentIn_subset _ _ hw1))
        (hSa (connectedComponentIn_subset _ _ hw2)) (hw1z.trans hw2z.symm)
    calc connectedComponentIn S x
        = connectedComponentIn S w1 := connectedComponentIn_eq hw1
      _ = connectedComponentIn S w2 := by rw [hw12]
      _ = connectedComponentIn S y := (connectedComponentIn_eq hw2).symm
  -- Main construction from one lower-imaged and one upper-imaged (distinct) component.
  have main : ∀ x' y' : M, ∀ r p : NNReal, 0 < r → p < 1 →
      a '' connectedComponentIn S x' = Ioo 0 r →
      a '' connectedComponentIn S y' = Ioo p 1 →
      connectedComponentIn S x' ≠ connectedComponentIn S y' →
      ∃ (W₀ W₁ : Set M) (r' p' : NNReal),
        S = W₀ ∪ W₁ ∧
        (∀ z ∈ W₀, connectedComponentIn S z = W₀) ∧
        (∀ z ∈ W₁, connectedComponentIn S z = W₁) ∧
        Disjoint W₀ W₁ ∧
        a '' W₀ = Ioo 0 r' ∧ a '' W₁ = Ioo p' 1 ∧
        0 < r' ∧ r' ≤ p' ∧ p' < 1 := by
    intro x' y' r p hr0 hp1 hxi hyi hne'
    have hcomp₀ : ∀ z ∈ connectedComponentIn S x',
        connectedComponentIn S z = connectedComponentIn S x' :=
      fun z hz => (connectedComponentIn_eq hz).symm
    have hcomp₁ : ∀ z ∈ connectedComponentIn S y',
        connectedComponentIn S z = connectedComponentIn S y' :=
      fun z hz => (connectedComponentIn_eq hz).symm
    have hdisj : Disjoint (connectedComponentIn S x') (connectedComponentIn S y') := by
      rw [Set.disjoint_left]
      intro z hz₀ hz₁
      exact hne' ((hcomp₀ z hz₀).symm.trans (hcomp₁ z hz₁))
    have hunion : S = connectedComponentIn S x' ∪ connectedComponentIn S y' := by
      apply subset_antisymm
      · intro z hz
        rcases outer z hz with ⟨p'', _, hp''1, hpi''⟩ | ⟨r'', hr''0, _, hri''⟩
        · right
          rw [← hup z y' p'' p hp''1 hp1 hpi'' hyi]
          exact mem_connectedComponentIn hz
        · left
          rw [← hlow z x' r'' r hr''0 hr0 hri'' hxi]
          exact mem_connectedComponentIn hz
      · exact union_subset (connectedComponentIn_subset _ _)
          (connectedComponentIn_subset _ _)
    have hrp : r ≤ p := by
      by_contra h
      rw [not_le] at h
      obtain ⟨t, ht1, ht2⟩ := exists_between (lt_min h hp1)
      have htW₀ : t ∈ a '' connectedComponentIn S x' :=
        hxi ▸ mem_Ioo.mpr ⟨(zero_le : (0 : NNReal) ≤ p).trans_lt ht1,
          ht2.trans_le (min_le_left _ _)⟩
      have htW₁ : t ∈ a '' connectedComponentIn S y' :=
        hyi ▸ mem_Ioo.mpr ⟨ht1, ht2.trans_le (min_le_right _ _)⟩
      obtain ⟨w1, hw1, hw1t⟩ := htW₀
      obtain ⟨w2, hw2, hw2t⟩ := htW₁
      have hw12 : w1 = w2 :=
        a.injOn (hSa (connectedComponentIn_subset _ _ hw1))
          (hSa (connectedComponentIn_subset _ _ hw2)) (hw1t.trans hw2t.symm)
      have hw2' : w1 ∈ connectedComponentIn S y' := by rw [hw12]; exact hw2
      exact Set.disjoint_left.mp hdisj hw1 hw2'
    exact ⟨connectedComponentIn S x', connectedComponentIn S y', r, p,
      hunion, hcomp₀, hcomp₁, hdisj, hxi, hyi, hr0, hrp, hp1⟩
  -- Produce two distinct components.
  obtain ⟨x₀, hx₀⟩ := hne
  have hSnW : ¬ (S ⊆ connectedComponentIn S x₀) := by
    intro h
    apply hdisc
    have hSW : S = connectedComponentIn S x₀ :=
      subset_antisymm h (connectedComponentIn_subset S x₀)
    rw [hSW]
    exact isConnected_connectedComponentIn_iff.mpr hx₀
  obtain ⟨y₀, hy₀S, hy₀W⟩ := not_subset.mp hSnW
  have hWW' : connectedComponentIn S x₀ ≠ connectedComponentIn S y₀ := by
    intro h
    apply hy₀W
    rw [h]
    exact mem_connectedComponentIn hy₀S
  rcases outer x₀ hx₀ with ⟨p, _, hp1, hpi⟩ | ⟨r, hr0, _, hri⟩ <;>
    rcases outer y₀ hy₀S with ⟨p', _, hp'1, hpi'⟩ | ⟨r', hr'0, _, hri'⟩
  · exact absurd (hup x₀ y₀ p p' hp1 hp'1 hpi hpi') hWW'
  · exact main y₀ x₀ r' p hr'0 hp1 hri' hpi (Ne.symm hWW')
  · exact main x₀ y₀ r p' hr0 hp'1 hri hpi' hWW'
  · exact absurd (hlow x₀ y₀ r r' hr0 hr'0 hri hri') hWW'

/-- The other chart also sees the two components as end-segments, one lower and one
upper (in one of the two possible arrangements). -/
theorem two_components_other_chart [T2Space M] (a b : OpenPartialHomeomorph M NNReal)
    (hbt : b.target = Ioo 0 1)
    (haconn : IsConnected a.source)
    (hab : (a.source \ b.source).Nonempty)
    {W₀ W₁ : Set M}
    (hW₀ : ∀ z ∈ W₀, connectedComponentIn (a.source ∩ b.source) z = W₀)
    (hW₁ : ∀ z ∈ W₁, connectedComponentIn (a.source ∩ b.source) z = W₁)
    (hne₀ : W₀.Nonempty) (hne₁ : W₁.Nonempty) (hd : Disjoint W₀ W₁) :
    ∃ s q : NNReal, 0 < s ∧ s ≤ q ∧ q < 1 ∧
      ((b '' W₀ = Ioo q 1 ∧ b '' W₁ = Ioo 0 s) ∨
       (b '' W₀ = Ioo 0 s ∧ b '' W₁ = Ioo q 1)) := by
  set S := a.source ∩ b.source with hSdef
  -- The components are inside the overlap.
  have hW₀S : W₀ ⊆ S := by
    intro z hz
    by_contra hzS
    have h1 : W₀ = (∅ : Set M) :=
      (hW₀ z hz).symm.trans (connectedComponentIn_eq_empty hzS)
    rw [h1] at hz
    simp at hz
  have hW₁S : W₁ ⊆ S := by
    intro z hz
    by_contra hzS
    have h1 : W₁ = (∅ : Set M) :=
      (hW₁ z hz).symm.trans (connectedComponentIn_eq_empty hzS)
    rw [h1] at hz
    simp at hz
  have hcomm : b.source ∩ a.source = S := by rw [hSdef]; exact inter_comm _ _
  -- The outer-overlap lemma seen from chart `b`.
  have outer : ∀ z ∈ S,
      (∃ q, 0 ≤ q ∧ q < 1 ∧ b '' connectedComponentIn S z = Ioo q 1) ∨
      (∃ s, 0 < s ∧ s ≤ 1 ∧ b '' connectedComponentIn S z = Ioo 0 s) := by
    intro z hz
    have hz' : z ∈ b.source ∩ a.source := ⟨hz.2, hz.1⟩
    have h := overlap_component_outer_Ioo b a hbt haconn hab hz'
    rwa [hcomm] at h
  obtain ⟨z₀, hz₀⟩ := hne₀
  obtain ⟨z₁, hz₁⟩ := hne₁
  have h₀ := outer z₀ (hW₀S hz₀)
  rw [hW₀ z₀ hz₀] at h₀
  have h₁ := outer z₁ (hW₁S hz₁)
  rw [hW₁ z₁ hz₁] at h₁
  -- A common point of the two `b`-images contradicts disjointness.
  have hcommon : ∀ t : NNReal, t ∈ b '' W₀ → t ∈ b '' W₁ → False := by
    intro t ht₀ ht₁
    obtain ⟨w1, hw1, hw1t⟩ := ht₀
    obtain ⟨w2, hw2, hw2t⟩ := ht₁
    have h12 : w1 = w2 :=
      b.injOn ((hW₀S.trans inter_subset_right) hw1)
        ((hW₁S.trans inter_subset_right) hw2) (hw1t.trans hw2t.symm)
    have hw2' : w1 ∈ W₁ := by rw [h12]; exact hw2
    exact Set.disjoint_left.mp hd hw1 hw2'
  rcases h₀ with ⟨q₀, _hq₀0, hq₀1, hbW₀⟩ | ⟨s₀, hs₀0, _hs₀1, hbW₀⟩ <;>
    rcases h₁ with ⟨q₁, _hq₁0, hq₁1, hbW₁⟩ | ⟨s₁, hs₁0, _hs₁1, hbW₁⟩
  · -- both upper: impossible
    exfalso
    obtain ⟨t, ht1, ht2⟩ := exists_between (max_lt hq₀1 hq₁1)
    exact hcommon t (hbW₀ ▸ mem_Ioo.mpr ⟨(le_max_left _ _).trans_lt ht1, ht2⟩)
      (hbW₁ ▸ mem_Ioo.mpr ⟨(le_max_right _ _).trans_lt ht1, ht2⟩)
  · -- `W₀` upper, `W₁` lower
    refine ⟨s₁, q₀, hs₁0, ?_, hq₀1, Or.inl ⟨hbW₀, hbW₁⟩⟩
    by_contra h
    rw [not_le] at h
    obtain ⟨t, ht1, ht2⟩ := exists_between (lt_min h hq₀1)
    exact hcommon t
      (hbW₀ ▸ mem_Ioo.mpr ⟨ht1, ht2.trans_le (min_le_right _ _)⟩)
      (hbW₁ ▸ mem_Ioo.mpr ⟨(zero_le : (0 : NNReal) ≤ q₀).trans_lt ht1,
        ht2.trans_le (min_le_left _ _)⟩)
  · -- `W₀` lower, `W₁` upper
    refine ⟨s₀, q₁, hs₀0, ?_, hq₁1, Or.inr ⟨hbW₀, hbW₁⟩⟩
    by_contra h
    rw [not_le] at h
    obtain ⟨t, ht1, ht2⟩ := exists_between (lt_min h hq₁1)
    exact hcommon t
      (hbW₀ ▸ mem_Ioo.mpr ⟨(zero_le : (0 : NNReal) ≤ q₁).trans_lt ht1,
        ht2.trans_le (min_le_left _ _)⟩)
      (hbW₁ ▸ mem_Ioo.mpr ⟨ht1, ht2.trans_le (min_le_right _ _)⟩)
  · -- both lower: impossible
    exfalso
    obtain ⟨t, ht1, ht2⟩ := exists_between (lt_min hs₀0 hs₁0)
    exact hcommon t (hbW₀ ▸ mem_Ioo.mpr ⟨ht1, ht2.trans_le (min_le_left _ _)⟩)
      (hbW₁ ▸ mem_Ioo.mpr ⟨ht1, ht2.trans_le (min_le_right _ _)⟩)

end OneMfld
