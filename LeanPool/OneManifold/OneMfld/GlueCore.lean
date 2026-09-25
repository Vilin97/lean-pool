/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.Outer
public import LeanPool.OneManifold.OneMfld.TransitionMono


/-! # Core lemmas for gluing overlapping charts

Two results feed the gluing construction:

* **Connectivity**: if `U` is a boundary chart (target `Iio v`), its overlap with any
  other chart is connected — every component's `U`-image is an upper end-segment
  `Ioo q v` (outer-overlap lemma), and two upper end-segments always intersect.

* **End-matching**: the transition map on the overlap is strictly monotone in the
  direction forced by which ends of the two chart images are *interior* (the endpoint
  belongs to the chart target). If both interior ends were paired with each other, the
  overlap would accumulate at two distinct points of `M` at once, contradicting `T2`.
-/

@[expose] public section

open Set Filter Topology

/-- A strictly antitone map of `Ioo p v` onto `Ioo q w` tends to `q` at the top end. -/
theorem tendsto_top_of_strictAntiOn_image {p v q w : NNReal} (hpv : p < v)
    {f : NNReal → NNReal} (hm : StrictAntiOn f (Ioo p v))
    (himg : f '' Ioo p v = Ioo q w) :
    Tendsto f (𝓝[<] v) (𝓝 q) := by
  have hne : (Ioo p v).Nonempty := nonempty_Ioo.2 hpv
  have hqw : q < w := nonempty_Ioo.1 (himg ▸ hne.image f)
  have hbdd : BddBelow (f '' Ioo p v) := himg ▸ bddBelow_Ioo
  have h := AntitoneOn.tendsto_nhdsWithin_Ioo_left hne hm.antitoneOn hbdd
  rwa [himg, csInf_Ioo hqw] at h

variable {M : Type*} [TopologicalSpace M]

/-- The overlap of a boundary chart `U` (target `Iio v`) with any other chart is
connected: every component's `U`-image is an upper end-segment of `Iio v`, and two upper
end-segments intersect, so there is only one component. -/
theorem overlap_connected [T2Space M]
    (U V : OpenPartialHomeomorph M NNReal) {v : NNReal}
    (hUt : U.target = Iio v)
    (hV : IsConnected V.source)
    (hUV : (U.source \ V.source).Nonempty)
    (hVU : (V.source \ U.source).Nonempty)
    (hne : (U.source ∩ V.source).Nonempty) :
    IsConnected (U.source ∩ V.source) := by
  set S := U.source ∩ V.source with hSdef
  obtain ⟨x, hx⟩ := hne
  have hSU : S ⊆ U.source := inter_subset_left
  have hkey : S = connectedComponentIn S x := by
    apply subset_antisymm _ (connectedComponentIn_subset S x)
    intro y hy
    obtain ⟨qx, hqx, hix⟩ := overlap_component_outer_Iio U V hUt hV hUV hVU hx
    obtain ⟨qy, hqy, hiy⟩ := overlap_component_outer_Iio U V hUt hV hUV hVU hy
    obtain ⟨z, hz1, hz2⟩ := exists_between (max_lt hqx hqy)
    have hzx : z ∈ U '' connectedComponentIn S x :=
      hix ▸ mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_left _ _) hz1, hz2⟩
    have hzy : z ∈ U '' connectedComponentIn S y :=
      hiy ▸ mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_right _ _) hz1, hz2⟩
    obtain ⟨w1, hw1, hw1z⟩ := hzx
    obtain ⟨w2, hw2, hw2z⟩ := hzy
    have hw12 : w1 = w2 :=
      U.injOn (hSU (connectedComponentIn_subset _ _ hw1))
        (hSU (connectedComponentIn_subset _ _ hw2)) (hw1z.trans hw2z.symm)
    have h1 : connectedComponentIn S x = connectedComponentIn S w1 :=
      connectedComponentIn_eq hw1
    have h2 : connectedComponentIn S y = connectedComponentIn S w2 :=
      connectedComponentIn_eq hw2
    rw [h1, hw12, ← h2]
    exact mem_connectedComponentIn hy
  rw [hkey]
  exact isConnected_connectedComponentIn_iff.mpr hx

/-- **End-matching, increasing case.** Suppose the overlap `S = a.source ∩ b.source` has
image `Ioo p r` in chart `a` and `Ioo q w` in chart `b`, where the `r`-end is interior to
`a.target` and the `q`-end is interior to `b.target`. Then the transition is increasing:
`a x < a y → b x < b y` on `S`. (If it were decreasing, the overlap would accumulate at
both `a.symm r` and `b.symm q` along the same filter, forcing them equal — but then that
point would lie in `S`, putting `r` in `Ioo p r`.) -/
theorem overlap_mono [T2Space M] (a b : OpenPartialHomeomorph M NNReal)
    {p r q w : NNReal}
    (ha : a '' (a.source ∩ b.source) = Ioo p r)
    (hb : b '' (a.source ∩ b.source) = Ioo q w)
    (hr : r ∈ a.target) (hq : q ∈ b.target) :
    ∀ x ∈ a.source ∩ b.source, ∀ y ∈ a.source ∩ b.source,
      a x < a y → b x < b y := by
  set S := a.source ∩ b.source with hSdef
  have hSa : S ⊆ a.source := inter_subset_left
  have hSb : S ⊆ b.source := inter_subset_right
  have hacoord : ∀ x ∈ S, a x ∈ Ioo p r := fun x hx => ha ▸ mem_image_of_mem a hx
  by_cases hpr : p < r
  swap
  · intro x hx y hy hxy
    exact absurd ((hacoord x hx).1.trans (hacoord x hx).2) hpr
  set τ : NNReal → NNReal := fun t => b (a.symm t) with hτdef
  have hsymm : ∀ t ∈ Ioo p r, a.symm t ∈ S ∧ a (a.symm t) = t := by
    intro t ht
    rw [← ha] at ht
    obtain ⟨x, hxS, rfl⟩ := ht
    rw [a.left_inv (hSa hxS)]
    exact ⟨hxS, rfl⟩
  have hkey : ∀ x ∈ S, τ (a x) = b x := by
    intro x hx
    simp only [hτdef]
    rw [a.left_inv (hSa hx)]
  have hτmaps : ∀ t ∈ Ioo p r, τ t ∈ Ioo q w := by
    intro t ht
    have hb' : b (a.symm t) ∈ b '' S := mem_image_of_mem b (hsymm t ht).1
    exact hb ▸ hb'
  have hIoo_target : Ioo p r ⊆ a.target := by
    rw [← ha]
    rintro y ⟨z, hz, rfl⟩
    exact a.map_source (hSa hz)
  have hqw_target : Ioo q w ⊆ b.target := by
    rw [← hb]
    rintro y ⟨z, hz, rfl⟩
    exact b.map_source (hSb hz)
  have hcont : ContinuousOn τ (Ioo p r) :=
    b.continuousOn.comp (a.symm.continuousOn.mono hIoo_target)
      (fun t ht => hSb (hsymm t ht).1)
  have hinj : InjOn τ (Ioo p r) := by
    intro t1 ht1 t2 ht2 heq
    obtain ⟨h1S, h1e⟩ := hsymm t1 ht1
    obtain ⟨h2S, h2e⟩ := hsymm t2 ht2
    have h12 : a.symm t1 = a.symm t2 := b.injOn (hSb h1S) (hSb h2S) heq
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
        obtain ⟨x, hxS, rfl⟩ := hy
        exact ⟨a x, hacoord x hxS, hkey x hxS⟩
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
      exact b.left_inv (hSb (hsymm t ht).1)
    have hz : a.symm r = b.symm q := tendsto_nhds_unique' hFne hlim1 hlim2'
    have hzS : a.symm r ∈ S := by
      refine ⟨a.map_target hr, ?_⟩
      rw [hz]
      exact b.map_target hq
    have hr' : a (a.symm r) ∈ Ioo p r := hacoord _ hzS
    rw [a.right_inv hr] at hr'
    exact lt_irrefl r hr'.2

/-- **End-matching, decreasing case.** Same setting, but now the `p`-end is interior to
`a.target` (and the `q`-end interior to `b.target`): the transition is decreasing. -/
theorem overlap_anti [T2Space M] (a b : OpenPartialHomeomorph M NNReal)
    {p r q w : NNReal}
    (ha : a '' (a.source ∩ b.source) = Ioo p r)
    (hb : b '' (a.source ∩ b.source) = Ioo q w)
    (hp : p ∈ a.target) (hq : q ∈ b.target) :
    ∀ x ∈ a.source ∩ b.source, ∀ y ∈ a.source ∩ b.source,
      a x < a y → b y < b x := by
  set S := a.source ∩ b.source with hSdef
  have hSa : S ⊆ a.source := inter_subset_left
  have hSb : S ⊆ b.source := inter_subset_right
  have hacoord : ∀ x ∈ S, a x ∈ Ioo p r := fun x hx => ha ▸ mem_image_of_mem a hx
  by_cases hpr : p < r
  swap
  · intro x hx y hy hxy
    exact absurd ((hacoord x hx).1.trans (hacoord x hx).2) hpr
  set τ : NNReal → NNReal := fun t => b (a.symm t) with hτdef
  have hsymm : ∀ t ∈ Ioo p r, a.symm t ∈ S ∧ a (a.symm t) = t := by
    intro t ht
    rw [← ha] at ht
    obtain ⟨x, hxS, rfl⟩ := ht
    rw [a.left_inv (hSa hxS)]
    exact ⟨hxS, rfl⟩
  have hkey : ∀ x ∈ S, τ (a x) = b x := by
    intro x hx
    simp only [hτdef]
    rw [a.left_inv (hSa hx)]
  have hτmaps : ∀ t ∈ Ioo p r, τ t ∈ Ioo q w := by
    intro t ht
    have hb' : b (a.symm t) ∈ b '' S := mem_image_of_mem b (hsymm t ht).1
    exact hb ▸ hb'
  have hIoo_target : Ioo p r ⊆ a.target := by
    rw [← ha]
    rintro y ⟨z, hz, rfl⟩
    exact a.map_source (hSa hz)
  have hqw_target : Ioo q w ⊆ b.target := by
    rw [← hb]
    rintro y ⟨z, hz, rfl⟩
    exact b.map_source (hSb hz)
  have hcont : ContinuousOn τ (Ioo p r) :=
    b.continuousOn.comp (a.symm.continuousOn.mono hIoo_target)
      (fun t ht => hSb (hsymm t ht).1)
  have hinj : InjOn τ (Ioo p r) := by
    intro t1 ht1 t2 ht2 heq
    obtain ⟨h1S, h1e⟩ := hsymm t1 ht1
    obtain ⟨h2S, h2e⟩ := hsymm t2 ht2
    have h12 : a.symm t1 = a.symm t2 := b.injOn (hSb h1S) (hSb h2S) heq
    rw [← h1e, ← h2e, h12]
  rcases strictMonoOn_or_strictAntiOn_of_injOn_Ioo hcont hinj with hmono | hanti
  · exfalso
    have himg : τ '' Ioo p r = Ioo q w := by
      apply subset_antisymm
      · rintro _ ⟨t, ht, rfl⟩
        exact hτmaps t ht
      · intro y hy
        rw [← hb] at hy
        obtain ⟨x, hxS, rfl⟩ := hy
        exact ⟨a x, hacoord x hxS, hkey x hxS⟩
    have hτlim : Tendsto τ (𝓝[>] p) (𝓝 q) :=
      tendsto_bot_of_strictMonoOn_image hpr hmono himg
    have hF : 𝓝[Ioo p r] p = 𝓝[>] p := nhdsWithin_Ioo_eq_nhdsGT hpr
    have hFne : (𝓝[Ioo p r] p).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      rw [closure_Ioo hpr.ne]
      exact ⟨le_refl p, hpr.le⟩
    have hlim1 : Tendsto a.symm (𝓝[Ioo p r] p) (𝓝 (a.symm p)) :=
      (a.symm.continuousOn p hp).mono hIoo_target
    have hτq : Tendsto τ (𝓝[Ioo p r] p) (𝓝 q) := hF ▸ hτlim
    have hτq' : Tendsto τ (𝓝[Ioo p r] p) (𝓝[b.target] q) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hτq, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hqw_target (hτmaps t ht)
    have hlim2 : Tendsto (b.symm ∘ τ) (𝓝[Ioo p r] p) (𝓝 (b.symm q)) :=
      Tendsto.comp (b.symm.continuousOn q hq) hτq'
    have hlim2' : Tendsto a.symm (𝓝[Ioo p r] p) (𝓝 (b.symm q)) := by
      apply Tendsto.congr' _ hlim2
      filter_upwards [self_mem_nhdsWithin] with t ht
      change b.symm (τ t) = a.symm t
      simp only [hτdef]
      exact b.left_inv (hSb (hsymm t ht).1)
    have hz : a.symm p = b.symm q := tendsto_nhds_unique' hFne hlim1 hlim2'
    have hzS : a.symm p ∈ S := by
      refine ⟨a.map_target hp, ?_⟩
      rw [hz]
      exact b.map_target hq
    have hp' : a (a.symm p) ∈ Ioo p r := hacoord _ hzS
    rw [a.right_inv hp] at hp'
    exact lt_irrefl p hp'.1
  · intro x hx y hy hxy
    have h := hanti (hacoord x hx) (hacoord y hy) hxy
    rwa [hkey x hx, hkey y hy] at h
