/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.UnitInterval
public import LeanPool.OneManifold.OneMfld.FiniteIntervalCharts
public import LeanPool.OneManifold.OneMfld.IntervalCharts
public import LeanPool.OneManifold.OneMfld.NiceCharts
public import LeanPool.OneManifold.OneMfld.ClosureOverlap
public import LeanPool.OneManifold.OneMfld.RealIntervals
public import LeanPool.OneManifold.OneMfld.PartialHomeomorphHelpers
public import LeanPool.OneManifold.OneMfld.Charts
public import LeanPool.OneManifold.OneMfld.Outer
public import LeanPool.OneManifold.OneMfld.TransitionMono
public import LeanPool.OneManifold.OneMfld.Normalize
public import LeanPool.OneManifold.OneMfld.GlueCore
public import LeanPool.OneManifold.OneMfld.GlueBlocks
public import LeanPool.OneManifold.OneMfld.GlueNNReal
public import LeanPool.OneManifold.OneMfld.GlueUI
public import LeanPool.OneManifold.OneMfld.TwoComponents
public import LeanPool.OneManifold.OneMfld.CircleBlocks
public import LeanPool.OneManifold.OneMfld.CircleGlue


/-!
# ClassifyOverlaps

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

open Set

variable
  {M : Type*}
  [TopologicalSpace M]
  [ConnectedSpace M]
  [T2Space M]

open Classical in
/-- Turn a homeomorphism of open subtypes `A ≃ₜ B` into a partial homeomorphism `X ⇀ Y`.

The `Nonempty` hypotheses are needed, and are not an artefact of the proof: a
`PartialEquiv X Y` carries a *total* `toFun : X → Y`, so `OpenPartialHomeomorph Unit Empty`
is an empty type even though `(∅ : Set Unit) ≃ₜ (∅ : Set Empty)` with both sets open. -/
noncomputable def Homeomorph.toOpenPartialHomeomorphOnOpens
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [Nonempty Y]
    {A : Set X} {B : Set Y} (h : A ≃ₜ B) (hA : IsOpen A) (hB : IsOpen B) :
    OpenPartialHomeomorph X Y where
  toFun x := if hx : x ∈ A then (h ⟨x, hx⟩ : Y) else Classical.arbitrary Y
  invFun y := if hy : y ∈ B then (h.symm ⟨y, hy⟩ : X) else Classical.arbitrary X
  source := A
  target := B
  map_source' x hx := by simp only [dite_eq_left hx]; exact (h ⟨x, hx⟩).2
  map_target' y hy := by simp only [dite_eq_left hy]; exact (h.symm ⟨y, hy⟩).2
  left_inv' x hx := by
    simp only [dite_eq_left hx, dite_eq_left (h ⟨x, hx⟩).2]
    have : (⟨(h ⟨x, hx⟩ : Y), (h ⟨x, hx⟩).2⟩ : B) = h ⟨x, hx⟩ := rfl
    rw [this, Homeomorph.symm_apply_apply]
  right_inv' y hy := by
    simp only [dite_eq_left hy, dite_eq_left (h.symm ⟨y, hy⟩).2]
    have : (⟨(h.symm ⟨y, hy⟩ : X), (h.symm ⟨y, hy⟩).2⟩ : A) = h.symm ⟨y, hy⟩ := rfl
    rw [this, Homeomorph.apply_symm_apply]
  open_source := hA
  open_target := hB
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (A.domRestrict fun x => if hx : x ∈ A then (h ⟨x, hx⟩ : Y) else Classical.arbitrary Y)
        = fun x : A => ((h x : B) : Y) := by
      funext x; simp only [Set.domRestrict_apply, dite_eq_left x.2]
    rw [this]
    exact continuous_subtype_val.comp h.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (B.domRestrict fun y => if hy : y ∈ B then (h.symm ⟨y, hy⟩ : X) else
        Classical.arbitrary X)
        = fun y : B => ((h.symm y : A) : X) := by
      funext y; simp only [Set.domRestrict_apply, dite_eq_left y.2]
    rw [this]
    exact continuous_subtype_val.comp h.symm.continuous

/-- An `OpenPartialHomeomorph` from a preconnected Hausdorff space onto the whole of a
compact space, with nonempty source, is a global homeomorphism: its source is compact
(hence closed) as well as open, so it is clopen and equals `univ`. -/
noncomputable def OpenPartialHomeomorph.toHomeomorphOfCompactTarget
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace X] [T2Space X] [CompactSpace Y]
    (φ : OpenPartialHomeomorph X Y)
    (hne : φ.source.Nonempty)
    (ht : φ.target = Set.univ) :
    Homeomorph X Y := by
  have ho : IsOpen φ.source := φ.open_source
  have hc : IsClosed φ.source := by
    have cpct' : CompactSpace φ.target := by
      rw [ht]
      exact (Homeomorph.Set.univ Y).symm.compactSpace
    have h : Homeomorph φ.target φ.source := φ.toHomeomorphSourceTarget.symm
    have hcs : CompactSpace φ.source := h.compactSpace
    have cpct : IsCompact φ.source := isCompact_iff_isCompact_univ.mpr CompactSpace.isCompact_univ
    exact cpct.isClosed
  have hs : φ.source = Set.univ := by
    have hco : IsClopen φ.source := ⟨hc, ho⟩
    have he' := isPreconnected_univ.subset_isClopen hco (by simpa using hne)
    exact Set.eq_univ_of_univ_subset he'
  exact φ.toHomeomorphOfSourceEqUnivTargetEqUniv hs ht

section OverlapHelpers

omit [ConnectedSpace M] [T2Space M] in
/-- The chart image of the overlap is never the whole target (since `U.source` is not
contained in `V.source`). -/
lemma overlap_image_ne_target (U V : OpenPartialHomeomorph M NNReal)
    (hUV : (U.source \ V.source).Nonempty) :
    U '' (U.source ∩ V.source) ≠ U.target := by
  intro heq
  obtain ⟨y, hyU, hyV⟩ := hUV
  have hy : U y ∈ U '' (U.source ∩ V.source) := heq ▸ U.map_source hyU
  obtain ⟨w, hwS, hwy⟩ := hy
  have hw : w = y := U.injOn hwS.1 hyU hwy
  exact hyV (hw ▸ hwS.2)

omit [ConnectedSpace M] in
/-- The outer-overlap lemma for a boundary chart, specialized to a connected overlap. -/
lemma overlap_image_Iio (U V : OpenPartialHomeomorph M NNReal) {v : NNReal}
    (hUt : U.target = Iio v)
    (hV : IsConnected V.source)
    (hUV : (U.source \ V.source).Nonempty)
    (hVU : (V.source \ U.source).Nonempty)
    (hc : IsConnected (U.source ∩ V.source)) :
    ∃ p, p < v ∧ U '' (U.source ∩ V.source) = Ioo p v := by
  obtain ⟨x, hx⟩ := hc.nonempty
  obtain ⟨p, hp, himg⟩ := overlap_component_outer_Iio U V hUt hV hUV hVU hx
  have hcomp : connectedComponentIn (U.source ∩ V.source) x = U.source ∩ V.source :=
    subset_antisymm (connectedComponentIn_subset _ _)
      (hc.isPreconnected.subset_connectedComponentIn hx subset_rfl)
  rw [hcomp] at himg
  exact ⟨p, hp, himg⟩

omit [ConnectedSpace M] in
/-- The outer-overlap lemma for an interior chart, specialized to a connected overlap. -/
lemma overlap_image_Ioo (U V : OpenPartialHomeomorph M NNReal) {u v : NNReal}
    (hUt : U.target = Ioo u v)
    (hV : IsConnected V.source)
    (hVU : (V.source \ U.source).Nonempty)
    (hc : IsConnected (U.source ∩ V.source)) :
    (∃ p, u ≤ p ∧ p < v ∧ U '' (U.source ∩ V.source) = Ioo p v) ∨
    (∃ q, u < q ∧ q ≤ v ∧ U '' (U.source ∩ V.source) = Ioo u q) := by
  obtain ⟨x, hx⟩ := hc.nonempty
  have hcomp : connectedComponentIn (U.source ∩ V.source) x = U.source ∩ V.source :=
    subset_antisymm (connectedComponentIn_subset _ _)
      (hc.isPreconnected.subset_connectedComponentIn hx subset_rfl)
  rcases overlap_component_outer_Ioo U V hUt hV hVU hx with ⟨p, h1, h2, himg⟩ | ⟨q, h1, h2, himg⟩
  · rw [hcomp] at himg
    exact Or.inl ⟨p, h1, h2, himg⟩
  · rw [hcomp] at himg
    exact Or.inr ⟨q, h1, h2, himg⟩

omit [ConnectedSpace M] in
/-- The overlap of a boundary chart with a connected chart is connected. -/
lemma hchart_overlap_connected (b : HChart M) (V : OpenPartialHomeomorph M NNReal)
    (hV : IsConnected V.source)
    (hbV : (b.source \ V.source).Nonempty)
    (hVb : (V.source \ b.source).Nonempty)
    (hne : (b.source ∩ V.source).Nonempty) :
    IsConnected (b.source ∩ V.source) := by
  obtain ⟨v, hv⟩ := b.target_iio
  exact overlap_connected b.toOpenPartialHomeomorph V hv.symm hV hbV hVb hne

lemma Ioc_union_Ioo_eq_Ioo {μ ν : NNReal} (hμν : μ < ν) :
    Ioc 0 μ ∪ Ioo μ ν = Ioo 0 ν := by
  ext y
  simp only [mem_union, mem_Ioc, mem_Ioo]
  constructor
  · rintro (⟨hy0, hy⟩ | ⟨hy, hy'⟩)
    · exact ⟨hy0, lt_of_le_of_lt hy hμν⟩
    · exact ⟨lt_of_le_of_lt (zero_le : (0 : NNReal) ≤ μ) hy, hy'⟩
  · rintro ⟨hy0, hy⟩
    rcases le_or_gt y μ with hle | hgt
    · exact Or.inl ⟨hy0, hle⟩
    · exact Or.inr ⟨hgt, hy⟩

lemma lt_div_self_of_lt_one {μ ρ : NNReal} (hμ0 : 0 < μ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    μ < μ / ρ := by
  rw [lt_div_iff₀ hρ0]
  exact mul_lt_of_lt_one_right hμ0 hρ1

end OverlapHelpers

section Orient

omit [ConnectedSpace M] in
/-- Re-orient an `OChart` with target `Ioo 0 1` (flipping if necessary) so that its image
of the overlap with `V.source` is the *lower* end-segment `Ioo 0 r` with `0 < r < 1`.
The source is unchanged. -/
lemma OChart.exists_orient_lower (a : OChart M) (V : OpenPartialHomeomorph M NNReal)
    (hat : a.target = Ioo 0 1)
    (hV : IsConnected V.source)
    (haV : (a.source \ V.source).Nonempty)
    (hVa : (V.source \ a.source).Nonempty)
    (hc : IsConnected (a.source ∩ V.source)) :
    ∃ (a' : OChart M) (r : NNReal), a'.source = a.source ∧ a'.target = Ioo 0 1 ∧
      0 < r ∧ r < 1 ∧
      a'.toOpenPartialHomeomorph '' (a.source ∩ V.source) = Ioo 0 r := by
  have hne := overlap_image_ne_target a.toOpenPartialHomeomorph V haV
  rcases overlap_image_Ioo a.toOpenPartialHomeomorph V hat hV hVa hc with
    ⟨p, -, hp1, himg⟩ | ⟨r, hr0, hr1, himg⟩
  · -- upper case: flip
    have hp0 : 0 < p := by
      rcases eq_or_lt_of_le (zero_le : (0 : NNReal) ≤ p) with heq | hlt
      · exfalso
        apply hne
        rw [himg, hat, ← heq]
      · exact hlt
    obtain ⟨a', ha's, ha't, ha'f⟩ := a.flip hat
    have himg' : a'.toOpenPartialHomeomorph '' (a.source ∩ V.source)
        = (fun y => 1 - y) '' (a.toOpenPartialHomeomorph '' (a.source ∩ V.source)) := by
      rw [← image_comp]
      exact image_congr (fun x hx => ha'f x hx.1)
    rw [himg, reflect_image_Ioo_upper hp1] at himg'
    exact ⟨a', 1 - p, ha's, ha't, tsub_pos_of_lt hp1, tsub_lt_self one_pos hp0, himg'⟩
  · -- lower case: already oriented
    have hr1' : r < 1 := by
      rcases eq_or_lt_of_le hr1 with heq | hlt
      · exfalso
        apply hne
        rw [himg, hat, heq]
      · exact hlt
    exact ⟨a, r, rfl, hat, hr0, hr1', himg⟩

omit [ConnectedSpace M] in
/-- Re-orient an `OChart` with target `Ioo 0 1` (flipping if necessary) so that its image
of the overlap with `V.source` is the *upper* end-segment `Ioo q 1` with `0 < q < 1`.
The source is unchanged. -/
lemma OChart.exists_orient_upper (a : OChart M) (V : OpenPartialHomeomorph M NNReal)
    (hat : a.target = Ioo 0 1)
    (hV : IsConnected V.source)
    (haV : (a.source \ V.source).Nonempty)
    (hVa : (V.source \ a.source).Nonempty)
    (hc : IsConnected (a.source ∩ V.source)) :
    ∃ (a' : OChart M) (q : NNReal), a'.source = a.source ∧ a'.target = Ioo 0 1 ∧
      0 < q ∧ q < 1 ∧
      a'.toOpenPartialHomeomorph '' (a.source ∩ V.source) = Ioo q 1 := by
  have hne := overlap_image_ne_target a.toOpenPartialHomeomorph V haV
  rcases overlap_image_Ioo a.toOpenPartialHomeomorph V hat hV hVa hc with
    ⟨q, hq0, hq1, himg⟩ | ⟨w, hw0, hw1, himg⟩
  · -- upper case: already oriented
    have hq0' : 0 < q := by
      rcases eq_or_lt_of_le hq0 with heq | hlt
      · exfalso
        apply hne
        rw [himg, hat, ← heq]
      · exact hlt
    exact ⟨a, q, rfl, hat, hq0', hq1, himg⟩
  · -- lower case: flip
    have hw1' : w < 1 := by
      rcases eq_or_lt_of_le hw1 with heq | hlt
      · exfalso
        apply hne
        rw [himg, hat, heq]
      · exact hlt
    obtain ⟨a', ha's, ha't, ha'f⟩ := a.flip hat
    have himg' : a'.toOpenPartialHomeomorph '' (a.source ∩ V.source)
        = (fun y => 1 - y) '' (a.toOpenPartialHomeomorph '' (a.source ∩ V.source)) := by
      rw [← image_comp]
      exact image_congr (fun x hx => ha'f x hx.1)
    rw [himg, reflect_image_Ioo_lower hw0 hw1] at himg'
    exact ⟨a', 1 - w, ha's, ha't, tsub_pos_of_lt hw1', tsub_lt_self one_pos hw0, himg'⟩

end Orient

omit [ConnectedSpace M] in
/-- Two overlapping H-charts glue to a chart of `M` onto the unit interval: rescale both
to target `Iio 1`, note the overlap is connected and appears as an upper end-segment in
each chart (outer-overlap lemma), and apply the unit-interval gluing. -/
lemma exists_glue_h_h (a : HChart M) (b : HChart M) (h : Overlap a.source b.source) :
    ∃ φ : OpenPartialHomeomorph M UnitInterval,
      φ.source = a.source ∪ b.source ∧ φ.target = Set.univ := by
  have hane : a.source.Nonempty := h.1.mono inter_subset_left
  have hbne : b.source.Nonempty := h.1.mono inter_subset_right
  obtain ⟨a', ha's, ha't, -⟩ := a.rescale hane
  obtain ⟨b', hb's, hb't, -⟩ := b.rescale hbne
  -- the overlap is connected
  have hc : IsConnected (a'.source ∩ b'.source) := by
    rw [ha's, hb's, inter_comm]
    exact hchart_overlap_connected b a.toOpenPartialHomeomorph
      (a.connected_source hane) h.2.2 h.2.1 (inter_comm a.source b.source ▸ h.1)
  -- each chart sees the overlap as an upper end-segment
  have hb'conn : IsConnected b'.source := b'.connected_source (hb's ▸ hbne)
  have ha'conn : IsConnected a'.source := a'.connected_source (ha's ▸ hane)
  obtain ⟨p, hp1, haimg⟩ := overlap_image_Iio a'.toOpenPartialHomeomorph
    b'.toOpenPartialHomeomorph ha't hb'conn
    (by rw [ha's, hb's]; exact h.2.1) (by rw [ha's, hb's]; exact h.2.2) hc
  obtain ⟨q, hq1, hbimg⟩ := overlap_image_Iio b'.toOpenPartialHomeomorph
    a'.toOpenPartialHomeomorph hb't ha'conn
    (by rw [ha's, hb's]; exact h.2.2) (by rw [ha's, hb's]; exact h.2.1)
    (inter_comm a'.source b'.source ▸ hc)
  rw [inter_comm] at hbimg
  -- glue
  obtain ⟨f, hfs, hft⟩ := glue_hh_ui a'.toOpenPartialHomeomorph b'.toOpenPartialHomeomorph
    ha't hb't haimg hp1 hbimg
  refine ⟨f, ?_, hft⟩
  rw [hfs, ha's, hb's]

/-- Glue two overlapping H-charts into a single chart of `M` onto the unit interval. -/
noncomputable def glueHH (a : HChart M) (b : HChart M) (h : Overlap a.source b.source) :
  { φ : OpenPartialHomeomorph M UnitInterval | φ.source = a.source ∪ b.source ∧ φ.target =
      Set.univ } :=
  ⟨(exists_glue_h_h a b h).choose, (exists_glue_h_h a b h).choose_spec⟩

/-- Join overlapping boundary charts into a homeomorphism with the closed unit interval. -/
noncomputable def handleHH (a : HChart M) (b : HChart M) (h : Overlap a.source b.source) :
  Homeomorph M UnitInterval := by
  obtain ⟨φ, hφ, hs⟩ := glueHH a b h
  have hne : φ.source.Nonempty := by
    rw [hφ]
    exact Set.Nonempty.inl (h.1.mono Set.inter_subset_left)
  exact φ.toHomeomorphOfCompactTarget hne hs

omit [ConnectedSpace M] in
/-- An O-chart and an H-chart with connected overlap glue to an H-chart on the union:
rescale both, orient the O-chart so the overlap sits at its lower end, and apply the
`ℝ≥0` gluing. -/
lemma exists_glue_o_h (a : OChart M) (b : HChart M) (h : Overlap a.source b.source)
    (hc : IsConnected (a.source ∩ b.source)) :
    ∃ f : HChart M, f.source = a.source ∪ b.source := by
  have hane : a.source.Nonempty := h.1.mono inter_subset_left
  have hbne : b.source.Nonempty := h.1.mono inter_subset_right
  obtain ⟨a₀, ha₀s, ha₀t, -⟩ := a.rescale hane
  obtain ⟨b', hb's, hb't, -⟩ := b.rescale hbne
  have hb'conn : IsConnected b'.source := b'.connected_source (hb's ▸ hbne)
  -- orient the O-chart so the overlap is its lower end-segment
  obtain ⟨a', r, ha's, ha't, hr0, hr1, haimg⟩ :=
    a₀.exists_orient_lower b'.toOpenPartialHomeomorph ha₀t hb'conn
      (by rw [ha₀s, hb's]; exact h.2.1) (by rw [ha₀s, hb's]; exact h.2.2)
      (by rw [ha₀s, hb's]; exact hc)
  have ha's' : a'.source = a.source := ha's.trans ha₀s
  have ha'conn : IsConnected a'.source := a'.connected_source (ha's' ▸ hane)
  -- the H-chart sees the overlap as an upper end-segment
  obtain ⟨q, hq1, hbimg⟩ := overlap_image_Iio b'.toOpenPartialHomeomorph
    a'.toOpenPartialHomeomorph hb't ha'conn
    (by rw [ha's', hb's]; exact h.2.2) (by rw [ha's', hb's]; exact h.2.1)
    (by rw [ha's', hb's, inter_comm]; exact hc)
  rw [inter_comm] at hbimg
  -- adjust the O-chart image statement to the primed sources
  have haimg' : a'.toOpenPartialHomeomorph '' (a'.source ∩ b'.source) = Ioo 0 r := by
    rw [ha's]
    exact haimg
  -- glue
  obtain ⟨f, hfs, μ, ρ, hqμ, hμ1, hρ0, hρ1, hft⟩ :=
    glue_nnreal a'.toOpenPartialHomeomorph b'.toOpenPartialHomeomorph ha't
      (by rw [hb't]) haimg' hr0 hr1 hbimg (by rw [hb't]; exact hq1)
  -- the glued target is `Iio (μ/ρ)`
  have hμ0 : 0 < μ := lt_of_le_of_lt zero_le hqμ
  have hμν : μ < μ / ρ := lt_div_self_of_lt_one hμ0 hρ0 hρ1
  have htarget : f.target = Iio (μ / ρ) := by
    rw [hft, hb't]
    have h1 : Iio 1 ∩ Iic μ = Iic μ :=
      inter_eq_right.mpr (fun y hy => lt_of_le_of_lt hy hμ1)
    rw [h1, Iic_union_Ioo_eq_Iio hμν]
  refine ⟨⟨f, ⟨μ / ρ, htarget.symm⟩⟩, ?_⟩
  change f.source = a.source ∪ b.source
  rw [hfs, ha's', hb's]

/-- Glue an O-chart and an H-chart with connected overlap into an H-chart on the union. -/
noncomputable def handleOH' (a : OChart M) (b : HChart M) (h : Overlap a.source b.source)
  (hc : IsConnected (a.source ∩ b.source)) :
  { f : HChart M | f.source = a.source ∪ b.source } :=
  ⟨(exists_glue_o_h a b h hc).choose, (exists_glue_o_h a b h hc).choose_spec⟩

/-- Glue an O-chart and an H-chart: the overlap with an H-chart is automatically
connected. -/
noncomputable def handleOH (a : OChart M) (b : HChart M) (h : Overlap a.source b.source) :
  { f : HChart M | f.source = a.source ∪ b.source } := by
  have hane : a.source.Nonempty := h.1.mono inter_subset_left
  have hc : IsConnected (a.source ∩ b.source) := by
    rw [inter_comm]
    exact hchart_overlap_connected b a.toOpenPartialHomeomorph
      (a.connected_source hane) h.2.2 h.2.1 (inter_comm a.source b.source ▸ h.1)
  exact handleOH' a b h hc

omit [ConnectedSpace M] in
/-- Two O-charts with connected overlap glue to an O-chart on the union: rescale both,
orient the first chart's overlap low and the second's high, and apply the `ℝ≥0`
gluing. -/
lemma exists_glue_o_o (a : OChart M) (b : OChart M) (h : Overlap a.source b.source)
    (hc : IsConnected (a.source ∩ b.source)) :
    ∃ f : OChart M, f.source = a.source ∪ b.source := by
  have hane : a.source.Nonempty := h.1.mono inter_subset_left
  have hbne : b.source.Nonempty := h.1.mono inter_subset_right
  obtain ⟨a₀, ha₀s, ha₀t, -⟩ := a.rescale hane
  obtain ⟨b₀, hb₀s, hb₀t, -⟩ := b.rescale hbne
  have hb₀conn : IsConnected b₀.source := b₀.connected_source (hb₀s ▸ hbne)
  -- orient the first chart's overlap low
  obtain ⟨a', r, ha's, ha't, hr0, hr1, haimg⟩ :=
    a₀.exists_orient_lower b₀.toOpenPartialHomeomorph ha₀t hb₀conn
      (by rw [ha₀s, hb₀s]; exact h.2.1) (by rw [ha₀s, hb₀s]; exact h.2.2)
      (by rw [ha₀s, hb₀s]; exact hc)
  have ha's' : a'.source = a.source := ha's.trans ha₀s
  have ha'conn : IsConnected a'.source := a'.connected_source (ha's' ▸ hane)
  -- orient the second chart's overlap high
  obtain ⟨b', q, hb's, hb't, hq0, hq1, hbimg⟩ :=
    b₀.exists_orient_upper a'.toOpenPartialHomeomorph hb₀t ha'conn
      (by rw [ha's', hb₀s]; exact h.2.2) (by rw [ha's', hb₀s]; exact h.2.1)
      (by rw [ha's', hb₀s, inter_comm]; exact hc)
  have hb's' : b'.source = b.source := hb's.trans hb₀s
  -- adjust both image statements to the primed sources
  have haimg' : a'.toOpenPartialHomeomorph '' (a'.source ∩ b'.source) = Ioo 0 r := by
    rw [ha's, hb's]
    exact haimg
  have hbimg' : b'.toOpenPartialHomeomorph '' (a'.source ∩ b'.source) = Ioo q 1 := by
    rw [hb's, inter_comm]
    exact hbimg
  -- glue
  obtain ⟨f, hfs, μ, ρ, hqμ, hμ1, hρ0, hρ1, hft⟩ :=
    glue_nnreal a'.toOpenPartialHomeomorph b'.toOpenPartialHomeomorph ha't
      (by rw [hb't]; exact Ioo_subset_Iio_self) haimg' hr0 hr1 hbimg'
      (by rw [hb't]; exact ⟨hq0, hq1⟩)
  -- the glued target is `Ioo 0 (μ/ρ)`
  have hμ0 : 0 < μ := lt_of_le_of_lt zero_le hqμ
  have hμν : μ < μ / ρ := lt_div_self_of_lt_one hμ0 hρ0 hρ1
  have htarget : f.target = Ioo 0 (μ / ρ) := by
    rw [hft, hb't]
    have h1 : Ioo 0 1 ∩ Iic μ = Ioc 0 μ := by
      ext y
      simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨⟨hy0, -⟩, hy⟩
        exact ⟨hy0, hy⟩
      · rintro ⟨hy0, hy⟩
        exact ⟨⟨hy0, lt_of_le_of_lt hy hμ1⟩, hy⟩
    rw [h1, Ioc_union_Ioo_eq_Ioo hμν]
  refine ⟨⟨f, ⟨0, μ / ρ, htarget.symm⟩⟩, ?_⟩
  change f.source = a.source ∪ b.source
  rw [hfs, ha's', hb's']

/-- A disconnected overlap of two O-charts closes `M` up into a circle: the glued chart
of `exists_circle_chart` maps `a.source ∪ b.source` onto the whole of `AddCircle 1`;
transfer to `Circle` and apply the compact-target argument. -/
noncomputable def circleOfDisconnectedOverlap (a : OChart M) (b : OChart M)
  (h : Overlap a.source b.source) (hc : ¬ IsConnected (a.source ∩ b.source)) :
  Homeomorph M Circle := by
  have H := exists_circle_chart a b h hc
  obtain ⟨hfs, hft⟩ := H.choose_spec
  let f' := H.choose.transHomeomorph (AddCircle.homeomorphCircle (one_ne_zero (α := ℝ)))
  have hfs' : f'.source = a.source ∪ b.source := hfs
  have hft' : f'.target = Set.univ := by
    change (AddCircle.homeomorphCircle _).symm ⁻¹' H.choose.target = Set.univ
    rw [hft]
    exact Set.preimage_univ
  have hne : f'.source.Nonempty := by
    rw [hfs']
    exact Set.Nonempty.inl (h.1.mono Set.inter_subset_left)
  exact f'.toHomeomorphOfCompactTarget hne hft'

/-- Glue two O-charts: with a connected overlap they merge into an O-chart on the union;
with a disconnected overlap, `M` is a circle. -/
noncomputable def handleOO (a : OChart M) (b : OChart M) (h : Overlap a.source b.source) :
  (Homeomorph M Circle) ⊕ { f : OChart M | f.source = a.source ∪ b.source } := by
  by_cases hc : IsConnected (a.source ∩ b.source)
  · exact Sum.inr ⟨(exists_glue_o_o a b h hc).choose, (exists_glue_o_o a b h hc).choose_spec⟩
  · exact Sum.inl (circleOfDisconnectedOverlap a b h hc)
