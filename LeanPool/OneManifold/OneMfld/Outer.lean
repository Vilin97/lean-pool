/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib
import LeanPool.OneManifold.OneMfld.ClosureOverlap
import LeanPool.OneManifold.OneMfld.LocallyConnected
import LeanPool.OneManifold.OneMfld.PartialHomeomorphHelpers
import LeanPool.OneManifold.OneMfld.ClassifyInterval

/-! # The outer-overlap lemma

The structural heart of the classification: when two interval charts `U`, `V` overlap
(neither source containing the other), the image under `U` of any connected component of
`U.source ∩ V.source` is an *end-segment* of `U.target` — its closure reaches an open
endpoint of the target. The mechanism: if the closure of the image stayed inside the
target, the component's closure in `M` would be trapped inside `U.source` (a compactness
argument), contradicting `nonempty_closure_inter_diff`, which forces the component's
closure to escape into `V.source \ U.source`.
-/

open Set

variable {M : Type*} [TopologicalSpace M]

section ComponentTransport

/-- A partial homeomorphism maps the connected component of `x` in a subset `S` of its
source onto the connected component of `φ x` in `φ '' S`. -/
lemma OpenPartialHomeomorph.image_connectedComponentIn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : OpenPartialHomeomorph X Y) {S : Set X} (hS : S ⊆ φ.source)
    {x : X} (hx : x ∈ S) :
    φ '' connectedComponentIn S x = connectedComponentIn (φ '' S) (φ x) := by
  have hST : φ '' S ⊆ φ.target := by
    rintro y ⟨z, hz, rfl⟩
    exact φ.map_source (hS hz)
  apply subset_antisymm
  · have hW : IsConnected (connectedComponentIn S x) :=
      isConnected_connectedComponentIn_iff.mpr hx
    have hWS : connectedComponentIn S x ⊆ S := connectedComponentIn_subset S x
    have himg : IsConnected (φ '' connectedComponentIn S x) :=
      hW.image _ (φ.continuousOn.mono (hWS.trans hS))
    apply himg.isPreconnected.subset_connectedComponentIn
    · exact ⟨x, mem_connectedComponentIn hx, rfl⟩
    · exact image_mono hWS
  · have hW' : IsConnected (connectedComponentIn (φ '' S) (φ x)) :=
      isConnected_connectedComponentIn_iff.mpr ⟨x, hx, rfl⟩
    have hW'T : connectedComponentIn (φ '' S) (φ x) ⊆ φ '' S :=
      connectedComponentIn_subset _ _
    have hsymm : IsConnected (φ.symm '' connectedComponentIn (φ '' S) (φ x)) :=
      hW'.image _ (φ.symm.continuousOn.mono (hW'T.trans hST))
    have hsub : φ.symm '' connectedComponentIn (φ '' S) (φ x)
        ⊆ connectedComponentIn S x := by
      apply hsymm.isPreconnected.subset_connectedComponentIn
      · exact ⟨φ x, mem_connectedComponentIn ⟨x, hx, rfl⟩, φ.left_inv (hS hx)⟩
      · calc φ.symm '' connectedComponentIn (φ '' S) (φ x)
            ⊆ φ.symm '' (φ '' S) := image_mono hW'T
          _ = S := φ.toPartialEquiv.symm_image_image_of_subset_source hS
    calc connectedComponentIn (φ '' S) (φ x)
        = φ '' (φ.symm '' connectedComponentIn (φ '' S) (φ x)) :=
          (φ.toPartialEquiv.image_symm_image_of_subset_target (hW'T.trans hST)).symm
      _ ⊆ φ '' connectedComponentIn S x := image_mono hsub

/-- Connected components of an open set contained in a chart source are open, because the
model space is locally connected. -/
lemma isOpen_connectedComponentIn_chart
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LocallyConnectedSpace Y]
    (φ : OpenPartialHomeomorph X Y) {S : Set X} (hS : S ⊆ φ.source)
    (hSo : IsOpen S) (x : X) :
    IsOpen (connectedComponentIn S x) := by
  by_cases hx : x ∈ S
  · have key := OpenPartialHomeomorph.image_connectedComponentIn φ hS hx
    have hWS : connectedComponentIn S x ⊆ S := connectedComponentIn_subset S x
    have hopen : IsOpen (connectedComponentIn (φ '' S) (φ x)) :=
      (φ.isOpen_image_of_subset_source hSo hS).connectedComponentIn
    have hsub : connectedComponentIn (φ '' S) (φ x) ⊆ φ.target := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := connectedComponentIn_subset _ _ hy
      exact φ.map_source (hS hz)
    have hrw : connectedComponentIn S x
        = φ.symm '' connectedComponentIn (φ '' S) (φ x) := by
      rw [← key]
      exact (φ.toPartialEquiv.symm_image_image_of_subset_source (hWS.trans hS)).symm
    rw [hrw]
    exact φ.isOpen_image_symm_of_subset_target hopen hsub
  · rw [connectedComponentIn_eq_empty hx]
    exact isOpen_empty

/-- Components of an open set contained in a chart source are relatively closed: a point
of `S` in the closure of a component of `S` lies in that component. -/
lemma mem_connectedComponentIn_of_mem_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LocallyConnectedSpace Y]
    (φ : OpenPartialHomeomorph X Y) {S : Set X} (hS : S ⊆ φ.source) (hSo : IsOpen S)
    {x z : X} (hz : z ∈ closure (connectedComponentIn S x)) (hzS : z ∈ S) :
    z ∈ connectedComponentIn S x := by
  have hW2open : IsOpen (connectedComponentIn S z) :=
    isOpen_connectedComponentIn_chart φ hS hSo z
  have hzW2 : z ∈ connectedComponentIn S z := mem_connectedComponentIn hzS
  obtain ⟨y, hyW2, hyW⟩ := mem_closure_iff.mp hz _ hW2open hzW2
  have h1 : connectedComponentIn S z = connectedComponentIn S y :=
    connectedComponentIn_eq hyW2
  have h2 : connectedComponentIn S x = connectedComponentIn S y :=
    connectedComponentIn_eq hyW
  rw [h2, ← h1]
  exact hzW2

end ComponentTransport

section Escape

/-- The image under `U` of a component of the overlap is not all of `U.target`
(because `U.source` is not contained in `V.source`). -/
lemma image_component_ne_target
    (U V : OpenPartialHomeomorph M NNReal)
    (hUV : (U.source \ V.source).Nonempty)
    {x : M} (hx : x ∈ U.source ∩ V.source) :
    U '' connectedComponentIn (U.source ∩ V.source) x ≠ U.target := by
  intro h
  obtain ⟨y, hyU, hyV⟩ := hUV
  have hWsub : connectedComponentIn (U.source ∩ V.source) x ⊆ U.source ∩ V.source :=
    connectedComponentIn_subset _ _
  have hyt : U y ∈ U '' connectedComponentIn (U.source ∩ V.source) x := by
    rw [h]
    exact U.map_source hyU
  obtain ⟨w, hwW, hwy⟩ := hyt
  have hwyeq : w = y := U.injOn (hWsub hwW).1 hyU hwy
  exact hyV (hwyeq ▸ (hWsub hwW).2)

/-- The heart of the outer-overlap argument: the closure (in `ℝ≥0`) of the image of an
overlap component cannot stay inside the (bounded) chart target. Otherwise the
component's closure in `M` would be a subset of the compact set
`U.symm '' closure (U '' W)` inside `U.source` — but by `nonempty_closure_inter_diff`
the component's closure must reach a point of `V.source` outside the component, and any
such point trapped in `U.source ∩ V.source` would belong to the component after all. -/
theorem not_closure_image_subset_target [T2Space M]
    (U V : OpenPartialHomeomorph M NNReal)
    (hUb : Bornology.IsBounded U.target)
    (hV : IsConnected V.source)
    (hVU : (V.source \ U.source).Nonempty)
    {x : M} (hx : x ∈ U.source ∩ V.source) :
    ¬ closure (U '' connectedComponentIn (U.source ∩ V.source) x) ⊆ U.target := by
  intro hcl
  set S := U.source ∩ V.source with hSdef
  set W := connectedComponentIn S x with hWdef
  set A := U '' W with hAdef
  have hSo : IsOpen S := U.open_source.inter V.open_source
  have hSU : S ⊆ U.source := inter_subset_left
  have hWS : W ⊆ S := connectedComponentIn_subset _ _
  -- the closure of the image is compact
  have hAT : A ⊆ U.target := by
    rintro y ⟨w, hw, rfl⟩
    exact U.map_source (hSU (hWS hw))
  have hAcomp : IsCompact (closure A) := (hUb.subset hAT).isCompact_closure
  -- its preimage under `U.symm` is compact, hence closed, and lives in `U.source`
  have hKcomp : IsCompact (U.symm '' closure A) :=
    hAcomp.image_of_continuousOn (U.symm.continuousOn.mono hcl)
  have hKclosed : IsClosed (U.symm '' closure A) := hKcomp.isClosed
  have hKU : U.symm '' closure A ⊆ U.source := by
    rintro z ⟨a, ha, rfl⟩
    exact U.map_target (hcl ha)
  have hWK : W ⊆ U.symm '' closure A := by
    intro w hw
    exact ⟨U w, subset_closure ⟨w, hw, rfl⟩, U.left_inv (hSU (hWS hw))⟩
  have hclWU : closure W ⊆ U.source :=
    (closure_minimal hWK hKclosed).trans hKU
  -- the component's closure must escape into `V.source \ W`
  have hWo : IsOpen W := isOpen_connectedComponentIn_chart U hSU hSo x
  have hWV : (W ∩ V.source).Nonempty := ⟨x, mem_connectedComponentIn hx, hx.2⟩
  obtain ⟨y, hyV, hyU⟩ := hVU
  have hVW : (V.source \ W).Nonempty :=
    ⟨y, hyV, fun hyW => hyU (hSU (hWS hyW))⟩
  obtain ⟨z, hzcl, hzV, hzW⟩ :=
    nonempty_closure_inter_diff hV hWo V.open_source hWV hVW
  have hzS : z ∈ S := ⟨hclWU hzcl, hzV⟩
  exact hzW (mem_connectedComponentIn_of_mem_closure U hSU hSo hzcl hzS)

end Escape

section EndpointAnalysis

/-- A nonempty open connected subset of `Iio v ⊆ ℝ≥0`, other than `Iio v` itself, whose
closure is not contained in `Iio v`, is an upper end-segment `Ioo p v`. -/
theorem eq_Ioo_of_closure_not_subset_Iio {v : NNReal} {A : Set NNReal}
    (hA : A ⊆ Iio v) (hAo : IsOpen A) (hAc : IsConnected A)
    (hAne : A ≠ Iio v)
    (hesc : ¬ closure A ⊆ Iio v) :
    ∃ p, p < v ∧ A = Ioo p v := by
  obtain ⟨e, heA, hev⟩ := not_subset.mp hesc
  have hve : v ≤ e := not_lt.mp hev
  obtain ⟨a, ha⟩ := hAc.nonempty
  rcases classify_connected_nnreal_interval A hAo hAc with ⟨p, q, hpq⟩ | ⟨q, hq⟩ | ⟨p, hp⟩ | h
  · -- `A = Ioo p q`: the escape forces `q = v`
    have hpq' : p < q := by
      have ha' : a ∈ Ioo p q := hpq.symm ▸ ha
      exact lt_trans ha'.1 ha'.2
    have hqv : q ≤ v := by
      by_contra hqv
      push Not at hqv
      obtain ⟨t, ht1, ht2⟩ := exists_between (max_lt hpq' hqv)
      have htA : t ∈ A := hpq ▸ mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_left p v) ht1, ht2⟩
      exact absurd (mem_Iio.mp (hA htA))
        (not_lt.mpr (le_trans (le_max_right p v) ht1.le))
    have hclA : closure A = Icc p q := by
      rw [← hpq]
      exact closure_Ioo hpq'.ne
    have heIcc : e ∈ Icc p q := hclA ▸ heA
    have hqveq : q = v := le_antisymm hqv (le_trans hve heIcc.2)
    exact ⟨p, hqveq ▸ hpq', by rw [← hpq, hqveq]⟩
  · -- `A = Iio q`: forces `A = Iio v`, contradiction
    exfalso
    have hqv : q ≤ v := by
      by_contra hqv
      push Not at hqv
      exact lt_irrefl v (hA (hq ▸ mem_Iio.mpr hqv))
    have hclA : closure A = Iic q := by
      rw [← hq]
      exact closure_Iio' ⟨a, hq.symm ▸ ha⟩
    have heq : e ≤ q := (hclA ▸ heA : e ∈ Iic q)
    have : q = v := le_antisymm hqv (le_trans hve heq)
    exact hAne (by rw [← hq, this])
  · -- `A = Ioi p`: unbounded, contradiction
    exfalso
    have h1 : max (p + 1) v ∈ A :=
      hp ▸ mem_Ioi.mpr (lt_of_lt_of_le (lt_add_one p) (le_max_left _ _))
    exact absurd (mem_Iio.mp (hA h1)) (not_lt.mpr (le_max_right _ _))
  · -- `A = univ`: unbounded, contradiction
    exfalso
    have h1 : v ∈ A := h.symm ▸ mem_univ v
    exact lt_irrefl v (hA h1)

/-- A nonempty open connected subset of `Ioo u v ⊆ ℝ≥0` whose closure is not contained in
`Ioo u v` is an end-segment: `Ioo p v` or `Ioo u q`. -/
theorem eq_end_segment_of_closure_not_subset_Ioo {u v : NNReal} {A : Set NNReal}
    (hA : A ⊆ Ioo u v) (hAo : IsOpen A) (hAc : IsConnected A)
    (hesc : ¬ closure A ⊆ Ioo u v) :
    (∃ p, u ≤ p ∧ p < v ∧ A = Ioo p v) ∨ (∃ q, u < q ∧ q ≤ v ∧ A = Ioo u q) := by
  obtain ⟨e, heA, hev⟩ := not_subset.mp hesc
  obtain ⟨a, ha⟩ := hAc.nonempty
  rcases classify_connected_nnreal_interval A hAo hAc with ⟨p, q, hpq⟩ | ⟨q, hq⟩ | ⟨p, hp⟩ | h
  · -- `A = Ioo p q`: the escape point pins one endpoint
    have hpq' : p < q := by
      have ha' : a ∈ Ioo p q := hpq.symm ▸ ha
      exact lt_trans ha'.1 ha'.2
    have hup : u ≤ p := by
      by_contra hup
      push Not at hup
      obtain ⟨t, ht1, ht2⟩ := exists_between (lt_min_iff.mpr ⟨hpq', hup⟩ : p < min q u)
      have htA : t ∈ A := hpq ▸ mem_Ioo.mpr ⟨ht1, lt_of_lt_of_le ht2 (min_le_left q u)⟩
      exact absurd (hA htA).1 (not_lt.mpr (le_trans ht2.le (min_le_right q u)))
    have hqv : q ≤ v := by
      by_contra hqv
      push Not at hqv
      obtain ⟨t, ht1, ht2⟩ := exists_between (max_lt_iff.mpr ⟨hpq', hqv⟩ : max p v < q)
      have htA : t ∈ A := hpq ▸ mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_left p v) ht1, ht2⟩
      exact absurd (hA htA).2 (not_lt.mpr (le_trans (le_max_right p v) ht1.le))
    have hclA : closure A = Icc p q := by
      rw [← hpq]
      exact closure_Ioo hpq'.ne
    have heIcc : e ∈ Icc p q := hclA ▸ heA
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hev
    rcases hev with heu | hve
    · -- `e ≤ u`: the lower endpoint is `u`
      have hpu : p = u := le_antisymm (le_trans heIcc.1 heu) hup
      exact Or.inr ⟨q, hpu ▸ hpq', hqv, by rw [← hpq, hpu]⟩
    · -- `v ≤ e`: the upper endpoint is `v`
      have hqveq : q = v := le_antisymm hqv (le_trans hve heIcc.2)
      exact Or.inl ⟨p, hup, hqveq ▸ hpq', by rw [← hpq, hqveq]⟩
  · -- `A = Iio q`: contains `0`, but `A ⊆ Ioo u v` — impossible
    exfalso
    have h0q : (0 : NNReal) < q :=
      lt_of_le_of_lt (zero_le : (0 : NNReal) ≤ a)
        (mem_Iio.mp (hq.symm ▸ ha : a ∈ Iio q))
    have h0A : (0 : NNReal) ∈ A := hq ▸ mem_Iio.mpr h0q
    exact absurd (hA h0A).1 (not_lt.mpr (zero_le : (0 : NNReal) ≤ u))
  · -- `A = Ioi p`: unbounded, contradiction
    exfalso
    have h1 : max (p + 1) v ∈ A :=
      hp ▸ mem_Ioi.mpr (lt_of_lt_of_le (lt_add_one p) (le_max_left _ _))
    exact absurd (hA h1).2 (not_lt.mpr (le_max_right _ _))
  · -- `A = univ`: unbounded, contradiction
    exfalso
    have h1 : v ∈ A := h.symm ▸ mem_univ v
    exact lt_irrefl v (hA h1).2

end EndpointAnalysis

section Outer

/-- **Outer-overlap lemma, boundary-chart case.** If `U` has target `Iio v` and overlaps
`V` (neither source containing the other), the image under `U` of any connected component
of the overlap is an upper end-segment `Ioo p v`. -/
theorem overlap_component_outer_Iio [T2Space M]
    (U V : OpenPartialHomeomorph M NNReal) {v : NNReal}
    (hUt : U.target = Iio v)
    (hV : IsConnected V.source)
    (hUV : (U.source \ V.source).Nonempty)
    (hVU : (V.source \ U.source).Nonempty)
    {x : M} (hx : x ∈ U.source ∩ V.source) :
    ∃ p, p < v ∧ U '' connectedComponentIn (U.source ∩ V.source) x = Ioo p v := by
  set S := U.source ∩ V.source with hSdef
  set W := connectedComponentIn S x with hWdef
  set A := U '' W with hAdef
  have hSU : S ⊆ U.source := inter_subset_left
  have hSo : IsOpen S := U.open_source.inter V.open_source
  have hWo : IsOpen W := isOpen_connectedComponentIn_chart U hSU hSo x
  have hWS : W ⊆ S := connectedComponentIn_subset _ _
  have hAo : IsOpen A := U.isOpen_image_of_subset_source hWo (hWS.trans hSU)
  have hAc : IsConnected A :=
    (isConnected_connectedComponentIn_iff.mpr hx).image _
      (U.continuousOn.mono (hWS.trans hSU))
  have hAsub : A ⊆ U.target := by
    rintro y ⟨w, hw, rfl⟩
    exact U.map_source (hSU (hWS hw))
  have hUb : Bornology.IsBounded U.target := by
    rw [hUt]
    have : Iio v = Ico 0 v := by
      ext z
      simp only [mem_Iio, mem_Ico, zero_le, true_and]
    rw [this]
    exact Metric.isBounded_Ico 0 v
  have hAne : A ≠ Iio v := by
    rw [← hUt]
    exact image_component_ne_target U V hUV hx
  have hesc : ¬ closure A ⊆ Iio v := by
    rw [← hUt]
    exact not_closure_image_subset_target U V hUb hV hVU hx
  exact eq_Ioo_of_closure_not_subset_Iio (hUt ▸ hAsub) hAo hAc hAne hesc

/-- **Outer-overlap lemma, interior-chart case.** If `U` has target `Ioo u v` and
overlaps `V`, the image under `U` of any connected component of the overlap is an
end-segment `Ioo p v` or `Ioo u q`. -/
theorem overlap_component_outer_Ioo [T2Space M]
    (U V : OpenPartialHomeomorph M NNReal) {u v : NNReal}
    (hUt : U.target = Ioo u v)
    (hV : IsConnected V.source)
    (hVU : (V.source \ U.source).Nonempty)
    {x : M} (hx : x ∈ U.source ∩ V.source) :
    (∃ p, u ≤ p ∧ p < v ∧ U '' connectedComponentIn (U.source ∩ V.source) x = Ioo p v) ∨
    (∃ q, u < q ∧ q ≤ v ∧ U '' connectedComponentIn (U.source ∩ V.source) x = Ioo u q) := by
  set S := U.source ∩ V.source with hSdef
  set W := connectedComponentIn S x with hWdef
  set A := U '' W with hAdef
  have hSU : S ⊆ U.source := inter_subset_left
  have hSo : IsOpen S := U.open_source.inter V.open_source
  have hWo : IsOpen W := isOpen_connectedComponentIn_chart U hSU hSo x
  have hWS : W ⊆ S := connectedComponentIn_subset _ _
  have hAo : IsOpen A := U.isOpen_image_of_subset_source hWo (hWS.trans hSU)
  have hAc : IsConnected A :=
    (isConnected_connectedComponentIn_iff.mpr hx).image _
      (U.continuousOn.mono (hWS.trans hSU))
  have hAsub : A ⊆ U.target := by
    rintro y ⟨w, hw, rfl⟩
    exact U.map_source (hSU (hWS hw))
  have hUb : Bornology.IsBounded U.target := by
    rw [hUt]
    exact Metric.isBounded_Ioo u v
  have hesc : ¬ closure A ⊆ Ioo u v := by
    rw [← hUt]
    exact not_closure_image_subset_target U V hUb hV hVU hx
  exact eq_end_segment_of_closure_not_subset_Ioo (hUt ▸ hAsub) hAo hAc hesc

end Outer
