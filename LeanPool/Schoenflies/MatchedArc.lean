/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Mathlib.Combinatorics.Graph.Maps
import LeanPool.Schoenflies.FaceCyclesProof

/-!
# Matching and cutting simple polygonal arcs

An ear can have an arbitrary finite number of abstract edges.  On the target side we only
obtain one set-level polygonal crosscut.  This module supplies the two facts that reconcile
those descriptions.

* Two named arcs admit an endpoint-preserving homeomorphism, obtained by matching their
  parameters.
* An arc contained in a polygonal arc is polygonal.  Consequently the images of all source
  edge arcs under the parameter-matching homeomorphism are polygonal target edge arcs.
-/

open Set unitInterval

namespace Schoenflies

/-! ## The inverse of a compact parametrisation -/

/-- A continuous injection of a compact set has a continuous `invFunOn` on its image. -/
theorem continuousOn_invFunOn_image' {f : ℝ → Plane} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hinj : InjOn f s) :
    ContinuousOn (Function.invFunOn f s) (f '' s) := by
  rw [continuousOn_iff_isClosed]
  intro F hF
  refine ⟨f '' (F ∩ s), (hs.inter_left hF).image_of_continuousOn (hf.mono inter_subset_right)
    |>.isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hx] at hy
    exact ⟨⟨x, ⟨hy, hx⟩, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨⟨x, ⟨hxF, hxs⟩, rfl⟩, -⟩
    exact ⟨by rw [mem_preimage, hinj.leftInvOn_invFunOn hxs]; exact hxF,
      ⟨x, hxs, rfl⟩⟩

/-! ## A subarc of a polygonal arc is polygonal -/

/-- An arc contained in another arc is the unique closed subarc between its two endpoints.
This form allows the ambient arc to have different endpoints. -/
theorem IsArcBetween.eq_of_subset_arc {A B C : Set Plane} {p q r s : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hC : IsArcBetween C r s) (hAC : A ⊆ C) (hBC : B ⊆ C) : A = B := by
  obtain ⟨f, hfc, hfi, rfl, -, -⟩ := hC
  let inv : Plane → ℝ := Function.invFunOn f I
  have hinv : ContinuousOn inv (f '' I) :=
    continuousOn_invFunOn_image' isCompact_I hfc hfi
  have hmaps : MapsTo inv (f '' I) I := by
    rintro _ ⟨t, ht, rfl⟩
    change Function.invFunOn f I (f t) ∈ I
    rw [hfi.leftInvOn_invFunOn ht]
    exact ht
  have image_inv (K : Set Plane) (hK : K ⊆ f '' I) : f '' (inv '' K) = K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x, hxK, rfl⟩, rfl⟩
      obtain ⟨t, ht, rfl⟩ := hK hxK
      simpa [inv, hfi.leftInvOn_invFunOn ht] using hxK
    · intro x hxK
      obtain ⟨t, ht, rfl⟩ := hK hxK
      exact ⟨inv (f t), ⟨f t, hxK, rfl⟩, by simp [inv, hfi.leftInvOn_invFunOn ht]⟩
  have image_is_interval (K : Set Plane) (hKarc : IsArcBetween K p q)
      (hK : K ⊆ f '' I) :
      inv '' K = uIcc (inv p) (inv q) := by
    obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hKarc
    let k : ℝ → ℝ := inv ∘ g
    have hgmap : MapsTo g I (f '' I) := fun t ht => hK (hgim ▸ Set.mem_image_of_mem g ht)
    have hkc : ContinuousOn k I := hinv.comp hgc hgmap
    have hki : InjOn k I := by
      intro x hx y hy hxy
      apply hgi hx hy
      have hleft : ∀ z ∈ K, f (inv z) = z := by
        intro z hz
        obtain ⟨t, ht, rfl⟩ := hK hz
        simp [inv, hfi.leftInvOn_invFunOn ht]
      rw [← hleft (g x) (hgim ▸ Set.mem_image_of_mem g hx),
        ← hleft (g y) (hgim ▸ Set.mem_image_of_mem g hy)]
      exact congrArg f (show inv (g x) = inv (g y) from hxy)
    have hkimage : k '' I = uIcc (k 0) (k 1) := by
      rcases hkc.strictMonoOn_of_injOn_Icc' zero_le_one hki with hmono | hanti
      · rw [hkc.image_Icc_of_monotoneOn zero_le_one hmono.monotoneOn,
          uIcc_of_le (hmono.monotoneOn zero_mem_I one_mem_I zero_le_one)]
      · rw [hkc.image_Icc_of_antitoneOn zero_le_one hanti.antitoneOn,
          uIcc_of_ge (hanti.antitoneOn zero_mem_I one_mem_I zero_le_one)]
    calc
      inv '' K = k '' I := by rw [← hgim, Set.image_image]; rfl
      _ = uIcc (k 0) (k 1) := hkimage
      _ = uIcc (inv p) (inv q) := by simp [k, Function.comp_def, hg0, hg1]
  have hAi := image_is_interval A hA hAC
  have hBi := image_is_interval B hB hBC
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ f '' (inv '' A) := by
      rw [image_inv A hAC]
      exact hx
    rw [hAi, ← hBi, image_inv B hBC] at hx'
    exact hx'
  · intro x hx
    have hx' : x ∈ f '' (inv '' B) := by
      rw [image_inv B hBC]
      exact hx
    rw [hBi, ← hAi, image_inv A hAC] at hx'
    exact hx'

/-- Every closed subarc of a polygonal arc is polygonal. -/
theorem IsArcBetween.isPolygonal_of_subset_arc {A C : Set Plane} {p q r s : Plane}
    (hA : IsArcBetween A p q) (hC : IsArcBetween C r s)
    (hpoly : IsPolygonal C) (hAC : A ⊆ C) : IsPolygonal A := by
  have hpq : p ≠ q := by
    obtain ⟨f, -, hi, -, h0, h1⟩ := hA
    intro hpq'
    exact zero_ne_one (hi zero_mem_I one_mem_I (by simpa [h0, h1] using hpq'))
  obtain ⟨vs, hvs, -, -, hsub, hvsArc⟩ :=
    exists_simple_poly_of_isPolygonal hpoly hC.isArc.isConnected.isPreconnected hpq
      (hAC hA.left_mem) (hAC hA.right_mem)
  have heq := hA.eq_of_subset_arc hvsArc hC hAC hsub
  exact ⟨vs, heq⟩

/-! ## Matching two named arcs -/

/-- A homeomorphism between two arcs, with the named endpoints matched in order.  The maps are
total functions because that is the shape needed by the split constructor; all inverse and
continuity assertions are restricted to the two arc carriers. -/
structure ArcHomeo (A B : Set Plane) (a b c d : Plane) where
  toFun : Plane → Plane
  invFun : Plane → Plane
  continuousOn_toFun : ContinuousOn toFun A
  continuousOn_invFun : ContinuousOn invFun B
  leftInvOn : LeftInvOn invFun toFun A
  rightInvOn : RightInvOn invFun toFun B
  image_eq : toFun '' A = B
  map_left : toFun a = c
  map_right : toFun b = d

namespace ArcHomeo

variable {A B : Set Plane} {a b c d : Plane}

theorem injOn (h : ArcHomeo A B a b c d) : InjOn h.toFun A := h.leftInvOn.injOn

theorem mapsTo (h : ArcHomeo A B a b c d) : MapsTo h.toFun A B := by
  intro x hx
  have hx' : h.toFun x ∈ h.toFun '' A := Set.mem_image_of_mem h.toFun hx
  simpa only [h.image_eq] using hx'

theorem mapsTo_invFun (h : ArcHomeo A B a b c d) : MapsTo h.invFun B A := by
  intro y hy
  rw [← h.image_eq] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [h.leftInvOn hx]
  exact hx

end ArcHomeo

/-- Any two named arcs admit an endpoint-preserving homeomorphism. -/
theorem exists_arcHomeo {A B : Set Plane} {a b c d : Plane}
    (hA : IsArcBetween A a b) (hB : IsArcBetween B c d) :
    Nonempty (ArcHomeo A B a b c d) := by
  classical
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  let fi : Plane → ℝ := Function.invFunOn f I
  let gi : Plane → ℝ := Function.invFunOn g I
  let toFun : Plane → Plane := g ∘ fi
  let invFun : Plane → Plane := f ∘ gi
  have hfiC : ContinuousOn fi A := by
    rw [← hfim]
    exact continuousOn_invFunOn_image' isCompact_I hfc hfi
  have hgiC : ContinuousOn gi B := by
    rw [← hgim]
    exact continuousOn_invFunOn_image' isCompact_I hgc hgi
  have hfiMap : MapsTo fi A I := by
    rw [← hfim]
    rintro _ ⟨t, ht, rfl⟩
    change Function.invFunOn f I (f t) ∈ I
    rw [hfi.leftInvOn_invFunOn ht]
    exact ht
  have hgiMap : MapsTo gi B I := by
    rw [← hgim]
    rintro _ ⟨t, ht, rfl⟩
    change Function.invFunOn g I (g t) ∈ I
    rw [hgi.leftInvOn_invFunOn ht]
    exact ht
  refine ⟨{
    toFun := toFun
    invFun := invFun
    continuousOn_toFun := hgc.comp hfiC hfiMap
    continuousOn_invFun := hfc.comp hgiC hgiMap
    leftInvOn := ?_
    rightInvOn := ?_
    image_eq := ?_
    map_left := ?_
    map_right := ?_
  }⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hfim ▸ hx
    simp [toFun, invFun, fi, gi, hfi.leftInvOn_invFunOn ht,
      hgi.leftInvOn_invFunOn ht]
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := hgim ▸ hy
    simp [toFun, invFun, fi, gi, hgi.leftInvOn_invFunOn ht,
      hfi.leftInvOn_invFunOn ht]
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hgim ▸ Set.mem_image_of_mem g (hfiMap hx)
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := hgim ▸ hy
      refine ⟨f t, hfim ▸ Set.mem_image_of_mem f ht, ?_⟩
      simp [toFun, fi, hfi.leftInvOn_invFunOn ht]
  · rw [← hf0, ← hg0]
    simp [toFun, fi, hfi.leftInvOn_invFunOn zero_mem_I]
  · rw [← hf1, ← hg1]
    simp [toFun, fi, hfi.leftInvOn_invFunOn one_mem_I]

/-! ## Transporting a plane drawing along an arc homeomorphism -/

end Schoenflies

open Schoenflies

namespace Graph

variable {β : Type*} {A B : Set Plane} {a b c d : Plane} {G : Graph Plane β}
  {drawing : β → ℝ → Plane}

/-- Apply the map of an arc homeomorphism to every edge parametrisation. -/
def mapDrawing (m : Schoenflies.ArcHomeo A B a b c d) (drawing : β → ℝ → Plane) :
    β → ℝ → Plane := fun e t => m.toFun (drawing e t)

theorem edgeArc_mapDrawing (m : Schoenflies.ArcHomeo A B a b c d) (e : β) :
    edgeArc (mapDrawing m drawing) e = m.toFun '' edgeArc drawing e := by
  rw [edgeArc, edgeArc, ← Set.image_comp]
  rfl

theorem pointSet_map_mapDrawing (m : Schoenflies.ArcHomeo A B a b c d) :
    pointSet (G.map m.toFun) (mapDrawing m drawing) = m.toFun '' pointSet G drawing := by
  rw [pointSet, pointSet, Graph.vertexSet_map, Graph.edgeSet_map, Set.image_union,
    Set.image_iUnion₂]
  congr 1
  exact Set.iUnion₂_congr fun e _ => edgeArc_mapDrawing m e

/-- A drawing whose whole point set is one arc transports along an arc homeomorphism. -/
theorem IsDrawing.map_arcHomeo (h : IsDrawing G drawing)
    (m : Schoenflies.ArcHomeo A B a b c d)
    (hpoint : pointSet G drawing = A) :
    IsDrawing (G.map m.toFun) (mapDrawing m drawing) where
  edge_param := by
    intro e he
    obtain ⟨hc, hi, hl⟩ := h.edge_param he
    have hedge : edgeArc drawing e ⊆ A := hpoint ▸ edgeArc_subset_pointSet he
    refine ⟨m.continuousOn_toFun.comp hc (fun t ht => hedge ⟨t, ht, rfl⟩), ?_, ?_⟩
    · intro s hs t ht hst
      exact hi hs ht (m.injOn (hedge ⟨s, hs, rfl⟩) (hedge ⟨t, ht, rfl⟩) hst)
    · exact hl.map m.toFun
  vertex_mem_edgeArc := by
    intro e x y v hlink hv hz
    rcases hlink with ⟨x', y', hxy, rfl, rfl⟩
    rw [Graph.vertexSet_map] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    rw [edgeArc_mapDrawing] at hz
    obtain ⟨z, hz, hmz⟩ := hz
    have hvA : v' ∈ A := hpoint ▸ vertexSet_subset_pointSet hv'
    have hzA : z ∈ A := hpoint ▸ edgeArc_subset_pointSet hxy.edge_mem hz
    have hvz : v' = z := m.injOn hvA hzA hmz.symm
    rcases h.vertex_mem_edgeArc hxy hv' (hvz ▸ hz) with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]
  edge_inter := by
    intro e f he hf hef p hpe hpf
    rw [Graph.edgeSet_map] at he hf
    rw [edgeArc_mapDrawing] at hpe hpf
    obtain ⟨x, hxe, hxp⟩ := hpe
    obtain ⟨y, hyf, hyp⟩ := hpf
    have hxA : x ∈ A := hpoint ▸ edgeArc_subset_pointSet he hxe
    have hyA : y ∈ A := hpoint ▸ edgeArc_subset_pointSet hf hyf
    have hxy : x = y := m.injOn hxA hyA (hxp.trans hyp.symm)
    subst y
    obtain ⟨hxV, hie, hif⟩ := h.edge_inter he hf hef hxe hyf
    subst p
    exact ⟨by rw [Graph.vertexSet_map]; exact ⟨x, hxV, rfl⟩,
      hie.map m.toFun, hif.map m.toFun⟩

end Graph
