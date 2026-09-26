/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.GluePathMatch
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueCrossDelta
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseDischarge
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PropThreeOpen

/-!
# Transport across a through-edge cut

A cut whose edge is a *through-edge* of the fragment -- both its
flags on the boundary -- carries no vertex data, so the colour and
vertex factors transport across the glue unchanged.  The two
transports here are what the colouring recursion needs at such a
cut.
-/

@[expose] public section

namespace RS



namespace EdgeSubset

open Fragment

/-! ## The shared participating context -/

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')
  (hpi : partnerSurvI hopen ∈ s')

/-- The glued edge subset. -/
local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairOpen i j hij hopen))

/-- The lifted edge subset. -/
local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc : EdgeSubset W)

/-! ## The even-colouring layer (participating, any configuration) -/

/-- Finset-supported multisets map equally along a bijection of
their supports. -/
theorem multiset_map_eq_of_bijT {γ δ X : Type _}
    (s : Finset γ) (t : Finset δ)
    (e : δ → γ) (hinj : Function.Injective e)
    (hmem : ∀ y, y ∈ t ↔ e y ∈ s)
    (hsurj : ∀ x ∈ s, ∃ y, e y = x)
    (g : γ → X) (g' : δ → X)
    (hg : ∀ y ∈ t, g (e y) = g' y) :
    s.val.map g = t.val.map g' := by
  have hset : s = t.map ⟨e, hinj⟩ := by
    ext x
    rw [Finset.mem_map]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hsurj x hx
      exact ⟨y, (hmem y).mpr hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mp hy
  rw [hset,
    show (t.map ⟨e, hinj⟩).val = t.val.map e from rfl,
    Multiset.map_map]
  refine Multiset.map_congr rfl ?_
  intro y hy
  exact hg y (Finset.mem_val.mp hy)

/-- The even colour multiset agrees (participating case). -/
theorem evenColoursAt_transport_T
    [LinearOrder α]
    {k : ℕ}
    (ψW : (Fl).EvenColouring k) (ψ' : (Fg).EvenColouring k)
    (hψ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∉ liftSubsetOpen hopen s') (h2 : g ∉ s'),
      ψW.val ⟨g.val, h1⟩ = ψ'.val ⟨g, h2⟩)
    (v : W.Vertex) :
    (Fl).evenColoursAt ψW v = (Fg).evenColoursAt ψ' v := by
  have hemb : ∀ x : {f' : (W.gluePairOpen i j hij hopen).Flag //
      f' ∉ (Fg).flags},
      x.val.val ∉ (Fl).flags := by
    intro x hmem
    exact x.prop ((surviving_val_mem_liftOpen_iff hopen s'
      x.val).mp hmem)
  have hinj : Function.Injective
      (fun x : {f' : (W.gluePairOpen i j hij hopen).Flag //
          f' ∉ (Fg).flags} =>
        (⟨x.val.val, hemb x⟩ : {f : W.Flag // f ∉ (Fl).flags}))
      := by
    intro x y hxy
    have hxy' : (⟨x.val.val, hemb x⟩ :
        {f : W.Flag // f ∉ (Fl).flags}) = ⟨y.val.val, hemb y⟩ :=
      hxy
    have hval : x.val.val = y.val.val := congrArg
      (fun z : {f : W.Flag // f ∉ (Fl).flags} => z.val) hxy'
    exact Subtype.ext (Subtype.ext hval)
  unfold EdgeSubset.evenColoursAt
  refine multiset_map_eq_of_bijT _ _
    (fun x => ⟨x.val.val, hemb x⟩) hinj ?_ ?_ ψW.val ψ'.val ?_
  · intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact glueAttach_inl_iff y.val v
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hsurv := vertex_flag_surviving (i := i) (j := j)
      x.val v hx
    have hnot : (⟨x.val, hsurv.1, hsurv.2⟩ :
        SurvivingFlag W i j) ∉ s' := by
      intro hmem
      exact x.prop ((surviving_val_mem_liftOpen_iff hopen s'
        ⟨x.val, hsurv.1, hsurv.2⟩).mpr hmem)
    exact ⟨⟨⟨x.val, hsurv.1, hsurv.2⟩, hnot⟩, Subtype.ext rfl⟩
  · intro y _
    exact hψ y.val (hemb y) y.prop

section VertexTransport

variable
  (κ' : (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairOpen i j hij hopen)).RelTransitionSystem)
  (o' : κ'.Orientation)

local notation "κW" =>
  RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ'

local notation "oW" =>
  unglueOrientationOpen hij hopen s' hc' hc κ' o'

/-- **The vertex factor transport (participating case).** -/
theorem vertexFactor_transport_T
    [LinearOrder α]
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (ψW : (Fl).EvenColouring k) (ψ' : (Fg).EvenColouring k)
    (hψ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∉ liftSubsetOpen hopen s') (h2 : g ∉ s'),
      ψW.val ⟨g.val, h1⟩ = ψ'.val ⟨g, h2⟩)
    (φW : (Fl).CoreOddColouring ℓ) (φ' : (Fg).CoreOddColouring ℓ)
    (hφ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∈ (Fl).coreFlags) (h2 : g ∈ (Fg).coreFlags),
      φW.val ⟨g.val, h1⟩ = φ'.val ⟨g, h2⟩)
    (v : W.Vertex) :
    ((Fl).coreOddSignAt (oW) φW v : ℂ) *
      h.evalOdd ((Fl).evenColoursAt ψW v)
        ((Fl).coreOddListAt (oW) φW v) =
    ((Fg).coreOddSignAt o' φ' v : ℂ) *
      h.evalOdd ((Fg).evenColoursAt ψ' v)
        ((Fg).coreOddListAt o' φ' v) := by
  rw [coreOddSignAt_transport_open hij hopen s' hc' hc κ' o'
      φW φ' hφ v,
    evenColoursAt_transport_T hij hopen s' hc' hc ψW ψ' hψ v,
    evalOdd_coreOddListAt_transport_open hij hopen s' hc' hc
      κ' o' h φW φ' hφ ((Fg).evenColoursAt ψ' v) v]

end VertexTransport

end EdgeSubset

end RS
