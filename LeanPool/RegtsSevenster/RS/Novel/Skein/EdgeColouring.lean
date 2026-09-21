/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.VertexSum
import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordLabels

/-!
# Colourings of the whole subset

RS21 colours every edge of the Eulerian subset: `φ : H → [2ℓ]`.
The edges of `H` with an end at an unlabelled vertex are the ones
the vertex product sees; the edges with both ends labelled are seen
only by the boundary vectors.  Both kinds are coloured, and the
colouring is one object.

This file is that object, and its restriction to the edges the
vertex product sees.  The restriction is a map between colouring
types, stated here so that the split the flag model makes is a
theorem about `EdgeOddColouring` rather than a definition in its
own right.
-/

namespace RS

namespace EdgeSubset

open Classical

variable {α : Type}

/-- **RS21's odd colouring**: a colour on every edge of the subset,
constant on the two flags of an edge. -/
def EdgeOddColouring {W : Fragment α}
    (F : EdgeSubset W) (ℓ : ℕ) : Type :=
  {φ : {f : W.Flag // f ∈ F.flags} → Fin (2 * ℓ) //
    ∀ f : {f : W.Flag // f ∈ F.flags},
      φ ⟨W.pairing f.val, F.pairing_mem f.val f.prop⟩ = φ f}

open scoped Classical in
/-- Edge odd colourings are finite in number. -/
noncomputable instance EdgeOddColouring.instFintype {W : Fragment α}
    (F : EdgeSubset W) (ℓ : ℕ) : Fintype (F.EdgeOddColouring ℓ) := by
  unfold EdgeOddColouring
  infer_instance

/-- The colouring restricted to the edges with an end at a vertex —
the ones the vertex product reads. -/
noncomputable def EdgeOddColouring.core {W : Fragment α}
    {F : EdgeSubset W} {ℓ : ℕ}
    (φ : F.EdgeOddColouring ℓ) : F.CoreOddColouring ℓ :=
  ⟨fun f => φ.val ⟨f.val, coreFlags_subset F f.prop⟩,
   fun f => φ.prop ⟨f.val, coreFlags_subset F f.prop⟩⟩

/-- **The colour of an edge is the colour of either of its
flags.** -/
theorem EdgeOddColouring.pairing {W : Fragment α}
    {F : EdgeSubset W} {ℓ : ℕ}
    (φ : F.EdgeOddColouring ℓ) (f : {f : W.Flag // f ∈ F.flags}) :
    φ.val ⟨W.pairing f.val, F.pairing_mem f.val f.prop⟩ = φ.val f :=
  φ.prop f

/-- **The boundary constraint** `φ ∼ χ₁`: at a used label the
colouring agrees with the state. -/
def edgeOddBoundaryMatch {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (st : GenBoundaryState k ℓ α) (φ : F.EdgeOddColouring ℓ) :
    Prop :=
  ∀ (i : α) (c : Fin (2 * ℓ)) (_ : st i = Sum.inr c)
    (hmem : W.boundaryFlag i ∈ F.flags),
    φ.val ⟨W.boundaryFlag i, hmem⟩ = c

/-! ### The colour a used flag is pinned to

On the support of the state every used label is odd, so a boundary
flag of the subset has a colour, and `φ ∼ χ₁` pins the colouring to
it.  Naming that colour is what lets a core colouring be extended
back over the through-edges.
-/

open Classical in
/-- The odd colour the state carries at a boundary flag of the
subset. -/
noncomputable def usedColour {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (χ : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags χ) {f : W.Flag}
    (hb : f ∈ F.boundaryFlags) : Fin (2 * ℓ) :=
  Classical.choose ((hbnd (F.boundaryLabel hb)).mp (by
    rw [boundaryFlag_boundaryLabel hb]
    exact mem_flags_of_boundaryFlags F hb))

open Classical in
/-- The named colour is the state's. -/
theorem usedColour_spec {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (χ : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags χ) {f : W.Flag}
    (hb : f ∈ F.boundaryFlags) :
    χ (F.boundaryLabel hb) = Sum.inr (usedColour F χ hbnd hb) :=
  Classical.choose_spec ((hbnd (F.boundaryLabel hb)).mp (by
    rw [boundaryFlag_boundaryLabel hb]
    exact mem_flags_of_boundaryFlags F hb))

open Classical in
/-- **A matching colouring takes the named colour at every used
flag.** -/
theorem edgeOddColouring_eq_usedColour {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    {φ : F.EdgeOddColouring ℓ} (hφ : edgeOddBoundaryMatch F χ φ)
    {f : W.Flag} (hb : f ∈ F.boundaryFlags) :
    φ.val ⟨f, mem_flags_of_boundaryFlags F hb⟩
      = usedColour F χ hbnd hb := by
  have hbf := boundaryFlag_boundaryLabel hb
  have hmem : W.boundaryFlag (F.boundaryLabel hb) ∈ F.flags := by
    rw [hbf]
    exact mem_flags_of_boundaryFlags F hb
  have h1 := hφ (F.boundaryLabel hb) (usedColour F χ hbnd hb)
    (usedColour_spec F χ hbnd hb) hmem
  rw [← h1]
  exact congrArg φ.val (Subtype.ext hbf.symm)

/-! ### The restriction is injective on matching colourings

Every flag of the subset either has an end at a vertex — and is
then read by the restriction — or has both ends labelled, and is
then pinned by `φ ∼ χ₁`.  So two matching colourings with the same
restriction agree.
-/

/-- A flag the restriction forgets is a boundary flag. -/
theorem mem_boundaryFlags_of_not_coreFlags {W : Fragment α}
    (F : EdgeSubset W)
    {f : W.Flag} (hf : f ∈ F.flags) (hc : f ∉ F.coreFlags) :
    f ∈ F.boundaryFlags := by
  refine (mem_internalFlags_or_boundaryFlags F hf).resolve_left ?_
  intro hint
  refine hc (mem_coreFlags_iff F |>.mpr ⟨hf, Or.inl ?_⟩)
  obtain ⟨-, v, hv⟩ := EdgeSubset.mem_internalFlags_iff.mp hint
  exact ⟨v, hv⟩

open Classical in
/-- **Two matching colourings with the same restriction are
equal.** -/
theorem edgeOddColouring_ext {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    {φ₁ φ₂ : F.EdgeOddColouring ℓ}
    (h₁ : edgeOddBoundaryMatch F χ φ₁)
    (h₂ : edgeOddBoundaryMatch F χ φ₂)
    (hcore : φ₁.core = φ₂.core) : φ₁ = φ₂ := by
  refine Subtype.ext (funext fun f => ?_)
  by_cases hc : f.val ∈ F.coreFlags
  · have h := congrArg Subtype.val hcore
    have hf := congrFun h ⟨f.val, hc⟩
    have he : (⟨f.val, coreFlags_subset F hc⟩ :
        {g : W.Flag // g ∈ F.flags}) = f := Subtype.ext rfl
    rw [← he]
    exact hf
  · have hb := mem_boundaryFlags_of_not_coreFlags F f.prop hc
    have e₁ := edgeOddColouring_eq_usedColour hbnd h₁ hb
    have e₂ := edgeOddColouring_eq_usedColour hbnd h₂ hb
    have hfe : (⟨f.val, mem_flags_of_boundaryFlags F hb⟩ :
        {g : W.Flag // g ∈ F.flags}) = f := Subtype.ext rfl
    rw [hfe] at e₁ e₂
    rw [e₁, e₂]

/-! ### Extending a core colouring over the through-edges

A core colouring is extended by giving each through-edge the colour
the state already carries at its two labelled ends.  That is well
defined exactly because those two ends agree, which is what `φ ∼ χ₁`
forces of any colouring of the whole subset.
-/

/-- The flags the restriction forgets are closed under the
pairing. -/
theorem not_coreFlags_pairing {W : Fragment α}
    (F : EdgeSubset W) {f : W.Flag}
    (hf : f ∈ F.flags) (hc : f ∉ F.coreFlags) :
    W.pairing f ∉ F.coreFlags := by
  intro hx
  refine hc ((mem_coreFlags_iff F).mpr ⟨hf, ?_⟩)
  obtain ⟨-, hd⟩ := (mem_coreFlags_iff F).mp hx
  rcases hd with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact Or.inr ⟨v, hv⟩
  · rw [W.pairing_invol] at hv
    exact Or.inl ⟨v, hv⟩

/-- **The agreement condition**: at a through-edge the state's two
legs carry one colour. -/
def ThroughAgree {W : Fragment α}
    {k ℓ : ℕ} (F : EdgeSubset W)
    (χ : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags χ) : Prop :=
  ∀ (f : W.Flag) (hb : f ∈ F.boundaryFlags)
    (hbp : W.pairing f ∈ F.boundaryFlags),
    usedColour F χ hbnd hbp = usedColour F χ hbnd hb

/-- Agreement reads only the state. -/
theorem throughAgree_congr {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ χ' : GenBoundaryState k ℓ α} (hcc : χ = χ')
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (hbnd' : genBoundarySubsetMatches W F.flags χ') :
    ThroughAgree F χ hbnd ↔ ThroughAgree F χ' hbnd' := by
  subst hcc
  exact Iff.rfl

/-- The named colour reads only the state's value at the label. -/
theorem usedColour_congr {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ χ' : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (hbnd' : genBoundarySubsetMatches W F.flags χ')
    {f : W.Flag} (hb : f ∈ F.boundaryFlags)
    (heq : χ (F.boundaryLabel hb) = χ' (F.boundaryLabel hb)) :
    usedColour F χ hbnd hb = usedColour F χ' hbnd' hb := by
  have h1 := usedColour_spec F χ hbnd hb
  have h2 := usedColour_spec F χ' hbnd' hb
  rw [heq, h2] at h1
  exact (Sum.inr.inj h1).symm

/-- **Agreement reads only the through-edges' labels.**  Two states
that agree there agree on the condition. -/
theorem throughAgree_of_eq_on_through {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ χ' : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (hbnd' : genBoundarySubsetMatches W F.flags χ')
    (heq : ∀ (f : W.Flag) (hb : f ∈ F.boundaryFlags),
      W.pairing f ∈ F.boundaryFlags →
      χ (F.boundaryLabel hb) = χ' (F.boundaryLabel hb))
    (hag : ThroughAgree F χ hbnd) : ThroughAgree F χ' hbnd' := by
  intro f hb hbp
  have hpp : W.pairing (W.pairing f) ∈ F.boundaryFlags := by
    rw [W.pairing_invol]; exact hb
  rw [← usedColour_congr hbnd hbnd' hbp (heq _ hbp hpp),
    ← usedColour_congr hbnd hbnd' hb (heq f hb hbp)]
  exact hag f hb hbp

/-- **Only agreeing states are coloured at all.**  A colouring of
the whole subset carries one colour on each edge, and `φ ∼ χ₁` pins
it at both labelled ends of a through-edge; so a state whose two
legs there disagree admits no colouring. -/
theorem throughAgree_of_edgeOddBoundaryMatch {W : Fragment α}
    {k ℓ : ℕ}
    {F : EdgeSubset W} {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    {φ : F.EdgeOddColouring ℓ} (hφ : edgeOddBoundaryMatch F χ φ) :
    ThroughAgree F χ hbnd := by
  intro f hb hbp
  have hbf : W.boundaryFlag (F.boundaryLabel hb) = f :=
    boundaryFlag_boundaryLabel hb
  have hbf' : W.boundaryFlag (F.boundaryLabel hbp) = W.pairing f :=
    boundaryFlag_boundaryLabel hbp
  have hmi : W.boundaryFlag (F.boundaryLabel hb) ∈ F.flags := by
    rw [hbf]; exact mem_flags_of_boundaryFlags F hb
  have hmj : W.boundaryFlag (F.boundaryLabel hbp) ∈ F.flags := by
    rw [hbf']; exact mem_flags_of_boundaryFlags F hbp
  have h1 : φ.val ⟨W.boundaryFlag (F.boundaryLabel hb), hmi⟩
      = usedColour F χ hbnd hb :=
    hφ _ _ (usedColour_spec F χ hbnd hb) hmi
  have h2 : φ.val ⟨W.boundaryFlag (F.boundaryLabel hbp), hmj⟩
      = usedColour F χ hbnd hbp :=
    hφ _ _ (usedColour_spec F χ hbnd hbp) hmj
  have heq : (⟨W.boundaryFlag (F.boundaryLabel hbp), hmj⟩ :
        {g : W.Flag // g ∈ F.flags})
      = ⟨W.pairing (W.boundaryFlag (F.boundaryLabel hb)),
          F.pairing_mem _ hmi⟩ :=
    Subtype.ext (show W.boundaryFlag (F.boundaryLabel hbp)
        = W.pairing (W.boundaryFlag (F.boundaryLabel hb)) by
      rw [hbf', hbf])
  rw [← h1, ← h2, heq]
  exact φ.prop ⟨W.boundaryFlag (F.boundaryLabel hb), hmi⟩

open Classical in
/-- The extension's value: the core colouring where it is defined,
and the state's own colour on a through-edge. -/
noncomputable def extendFun {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (φ' : F.CoreOddColouring ℓ) :
    {f : W.Flag // f ∈ F.flags} → Fin (2 * ℓ) :=
  fun f =>
    if hc : f.val ∈ F.coreFlags then φ'.val ⟨f.val, hc⟩
    else usedColour F χ hbnd
      (mem_boundaryFlags_of_not_coreFlags F f.prop hc)

open Classical in
/-- The extension is constant on the two flags of an edge. -/
theorem extendFun_pairing {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (hag : ThroughAgree F χ hbnd) (φ' : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.flags}) :
    extendFun hbnd φ' ⟨W.pairing f.val, F.pairing_mem f.val f.prop⟩
      = extendFun hbnd φ' f := by
  unfold extendFun
  by_cases hc : f.val ∈ F.coreFlags
  · rw [dif_pos hc, dif_pos (F.pairing_mem_coreFlags hc)]
    exact φ'.prop ⟨f.val, hc⟩
  · rw [dif_neg hc, dif_neg (not_coreFlags_pairing F f.prop hc)]
    exact hag f.val _ _

open Classical in
/-- **Extend a core colouring over the through-edges.** -/
noncomputable def CoreOddColouring.extend {W : Fragment α}
    {k ℓ : ℕ}
    {F : EdgeSubset W} {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (hag : ThroughAgree F χ hbnd) (φ' : F.CoreOddColouring ℓ) :
    F.EdgeOddColouring ℓ :=
  ⟨extendFun hbnd φ', extendFun_pairing hbnd hag φ'⟩

open Classical in
/-- **The extension restricts to what it extended.** -/
theorem CoreOddColouring.core_extend {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (hag : ThroughAgree F χ hbnd) (φ' : F.CoreOddColouring ℓ) :
    (CoreOddColouring.extend hbnd hag φ').core = φ' := by
  refine Subtype.ext (funext fun f => ?_)
  show extendFun hbnd φ' ⟨f.val, coreFlags_subset F f.prop⟩
    = φ'.val f
  unfold extendFun
  rw [dif_pos f.prop]

/-- A matching colouring restricts to a matching core colouring. -/
theorem coreOddBoundaryMatch_core {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ : GenBoundaryState k ℓ α} {φ : F.EdgeOddColouring ℓ}
    (hφ : edgeOddBoundaryMatch F χ φ) :
    F.coreOddBoundaryMatch χ φ.core := by
  intro i c hci hcore
  exact hφ i c hci (coreFlags_subset F hcore)

/-! ### The round trip

The extension of a matching core colouring matches, and extending
a matching colouring's restriction returns it.  With injectivity
this makes the restriction a bijection between the matching
colourings of the whole subset and those of its core.
-/

open Classical in
/-- **The extension matches the state.** -/
theorem edgeOddBoundaryMatch_extend {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (hag : ThroughAgree F χ hbnd) {φ' : F.CoreOddColouring ℓ}
    (hφ' : F.coreOddBoundaryMatch χ φ') :
    edgeOddBoundaryMatch F χ
      (CoreOddColouring.extend hbnd hag φ') := by
  intro i c hci hmem
  show extendFun hbnd φ' ⟨W.boundaryFlag i, hmem⟩ = c
  unfold extendFun
  by_cases hc : W.boundaryFlag i ∈ F.coreFlags
  · rw [dif_pos hc]
    exact hφ' i c hci hc
  · rw [dif_neg hc]
    have hb := mem_boundaryFlags_of_not_coreFlags F hmem hc
    have hli : F.boundaryLabel hb = i :=
      boundaryLabel_eq_of_attach hb (W.attach_boundaryFlag i)
    have hspec := usedColour_spec F χ hbnd hb
    rw [hli, hci] at hspec
    exact (Sum.inr.inj hspec).symm

open Classical in
/-- **Extending a matching colouring's restriction returns it.** -/
theorem extend_core {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (hag : ThroughAgree F χ hbnd) {φ : F.EdgeOddColouring ℓ}
    (hφ : edgeOddBoundaryMatch F χ φ) :
    CoreOddColouring.extend hbnd hag φ.core = φ := by
  refine edgeOddColouring_ext hbnd ?_ hφ ?_
  · exact edgeOddBoundaryMatch_extend hbnd hag
      (coreOddBoundaryMatch_core hφ)
  · exact CoreOddColouring.core_extend hbnd hag φ.core

/-! ### The sum over colourings of the whole subset

The restriction being a bijection on the matching colourings, a sum
over RS21's colourings of all of `H` is a sum over the flag model's
colourings of its core.  This is the theorem the flag model's split
rests on; nothing above it assumes the split.
-/

open Classical in
/-- **The colouring sum over the whole subset is the sum over its
core.** -/
theorem sum_edgeOddColouring {W : Fragment α}
    {k ℓ : ℕ} {F : EdgeSubset W}
    {χ : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags χ)
    (hag : ThroughAgree F χ hbnd) (G : F.CoreOddColouring ℓ → ℂ) :
    (∑ φ : F.EdgeOddColouring ℓ,
        if edgeOddBoundaryMatch F χ φ then G φ.core else 0)
      = ∑ φ' : F.CoreOddColouring ℓ,
          if F.coreOddBoundaryMatch χ φ' then G φ' else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun φ => φ.core)
    (fun φ' => CoreOddColouring.extend hbnd hag φ') ?_ ?_ ?_ ?_
    ?_
  · intro φ hφ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      coreOddBoundaryMatch_core (Finset.mem_filter.mp hφ).2⟩
  · intro φ' hφ'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      edgeOddBoundaryMatch_extend hbnd hag
        (Finset.mem_filter.mp hφ').2⟩
  · intro φ hφ
    exact extend_core hbnd hag (Finset.mem_filter.mp hφ).2
  · intro φ' _
    exact CoreOddColouring.core_extend hbnd hag φ'
  · intro φ _
    rfl

end EdgeSubset

end RS
