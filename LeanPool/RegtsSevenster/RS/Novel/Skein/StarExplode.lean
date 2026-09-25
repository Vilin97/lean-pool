/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueFold
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConnectionRank

/-!
# Exploding a closed fragment into stars

The accompanying paper's "stars and closed graphs" (§3.2): a closed
fragment
is its own star union, reglued along the edge matching.  The
explosion is parameterized by a pairing-closed set `C` of cut
flags: each cut flag's edge is severed, the freed half-edge
becoming a pendant boundary edge of its vertex's star.  At
`C = ∅` the explosion is the fragment itself; at `C = univ` it is
the disjoint union of vertex stars.  Regluing shrinks `C` one
edge at a time (`explodeAtGluePair`, next file), giving the star
decomposition by induction.
-/

@[expose] public section

namespace RS

/-- The vertex of a flag in a closed fragment. -/
def ClosedFragment.vertexOf (W : ClosedFragment) (f : W.Flag) :
    W.Vertex :=
  (W.attach f).elim id Fin.elim0

/-- Every flag of a closed fragment attaches to its vertex. -/
theorem ClosedFragment.attach_eq_vertexOf (W : ClosedFragment)
    (f : W.Flag) :
    W.attach f = Sum.inl (ClosedFragment.vertexOf W f) := by
  unfold ClosedFragment.vertexOf
  rcases h : W.attach f with v | ℓ
  · rfl
  · exact Fin.elim0 ℓ

/-- A pairing-closed cut set: with each flag, its partner. -/
def CutClosed (W : ClosedFragment) (C : Finset W.Flag) : Prop :=
  ∀ f ∈ C, W.pairing f ∈ C

/-- Membership of the partner, from cut closure. -/
theorem CutClosed.pairing_mem {W : ClosedFragment}
    {C : Finset W.Flag} (hC : CutClosed W C) {f : W.Flag} :
    W.pairing f ∈ C ↔ f ∈ C :=
  ⟨fun h => W.pairing_invol f ▸ hC _ h, fun h => hC f h⟩

/-- **The explosion at a cut set**: sever each cut flag's edge,
the freed half-edge becoming a pendant boundary edge labelled by
the cut flag itself. -/
def explodeAt (W : ClosedFragment) (C : Finset W.Flag)
    (hC : CutClosed W C) : Fragment {f : W.Flag // f ∈ C} where
  Flag := W.Flag ⊕ {f : W.Flag // f ∈ C}
  Vertex := W.Vertex
  attach := fun g =>
    match g with
    | Sum.inl f => Sum.inl (ClosedFragment.vertexOf W f)
    | Sum.inr s => Sum.inr s
  pairing := fun g =>
    match g with
    | Sum.inl f =>
        if h : f ∈ C then Sum.inr ⟨f, h⟩
        else Sum.inl (W.pairing f)
    | Sum.inr s => Sum.inl s.val
  pairing_invol := fun g => by
    rcases g with f | s
    · by_cases h : f ∈ C
      · simp only [dite_eq_left h]
      · simp only [dite_eq_right h,
          dite_eq_right (fun hp => h (hC.pairing_mem.mp hp)),
          W.pairing_invol]
    · simp only [dite_eq_left s.prop]
  pairing_ne := fun g h => by
    rcases g with f | s
    · have h' : (if h' : f ∈ C then
          (Sum.inr ⟨f, h'⟩ : W.Flag ⊕ {f : W.Flag // f ∈ C})
          else Sum.inl (W.pairing f)) = Sum.inl f := h
      by_cases hf : f ∈ C
      · rw [dite_eq_left hf] at h'
        exact Sum.inr_ne_inl h'
      · rw [dite_eq_right hf] at h'
        exact W.pairing_ne f (Sum.inl.inj h')
    · exact Sum.inl_ne_inr h
  boundaryFlag := fun s => Sum.inr s
  attach_boundaryFlag := fun s => rfl
  eq_boundaryFlag := fun s g h => by
    rcases g with f | s'
    · exact absurd h (by simp)
    · exact congrArg Sum.inr (Sum.inr.inj h)
  circles := W.circles

/-! ### One regluing step -/

section GlueStep

variable (W : ClosedFragment) (C : Finset W.Flag)
  (hC : CutClosed W C) (f₀ : W.Flag) (h₀ : f₀ ∈ C)

/-- The shrunken cut set: the edge of `f₀` restored. -/
def cutErase : Finset W.Flag :=
  (C.erase f₀).erase (W.pairing f₀)

/-- Erasing one edge from the cut set removes exactly its two
flags. -/
theorem mem_cutErase {g : W.Flag} :
    g ∈ cutErase W C f₀ ↔
      g ∈ C ∧ g ≠ f₀ ∧ g ≠ W.pairing f₀ := by
  unfold cutErase
  simp only [Finset.mem_erase]
  tauto

include hC in
/-- The erased set is still pairing-closed, so the explosion
recurses. -/
theorem cutErase_closed : CutClosed W (cutErase W C f₀) := by
  intro g hg
  rw [mem_cutErase] at hg ⊢
  refine ⟨hC g hg.1, ?_, ?_⟩
  · intro h
    exact hg.2.2 (by rw [← W.pairing_invol g, h])
  · intro h
    exact hg.2.1 (by rw [← W.pairing_invol g, h, W.pairing_invol])

/-- The glued labels of the step, as labels of the explosion. -/
def stepLabelI : {f : W.Flag // f ∈ C} := ⟨f₀, h₀⟩

/-- The partner label of the step. -/
def stepLabelJ : {f : W.Flag // f ∈ C} :=
  ⟨W.pairing f₀, hC f₀ h₀⟩

/-- The two labels the severed edge creates are distinct. -/
theorem stepLabel_ne : stepLabelI W C f₀ h₀ ≠
    stepLabelJ W C hC f₀ h₀ := fun h =>
  W.pairing_ne f₀ (congrArg Subtype.val h).symm

/-- The surviving labels of the step are the shrunken cut set. -/
def stepLabelEquiv :
    {f : W.Flag // f ∈ cutErase W C f₀} ≃
      Fragment.SurvivingLabel {f : W.Flag // f ∈ C}
        (stepLabelI W C f₀ h₀) (stepLabelJ W C hC f₀ h₀) where
  toFun s :=
    ⟨⟨s.val, ((mem_cutErase W C f₀).mp s.prop).1⟩,
      fun h => ((mem_cutErase W C f₀).mp s.prop).2.1
        (congrArg Subtype.val h),
      fun h => ((mem_cutErase W C f₀).mp s.prop).2.2
        (congrArg Subtype.val h)⟩
  invFun t :=
    ⟨t.val.val, (mem_cutErase W C f₀).mpr
      ⟨t.val.prop,
        fun h => t.prop.1 (Subtype.ext h),
        fun h => t.prop.2 (Subtype.ext h)⟩⟩
  left_inv _s := Subtype.ext rfl
  right_inv _t := Subtype.ext (Subtype.ext rfl)

/-- The surviving flags of the step are the flags of the smaller
explosion. -/
def stepFlagEquiv :
    Fragment.SurvivingFlag (explodeAt W C hC)
        (stepLabelI W C f₀ h₀) (stepLabelJ W C hC f₀ h₀) ≃
      (W.Flag ⊕ {f : W.Flag // f ∈ cutErase W C f₀}) where
  toFun g :=
    match g with
    | ⟨Sum.inl f, _⟩ => Sum.inl f
    | ⟨Sum.inr s, hs⟩ =>
        Sum.inr ⟨s.val, (mem_cutErase W C f₀).mpr
          ⟨s.prop,
            fun h => hs.1 (congrArg Sum.inr (Subtype.ext h)),
            fun h => hs.2 (congrArg Sum.inr (Subtype.ext h))⟩⟩
  invFun g :=
    match g with
    | Sum.inl f =>
        ⟨Sum.inl f, Sum.inl_ne_inr, Sum.inl_ne_inr⟩
    | Sum.inr s' =>
        ⟨Sum.inr ⟨s'.val,
            ((mem_cutErase W C f₀).mp s'.prop).1⟩,
          fun h => ((mem_cutErase W C f₀).mp s'.prop).2.1
            (congrArg Subtype.val (Sum.inr.inj h)),
          fun h => ((mem_cutErase W C f₀).mp s'.prop).2.2
            (congrArg Subtype.val (Sum.inr.inj h))⟩
  left_inv g := by
    obtain ⟨gv, hg⟩ := g
    rcases gv with f | s
    · rfl
    · exact Subtype.ext (congrArg Sum.inr (Subtype.ext rfl))
  right_inv g := by
    rcases g with f | s'
    · rfl
    · exact congrArg Sum.inr (Subtype.ext rfl)

private theorem explodeAt_rewire_pairing
    (hopen : (explodeAt W C hC).pairing
      ((explodeAt W C hC).boundaryFlag (stepLabelI W C f₀ h₀)) ≠
      (explodeAt W C hC).boundaryFlag (stepLabelJ W C hC f₀ h₀))
    (g : Fragment.SurvivingFlag (explodeAt W C hC)
      (stepLabelI W C f₀ h₀) (stepLabelJ W C hC f₀ h₀)) :
    stepFlagEquiv W C hC f₀ h₀ (Fragment.rewire hopen g) =
      (explodeAt W (cutErase W C f₀) (cutErase_closed W C hC f₀)).pairing
        (stepFlagEquiv W C hC f₀ h₀ g) := by
  obtain ⟨gv, hg⟩ := g
  rcases gv with f | s
  · -- ═══════ An old flag: case-split on the rewire ═══════
    change (stepFlagEquiv W C hC f₀ h₀)
      (Fragment.rewire hopen ⟨Sum.inl f, hg⟩) =
      ((explodeAt W (cutErase W C f₀) (cutErase_closed W C hC f₀)).relabel
        (stepLabelEquiv W C hC f₀ h₀)).pairing
      ((stepFlagEquiv W C hC f₀ h₀) ⟨Sum.inl f, hg⟩)
    unfold Fragment.rewire
    split
    · -- first branch: partner = boundary i → f = f₀
      rename_i h
      have h' : (if hf : f ∈ C then
          (Sum.inr ⟨f, hf⟩ : W.Flag ⊕ {f : W.Flag // f ∈ C})
          else Sum.inl (W.pairing f)) =
          Sum.inr ⟨f₀, h₀⟩ := h
      by_cases hf : f ∈ C
      · rw [dite_eq_left hf] at h'
        have feq : f = f₀ :=
          congrArg Subtype.val (Sum.inr.inj h')
        -- LHS: rewire first branch gives ⟨Sum.inl (W.pairing f₀), _⟩;
        --   stepFlagEquiv maps this to Sum.inl (W.pairing f₀).
        -- RHS: stepFlagEquiv sends ⟨Sum.inl f, _⟩ to Sum.inl f;
        --   the smaller explosion's pairing at Sum.inl f, with
        --   f ∉ cutErase (since f = f₀), gives Sum.inl (W.pairing f).
        -- Both sides = Sum.inl (W.pairing f₀) via feq.
        have hne : f ∉ cutErase W C f₀ := by
          rw [mem_cutErase, feq]; tauto
        -- Expose the dite on the RHS
        have hrhs : (if h'' : f ∈ cutErase W C f₀ then
            (Sum.inr ⟨f, h''⟩ :
              W.Flag ⊕ {g : W.Flag // g ∈ cutErase W C f₀})
            else Sum.inl (W.pairing f)) =
            Sum.inl (W.pairing f) := dite_eq_right hne
        simp only [feq]
        -- LHS: stepFlagEquiv ⟨Sum.inl (W.pairing f₀), _⟩ = Sum.inl
        --   (W.pairing f₀)
        -- RHS: (relabel ...).pairing (Sum.inl f₀) = dite(f₀ ∈
        --   cutErase...)
        -- f₀ ∉ cutErase so dite resolves to Sum.inl (W.pairing f₀)
        have hne₀ : f₀ ∉ cutErase W C f₀ :=
          fun hm => ((mem_cutErase W C f₀).mp hm).2.1 rfl
        change (Sum.inl (W.pairing f₀) :
              W.Flag ⊕ {g : W.Flag // g ∈ cutErase W C f₀}) =
          (if h'' : f₀ ∈ cutErase W C f₀ then
            (Sum.inr ⟨f₀, h''⟩ :
              W.Flag ⊕ {g : W.Flag // g ∈ cutErase W C f₀})
            else Sum.inl (W.pairing f₀))
        rw [dite_eq_right hne₀]
      · rw [dite_eq_right hf] at h'
        exact absurd h' Sum.inl_ne_inr
    · split
      · -- second branch: partner = boundary j → f = W.pairing f₀
        rename_i hni h
        have h' : (if hf : f ∈ C then
            (Sum.inr ⟨f, hf⟩ : W.Flag ⊕ {f : W.Flag // f ∈ C})
            else Sum.inl (W.pairing f)) =
            Sum.inr ⟨W.pairing f₀, hC f₀ h₀⟩ := h
        by_cases hf : f ∈ C
        · rw [dite_eq_left hf] at h'
          have feq : f = W.pairing f₀ :=
            congrArg Subtype.val (Sum.inr.inj h')
          -- Rewire second branch gives ⟨Sum.inl f₀, _⟩;
          -- stepFlagEquiv maps to Sum.inl f₀.
          -- RHS: stepFlagEquiv sends ⟨Sum.inl f, _⟩ to Sum.inl f =
          --   Sum.inl (W.pairing f₀); smaller explosion's pairing
          --   at Sum.inl (W.pairing f₀), with W.pairing f₀ ∉ cutErase,
          --   gives Sum.inl (W.pairing (W.pairing f₀)) = Sum.inl f₀
          --   by pairing_invol.
          simp only [feq]
          have hne₁ : W.pairing f₀ ∉ cutErase W C f₀ :=
            fun hm => ((mem_cutErase W C f₀).mp hm).2.2 rfl
          change (Sum.inl f₀ :
                W.Flag ⊕ {g : W.Flag // g ∈ cutErase W C f₀}) =
            (if h'' : W.pairing f₀ ∈ cutErase W C f₀ then
              (Sum.inr ⟨W.pairing f₀, h''⟩ :
                W.Flag ⊕ {g : W.Flag // g ∈ cutErase W C f₀})
              else Sum.inl (W.pairing (W.pairing f₀)))
          rw [dite_eq_right hne₁, W.pairing_invol]
        · rw [dite_eq_right hf] at h'
          exact absurd h' Sum.inl_ne_inr
      · -- else branch: partner is neither boundary flag
        rename_i hni hnj
        -- hni/hnj: pairing ≠ boundary i/j.
        -- Rewire gives ⟨(explodeAt ...).pairing (Sum.inl f), hni, hnj⟩.
        -- Expose the pairing dite.
        have hni' : (if hf' : f ∈ C then
            (Sum.inr ⟨f, hf'⟩ : W.Flag ⊕ {f : W.Flag // f ∈ C})
            else Sum.inl (W.pairing f)) ≠
            Sum.inr ⟨f₀, h₀⟩ := hni
        have hnj' : (if hf' : f ∈ C then
            (Sum.inr ⟨f, hf'⟩ : W.Flag ⊕ {f : W.Flag // f ∈ C})
            else Sum.inl (W.pairing f)) ≠
            Sum.inr ⟨W.pairing f₀, hC f₀ h₀⟩ := hnj
        by_cases hf : f ∈ C
        · -- f ∈ C, f ≠ f₀, f ≠ W.pairing f₀ → f ∈ cutErase
          rw [dite_eq_left hf] at hni' hnj'
          have hfne₀ : f ≠ f₀ := fun h =>
            hni' (congrArg Sum.inr (Subtype.ext h))
          have hfne₁ : f ≠ W.pairing f₀ := fun h =>
            hnj' (congrArg Sum.inr (Subtype.ext h))
          have hmem : f ∈ cutErase W C f₀ :=
            (mem_cutErase W C f₀).mpr ⟨hf, hfne₀, hfne₁⟩
          -- Both sides reduce to Sum.inr ⟨f, _⟩
          -- Compute LHS pairing via defeq-ascription
          have hp₁ : (explodeAt W C hC).pairing (Sum.inl f) =
              (Sum.inr ⟨f, hf⟩ :
                W.Flag ⊕ {f : W.Flag // f ∈ C}) := by
            exact (show (if hf' : f ∈ C then
                (Sum.inr ⟨f, hf'⟩ : W.Flag ⊕ {f : W.Flag // f ∈ C})
                else Sum.inl (W.pairing f)) = _ from dite_eq_left hf)
          -- Compute RHS pairing via defeq-ascription
          have hp₂ : (explodeAt W (cutErase W C f₀)
              (cutErase_closed W C hC f₀)).pairing (Sum.inl f) =
              (Sum.inr ⟨f, hmem⟩ :
                W.Flag ⊕ {g : W.Flag // g ∈ cutErase W C f₀}) := by
            exact (show (if hf' : f ∈ cutErase W C f₀ then
                (Sum.inr ⟨f, hf'⟩ :
                  W.Flag ⊕ {g : W.Flag // g ∈ cutErase W C f₀})
                else Sum.inl (W.pairing f)) = _ from
              dite_eq_left hmem)
          simp only [hp₁]
          exact hp₂.symm
        · -- f ∉ C → pairing = Sum.inl (W.pairing f)
          rw [dite_eq_right hf] at hni' hnj'
          have hne : f ∉ cutErase W C f₀ := fun hm =>
            hf ((mem_cutErase W C f₀).mp hm).1
          -- Compute both pairing values via defeq-ascription trick
          have hp₁ : (explodeAt W C hC).pairing (Sum.inl f) =
              (Sum.inl (W.pairing f) :
                W.Flag ⊕ {f : W.Flag // f ∈ C}) := by
            exact (show (if hf' : f ∈ C then
                (Sum.inr ⟨f, hf'⟩ : W.Flag ⊕ {f : W.Flag // f ∈ C})
                else Sum.inl (W.pairing f)) =
              Sum.inl (W.pairing f) from dite_eq_right hf)
          have hp₂ : (explodeAt W (cutErase W C f₀)
              (cutErase_closed W C hC f₀)).pairing (Sum.inl f) =
              (Sum.inl (W.pairing f) :
                W.Flag ⊕ {g : W.Flag // g ∈ cutErase W C f₀}) := by
            exact (show (if hf' : f ∈ cutErase W C f₀ then
                (Sum.inr ⟨f, hf'⟩ :
                  W.Flag ⊕ {g : W.Flag // g ∈ cutErase W C f₀})
                else Sum.inl (W.pairing f)) =
              Sum.inl (W.pairing f) from dite_eq_right hne)
          simp only [hp₁]
          exact hp₂.symm
  · -- ═══════ A new star flag ═══════
    change (stepFlagEquiv W C hC f₀ h₀)
      (Fragment.rewire hopen ⟨Sum.inr s, hg⟩) =
      ((explodeAt W (cutErase W C f₀) (cutErase_closed W C hC f₀)).relabel
        (stepLabelEquiv W C hC f₀ h₀)).pairing
      ((stepFlagEquiv W C hC f₀ h₀) ⟨Sum.inr s, hg⟩)
    unfold Fragment.rewire
    split
    · rename_i h; exact absurd h Sum.inl_ne_inr
    · split
      · rename_i _ h; exact absurd h Sum.inl_ne_inr
      · -- else branch: result is ⟨Sum.inl s.val, ...⟩
        rfl

/-- **One regluing step**: gluing the two cut ends of the edge of
`f₀` in the explosion at `C` is the explosion at the shrunken cut
set. -/
noncomputable def explodeAtGluePair (W : ClosedFragment)
    (C : Finset W.Flag) (hC : CutClosed W C) (f₀ : W.Flag)
    (h₀ : f₀ ∈ C) :
    ((explodeAt W C hC).gluePair (stepLabelI W C f₀ h₀)
        (stepLabelJ W C hC f₀ h₀)
        (stepLabel_ne W C hC f₀ h₀)).Equiv
      ((explodeAt W (cutErase W C f₀)
          (cutErase_closed W C hC f₀)).relabel
        (stepLabelEquiv W C hC f₀ h₀)) := by
  -- The glue is open: pairing (boundaryFlag i) = Sum.inl f₀ ≠ Sum.inr ... =
  --   boundaryFlag j
  have hopen : (explodeAt W C hC).pairing
      ((explodeAt W C hC).boundaryFlag (stepLabelI W C f₀ h₀)) ≠
      (explodeAt W C hC).boundaryFlag (stepLabelJ W C hC f₀ h₀) :=
    Sum.inl_ne_inr
  -- Bridge gluePair = gluePairOpen via dif_neg
  have heq : (explodeAt W C hC).gluePair (stepLabelI W C f₀ h₀)
      (stepLabelJ W C hC f₀ h₀) (stepLabel_ne W C hC f₀ h₀) =
      (explodeAt W C hC).gluePairOpen (stepLabelI W C f₀ h₀)
        (stepLabelJ W C hC f₀ h₀) (stepLabel_ne W C hC f₀ h₀) hopen :=
    dite_eq_right hopen
  rw [heq]
  exact {
    flagEquiv := stepFlagEquiv W C hC f₀ h₀
    vertexEquiv := _root_.Equiv.refl W.Vertex
    circles_eq := rfl
    -- ═══════ ATTACHMENT ═══════
    attach_comm := fun f => by
        obtain ⟨fv, hf⟩ := f
        rcases fv with g | s
        · rfl
        · rfl
    -- ═══════ PAIRING ═══════
    pairing_comm := explodeAt_rewire_pairing W C hC f₀ h₀ hopen
  }

end GlueStep

end RS
