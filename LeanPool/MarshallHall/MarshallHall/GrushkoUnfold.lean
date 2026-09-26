/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.GrushkoEdge


/-!
## The local source unfold

This file formalizes the local graph move used in the last case of the
Stallings proof of Grushko's theorem.  Fix an oriented edge `e₀` leaving a
vertex `a`.  The source is split into an old copy and a new copy.  All
original arrows labelled in the colour of `e₀` remain attached to the old
copy, the other coloured arrows are attached to the new copy, and a second
copy of `e₀` is attached to the new copy.

The construction is intentionally local.  In particular, it does not yet
choose a new marking or perform the subsequent monochromatic-vertex
contraction.  The main certified fact here is that the old copy is
monochromatic, exactly the invariant needed by that contraction.
-/

@[expose] public section



open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u v

variable {G H : Type v} [Group G] [Group H]
  {V : Type u} [Fintype V] [Quiver V] [HasInvolutiveReverse V]
  [∀ a b : V, Fintype (a ⟶ b)]

/-! ### Split vertices and duplicated arrows -/

/-- A copy of `a` is added to the original vertex set.  `false` denotes the
old copy and `true` the new copy. -/
abbrev UnfoldVertex (a : V) := {x : V // x ≠ a} ⊕ Bool

noncomputable instance unfoldVertexFintype (a : V) : Fintype (UnfoldVertex a) := by
  classical
  dsimp [UnfoldVertex]
  infer_instance

/-- The original copy of the vertex split by unfolding. -/
def unfoldOld (a : V) : UnfoldVertex a := Sum.inr false

/-- The new copy of the vertex created by unfolding. -/
def unfoldNew (a : V) : UnfoldVertex a := Sum.inr true

omit [Fintype V] [Quiver.HasInvolutiveReverse V] [(a b : V) → Fintype (a ⟶ b)] in
omit [Quiver V] in
theorem unfoldOld_ne_new (a : V) : unfoldOld a ≠ unfoldNew a := by
  intro h
  cases h

omit [Fintype V] [Quiver.HasInvolutiveReverse V] [(a b : V) → Fintype (a ⟶ b)] in
omit [Quiver V] in
theorem unfoldNew_ne_old (a : V) : unfoldNew a ≠ unfoldOld a := by
  exact (unfoldOld_ne_new a).symm

/-- The factor containing an edge's label. -/
def unfoldEdgeColor (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e : AllArrow (V := V)) : Bool :=
  binarySumIndex (G := G) (H := H) (allArrowLabel L e)

/-- Chooses the appropriate copy of the split vertex according to the incident factor. -/
def unfoldVertexAt (L : BinaryLabelling (G := G) (H := H) (V := V))
    (a : V) (e₀ : AllArrow (V := V)) (x : V) (c : Bool) :
    UnfoldVertex a :=
  by
    classical
    exact if h : x = a then
      Sum.inr (if c = unfoldEdgeColor L e₀ then false else true)
    else
      Sum.inl ⟨x, h⟩

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldVertexAt_eq_old_iff
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (a : V) (e₀ : AllArrow (V := V)) (x : V) (c : Bool) :
    unfoldVertexAt L a e₀ x c = unfoldOld a ↔
      x = a ∧ c = unfoldEdgeColor L e₀ := by
  classical
  by_cases hx : x = a
  · subst x
    cases hcol : unfoldEdgeColor L e₀ <;> cases c <;>
      simp [unfoldVertexAt, unfoldOld, hcol]
  · simp [unfoldVertexAt, unfoldOld, hx]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldVertexAt_eq_new_iff
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (a : V) (e₀ : AllArrow (V := V)) (x : V) (c : Bool) :
    unfoldVertexAt L a e₀ x c = unfoldNew a ↔
      x = a ∧ c ≠ unfoldEdgeColor L e₀ := by
  classical
  by_cases hx : x = a
  · subst x
    cases hcol : unfoldEdgeColor L e₀ <;> cases c <;>
      simp [unfoldVertexAt, unfoldNew, hcol]
  · simp [unfoldVertexAt, unfoldNew, hx]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldVertexAt_of_ne
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (x : V) (c : Bool) (hx : x ≠ a) :
    unfoldVertexAt L a e₀ x c = Sum.inl ⟨x, hx⟩ := by
  classical
  simp [unfoldVertexAt, hx]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldEdgeColor_reverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e : AllArrow (V := V)) :
    unfoldEdgeColor L (allArrowReverse e) = unfoldEdgeColor L e := by
  simp only [unfoldEdgeColor, allArrowLabel_reverse,
    binarySumIndex_factorWordInv]

/-! ### The unfolded edge type and its quiver -/

/-- The old oriented edges together with the two orientations of a duplicated
edge.  The `Bool` component is the orientation of the duplicate. -/
abbrev UnfoldEdge :=
  AllArrow (V := V) ⊕ Bool

noncomputable instance unfoldEdgeFintype :
    Fintype (UnfoldEdge (V := V)) := by
  dsimp [UnfoldEdge]
  infer_instance

/-- Reverses an original or duplicated edge in the unfolded graph. -/
def unfoldEdgeReverse :
    UnfoldEdge (V := V) → UnfoldEdge (V := V)
  | Sum.inl e => Sum.inl (allArrowReverse e)
  | Sum.inr false => Sum.inr true
  | Sum.inr true => Sum.inr false

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
@[simp]
theorem unfoldEdgeReverse_reverse
    (e : UnfoldEdge (V := V)) :
    unfoldEdgeReverse (unfoldEdgeReverse e) = e := by
  cases e with
  | inl e => simp [unfoldEdgeReverse]
  | inr b => cases b <;> rfl

/-- The source of an edge after the vertex has been split by factor. -/
def unfoldEdgeSource
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    UnfoldEdge (V := V) → UnfoldVertex (allArrowSource e₀)
  | Sum.inl e =>
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowSource e) (unfoldEdgeColor L e)
  | Sum.inr false => unfoldNew (allArrowSource e₀)
  | Sum.inr true =>
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L e₀)

/-- The target of an edge after the vertex has been split by factor. -/
def unfoldEdgeTarget
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    UnfoldEdge (V := V) → UnfoldVertex (allArrowSource e₀)
  | Sum.inl e =>
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e) (unfoldEdgeColor L e)
  | Sum.inr false =>
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L e₀)
  | Sum.inr true => unfoldNew (allArrowSource e₀)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldEdgeSource_reverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (e : UnfoldEdge (V := V)) :
    unfoldEdgeSource L e₀ (unfoldEdgeReverse e) =
      unfoldEdgeTarget L e₀ e := by
  cases e with
  | inl e =>
      simp [unfoldEdgeSource, unfoldEdgeTarget, unfoldEdgeReverse,
        unfoldEdgeColor_reverse]
  | inr b => cases b <;> rfl

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldEdgeTarget_reverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (e : UnfoldEdge (V := V)) :
    unfoldEdgeTarget L e₀ (unfoldEdgeReverse e) =
      unfoldEdgeSource L e₀ e := by
  cases e with
  | inl e =>
      simp [unfoldEdgeSource, unfoldEdgeTarget, unfoldEdgeReverse,
        unfoldEdgeColor_reverse]
  | inr b => cases b <;> rfl

/-- The quiver obtained by splitting a vertex and duplicating the selected edge. -/
@[reducible]
def unfoldQuiver
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    Quiver (UnfoldVertex (allArrowSource e₀)) where
  Hom x y := {e : UnfoldEdge (V := V) //
    unfoldEdgeSource L e₀ e = x ∧ unfoldEdgeTarget L e₀ e = y}

/-- A finite enumeration of arrows in the unfolded quiver. -/
@[instance_reducible]
noncomputable def unfoldQuiverHomFintype
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (x y : UnfoldVertex (allArrowSource e₀)) :
    Fintype (@Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) x y) := by
  classical
  change Fintype {e : UnfoldEdge (V := V) //
    unfoldEdgeSource L e₀ e = x ∧ unfoldEdgeTarget L e₀ e = y}
  infer_instance

noncomputable instance unfoldAllArrowFintype
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    Fintype (@AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)) := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  letI (x y : UnfoldVertex (allArrowSource e₀)) :
      Fintype (x ⟶ y) := by
    exact unfoldQuiverHomFintype L e₀ x y
  exact allArrowFintype

/-- Reverses an arrow of the unfolded quiver. -/
def unfoldReverseArrow
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {x y : UnfoldVertex (allArrowSource e₀)}
    (e : @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) x y) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) y x := by
  refine ⟨unfoldEdgeReverse e.1, ?_, ?_⟩
  · rw [unfoldEdgeSource_reverse, e.2.2]
  · rw [unfoldEdgeTarget_reverse, e.2.1]

/-- The involutive reversal on the unfolded quiver. -/
@[instance_reducible]
def unfoldHasReverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @Quiver.HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) :=
  @Quiver.HasInvolutiveReverse.mk
    (UnfoldVertex (allArrowSource e₀))
    (unfoldQuiver L e₀)
    (@Quiver.HasReverse.mk
      (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (fun {x y} e => unfoldReverseArrow L e₀ e))
    (by
      intro x y e
      apply Subtype.ext
      exact unfoldEdgeReverse_reverse e.1)

/-- The label of an unfolded edge, using the selected edge's label for its duplicate. -/
def unfoldEdgeLabel
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) : UnfoldEdge (V := V) → Sum G H
  | Sum.inl e => allArrowLabel L e
  | Sum.inr false => allArrowLabel L e₀
  | Sum.inr true => factorWordInv (allArrowLabel L e₀)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldEdgeLabel_reverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (e : UnfoldEdge (V := V)) :
    unfoldEdgeLabel L e₀ (unfoldEdgeReverse e) =
      factorWordInv (unfoldEdgeLabel L e₀ e) := by
  cases e with
  | inl e =>
      simp [unfoldEdgeLabel, unfoldEdgeReverse, allArrowLabel_reverse]
  | inr b =>
      cases b
      · rfl
      · simp [unfoldEdgeLabel, unfoldEdgeReverse,
          factorWordInv_factorWordInv]

/-- The factor labelling on the unfolded graph. -/
def unfoldLabelling
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @BinaryLabelling G H (UnfoldVertex (allArrowSource e₀)) _ _
      (unfoldQuiver L e₀) (unfoldHasReverse L e₀) := by
  exact @BinaryLabelling.mk G H (UnfoldVertex (allArrowSource e₀)) _ _
    (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
    (fun {x y} e => unfoldEdgeLabel L e₀ e.1)
    (by
      intro x y e
      exact unfoldEdgeLabel_reverse L e₀ e.1)

/-! ### The old copy is monochromatic -/

/-- An unfolded arrow is incident to the original copy of the split vertex. -/
def unfoldOldIncident
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    (e : @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)) : Prop :=
  e.1 = unfoldOld (allArrowSource e₀) ∨
    e.2.1 = unfoldOld (allArrowSource e₀)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfold_old_incident_color
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    (e : @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀))
    (h : unfoldOldIncident L e₀ e) :
    binarySumIndex (G := G) (H := H)
        (unfoldEdgeLabel L e₀ e.2.2.1) =
      unfoldEdgeColor L e₀ := by
  rcases e with ⟨x, y, e⟩
  rcases e with ⟨edge, hs, ht⟩
  change x = unfoldOld (allArrowSource e₀) ∨
    y = unfoldOld (allArrowSource e₀) at h
  cases edge with
  | inl e =>
      have hc : unfoldEdgeColor L e = unfoldEdgeColor L e₀ := by
        rcases h with h | h
        · have hsold :
              unfoldVertexAt L (allArrowSource e₀) e₀
                (allArrowSource e) (unfoldEdgeColor L e) =
              unfoldOld (allArrowSource e₀) := by
            exact hs.trans h
          exact (unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
            (allArrowSource e) (unfoldEdgeColor L e)).mp hsold |>.2
        · have htold :
              unfoldVertexAt L (allArrowSource e₀) e₀
                (allArrowTarget e) (unfoldEdgeColor L e) =
              unfoldOld (allArrowSource e₀) := by
            exact ht.trans h
          exact (unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
            (allArrowTarget e) (unfoldEdgeColor L e)).mp htold |>.2
      exact hc
  | inr b =>
      cases b <;>
        simp [unfoldEdgeLabel, unfoldEdgeColor, binarySumIndex_factorWordInv]

/-- The unfolded arrow corresponding to an original edge. -/
def unfoldOriginalEdge
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldVertexAt L (allArrowSource e₀) e₀ x
        (unfoldEdgeColor L (allArrowOf e)))
      (unfoldVertexAt L (allArrowSource e₀) e₀ y
        (unfoldEdgeColor L (allArrowOf e))) :=
  ⟨Sum.inl (allArrowOf e), rfl, rfl⟩

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldOriginalEdge_label
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    unfoldEdgeLabel L e₀ (Sum.inl (allArrowOf e)) = L.label e := by
  rfl

/-- The unfolded original edge with its factor made explicit in the endpoints. -/
def unfoldOriginalEdgeAtColor
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y)
    (color : Bool) (hc : unfoldEdgeColor L (allArrowOf e) = color) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldVertexAt L (allArrowSource e₀) e₀ x color)
      (unfoldVertexAt L (allArrowSource e₀) e₀ y color) := by
  refine ⟨Sum.inl (allArrowOf e), ?_, ?_⟩
  · change unfoldVertexAt L (allArrowSource e₀) e₀ x
      (unfoldEdgeColor L (allArrowOf e)) =
        unfoldVertexAt L (allArrowSource e₀) e₀ x color
    rw [hc]
  · change unfoldVertexAt L (allArrowSource e₀) e₀ y
      (unfoldEdgeColor L (allArrowOf e)) =
        unfoldVertexAt L (allArrowSource e₀) e₀ y color
    rw [hc]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldOriginalEdgeAtColor_label
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y)
    (color : Bool) (hc : unfoldEdgeColor L (allArrowOf e) = color) :
    unfoldEdgeLabel L e₀
        (unfoldOriginalEdgeAtColor L e₀ e color hc).1 = L.label e := by
  rfl

/-- Lifts a monochromatic path to the corresponding factor side of the unfolded graph. -/
def unfoldMonochromaticPath
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (color : Bool) :
    ∀ {x y : V} (p : @Quiver.Path V _ x y),
      L.IsMonochromatic p color →
      @Quiver.Path (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldVertexAt L (allArrowSource e₀) e₀ x color)
        (unfoldVertexAt L (allArrowSource e₀) e₀ y color)
  | _, _, Path.nil, _ =>
      @Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) _
  | _, _, Path.cons p e, hp => by
      have htail : L.IsMonochromatic p color := by
        intro z hz
        exact hp z (by
          simp only [BinaryLabelling.pathLabels, List.mem_append]
          exact Or.inl hz)
      have hecolor : binarySumIndex (G := G) (H := H) (L.label e) = color := by
        exact hp (L.label e) (by
          simp only [BinaryLabelling.pathLabels, List.mem_append,
            List.mem_singleton]
          exact Or.inr trivial)
      have hecolor' : unfoldEdgeColor L (allArrowOf e) = color := by
        exact hecolor
      have edge := unfoldOriginalEdgeAtColor L e₀ e color hecolor'
      exact @Quiver.Path.cons
        (UnfoldVertex (allArrowSource e₀)) (unfoldQuiver L e₀)
        (unfoldVertexAt L (allArrowSource e₀) e₀ _ color) _
        (unfoldVertexAt L (allArrowSource e₀) e₀ _ color)
        (unfoldMonochromaticPath L e₀ color p htail) edge

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldMonochromaticPath_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (color : Bool)
    {x y : V} (p : @Quiver.Path V _ x y)
    (hp : L.IsMonochromatic p color) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀)
      _ _ (unfoldMonochromaticPath L e₀ color p hp)) =
      L.pathRead p := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  induction p with
  | nil =>
      simp [unfoldMonochromaticPath, BinaryLabelling.pathRead,
        BinaryLabelling.pathLabels, factorWordProd]
  | cons p e ih =>
      have htail : L.IsMonochromatic p color := by
        intro z hz
        exact hp z (by
          simp only [BinaryLabelling.pathLabels, List.mem_append]
          exact Or.inl hz)
      have hecolor : binarySumIndex (G := G) (H := H) (L.label e) = color := by
        exact hp (L.label e) (by
          simp only [BinaryLabelling.pathLabels, List.mem_append,
            List.mem_singleton]
          exact Or.inr trivial)
      simp only [unfoldMonochromaticPath]
      rw [← Path.comp_toPath_eq_cons, ← Path.comp_toPath_eq_cons,
        BinaryLabelling.pathRead_comp, ih htail,
        BinaryLabelling.pathRead_toPath]
      change L.pathRead p * separatedMap (L.label e) = L.pathRead (p.cons e)
      rw [← Path.comp_toPath_eq_cons, L.pathRead_comp,
        L.pathRead_toPath]

/-! ### Cardinal bookkeeping -/

omit [Quiver.HasInvolutiveReverse V] in
theorem unfoldEdge_card
     :
    Fintype.card (UnfoldEdge (V := V)) =
      Fintype.card (AllArrow (V := V)) + 2 := by
  change Fintype.card (AllArrow (V := V) ⊕ Bool) =
    Fintype.card (AllArrow (V := V)) + 2
  rw [Fintype.card_sum, Fintype.card_bool]

/-- Identifies packaged arrows in the unfolded quiver with its explicit edge type. -/
def unfoldAllArrowEquivEdge
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) ≃ UnfoldEdge (V := V) :=
  { toFun := fun e => e.2.2.1
    invFun := fun e =>
      ⟨unfoldEdgeSource L e₀ e, unfoldEdgeTarget L e₀ e,
        ⟨e, rfl, rfl⟩⟩
    left_inv := by
      intro e
      cases e with
      | mk x be =>
          cases be with
          | mk y e =>
              cases e with
              | mk edge h =>
                  cases h.1
                  cases h.2
                  rfl
    right_inv := by
      intro e
      rfl }

theorem unfoldAllArrow_card
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    Fintype.card (@AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)) =
      Fintype.card (AllArrow (V := V)) + 2 := by
  rw [Fintype.card_congr (unfoldAllArrowEquivEdge L e₀),
    unfoldEdge_card]

omit [Quiver.HasInvolutiveReverse V] [(a b : V) → Fintype (a ⟶ b)] in
omit [Quiver V] in
theorem unfoldVertex_card (a : V) :
    Fintype.card (UnfoldVertex a) = Fintype.card V + 1 := by
  classical
  have hcomp := Fintype.card_subtype_compl (fun x : V => x = a)
  have heq : Fintype.card {x : V // x = a} = 1 := by
    simp
  have hpos : 1 ≤ Fintype.card V := by
    exact Fintype.card_pos_iff.mpr ⟨a⟩
  change Fintype.card ({x : V // x ≠ a} ⊕ Bool) =
    Fintype.card V + 1
  rw [Fintype.card_sum, Fintype.card_bool, hcomp, heq]
  omega

theorem unfold_euler_bound {n : ℕ}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    (hEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1)) :
    Fintype.card (@AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)) ≤
      2 * (n + Fintype.card (UnfoldVertex (allArrowSource e₀)) - 1) := by
  calc
    Fintype.card (@AllArrow (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)) = Fintype.card (AllArrow (V := V)) + 2 :=
      unfoldAllArrow_card L e₀
    _ ≤ 2 * (n + Fintype.card V - 1) + 2 := by
      exact Nat.add_le_add_right hEuler 2
    _ = 2 * (n + Fintype.card (UnfoldVertex (allArrowSource e₀)) - 1) := by
      rw [unfoldVertex_card]
      have hA : 1 ≤ n + Fintype.card V := by
        have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr
          ⟨allArrowSource e₀⟩
        omega
      have hsub : n + Fintype.card V - 1 + 1 =
          n + Fintype.card V := Nat.sub_add_cancel hA
      calc
        2 * (n + Fintype.card V - 1) + 2 =
            2 * (n + Fintype.card V - 1) + 2 * 1 := by simp
        _ = 2 * (n + Fintype.card V - 1 + 1) := by
          rw [Nat.mul_add]
        _ = 2 * (n + Fintype.card V) := by rw [hsub]
        _ = 2 * (n + (Fintype.card V + 1) - 1) := by
          congr 2

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfold_allArrow_reverse_ne
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    (hfree : ReverseFree (V := V)) :
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) :=
      unfoldQuiver L e₀
    letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
      unfoldHasReverse L e₀
    ∀ e : @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀), allArrowReverse e ≠ e := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  intro e he
  rcases e with ⟨x, y, e⟩
  rcases e with ⟨edge, hs, ht⟩
  have hedge : unfoldEdgeReverse edge = edge := by
    have he' := congrArg
      (fun z : @AllArrow (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) => z.2.2.1) he
    change unfoldEdgeReverse edge = edge at he'
    exact he'
  cases edge with
  | inl e =>
      apply hfree e
      simpa [unfoldEdgeReverse] using hedge
  | inr b => cases b <;> simp [unfoldEdgeReverse] at hedge

/-! ### The zero-labelled switch paths -/

/-- The selected original edge starting at the original copy of the split vertex. -/
def unfoldBaseEdge
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldOld (allArrowSource e₀))
      (unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L e₀)) := by
  refine ⟨Sum.inl e₀, ?_, rfl⟩
  change unfoldVertexAt L (allArrowSource e₀) e₀
      (allArrowSource e₀) (unfoldEdgeColor L e₀) =
    unfoldOld (allArrowSource e₀)
  exact (unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
    (allArrowSource e₀) (unfoldEdgeColor L e₀)).mpr ⟨rfl, rfl⟩

/-- The reverse of the selected original edge in the unfolded graph. -/
def unfoldBaseReverseEdge
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L e₀))
      (unfoldOld (allArrowSource e₀)) := by
  refine ⟨Sum.inl (allArrowReverse e₀), ?_, ?_⟩
  · change unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L (allArrowReverse e₀)) =
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L e₀)
    rw [unfoldEdgeColor_reverse]
  · change unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowSource e₀) (unfoldEdgeColor L (allArrowReverse e₀)) =
      unfoldOld (allArrowSource e₀)
    rw [unfoldEdgeColor_reverse]
    exact (unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
      (allArrowSource e₀) (unfoldEdgeColor L e₀)).mpr ⟨rfl, rfl⟩

/-- The duplicate of the selected edge starting at the new vertex. -/
def unfoldDuplicateForward
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L e₀)) :=
  ⟨Sum.inr false, rfl, rfl⟩

/-- The reverse orientation of the duplicated selected edge. -/
def unfoldDuplicateBackward
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L e₀))
      (unfoldNew (allArrowSource e₀)) :=
  ⟨Sum.inr true, rfl, rfl⟩

/-- The path from the original split vertex to its new copy through the selected edge pair. -/
def unfoldSwitchOldNew
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldOld (allArrowSource e₀))
      (unfoldNew (allArrowSource e₀)) :=
  by
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
    exact (unfoldBaseEdge L e₀).toPath.comp
      (unfoldDuplicateBackward L e₀).toPath

/-- The reverse switching path from the new split vertex to its original copy. -/
def unfoldSwitchNewOld
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldNew (allArrowSource e₀))
      (unfoldOld (allArrowSource e₀)) :=
  by
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
    exact (unfoldDuplicateForward L e₀).toPath.comp
      (unfoldBaseReverseEdge L e₀).toPath

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldSwitchOldNew_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _ (unfoldSwitchOldNew L e₀)) = 1 := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  simp only [unfoldSwitchOldNew]
  rw [BinaryLabelling.pathRead_comp,
    BinaryLabelling.pathRead_toPath, BinaryLabelling.pathRead_toPath]
  simp [unfoldBaseEdge, unfoldDuplicateBackward, unfoldLabelling, unfoldEdgeLabel,
    separatedMap_factorWordInv]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldSwitchNewOld_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _ (unfoldSwitchNewOld L e₀)) = 1 := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  simp only [unfoldSwitchNewOld]
  rw [BinaryLabelling.pathRead_comp,
    BinaryLabelling.pathRead_toPath, BinaryLabelling.pathRead_toPath]
  simp? [unfoldDuplicateForward, unfoldBaseReverseEdge, unfoldLabelling,
    unfoldEdgeLabel]
  change separatedMap (allArrowLabel L e₀) *
    separatedMap (allArrowLabel L (allArrowReverse e₀)) = 1
  rw [allArrowLabel_reverse]
  simp [separatedMap_factorWordInv]

/-! ### Canonical endpoints and path lifting -/

/-- The canonical lift of an original vertex, choosing the original copy at the split vertex. -/
def unfoldCanonical (a x : V) : UnfoldVertex a := by
  classical
  exact if h : x = a then unfoldOld a else Sum.inl ⟨x, h⟩

omit [Fintype V] [Quiver.HasInvolutiveReverse V] [(a b : V) → Fintype (a ⟶ b)] in
omit [Quiver V] in
theorem unfoldCanonical_eq_old (a : V) :
    unfoldCanonical a a = unfoldOld a := by
  simp [unfoldCanonical]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldCanonical_eq_vertexAt_of_ne
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x : V} (hx : x ≠ allArrowSource e₀)
    (color : Bool) :
    unfoldCanonical (allArrowSource e₀) x =
      unfoldVertexAt L (allArrowSource e₀) e₀ x color := by
  simp [unfoldCanonical, unfoldVertexAt, hx]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldVertexAt_eq_new_of_ne_color
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (color : Bool)
    (hc : color ≠ unfoldEdgeColor L e₀) :
    unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowSource e₀) color = unfoldNew (allArrowSource e₀) := by
  exact (unfoldVertexAt_eq_new_iff L (allArrowSource e₀) e₀
    (allArrowSource e₀) color).mpr ⟨rfl, hc⟩

/-- The switching path before an unfolded edge, from its canonical source to its factor side. -/
def unfoldPrePath
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldCanonical (allArrowSource e₀) x)
      (unfoldVertexAt L (allArrowSource e₀) e₀ x
        (unfoldEdgeColor L (allArrowOf e))) := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  by_cases hx : x ≠ allArrowSource e₀
  · exact @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldVertexAt L (allArrowSource e₀) e₀ x
        (unfoldEdgeColor L (allArrowOf e)))
      (unfoldVertexAt L (allArrowSource e₀) e₀ x
        (unfoldEdgeColor L (allArrowOf e)))
      (unfoldCanonical (allArrowSource e₀) x)
      (unfoldVertexAt L (allArrowSource e₀) e₀ x
        (unfoldEdgeColor L (allArrowOf e)))
      (unfoldCanonical_eq_vertexAt_of_ne L e₀ hx
        (unfoldEdgeColor L (allArrowOf e))).symm rfl
      (@Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldVertexAt L (allArrowSource e₀) e₀ x
          (unfoldEdgeColor L (allArrowOf e))))
  · have hx' : x = allArrowSource e₀ := by
      exact Classical.byContradiction hx
    subst x
    by_cases hcolor : unfoldEdgeColor L (allArrowOf e) =
        unfoldEdgeColor L e₀
    · exact @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldOld (allArrowSource e₀))
        (unfoldOld (allArrowSource e₀))
        (unfoldCanonical (allArrowSource e₀) (allArrowSource e₀))
        (unfoldVertexAt L (allArrowSource e₀) e₀
          (allArrowSource e₀) (unfoldEdgeColor L (allArrowOf e)))
        (unfoldCanonical_eq_old (allArrowSource e₀)).symm
        ((unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
          (allArrowSource e₀) (unfoldEdgeColor L (allArrowOf e))).mpr
          ⟨rfl, hcolor⟩).symm
        (@Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver L e₀) (unfoldOld (allArrowSource e₀)))
    · exact @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldOld (allArrowSource e₀))
        (unfoldNew (allArrowSource e₀))
        (unfoldCanonical (allArrowSource e₀) (allArrowSource e₀))
        (unfoldVertexAt L (allArrowSource e₀) e₀
          (allArrowSource e₀) (unfoldEdgeColor L (allArrowOf e)))
        (unfoldCanonical_eq_old (allArrowSource e₀)).symm
        (unfoldVertexAt_eq_new_of_ne_color L e₀
          (unfoldEdgeColor L (allArrowOf e)) hcolor).symm
        (unfoldSwitchOldNew L e₀)

/-- The switching path after an unfolded edge, from its factor side to its canonical target. -/
def unfoldPostPath
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldVertexAt L (allArrowSource e₀) e₀ y
        (unfoldEdgeColor L (allArrowOf e)))
      (unfoldCanonical (allArrowSource e₀) y) := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  by_cases hy : y ≠ allArrowSource e₀
  · exact @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldVertexAt L (allArrowSource e₀) e₀ y
        (unfoldEdgeColor L (allArrowOf e)))
      (unfoldVertexAt L (allArrowSource e₀) e₀ y
        (unfoldEdgeColor L (allArrowOf e)))
      (unfoldVertexAt L (allArrowSource e₀) e₀ y
        (unfoldEdgeColor L (allArrowOf e)))
      (unfoldCanonical (allArrowSource e₀) y)
      rfl
      (unfoldCanonical_eq_vertexAt_of_ne L e₀ hy
        (unfoldEdgeColor L (allArrowOf e))).symm
      (@Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldVertexAt L (allArrowSource e₀) e₀ y
          (unfoldEdgeColor L (allArrowOf e))))
  · have hy' : y = allArrowSource e₀ := by
      exact Classical.byContradiction hy
    subst y
    by_cases hcolor : unfoldEdgeColor L (allArrowOf e) =
        unfoldEdgeColor L e₀
    · exact @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldOld (allArrowSource e₀))
        (unfoldOld (allArrowSource e₀))
        (unfoldVertexAt L (allArrowSource e₀) e₀
          (allArrowSource e₀) (unfoldEdgeColor L (allArrowOf e)))
        (unfoldCanonical (allArrowSource e₀) (allArrowSource e₀))
        ((unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
          (allArrowSource e₀) (unfoldEdgeColor L (allArrowOf e))).mpr
          ⟨rfl, hcolor⟩).symm
        (unfoldCanonical_eq_old (allArrowSource e₀)).symm
        (@Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver L e₀) (unfoldOld (allArrowSource e₀)))
    · exact @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldNew (allArrowSource e₀))
        (unfoldOld (allArrowSource e₀))
        (unfoldVertexAt L (allArrowSource e₀) e₀
          (allArrowSource e₀) (unfoldEdgeColor L (allArrowOf e)))
        (unfoldCanonical (allArrowSource e₀) (allArrowSource e₀))
        (unfoldVertexAt_eq_new_of_ne_color L e₀
          (unfoldEdgeColor L (allArrowOf e)) hcolor).symm
        (unfoldCanonical_eq_old (allArrowSource e₀)).symm
        (unfoldSwitchNewOld L e₀)

/-- Lifts an original edge as a path between canonical lifted endpoints. -/
def unfoldLiftEdge
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldCanonical (allArrowSource e₀) x)
      (unfoldCanonical (allArrowSource e₀) y) := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  exact (unfoldPrePath L e₀ e).comp
    ((unfoldOriginalEdgeAtColor L e₀ e
      (unfoldEdgeColor L (allArrowOf e)) rfl).toPath.comp
      (unfoldPostPath L e₀ e))

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldPrePath_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _ (unfoldPrePath L e₀ e)) = 1 := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  by_cases hx : x ≠ allArrowSource e₀
  · simp [unfoldPrePath, hx,
      BinaryLabelling.pathRead_cast]
  · have hx' : x = allArrowSource e₀ := by
      exact Classical.byContradiction hx
    subst x
    by_cases hcolor : unfoldEdgeColor L (allArrowOf e) =
        unfoldEdgeColor L e₀
    · simp [unfoldPrePath, hx, hcolor,
        BinaryLabelling.pathRead_cast]
    · simp [unfoldPrePath, hx, hcolor,
        BinaryLabelling.pathRead_cast, unfoldSwitchOldNew_read]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldPostPath_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _ (unfoldPostPath L e₀ e)) = 1 := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  by_cases hy : y ≠ allArrowSource e₀
  · simp [unfoldPostPath, hy,
      BinaryLabelling.pathRead_cast]
  · have hy' : y = allArrowSource e₀ := by
      exact Classical.byContradiction hy
    subst y
    by_cases hcolor : unfoldEdgeColor L (allArrowOf e) =
        unfoldEdgeColor L e₀
    · simp [unfoldPostPath, hy, hcolor,
        BinaryLabelling.pathRead_cast]
    · simp [unfoldPostPath, hy, hcolor,
        BinaryLabelling.pathRead_cast, unfoldSwitchNewOld_read]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldLiftEdge_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _ (unfoldLiftEdge L e₀ e)) =
      L.pathRead e.toPath := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  rw [unfoldLiftEdge, BinaryLabelling.pathRead_comp,
    BinaryLabelling.pathRead_comp, unfoldPrePath_read,
    BinaryLabelling.pathRead_toPath, unfoldPostPath_read]
  simpa [unfoldLabelling] using congrArg separatedMap
    (unfoldOriginalEdgeAtColor_label L e₀ e
      (unfoldEdgeColor L (allArrowOf e)) rfl)

/-- Lifts an ordinary path to a path between canonical vertices of the unfolded graph. -/
def unfoldLiftPath
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    ∀ {x y : V}, @Quiver.Path V _ x y →
      @Quiver.Path (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldCanonical (allArrowSource e₀) x)
        (unfoldCanonical (allArrowSource e₀) y)
  | _, _, Quiver.Path.nil =>
      @Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) _
  | _, _, Quiver.Path.cons p e =>
      @Quiver.Path.comp (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) _ _ _
        (unfoldLiftPath L e₀ p)
        (unfoldLiftEdge L e₀ e)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldLiftPath_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V}
    (p : @Quiver.Path V _ x y) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _ (unfoldLiftPath L e₀ p)) =
      L.pathRead p := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  induction p with
  | nil =>
      simp [unfoldLiftPath]
  | cons p e ih =>
      rw [unfoldLiftPath, BinaryLabelling.pathRead_comp, ih,
        unfoldLiftEdge_read]
      rw [← Path.comp_toPath_eq_cons, L.pathRead_comp]

/-- Lifts a symmetrized arrow to a path in the unfolded graph. -/
def unfoldSymmLiftArrow
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) x y) :
    @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldCanonical (allArrowSource e₀) (show V from x))
      (unfoldCanonical (allArrowSource e₀) (show V from y)) := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  cases e with
  | inl f =>
      exact unfoldLiftEdge L e₀ f
  | inr f =>
      exact @Quiver.Path.reverse (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) (unfoldHasReverse L e₀).toHasReverse _ _
        (unfoldLiftEdge L e₀ f)

/-- Lifts a symmetrized path to a path in the unfolded graph. -/
def unfoldSymmLiftPath
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    ∀ {x y : Symmetrify V},
      @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) x y →
      @Quiver.Path (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldCanonical (allArrowSource e₀) (show V from x))
        (unfoldCanonical (allArrowSource e₀) (show V from y))
  | _, _, Quiver.Path.nil =>
      @Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) _
  | _, _, Quiver.Path.cons p e =>
      @Quiver.Path.comp (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) _ _ _
        (unfoldSymmLiftPath L e₀ p)
        (unfoldSymmLiftArrow L e₀ e)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldSymmLiftArrow_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) x y) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _ (unfoldSymmLiftArrow L e₀ e)) =
      separatedMap (L.symmLabel e) := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  cases e with
  | inl f =>
      exact (unfoldLiftEdge_read L e₀ f).trans (L.pathRead_toPath f)
  | inr f =>
      rw [unfoldSymmLiftArrow, BinaryLabelling.pathRead_reverse,
        unfoldLiftEdge_read, BinaryLabelling.pathRead_toPath]
      change (separatedMap (L.label f))⁻¹ =
        separatedMap (factorWordInv (L.label f))
      rw [← separatedMap_factorWordInv]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldSymmLiftPath_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) x y) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _ (unfoldSymmLiftPath L e₀ p)) =
      L.symmPathRead p := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  induction p with
  | nil =>
      simp [unfoldSymmLiftPath, BinaryLabelling.pathRead,
        BinaryLabelling.symmPathRead,
        BinaryLabelling.symmPathLabels, factorWordProd]
  | cons p e ih =>
      rw [unfoldSymmLiftPath, BinaryLabelling.pathRead_comp, ih,
        unfoldSymmLiftArrow_read]
      rw [← Path.comp_toPath_eq_cons, L.symmPathRead_comp,
        L.symmPathRead_toPath]

/-- Lifts a monochromatic symmetrized path to its factor side in the unfolded graph. -/
def unfoldSymmMonochromaticPath
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (color : Bool) :
    ∀ {x y : Symmetrify V},
      (p : @Quiver.Path (Symmetrify V)
        (@Quiver.symmetrifyQuiver V _) x y) →
      L.symmIsMonochromatic p color →
      @Quiver.Path (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldVertexAt L (allArrowSource e₀) e₀ (show V from x) color)
        (unfoldVertexAt L (allArrowSource e₀) e₀ (show V from y) color)
  | _, _, Quiver.Path.nil, _ =>
      @Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) _
  | _, _, Quiver.Path.cons p e, hp => by
      have htail : L.symmIsMonochromatic p color := by
        intro z hz
        exact hp z (by
          simp only [BinaryLabelling.symmPathLabels, List.mem_append]
          exact Or.inl hz)
      have hecolor' :
          binarySumIndex (G := G) (H := H) (L.symmLabel e) = color := by
        exact hp (L.symmLabel e) (by
          simp only [BinaryLabelling.symmPathLabels, List.mem_append,
            List.mem_singleton]
          exact Or.inr trivial)
      cases e with
      | inl f =>
          have hecolor :
              binarySumIndex (G := G) (H := H) (L.label f) = color := by
            simpa [BinaryLabelling.symmLabel] using hecolor'
          have hfmono : L.IsMonochromatic f.toPath color := by
            intro z hz
            have hz' : z = L.label f := by
              exact List.mem_singleton.mp hz
            rw [hz']
            exact hecolor
          exact @Quiver.Path.comp (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver L e₀) _ _ _
            (unfoldSymmMonochromaticPath L e₀ color p htail)
            (unfoldMonochromaticPath L e₀ color f.toPath hfmono)
      | inr f =>
          have hecolor :
              binarySumIndex (G := G) (H := H) (L.label f) = color := by
            change binarySumIndex (G := G) (H := H)
              (factorWordInv (L.label f)) = color at hecolor'
            simpa only [binarySumIndex_factorWordInv] using hecolor'
          have hfmono : L.IsMonochromatic f.toPath color := by
            intro z hz
            have hz' : z = L.label f := by
              exact List.mem_singleton.mp hz
            rw [hz']
            exact hecolor
          exact @Quiver.Path.comp (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver L e₀) _ _ _
            (unfoldSymmMonochromaticPath L e₀ color p htail)
            (@Quiver.Path.reverse (UnfoldVertex (allArrowSource e₀))
              (unfoldQuiver L e₀) (unfoldHasReverse L e₀).toHasReverse _ _
              (unfoldMonochromaticPath L e₀ color f.toPath hfmono))

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldSymmMonochromaticPath_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (color : Bool)
    {x y : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) x y)
    (hp : L.symmIsMonochromatic p color) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _
      (unfoldSymmMonochromaticPath L e₀ color p hp)) =
      L.symmPathRead p := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  induction p with
  | nil =>
      simp [unfoldSymmMonochromaticPath, BinaryLabelling.pathRead,
        BinaryLabelling.symmPathRead,
        BinaryLabelling.symmPathLabels, factorWordProd]
  | cons p e ih =>
      have htail : L.symmIsMonochromatic p color := by
        intro z hz
        exact hp z (by
          simp only [BinaryLabelling.symmPathLabels, List.mem_append]
          exact Or.inl hz)
      cases e with
      | inl f =>
          rw [unfoldSymmMonochromaticPath, BinaryLabelling.pathRead_comp,
            ih htail]
          have hecolor :
              binarySumIndex (G := G) (H := H) (L.label f) = color := by
            exact hp (L.label f) (by
              simp only [BinaryLabelling.symmPathLabels, List.mem_append,
                List.mem_singleton, BinaryLabelling.symmLabel]
              exact Or.inr trivial)
          have hfmono : L.IsMonochromatic f.toPath color := by
            intro z hz
            have hz' : z = L.label f := by
              exact List.mem_singleton.mp hz
            rw [hz']
            exact hecolor
          rw [unfoldMonochromaticPath_read L e₀ color f.toPath hfmono,
            ← Path.comp_toPath_eq_cons, L.symmPathRead_comp,
            L.symmPathRead_toPath]
          exact congrArg (L.symmPathRead p * ·) (L.pathRead_toPath f)
      | inr f =>
          rw [unfoldSymmMonochromaticPath, BinaryLabelling.pathRead_comp,
            ih htail]
          have hecolor :
              binarySumIndex (G := G) (H := H) (L.label f) = color := by
            have h := hp (L.symmLabel (Sum.inr f)) (by
              simp only [BinaryLabelling.symmPathLabels, List.mem_append,
                List.mem_singleton]
              exact Or.inr trivial)
            change binarySumIndex (G := G) (H := H)
              (factorWordInv (L.label f)) = color at h
            simpa only [binarySumIndex_factorWordInv] using h
          have hfmono : L.IsMonochromatic f.toPath color := by
            intro z hz
            have hz' : z = L.label f := by
              exact List.mem_singleton.mp hz
            rw [hz']
            exact hecolor
          rw [BinaryLabelling.pathRead_reverse,
            unfoldMonochromaticPath_read L e₀ color f.toPath hfmono,
            ← Path.comp_toPath_eq_cons, L.symmPathRead_comp,
            L.symmPathRead_toPath]
          exact congrArg (L.symmPathRead p * ·)
            ((congrArg Inv.inv (L.pathRead_toPath f)).trans
              (separatedMap_factorWordInv (L.label f)).symm)

/-! ### The duplicated edge and its complementary tail -/

/-- The path beginning with the duplicated edge and following the lifted monochromatic
continuation. -/
def unfoldDuplicatePath
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {b : Symmetrify V}
    (q : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) (show V from allArrowTarget e₀) b)
    (hq : L.symmIsMonochromatic q (unfoldEdgeColor L e₀)) :
    @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt L (allArrowSource e₀) e₀ (show V from b)
        (unfoldEdgeColor L e₀)) := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  exact (unfoldDuplicateForward L e₀).toPath.comp
    (unfoldSymmMonochromaticPath L e₀ (unfoldEdgeColor L e₀) q hq)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldDuplicatePath_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {b : Symmetrify V}
    (q : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) (show V from allArrowTarget e₀) b)
    (hq : L.symmIsMonochromatic q (unfoldEdgeColor L e₀)) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀) _ _
      (unfoldDuplicatePath L e₀ q hq)) =
      separatedMap (allArrowLabel L e₀) * L.symmPathRead q := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  rw [unfoldDuplicatePath, BinaryLabelling.pathRead_comp,
    BinaryLabelling.pathRead_toPath]
  exact congrArg (separatedMap (allArrowLabel L e₀) * ·)
    (unfoldSymmMonochromaticPath_read L e₀ (unfoldEdgeColor L e₀) q hq)

/-- The list of explicit unfolded edges traversed by a path. -/
def unfoldPathEdges
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    ∀ {x y : UnfoldVertex (allArrowSource e₀)},
      @Quiver.Path (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) x y → List (UnfoldEdge (V := V))
  := by
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
    intro x y p
    induction p with
    | nil => exact []
    | cons p e ih => exact ih ++ [e.1]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldPathEdges_comp
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {x y : UnfoldVertex (allArrowSource e₀)}
    (p : @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) x y) :
    ∀ {z : UnfoldVertex (allArrowSource e₀)}
      (q : @Quiver.Path (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) y z),
      unfoldPathEdges L e₀
          (@Quiver.Path.comp (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver L e₀) _ _ _ p q) =
        unfoldPathEdges L e₀ p ++ unfoldPathEdges L e₀ q
    := by
    let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
    intro z q
    induction q with
    | nil => simp [unfoldPathEdges]
    | cons q e ih =>
        change unfoldPathEdges L e₀ (p.comp q) ++ [e.1] =
          unfoldPathEdges L e₀ p ++
            (unfoldPathEdges L e₀ q ++ [e.1])
        rw [ih, List.append_assoc]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldPathEdges_reverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {x y : UnfoldVertex (allArrowSource e₀)}
    (p : @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) x y) :
    unfoldPathEdges L e₀
        (@Quiver.Path.reverse (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver L e₀) (unfoldHasReverse L e₀).toHasReverse _ _ p) =
      (unfoldPathEdges L e₀ p).reverse.map unfoldEdgeReverse := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  induction p with
  | nil => rfl
  | cons p e ih =>
      change unfoldPathEdges L e₀
          ((Quiver.reverse e).toPath.comp p.reverse) =
        (unfoldPathEdges L e₀ p ++ [e.1]).reverse.map unfoldEdgeReverse
      rw [unfoldPathEdges_comp L e₀, ih]
      rw [List.reverse_append]
      simp only [List.reverse_cons, List.reverse_nil]
      change [unfoldEdgeReverse e.1] ++
          (unfoldPathEdges L e₀ p).reverse.map unfoldEdgeReverse =
        List.map unfoldEdgeReverse
          ([e.1] ++ (unfoldPathEdges L e₀ p).reverse)
      rfl

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldMonochromaticPath_edges_original
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (color : Bool)
    {x y : V} (p : @Quiver.Path V _ x y)
    (hp : L.IsMonochromatic p color) :
    ∀ z ∈ unfoldPathEdges L e₀
        (unfoldMonochromaticPath L e₀ color p hp),
      ∃ f : AllArrow (V := V), z = Sum.inl f := by
  induction p with
  | nil =>
      simp [unfoldMonochromaticPath, unfoldPathEdges]
  | cons p e ih =>
      have htail : L.IsMonochromatic p color := by
        intro z hz
        exact hp z (by
          simp only [BinaryLabelling.pathLabels, List.mem_append]
          exact Or.inl hz)
      have hecolor :
          binarySumIndex (G := G) (H := H) (L.label e) = color := by
        exact hp (L.label e) (by
          simp only [BinaryLabelling.pathLabels, List.mem_append,
            List.mem_singleton]
          exact Or.inr trivial)
      have ih' := ih htail
      simp only [unfoldMonochromaticPath, unfoldPathEdges]
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact ih' z hz
      · obtain rfl := List.mem_singleton.mp hz
        exact ⟨allArrowOf e, rfl⟩

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldSymmMonochromaticPath_edges_original
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (color : Bool)
    {x y : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) x y)
    (hp : L.symmIsMonochromatic p color) :
    ∀ z ∈ unfoldPathEdges L e₀
        (unfoldSymmMonochromaticPath L e₀ color p hp),
      ∃ f : AllArrow (V := V), z = Sum.inl f := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  induction p with
  | nil =>
      simp [unfoldSymmMonochromaticPath, unfoldPathEdges]
  | cons p e ih =>
      have htail : L.symmIsMonochromatic p color := by
        intro z hz
        exact hp z (by
          simp only [BinaryLabelling.symmPathLabels, List.mem_append]
          exact Or.inl hz)
      have ih' := ih htail
      cases e with
      | inl f =>
          have hecolor :
              binarySumIndex (G := G) (H := H) (L.label f) = color := by
            exact hp (L.label f) (by
              simp only [BinaryLabelling.symmPathLabels, List.mem_append,
                List.mem_singleton, BinaryLabelling.symmLabel]
              exact Or.inr trivial)
          have hfmono : L.IsMonochromatic f.toPath color := by
            intro z hz
            have hz' : z = L.label f := by
              exact List.mem_singleton.mp hz
            rw [hz']
            exact hecolor
          rw [unfoldSymmMonochromaticPath, unfoldPathEdges_comp]
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact ih' z hz
          · exact unfoldMonochromaticPath_edges_original L e₀ color
              f.toPath hfmono z hz
      | inr f =>
          have hecolor :
              binarySumIndex (G := G) (H := H) (L.label f) = color := by
            have h := hp (L.symmLabel (Sum.inr f)) (by
              simp only [BinaryLabelling.symmPathLabels, List.mem_append,
                List.mem_singleton]
              exact Or.inr trivial)
            change binarySumIndex (G := G) (H := H)
              (factorWordInv (L.label f)) = color at h
            simpa only [binarySumIndex_factorWordInv] using h
          have hfmono : L.IsMonochromatic f.toPath color := by
            intro z hz
            have hz' : z = L.label f := by
              exact List.mem_singleton.mp hz
            rw [hz']
            exact hecolor
          rw [unfoldSymmMonochromaticPath, unfoldPathEdges_comp]
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact ih' z hz
          · have hrev := unfoldPathEdges_reverse L e₀
                (unfoldMonochromaticPath L e₀ color f.toPath hfmono)
            rw [hrev] at hz
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
            have hw' : w ∈ unfoldPathEdges L e₀
                (unfoldMonochromaticPath L e₀ color f.toPath hfmono) :=
              List.mem_reverse.mp hw
            obtain ⟨g, hg⟩ := unfoldMonochromaticPath_edges_original
              L e₀ color f.toPath hfmono w hw'
            refine ⟨allArrowReverse g, ?_⟩
            rw [hg]
            rfl

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldPath_avoid_duplicate
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {x y : UnfoldVertex (allArrowSource e₀)}
    (r : @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) x y)
    (hr : ∀ z ∈ unfoldPathEdges L e₀ r,
      ∃ f : AllArrow (V := V), z = Sum.inl f) :
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
    letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
      unfoldHasReverse L e₀
    foldSymmPathAvoid (qV := unfoldQuiver L e₀)
      (allArrowOf (unfoldDuplicateForward L e₀))
      ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)).mapPath r) := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  induction r with
  | nil =>
      simp [foldSymmPathAvoid]
  | cons r e ih =>
      have htail : ∀ z ∈ unfoldPathEdges L e₀ r,
          ∃ f : AllArrow (V := V), z = Sum.inl f := by
        intro z hz
        apply hr z
        change z ∈ unfoldPathEdges L e₀ r ++ [e.1]
        exact List.mem_append.mpr (Or.inl hz)
      have he : ∃ f : AllArrow (V := V), e.1 = Sum.inl f := by
        apply hr e.1
        change e.1 ∈ unfoldPathEdges L e₀ r ++ [e.1]
        exact List.mem_append.mpr (Or.inr (by simp))
      have hih := ih htail
      obtain ⟨f, hf⟩ := he
      have hne : allArrowOf e ≠
          allArrowOf (unfoldDuplicateForward L e₀) := by
        intro h
        have h' := congrArg (fun z : AllArrow
            (V := UnfoldVertex (allArrowSource e₀)) => z.2.2.1) h
        change e.1 = Sum.inr false at h'
        rw [hf] at h'
        cases h'
      have hne' : allArrowOf e ≠
          allArrowReverse (allArrowOf (unfoldDuplicateForward L e₀)) := by
        intro h
        have h' := congrArg (fun z : AllArrow
            (V := UnfoldVertex (allArrowSource e₀)) => z.2.2.1) h
        change e.1 = Sum.inr true at h'
        rw [hf] at h'
        cases h'
      change foldSymmPathAvoid (qV := unfoldQuiver L e₀)
        (allArrowOf (unfoldDuplicateForward L e₀))
        (((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver L e₀)).mapPath r).cons
          ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver L e₀)).map e))
      simpa only [foldSymmPathAvoid] using ⟨hih, hne, hne'⟩

/-- The duplicate-edge detour packaged as a path for the subsequent fold. -/
def unfoldDuplicateFoldPath
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {b : Symmetrify V}
    (q : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) (show V from allArrowTarget e₀) b)
    (hq : L.symmIsMonochromatic q (unfoldEdgeColor L e₀)) :
    @Quiver.Path (Symmetrify (UnfoldVertex (allArrowSource e₀)))
      (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀))
      (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt L (allArrowSource e₀) e₀ (show V from b)
        (unfoldEdgeColor L e₀)) := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let eD : @Quiver.Hom (Symmetrify (UnfoldVertex (allArrowSource e₀)))
      (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀))
      (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt L (allArrowSource e₀) e₀ (allArrowTarget e₀)
        (unfoldEdgeColor L e₀)) :=
    Sum.inl (unfoldDuplicateForward L e₀)
  exact eD.toPath.comp
    ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)).mapPath
      (unfoldSymmMonochromaticPath L e₀ (unfoldEdgeColor L e₀) q hq))

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldDuplicateFoldPath_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {b : Symmetrify V}
    (q : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) (show V from allArrowTarget e₀) b)
    (hq : L.symmIsMonochromatic q (unfoldEdgeColor L e₀)) :
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
    letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
      unfoldHasReverse L e₀
    (unfoldLabelling L e₀).symmPathRead
      (unfoldDuplicateFoldPath L e₀ q hq) =
      separatedMap (allArrowLabel L e₀) * L.symmPathRead q := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  let qlift := unfoldSymmMonochromaticPath L e₀
    (unfoldEdgeColor L e₀) q hq
  let eD : @Quiver.Hom (Symmetrify (UnfoldVertex (allArrowSource e₀)))
      (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀))
      (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt L (allArrowSource e₀) e₀ (allArrowTarget e₀)
        (unfoldEdgeColor L e₀)) :=
    Sum.inl (unfoldDuplicateForward L e₀)
  have hD : (unfoldLabelling L e₀).symmPathRead eD.toPath =
      separatedMap (allArrowLabel L e₀) := by
    exact (unfoldLabelling L e₀).symmPathRead_toPath eD
  have hmap : (unfoldLabelling L e₀).symmPathRead
        ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver L e₀)).mapPath qlift) =
      (unfoldLabelling L e₀).pathRead qlift :=
    (unfoldLabelling L e₀).symmPathRead_map_of qlift
  change (unfoldLabelling L e₀).symmPathRead
      (eD.toPath.comp
        ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver L e₀)).mapPath qlift)) = _
  exact ((unfoldLabelling L e₀).symmPathRead_comp eD.toPath _).trans
    (congrArg₂ (· * ·) hD (hmap.trans
      (unfoldSymmMonochromaticPath_read L e₀ (unfoldEdgeColor L e₀) q hq)))

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfold_duplicate_safe_tail
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {b : Symmetrify V}
    (q : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _)
      (show V from allArrowTarget e₀)
      b)
    (hq : L.symmIsMonochromatic q (unfoldEdgeColor L e₀))
    (hread : L.symmPathRead q =
      (separatedMap (allArrowLabel L e₀))⁻¹) :
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
    letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
      unfoldHasReverse L e₀
    foldSymmPathAvoid (qV := unfoldQuiver L e₀)
        (allArrowOf (unfoldDuplicateForward L e₀))
        ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver L e₀)).mapPath
          (unfoldSymmMonochromaticPath L e₀
            (unfoldEdgeColor L e₀) q hq)) ∧
      (unfoldLabelling L e₀).symmPathRead
        (unfoldDuplicateFoldPath L e₀ q hq) = 1 := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  constructor
  · exact unfoldPath_avoid_duplicate L e₀
      (unfoldSymmMonochromaticPath L e₀
        (unfoldEdgeColor L e₀) q hq)
      (unfoldSymmMonochromaticPath_edges_original L e₀
        (unfoldEdgeColor L e₀) q hq)
  · rw [unfoldDuplicateFoldPath_read L e₀ q hq, hread,
      mul_inv_cancel]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldDuplicateFoldPath_target_eq_old
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
     :
    unfoldVertexAt L (allArrowSource e₀) e₀
        (show V from allArrowSource e₀) (unfoldEdgeColor L e₀) =
      unfoldOld (allArrowSource e₀) := by
  exact (unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
    (allArrowSource e₀) (unfoldEdgeColor L e₀)).mpr ⟨rfl, rfl⟩

/-- The unfolded marked graph based at the original copy of its split base vertex. -/
def unfoldedMarkedGraph {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base) :
    @MarkedBinaryGraph G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀) n := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver M.labeling e₀
  letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse M.labeling e₀
  have hbase :
      unfoldCanonical (allArrowSource e₀) M.base =
        unfoldOld (allArrowSource e₀) := by
    calc
      unfoldCanonical (allArrowSource e₀) M.base =
          unfoldCanonical (allArrowSource e₀) (allArrowSource e₀) :=
        congrArg (unfoldCanonical (allArrowSource e₀)) ha.symm
      _ = unfoldOld (allArrowSource e₀) :=
        unfoldCanonical_eq_old (allArrowSource e₀)
  refine
    { base := unfoldOld (allArrowSource e₀)
      labeling := unfoldLabelling M.labeling e₀
      loops := fun i => ?_ }
  exact @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
    (unfoldQuiver M.labeling e₀)
    (unfoldCanonical (allArrowSource e₀) M.base)
    (unfoldCanonical (allArrowSource e₀) M.base)
    (unfoldOld (allArrowSource e₀))
    (unfoldOld (allArrowSource e₀)) hbase hbase
    (unfoldLiftPath M.labeling e₀ (M.loops i))

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldedMarkedGraph_read {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base) (i : Fin n) :
    (@MarkedBinaryGraph.read n G H (UnfoldVertex (allArrowSource e₀)) _ _
      (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
      (unfoldedMarkedGraph M e₀ ha)) i = M.read i := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver M.labeling e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse M.labeling e₀
  have hbase :
      unfoldCanonical (allArrowSource e₀) M.base =
        unfoldOld (allArrowSource e₀) := by
    calc
      unfoldCanonical (allArrowSource e₀) M.base =
          unfoldCanonical (allArrowSource e₀) (allArrowSource e₀) :=
        congrArg (unfoldCanonical (allArrowSource e₀)) ha.symm
      _ = unfoldOld (allArrowSource e₀) :=
        unfoldCanonical_eq_old (allArrowSource e₀)
  change (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
      (unfoldLabelling M.labeling e₀) _ _
      ((unfoldedMarkedGraph M e₀ ha).loops i)) =
    M.labeling.pathRead (M.loops i)
  change (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
      (unfoldLabelling M.labeling e₀) _ _
      (@Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver M.labeling e₀)
        (unfoldCanonical (allArrowSource e₀) M.base)
        (unfoldCanonical (allArrowSource e₀) M.base)
        (unfoldOld (allArrowSource e₀))
        (unfoldOld (allArrowSource e₀)) hbase hbase
        (unfoldLiftPath M.labeling e₀ (M.loops i)))) =
    M.labeling.pathRead (M.loops i)
  rw [BinaryLabelling.pathRead_cast, unfoldLiftPath_read]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldedMarkedGraph_isGenerating {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base) (hgen : M.IsGenerating) :
    (@MarkedBinaryGraph.IsGenerating n G H
      (UnfoldVertex (allArrowSource e₀)) _ _
      (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
      (unfoldedMarkedGraph M e₀ ha)) := by
  change Subgroup.closure (Set.range (@MarkedBinaryGraph.read n G H
    (UnfoldVertex (allArrowSource e₀)) _ _
    (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
    (unfoldedMarkedGraph M e₀ ha))) = ⊤
  have hread :
      @MarkedBinaryGraph.read n G H (UnfoldVertex (allArrowSource e₀)) _ _
        (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
        (unfoldedMarkedGraph M e₀ ha) = M.read := by
    funext i
    exact unfoldedMarkedGraph_read M e₀ ha i
  rw [hread]
  exact hgen

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldedMarkedGraph_weaklyConnected {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base)
    (hconn : M.WeaklyConnected) :
    (@MarkedBinaryGraph.WeaklyConnected n G H
      (UnfoldVertex (allArrowSource e₀)) _ _
      (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
      (unfoldedMarkedGraph M e₀ ha)) := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver M.labeling e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse M.labeling e₀
  have hbase :
      unfoldCanonical (allArrowSource e₀) M.base =
        unfoldOld (allArrowSource e₀) := by
    calc
      unfoldCanonical (allArrowSource e₀) M.base =
          unfoldCanonical (allArrowSource e₀) (allArrowSource e₀) :=
        congrArg (unfoldCanonical (allArrowSource e₀)) ha.symm
      _ = unfoldOld (allArrowSource e₀) :=
        unfoldCanonical_eq_old (allArrowSource e₀)
  intro z
  cases z with
  | inl z =>
      obtain ⟨v, hv⟩ := z
      obtain ⟨p⟩ := hconn v
      have htarget :
          unfoldCanonical (allArrowSource e₀) v = Sum.inl ⟨v, hv⟩ := by
        simp [unfoldCanonical, hv]
      refine ⟨@Prefunctor.mapPath (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver M.labeling e₀)
        (Symmetrify (UnfoldVertex (allArrowSource e₀)))
        (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver M.labeling e₀))
        (@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver M.labeling e₀)) _ _ ?_⟩
      exact @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver M.labeling e₀)
          (unfoldCanonical (allArrowSource e₀) M.base)
          (unfoldCanonical (allArrowSource e₀) v)
          (unfoldOld (allArrowSource e₀))
          (Sum.inl ⟨v, hv⟩) hbase htarget
          (unfoldSymmLiftPath M.labeling e₀ p)
  | inr b =>
      cases b with
      | false =>
          refine ⟨@Prefunctor.mapPath (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver M.labeling e₀)
            (Symmetrify (UnfoldVertex (allArrowSource e₀)))
            (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
              (unfoldQuiver M.labeling e₀))
            (@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
              (unfoldQuiver M.labeling e₀)) _ _
            (@Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
              (unfoldQuiver M.labeling e₀)
              (unfoldOld (allArrowSource e₀)))⟩
      | true =>
          refine ⟨@Prefunctor.mapPath (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver M.labeling e₀)
            (Symmetrify (UnfoldVertex (allArrowSource e₀)))
            (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
              (unfoldQuiver M.labeling e₀))
            (@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
              (unfoldQuiver M.labeling e₀)) _ _
            (unfoldSwitchOldNew M.labeling e₀)⟩

/-! ### Rerooting the unfolded marking at the new source -/

/-- The unfolded marked graph rerooted at the new copy of its split base vertex. -/
def unfoldedMarkedGraphNew {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base) :
    @MarkedBinaryGraph G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀) n := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver M.labeling e₀
  letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse M.labeling e₀
  have hbase :
      (unfoldedMarkedGraph M e₀ ha).base = unfoldOld (allArrowSource e₀) := rfl
  refine
    { base := unfoldNew (allArrowSource e₀)
      labeling := unfoldLabelling M.labeling e₀
      loops := fun i => by
        let oldLoop : @Quiver.Path (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver M.labeling e₀)
            (unfoldOld (allArrowSource e₀))
            (unfoldOld (allArrowSource e₀)) :=
          @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver M.labeling e₀)
            (unfoldedMarkedGraph M e₀ ha).base
            (unfoldedMarkedGraph M e₀ ha).base
            (unfoldOld (allArrowSource e₀))
            (unfoldOld (allArrowSource e₀)) hbase hbase
            ((unfoldedMarkedGraph M e₀ ha).loops i)
        exact (unfoldSwitchNewOld M.labeling e₀).comp
          (oldLoop.comp (unfoldSwitchOldNew M.labeling e₀)) }

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldedMarkedGraphNew_read {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base) (i : Fin n) :
    (@MarkedBinaryGraph.read n G H (UnfoldVertex (allArrowSource e₀)) _ _
      (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
      (unfoldedMarkedGraphNew M e₀ ha)) i = M.read i := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver M.labeling e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse M.labeling e₀
  have hbase :
      (unfoldedMarkedGraph M e₀ ha).base = unfoldOld (allArrowSource e₀) := rfl
  let oldLoop : @Quiver.Path (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver M.labeling e₀)
      (unfoldOld (allArrowSource e₀))
      (unfoldOld (allArrowSource e₀)) :=
    @Quiver.Path.cast (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver M.labeling e₀)
      (unfoldedMarkedGraph M e₀ ha).base
      (unfoldedMarkedGraph M e₀ ha).base
      (unfoldOld (allArrowSource e₀))
      (unfoldOld (allArrowSource e₀)) hbase hbase
      ((unfoldedMarkedGraph M e₀ ha).loops i)
  have holdread :
      (unfoldLabelling M.labeling e₀).pathRead
          ((unfoldedMarkedGraph M e₀ ha).loops i) = M.read i := by
    exact unfoldedMarkedGraph_read M e₀ ha i
  change (unfoldLabelling M.labeling e₀).pathRead
      ((unfoldSwitchNewOld M.labeling e₀).comp
        (oldLoop.comp
        (unfoldSwitchOldNew M.labeling e₀))) = M.read i
  rw [BinaryLabelling.pathRead_comp, BinaryLabelling.pathRead_comp,
    unfoldSwitchNewOld_read, BinaryLabelling.pathRead_cast,
    holdread, unfoldSwitchOldNew_read]
  simp

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldedMarkedGraphNew_isGenerating {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base) (hgen : M.IsGenerating) :
    (@MarkedBinaryGraph.IsGenerating n G H
      (UnfoldVertex (allArrowSource e₀)) _ _
      (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
      (unfoldedMarkedGraphNew M e₀ ha)) := by
  change Subgroup.closure (Set.range (@MarkedBinaryGraph.read n G H
    (UnfoldVertex (allArrowSource e₀)) _ _
    (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
    (unfoldedMarkedGraphNew M e₀ ha))) = ⊤
  have hread :
      @MarkedBinaryGraph.read n G H (UnfoldVertex (allArrowSource e₀)) _ _
        (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
        (unfoldedMarkedGraphNew M e₀ ha) = M.read := by
    funext i
    exact unfoldedMarkedGraphNew_read M e₀ ha i
  rw [hread]
  exact hgen

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldedMarkedGraphNew_weaklyConnected {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base)
    (hconn : M.WeaklyConnected) :
    (@MarkedBinaryGraph.WeaklyConnected n G H
      (UnfoldVertex (allArrowSource e₀)) _ _
      (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
      (unfoldedMarkedGraphNew M e₀ ha)) := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver M.labeling e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse M.labeling e₀
  intro z
  obtain ⟨p⟩ := unfoldedMarkedGraph_weaklyConnected M e₀ ha hconn z
  refine ⟨?_⟩
  exact (@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver M.labeling e₀)).mapPath
      (unfoldSwitchNewOld M.labeling e₀) |>.comp p

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldNew_ne_sourceAt_color
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    unfoldNew (allArrowSource e₀) ≠
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowSource e₀) (unfoldEdgeColor L e₀) := by
  intro h
  have hold :
      unfoldVertexAt L (allArrowSource e₀) e₀
          (allArrowSource e₀) (unfoldEdgeColor L e₀) =
        unfoldOld (allArrowSource e₀) :=
    (unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
      (allArrowSource e₀) (unfoldEdgeColor L e₀)).mpr ⟨rfl, rfl⟩
  exact unfoldNew_ne_old (allArrowSource e₀) (h.trans hold)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldNew_ne_vertexAt_of_ne_source
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {b : Symmetrify V}
    (hb : (show V from b) ≠ allArrowSource e₀) :
    unfoldNew (allArrowSource e₀) ≠
      unfoldVertexAt L (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor L e₀) := by
  intro h
  have h' : unfoldVertexAt L (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor L e₀) =
      unfoldNew (allArrowSource e₀) := h.symm
  exact hb ((unfoldVertexAt_eq_new_iff L (allArrowSource e₀) e₀
    (show V from b) (unfoldEdgeColor L e₀)).mp h').1

/-! ### The source-unfold branch supplies a safe fold -/

omit [(a b : V) → Fintype (a ⟶ b)] in
theorem exists_safe_fold_after_unfold {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base)
    {b : Symmetrify V}
    (q : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V _) (show V from allArrowTarget e₀)
      b)
    (hb : (show V from b) ≠ allArrowSource e₀)
    (hq : M.labeling.symmIsMonochromatic q
      (unfoldEdgeColor M.labeling e₀))
    (hread : M.labeling.symmPathRead q =
      (separatedMap (allArrowLabel M.labeling e₀))⁻¹)
    (hgen : M.IsGenerating) (hconn : M.WeaklyConnected) :
    letI : Fintype (UnfoldVertex (allArrowSource e₀)) :=
      unfoldVertexFintype (allArrowSource e₀)
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) :=
      unfoldQuiver M.labeling e₀
    letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
      unfoldHasReverse M.labeling e₀
    ∃ e₁ : AllArrow,
      ∃ ha₁ : allArrowSource e₁ = unfoldNew (allArrowSource e₀),
        ∃ q₁ : @Quiver.Path
          (Symmetrify (UnfoldVertex (allArrowSource e₀)))
          (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver M.labeling e₀))
          ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver M.labeling e₀)).obj (allArrowTarget e₁))
          ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
            (unfoldQuiver M.labeling e₀)).obj
            (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
              (show V from b) (unfoldEdgeColor M.labeling e₀))),
          ∃ hq₁ : foldSymmPathAvoid (qV := unfoldQuiver M.labeling e₀)
              e₁ q₁,
            @MarkedBinaryGraph.IsGenerating n G H
                (foldVertex (unfoldNew (allArrowSource e₀))
                  (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
                    (show V from b) (unfoldEdgeColor M.labeling e₀)))
                _ _ (foldQuiver e₁) (foldHasReverse e₁)
                (foldedMarkedGraphSymm
                  (unfoldedMarkedGraphNew M e₀ ha) e₁ ha₁ q₁ hq₁) ∧
            @MarkedBinaryGraph.WeaklyConnected n G H
                (foldVertex (unfoldNew (allArrowSource e₀))
                  (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
                    (show V from b) (unfoldEdgeColor M.labeling e₀)))
                _ _ (foldQuiver e₁) (foldHasReverse e₁)
                (foldedMarkedGraphSymm
                  (unfoldedMarkedGraphNew M e₀ ha) e₁ ha₁ q₁ hq₁) ∧
            Fintype.card (foldVertex (unfoldNew (allArrowSource e₀))
              (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
                (show V from b) (unfoldEdgeColor M.labeling e₀))) <
              Fintype.card (UnfoldVertex (allArrowSource e₀)) := by
  let : Fintype (UnfoldVertex (allArrowSource e₀)) :=
    unfoldVertexFintype (allArrowSource e₀)
  let : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver M.labeling e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse M.labeling e₀
  let b₁ : UnfoldVertex (allArrowSource e₀) :=
    unfoldVertexAt M.labeling (allArrowSource e₀) e₀
      (show V from b) (unfoldEdgeColor M.labeling e₀)
  let p₀ := unfoldDuplicateFoldPath M.labeling e₀ q hq
  let hp : @Quiver.Path (Symmetrify (UnfoldVertex (allArrowSource e₀)))
      (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver M.labeling e₀))
      (unfoldNew (allArrowSource e₀))
      ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver M.labeling e₀)).obj b₁) := by
    exact p₀
  have hpread :
      (unfoldLabelling M.labeling e₀).symmPathRead hp = 1 := by
    dsimp [hp, p₀, b₁]
    exact (unfold_duplicate_safe_tail M.labeling e₀ q hq hread).2
  have hdecomp : ∃ c : Symmetrify (UnfoldVertex (allArrowSource e₀)),
      ∃ e : @Quiver.Hom (Symmetrify (UnfoldVertex (allArrowSource e₀)))
        (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver M.labeling e₀))
        (show Symmetrify (UnfoldVertex (allArrowSource e₀)) from
          unfoldNew (allArrowSource e₀)) c,
      ∃ q₁ : @Quiver.Path
        (Symmetrify (UnfoldVertex (allArrowSource e₀)))
        (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver M.labeling e₀)) c
        (show Symmetrify (UnfoldVertex (allArrowSource e₀)) from b₁),
        hp = e.toPath.comp q₁ ∧ foldSymmPathAvoid (symmOrientedArrow e) q₁ := by
    let eD : @Quiver.Hom
        (Symmetrify (UnfoldVertex (allArrowSource e₀)))
        (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
          (unfoldQuiver M.labeling e₀))
        (unfoldNew (allArrowSource e₀))
        (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
          (allArrowTarget e₀) (unfoldEdgeColor M.labeling e₀)) :=
      Sum.inl (unfoldDuplicateForward M.labeling e₀)
    let q₁ := (@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver M.labeling e₀)).mapPath
      (unfoldSymmMonochromaticPath M.labeling e₀
        (unfoldEdgeColor M.labeling e₀) q hq)
    refine ⟨_, eD, q₁, ?_, ?_⟩
    · change unfoldDuplicateFoldPath M.labeling e₀ q hq =
        eD.toPath.comp q₁
      rfl
    · exact (unfold_duplicate_safe_tail M.labeling e₀ q hq hread).1
  have hgen' :
      (@MarkedBinaryGraph.IsGenerating n G H
        (UnfoldVertex (allArrowSource e₀)) _ _
        (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
        (unfoldedMarkedGraphNew M e₀ ha)) :=
    unfoldedMarkedGraphNew_isGenerating M e₀ ha hgen
  have hconn' :
      (@MarkedBinaryGraph.WeaklyConnected n G H
        (UnfoldVertex (allArrowSource e₀)) _ _
        (unfoldQuiver M.labeling e₀) (unfoldHasReverse M.labeling e₀)
        (unfoldedMarkedGraphNew M e₀ ha)) :=
    unfoldedMarkedGraphNew_weaklyConnected M e₀ ha hconn
  obtain ⟨e₁, ha₁, q₁, hq₁, hgen₁, hconn₁, hcard₁⟩ :=
    exists_safe_folded_marked_graph
      (M := unfoldedMarkedGraphNew M e₀ ha)
      (a := unfoldNew (allArrowSource e₀)) (b := b₁)
      (unfoldNew_ne_vertexAt_of_ne_source M.labeling e₀ hb) hp hpread hdecomp
      hgen' hconn'
  exact ⟨e₁, ha₁, q₁, hq₁, hgen₁, hconn₁, hcard₁⟩

end GeneralGrushko
end MarshallHall
