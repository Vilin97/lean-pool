/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.GrushkoEdge


/-!
## Removing a monochromatic vertex

When every edge at a vertex has one factor colour, an incident edge can be
contracted after sliding the other incident edges across it.  The resulting
labels are products inside that one factor, so the operation stays within the
binary labelling format.  This is the marking-preserving contraction used in
the unsafe source-unfold branch of the Grushko proof.
-/

@[expose] public section



open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u v

variable {G H : Type u} [Group G] [Group H]
  {V : Type v} [Fintype V] [qV : Quiver V]
  [hV : HasInvolutiveReverse V]
  [∀ a b : V, Fintype (a ⟶ b)]

/-! ### Products in one of the two factors -/

/-- Multiplies letters in the same factor, returning a factor identity for mismatched tags. -/
def factorMul (x y : Sum G H) : Sum G H := by
  cases x with
  | inl x =>
      cases y with
      | inl y => exact Sum.inl (x * y)
      | inr y => exact Sum.inl 1
  | inr x =>
      cases y with
      | inl y => exact Sum.inl 1
      | inr y => exact Sum.inr (x * y)

@[simp]
theorem binarySumIndex_factorMul (x y : Sum G H)
    (hxy : binarySumIndex (G := G) (H := H) x =
      binarySumIndex (G := G) (H := H) y) :
    binarySumIndex (G := G) (H := H) (factorMul x y) =
      binarySumIndex (G := G) (H := H) x := by
  cases x with
  | inl x =>
      cases y with
      | inl y => simp [factorMul]
      | inr y => cases hxy
  | inr x =>
      cases y with
      | inl y => cases hxy
      | inr y => simp [factorMul]

theorem separatedMap_factorMul (x y : Sum G H)
    (hxy : binarySumIndex (G := G) (H := H) x =
      binarySumIndex (G := G) (H := H) y) :
    separatedMap (factorMul x y) =
      separatedMap x * separatedMap y := by
  cases x with
  | inl x =>
      cases y with
      | inl y => simp [factorMul, separatedMap]
      | inr y => cases hxy
  | inr x =>
      cases y with
      | inl y => cases hxy
      | inr y => simp [factorMul, separatedMap]

theorem factorWordInv_factorMul (x y : Sum G H)
    (hxy : binarySumIndex (G := G) (H := H) x =
      binarySumIndex (G := G) (H := H) y) :
    factorWordInv (factorMul x y) =
      factorMul (factorWordInv y) (factorWordInv x) := by
  cases x with
  | inl x =>
      cases y with
      | inl y => simp [factorMul, factorWordInv]
      | inr y => cases hxy
  | inr x =>
      cases y with
      | inl y => cases hxy
      | inr y => simp [factorMul, factorWordInv]

theorem factorMul_assoc (x y z : Sum G H)
    (hxy : binarySumIndex (G := G) (H := H) x =
      binarySumIndex (G := G) (H := H) y)
    (hyz : binarySumIndex (G := G) (H := H) y =
      binarySumIndex (G := G) (H := H) z)
    (hleft : binarySumIndex (G := G) (H := H) (factorMul x y) =
      binarySumIndex (G := G) (H := H) z)
    (hright : binarySumIndex (G := G) (H := H) x =
      binarySumIndex (G := G) (H := H) (factorMul y z)) :
    factorMul (factorMul x y) z =
      factorMul x (factorMul y z) := by
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          cases z with
          | inl z => simp [factorMul, mul_assoc]
          | inr z => cases hyz
      | inr y => cases hxy
  | inr x =>
      cases y with
      | inl y => cases hxy
      | inr y =>
          cases z with
          | inl z => cases hyz
          | inr z => simp [factorMul, mul_assoc]

theorem factorMul_reverse_both (x y : Sum G H)
    (hxy : binarySumIndex (G := G) (H := H) x =
      binarySumIndex (G := G) (H := H) y) :
    factorMul (factorMul (factorWordInv x) (factorWordInv y)) x =
      factorWordInv (factorMul (factorMul (factorWordInv x) y) x) := by
  cases x <;> cases y <;> simp_all [factorMul, factorWordInv, mul_assoc]

theorem factorMul_reverse_source (x y : Sum G H)
    (hxy : binarySumIndex (G := G) (H := H) x =
      binarySumIndex (G := G) (H := H) y) :
    factorMul (factorWordInv x) (factorWordInv y) =
      factorWordInv (factorMul y x) := by
  cases x <;> cases y <;> simp_all [factorMul, factorWordInv]

theorem factorMul_reverse_target (x y : Sum G H)
    (hxy : binarySumIndex (G := G) (H := H) x =
      binarySumIndex (G := G) (H := H) y) :
    factorMul (factorWordInv y) x =
      factorWordInv (factorMul (factorWordInv x) y) := by
  cases x <;> cases y <;> simp_all [factorMul, factorWordInv]

/-! ### The contracted vertex and edge types -/

/-- The vertices remaining after deletion of the specified vertex. -/
abbrev RemovedVertex (v : V) := {x : V // x ≠ v}

noncomputable instance removedVertexFintype (v : V) :
    Fintype (RemovedVertex (V := V) v) := by
  classical
  dsimp [RemovedVertex]
  infer_instance

/-- The oriented arrows outside the deleted edge and its reverse. -/
abbrev RemovedEdge (e₀ : AllArrow (V := V)) :=
  deletedEdge (AllArrow (V := V)) e₀ (allArrowReverse e₀)

noncomputable instance removedEdgeFintype (e₀ : AllArrow (V := V)) :
    Fintype (RemovedEdge (V := V) e₀) := by
  dsimp [RemovedEdge]
  infer_instance

/-- The surviving endpoint used to replace the deleted vertex. -/
def removeAnchorTarget {v : V} (e₀ : AllArrow (V := V))
    (hn : allArrowTarget e₀ ≠ v) : RemovedVertex v :=
  ⟨allArrowTarget e₀, hn⟩

/-- Sends the deleted vertex to the anchor and leaves other vertices unchanged. -/
def removeEndpoint {v : V} (w : RemovedVertex v) (x : V) :
    RemovedVertex v := by
  classical
  exact if hx : x = v then w else ⟨x, hx⟩

omit [Fintype V] [hV : Quiver.HasInvolutiveReverse V] [(a b : V) → Fintype (a ⟶ b)] in
omit [qV : Quiver V] in
@[simp]
theorem removeEndpoint_eq_of_ne {v : V}
    (w : RemovedVertex v) {x : V} (hx : x ≠ v) :
    removeEndpoint w x = ⟨x, hx⟩ := by
  simp [removeEndpoint, hx]

omit [Fintype V] [hV : Quiver.HasInvolutiveReverse V] [(a b : V) → Fintype (a ⟶ b)] in
omit [qV : Quiver V] in
@[simp]
theorem removeEndpoint_eq_anchor {v : V}
    (w : RemovedVertex v) : removeEndpoint w v = w := by
  simp [removeEndpoint]

/-- The source of a surviving edge after redirecting the deleted vertex to its anchor. -/
def removeEdgeSource {v : V} (e₀ : AllArrow (V := V))
     (hn : allArrowTarget e₀ ≠ v)
    (e : RemovedEdge (V := V) e₀) : RemovedVertex v :=
  removeEndpoint (removeAnchorTarget e₀ hn) (allArrowSource e.1)

/-- The target of a surviving edge after redirecting the deleted vertex to its anchor. -/
def removeEdgeTarget {v : V} (e₀ : AllArrow (V := V))
     (hn : allArrowTarget e₀ ≠ v)
    (e : RemovedEdge (V := V) e₀) : RemovedVertex v :=
  removeEndpoint (removeAnchorTarget e₀ hn) (allArrowTarget e.1)

/-- The quiver obtained by deleting a vertex and its anchor edge and redirecting incident edges. -/
@[reducible]
def removeQuiver {v : V} (e₀ : AllArrow (V := V))
     (hn : allArrowTarget e₀ ≠ v) :
    Quiver (RemovedVertex v) where
  Hom x y := {e : RemovedEdge (V := V) e₀ //
    removeEdgeSource e₀ hn e = x ∧ removeEdgeTarget e₀ hn e = y}

/-- A finite enumeration of arrows in the quiver after vertex removal. -/
@[instance_reducible]
noncomputable def removeQuiverHomFintype {v : V}
    (e₀ : AllArrow (V := V))
    (hn : allArrowTarget e₀ ≠ v) (x y : RemovedVertex v) :
    Fintype (@Quiver.Hom (RemovedVertex v) (removeQuiver e₀ hn) x y) := by
  classical
  change Fintype {e : RemovedEdge (V := V) e₀ //
    removeEdgeSource e₀ hn e = x ∧ removeEdgeTarget e₀ hn e = y}
  infer_instance

/-- Reverses a surviving edge while retaining its avoidance of the deleted pair. -/
def removeEdgeReverse (e₀ : AllArrow (V := V))
    (e : RemovedEdge (V := V) e₀) : RemovedEdge (V := V) e₀ := by
  refine ⟨allArrowReverse e.1, ?_, ?_⟩
  · intro h
    apply e.2.2
    calc
      e.1 = allArrowReverse (allArrowReverse e.1) :=
        (allArrowReverse_reverse e.1).symm
      _ = allArrowReverse e₀ := congrArg (allArrowReverse (V := V)) h
  · intro h
    apply e.2.1
    simpa using congrArg (allArrowReverse (V := V)) h

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgeReverse_reverse (e₀ : AllArrow (V := V))
    (e : RemovedEdge (V := V) e₀) :
    removeEdgeReverse e₀ (removeEdgeReverse e₀ e) = e := by
  apply Subtype.ext
  simp [removeEdgeReverse]

/-- The reverse arrow in the quiver after vertex removal. -/
def removeReverseArrow {v : V} (e₀ : AllArrow (V := V))
     (hn : allArrowTarget e₀ ≠ v)
    {x y : RemovedVertex v}
    (e : @Quiver.Hom (RemovedVertex v) (removeQuiver e₀ hn) x y) :
    @Quiver.Hom (RemovedVertex v) (removeQuiver e₀ hn) y x := by
  refine ⟨removeEdgeReverse e₀ e.1, ?_, ?_⟩
  · change removeEndpoint (removeAnchorTarget e₀ hn)
        (allArrowSource (allArrowReverse e.1.1)) = y
    rw [allArrowSource_reverse]
    exact e.2.2
  · change removeEndpoint (removeAnchorTarget e₀ hn)
        (allArrowTarget (allArrowReverse e.1.1)) = x
    rw [allArrowTarget_reverse]
    exact e.2.1

/-- The involutive reversal inherited by the quiver after vertex removal. -/
@[instance_reducible]
def removeHasReverse {v : V} (e₀ : AllArrow (V := V))
     (hn : allArrowTarget e₀ ≠ v) :
    @Quiver.HasInvolutiveReverse (RemovedVertex v)
      (removeQuiver e₀ hn) :=
  @Quiver.HasInvolutiveReverse.mk
    (RemovedVertex v) (removeQuiver e₀ hn)
    (@Quiver.HasReverse.mk
      (RemovedVertex v) (removeQuiver e₀ hn)
      (fun {x y} e => removeReverseArrow e₀ hn e))
    (by
      intro x y e
      apply Subtype.ext
      exact removeEdgeReverse_reverse e₀ e.1)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeReverseFree {v : V} (e₀ : AllArrow (V := V))
     (hn : allArrowTarget e₀ ≠ v)
    (hfree : ReverseFree (V := V)) :
    letI : Quiver (RemovedVertex v) := removeQuiver e₀ hn
    letI : HasInvolutiveReverse (RemovedVertex v) :=
      removeHasReverse e₀ hn
    ReverseFree (V := RemovedVertex v) := by
  let : Quiver (RemovedVertex v) := removeQuiver e₀ hn
  let : HasInvolutiveReverse (RemovedVertex v) :=
    removeHasReverse e₀ hn
  intro e h
  apply hfree e.2.2.1.1
  have h' := congrArg
    (fun z : @AllArrow (RemovedVertex v) (removeQuiver e₀ hn) =>
      z.2.2.1.1) h
  change allArrowReverse (e.2.2.1.1) = e.2.2.1.1 at h'
  exact h'

noncomputable instance removedAllArrowFintype {v : V}
    (e₀ : AllArrow (V := V))
    (hn : allArrowTarget e₀ ≠ v) :
    Fintype (@AllArrow (RemovedVertex v) (removeQuiver e₀ hn)) := by
  letI : Quiver (RemovedVertex v) := removeQuiver e₀ hn
  letI (x y : RemovedVertex v) :
      Fintype (@Quiver.Hom (RemovedVertex v)
        (removeQuiver e₀ hn) x y) :=
    by
        classical
        change Fintype {e : RemovedEdge e₀ // _}
        infer_instance
  exact allArrowFintype

/-- Identifies packaged arrows in the reduced quiver with surviving original edges. -/
def removeAllArrowEquivEdge {v : V} (e₀ : AllArrow (V := V))
     (hn : allArrowTarget e₀ ≠ v) :
    @AllArrow (RemovedVertex v) (removeQuiver e₀ hn) ≃
      RemovedEdge (V := V) e₀ :=
  { toFun := fun e => e.2.2.1
    invFun := fun e =>
      ⟨removeEdgeSource e₀ hn e, removeEdgeTarget e₀ hn e,
        ⟨e, rfl, rfl⟩⟩
    left_inv := by
      intro e
      cases e with
      | mk a be =>
          cases be with
          | mk b he =>
              cases he with
              | mk edge h =>
                  cases h.1
                  cases h.2
                  rfl
    right_inv := by
      intro e
      rfl }

theorem removeAllArrow_card_eq_removedEdge_card {v : V}
    (e₀ : AllArrow (V := V))
    (hn : allArrowTarget e₀ ≠ v) :
    Fintype.card (@AllArrow (RemovedVertex v) (removeQuiver e₀ hn)) =
      Fintype.card (RemovedEdge (V := V) e₀) := by
  exact Fintype.card_congr (removeAllArrowEquivEdge e₀ hn)

omit [hV : Quiver.HasInvolutiveReverse V] [(a b : V) → Fintype (a ⟶ b)] in
omit [qV : Quiver V] in
theorem removedVertex_card_add_one (v : V) :
    Fintype.card (RemovedVertex v) + 1 = Fintype.card V := by
  classical
  have h := Fintype.card_subtype_compl (α := V) (fun x : V => x = v)
  have hcard : Fintype.card (RemovedVertex v) = Fintype.card V - 1 := by
    simp [RemovedVertex]
  have hpos : 1 ≤ Fintype.card V := by
    let : Nonempty V := ⟨v⟩
    exact Fintype.card_pos
  omega

/-! ### The marking-preserving label slide -/

/-- Every edge incident to the vertex has its label in the specified factor. -/
def MonochromaticVertex (L : BinaryLabelling (G := G) (H := H) (V := V))
    (v : V) (color : Bool) : Prop :=
  ∀ e : AllArrow (V := V),
    allArrowSource e = v ∨ allArrowTarget e = v →
      binarySumIndex (G := G) (H := H) (allArrowLabel L e) = color

/-- The adjusted label of a surviving edge after removing a monochromatic vertex. -/
def removeEdgeLabel {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
     (color : Bool)
    (hmono : MonochromaticVertex L v color)
    (e : RemovedEdge (V := V) e₀) : Sum G H := by
  let g₀ := allArrowLabel L e₀
  let l := allArrowLabel L e.1
  have hg : binarySumIndex (G := G) (H := H) g₀ = color := by
    exact hmono e₀ (Or.inl ha)
  by_cases hs : allArrowSource e.1 = v
  · have hl : binarySumIndex (G := G) (H := H) l = color :=
      hmono e.1 (Or.inl hs)
    by_cases ht : allArrowTarget e.1 = v
    · exact factorMul (factorMul (factorWordInv g₀) l) g₀
    · exact factorMul (factorWordInv g₀) l
  · by_cases ht : allArrowTarget e.1 = v
    · have hl : binarySumIndex (G := G) (H := H) l = color :=
        hmono e.1 (Or.inr ht)
      exact factorMul l g₀
    · exact l

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgeLabel_index {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
     (color : Bool)
    (hmono : MonochromaticVertex L v color)
    (e : RemovedEdge (V := V) e₀) :
    binarySumIndex (G := G) (H := H)
        (removeEdgeLabel L e₀ ha color hmono e) =
    binarySumIndex (G := G) (H := H) (allArrowLabel L e.1) := by
  classical
  let g₀ := allArrowLabel L e₀
  let l := allArrowLabel L e.1
  have hg : binarySumIndex (G := G) (H := H) g₀ = color := by
    exact hmono e₀ (Or.inl ha)
  by_cases hs : allArrowSource e.1 = v
  · have hl : binarySumIndex (G := G) (H := H) l = color :=
      hmono e.1 (Or.inl hs)
    by_cases ht : allArrowTarget e.1 = v
    · have hxy : binarySumIndex (G := G) (H := H)
          (factorWordInv g₀) =
          binarySumIndex (G := G) (H := H) l := by
        rw [binarySumIndex_factorWordInv, hl, hg]
      simp [removeEdgeLabel, hs, ht, g₀, l, hg, hl, hxy]
    · have hxy : binarySumIndex (G := G) (H := H)
          (factorWordInv g₀) =
          binarySumIndex (G := G) (H := H) l := by
        rw [binarySumIndex_factorWordInv, hl, hg]
      simp [removeEdgeLabel, hs, ht, g₀, l, hl, hxy]
  · by_cases ht : allArrowTarget e.1 = v
    · have hl : binarySumIndex (G := G) (H := H) l = color :=
        hmono e.1 (Or.inr ht)
      simp [removeEdgeLabel, hs, ht, g₀, l, hg, hl]
    · simp [removeEdgeLabel, hs, ht]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgeLabel_eq_source_target {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
     (color : Bool)
    (hmono : MonochromaticVertex L v color)
    (e : RemovedEdge (V := V) e₀)
    (hs : allArrowSource e.1 = v) (ht : allArrowTarget e.1 = v) :
    removeEdgeLabel L e₀ ha color hmono e =
      factorMul (factorMul (factorWordInv (allArrowLabel L e₀))
        (allArrowLabel L e.1)) (allArrowLabel L e₀) := by
  simp [removeEdgeLabel, hs, ht]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgeLabel_eq_source_only {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
     (color : Bool)
    (hmono : MonochromaticVertex L v color)
    (e : RemovedEdge (V := V) e₀)
    (hs : allArrowSource e.1 = v) (ht : allArrowTarget e.1 ≠ v) :
    removeEdgeLabel L e₀ ha color hmono e =
      factorMul (factorWordInv (allArrowLabel L e₀))
        (allArrowLabel L e.1) := by
  simp [removeEdgeLabel, hs, ht]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgeLabel_eq_target_only {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
     (color : Bool)
    (hmono : MonochromaticVertex L v color)
    (e : RemovedEdge (V := V) e₀)
    (hs : allArrowSource e.1 ≠ v) (ht : allArrowTarget e.1 = v) :
    removeEdgeLabel L e₀ ha color hmono e =
      factorMul (allArrowLabel L e.1) (allArrowLabel L e₀) := by
  simp [removeEdgeLabel, hs, ht]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgeLabel_eq_neither {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
     (color : Bool)
    (hmono : MonochromaticVertex L v color)
    (e : RemovedEdge (V := V) e₀)
    (hs : allArrowSource e.1 ≠ v) (ht : allArrowTarget e.1 ≠ v) :
    removeEdgeLabel L e₀ ha color hmono e = allArrowLabel L e.1 := by
  simp [removeEdgeLabel, hs, ht]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgeLabel_reverse {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
     (color : Bool)
    (hmono : MonochromaticVertex L v color)
    (e : RemovedEdge (V := V) e₀) :
    removeEdgeLabel L e₀ ha color hmono
        (removeEdgeReverse e₀ e) =
      factorWordInv (removeEdgeLabel L e₀ ha color hmono e) := by
  classical
  let g₀ := allArrowLabel L e₀
  let l := allArrowLabel L e.1
  have hg : binarySumIndex (G := G) (H := H) g₀ = color := by
    exact hmono e₀ (Or.inl ha)
  have hlabelr : allArrowLabel L (allArrowReverse e.1) =
      factorWordInv (allArrowLabel L e.1) := by
    change L.label (Quiver.reverse (allArrowHom e.1)) =
      factorWordInv (L.label (allArrowHom e.1))
    exact L.reverse_label (allArrowHom e.1)
  by_cases hs : allArrowSource e.1 = v
  · have hl : binarySumIndex (G := G) (H := H) l = color :=
      hmono e.1 (Or.inl hs)
    by_cases ht : allArrowTarget e.1 = v
    · have hs' : allArrowSource (removeEdgeReverse e₀ e).1 = v := by
        simpa [removeEdgeReverse, allArrowSource_reverse] using ht
      have ht' : allArrowTarget (removeEdgeReverse e₀ e).1 = v := by
        simpa [removeEdgeReverse, allArrowTarget_reverse] using hs
      rw [removeEdgeLabel_eq_source_target L e₀ ha color hmono
        (removeEdgeReverse e₀ e) hs' ht']
      rw [removeEdgeLabel_eq_source_target L e₀ ha color hmono e hs ht]
      change factorMul (factorMul (factorWordInv g₀)
          (allArrowLabel L (allArrowReverse e.1))) g₀ =
        factorWordInv (factorMul (factorMul (factorWordInv g₀) l) g₀)
      rw [hlabelr]
      apply factorMul_reverse_both
      rw [hg, hl]
    · have hs' : allArrowSource (removeEdgeReverse e₀ e).1 ≠ v := by
        simpa [removeEdgeReverse, allArrowSource_reverse] using ht
      have ht' : allArrowTarget (removeEdgeReverse e₀ e).1 = v := by
        simpa [removeEdgeReverse, allArrowTarget_reverse] using hs
      rw [removeEdgeLabel_eq_target_only L e₀ ha color hmono
        (removeEdgeReverse e₀ e) hs' ht']
      rw [removeEdgeLabel_eq_source_only L e₀ ha color hmono e hs ht]
      change factorMul (allArrowLabel L (allArrowReverse e.1)) g₀ =
        factorWordInv (factorMul (factorWordInv g₀) l)
      rw [hlabelr]
      apply factorMul_reverse_target
      rw [hg, hl]
  · by_cases ht : allArrowTarget e.1 = v
    · have hl : binarySumIndex (G := G) (H := H) l = color :=
        hmono e.1 (Or.inr ht)
      have hs' : allArrowSource (removeEdgeReverse e₀ e).1 = v := by
        simpa [removeEdgeReverse, allArrowSource_reverse] using ht
      have ht' : allArrowTarget (removeEdgeReverse e₀ e).1 ≠ v := by
        simpa [removeEdgeReverse, allArrowTarget_reverse] using hs
      rw [removeEdgeLabel_eq_source_only L e₀ ha color hmono
        (removeEdgeReverse e₀ e) hs' ht']
      rw [removeEdgeLabel_eq_target_only L e₀ ha color hmono e hs ht]
      change factorMul (factorWordInv g₀)
          (allArrowLabel L (allArrowReverse e.1)) =
        factorWordInv (factorMul l g₀)
      rw [hlabelr]
      apply factorMul_reverse_source
      rw [hg, hl]
    · have hs' : allArrowSource (removeEdgeReverse e₀ e).1 ≠ v := by
        simpa [removeEdgeReverse, allArrowSource_reverse] using ht
      have ht' : allArrowTarget (removeEdgeReverse e₀ e).1 ≠ v := by
        simpa [removeEdgeReverse, allArrowTarget_reverse] using hs
      rw [removeEdgeLabel_eq_neither L e₀ ha color hmono
        (removeEdgeReverse e₀ e) hs' ht']
      rw [removeEdgeLabel_eq_neither L e₀ ha color hmono e hs ht]
      change allArrowLabel L (allArrowReverse e.1) = factorWordInv l
      exact hlabelr

/-- The factor labelling on the quiver obtained by removing a monochromatic vertex. -/
def removeLabelling {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
    (hn : allArrowTarget e₀ ≠ v) (color : Bool)
    (hmono : MonochromaticVertex L v color) :
    @BinaryLabelling G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn) (removeHasReverse e₀ hn) := by
  exact @BinaryLabelling.mk G H (RemovedVertex v) _ _
    (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
    (fun {x y} e => removeEdgeLabel L e₀ ha color hmono e.1)
    (by
      intro x y e
      exact removeEdgeLabel_reverse L e₀ ha color hmono e.1)

/-! ### Paths through the contraction -/

/-- The image of an original arrow outside the deleted reversal pair. -/
def removeEdgeOf {v : V} (e₀ : AllArrow (V := V))
     (hn : allArrowTarget e₀ ≠ v)
    {x y : V} (e : x ⟶ y)
    (he₀ : allArrowOf e ≠ e₀)
    (her : allArrowOf e ≠ allArrowReverse e₀) :
    @Quiver.Hom (RemovedVertex v) (removeQuiver e₀ hn)
      (removeEndpoint (removeAnchorTarget e₀ hn) x)
      (removeEndpoint (removeAnchorTarget e₀ hn) y) :=
  ⟨⟨allArrowOf e, he₀, her⟩, rfl, rfl⟩

/-- The trivial replacement path for the deleted anchor edge in its forward orientation. -/
def removeDeletedPathForward {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x y : V} (e : x ⟶ y)
    (h : allArrowOf e = e₀) :
    @Quiver.Path (RemovedVertex v) (removeQuiver e₀ hn)
      (removeEndpoint (removeAnchorTarget e₀ hn) x)
      (removeEndpoint (removeAnchorTarget e₀ hn) y) := by
  classical
  have hcontract :
      removeEndpoint (removeAnchorTarget e₀ hn) (allArrowSource e₀) =
        removeEndpoint (removeAnchorTarget e₀ hn) (allArrowTarget e₀) := by
    simp [removeAnchorTarget, ha, hn]
  have hs : x = allArrowSource e₀ := congrArg allArrowSource h
  have ht : y = allArrowTarget e₀ := congrArg allArrowTarget h
  exact @Quiver.Path.cast (RemovedVertex v) (removeQuiver e₀ hn)
    _ _ _ _ rfl (by rw [ht, hs, hcontract])
    (@Quiver.Path.nil (RemovedVertex v) (removeQuiver e₀ hn)
      (removeEndpoint (removeAnchorTarget e₀ hn) x))

/-- The trivial replacement path for the reverse of the deleted anchor edge. -/
def removeDeletedPathBackward {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x y : V} (e : x ⟶ y)
    (h : allArrowOf e = allArrowReverse e₀) :
    @Quiver.Path (RemovedVertex v) (removeQuiver e₀ hn)
      (removeEndpoint (removeAnchorTarget e₀ hn) x)
      (removeEndpoint (removeAnchorTarget e₀ hn) y) := by
  classical
  have hcontract :
      removeEndpoint (removeAnchorTarget e₀ hn) (allArrowSource e₀) =
        removeEndpoint (removeAnchorTarget e₀ hn) (allArrowTarget e₀) := by
    simp [removeAnchorTarget, ha, hn]
  have hs : x = allArrowTarget e₀ := by
    calc
      x = allArrowSource (allArrowReverse e₀) := congrArg allArrowSource h
      _ = allArrowTarget e₀ := by simp
  have ht : y = allArrowSource e₀ := by
    calc
      y = allArrowTarget (allArrowReverse e₀) := congrArg allArrowTarget h
      _ = allArrowSource e₀ := by simp
  exact @Quiver.Path.cast (RemovedVertex v) (removeQuiver e₀ hn)
    _ _ _ _ rfl (by rw [ht, hs, hcontract, eq_comm])
    (@Quiver.Path.nil (RemovedVertex v) (removeQuiver e₀ hn)
      (removeEndpoint (removeAnchorTarget e₀ hn) x))

/-- The trivial path replacing either orientation of the deleted anchor edge. -/
def removeDeletedPath {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x y : V} (e : x ⟶ y)
    (h : allArrowOf e = e₀ ∨ allArrowOf e = allArrowReverse e₀) :
    @Quiver.Path (RemovedVertex v) (removeQuiver e₀ hn)
      (removeEndpoint (removeAnchorTarget e₀ hn) x)
      (removeEndpoint (removeAnchorTarget e₀ hn) y) := by
  classical
  by_cases he₀ : allArrowOf e = e₀
  · exact removeDeletedPathForward e₀ ha hn e he₀
  · exact removeDeletedPathBackward e₀ ha hn e (h.resolve_left he₀)

/-- Replaces an original edge by its surviving edge or the trivial deleted-edge path. -/
def removeEdgePath {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x y : V} (e : x ⟶ y) :
    @Quiver.Path (RemovedVertex v) (removeQuiver e₀ hn)
      (removeEndpoint (removeAnchorTarget e₀ hn) x)
      (removeEndpoint (removeAnchorTarget e₀ hn) y) := by
  classical
  by_cases he₀ : allArrowOf e = e₀
  · exact removeDeletedPath e₀ ha hn e (Or.inl he₀)
  by_cases her : allArrowOf e = allArrowReverse e₀
  · exact removeDeletedPath e₀ ha hn e (Or.inr her)
  · exact @Quiver.Hom.toPath (RemovedVertex v) (removeQuiver e₀ hn)
      _ _ (removeEdgeOf e₀ hn e he₀ her)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgePath_of_retained {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x y : V} (e : x ⟶ y)
    (he₀ : allArrowOf e ≠ e₀)
    (her : allArrowOf e ≠ allArrowReverse e₀) :
    removeEdgePath e₀ ha hn e =
      @Quiver.Hom.toPath (RemovedVertex v) (removeQuiver e₀ hn)
        _ _ (removeEdgeOf e₀ hn e he₀ her) := by
  simp [removeEdgePath, he₀, her]

/-- Transports an ordinary path through the vertex-removal construction. -/
def removePath {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v) :
    ∀ {x y : V},
      @Quiver.Path V qV x y →
      @Quiver.Path (RemovedVertex v) (removeQuiver e₀ hn)
        (removeEndpoint (removeAnchorTarget e₀ hn) x)
        (removeEndpoint (removeAnchorTarget e₀ hn) y)
  | _, _, Path.nil =>
      @Quiver.Path.nil (RemovedVertex v) (removeQuiver e₀ hn) _
  | _, _, Path.cons p e =>
      @Quiver.Path.comp (RemovedVertex v) (removeQuiver e₀ hn) _ _ _
        (removePath e₀ ha hn p)
        (removeEdgePath e₀ ha hn e)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
@[simp]
theorem removePath_nil {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x : V} :
    removePath e₀ ha hn (@Quiver.Path.nil V qV x) =
      @Quiver.Path.nil (RemovedVertex v) (removeQuiver e₀ hn) _ :=
  by simp only [removePath]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
@[simp]
theorem removePath_cons {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x y z : V} (p : @Quiver.Path V qV x y) (e : y ⟶ z) :
    removePath e₀ ha hn (Path.cons p e) =
      @Quiver.Path.comp (RemovedVertex v) (removeQuiver e₀ hn) _ _ _
        (removePath e₀ ha hn p) (removeEdgePath e₀ ha hn e) :=
  by simp only [removePath]

/-- The label correction at a vertex, equal to the anchor-edge label only at the deleted vertex. -/
def removePotential {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (x : V) : G ∗ H :=
  by
    classical
    exact if x = v then separatedMap (allArrowLabel L e₀) else 1

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
@[simp]
theorem removePotential_eq_vertex {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    removePotential (v := v) L e₀ v = separatedMap (allArrowLabel L e₀) := by
  simp [removePotential]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
@[simp]
theorem removePotential_eq_one_of_ne {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x : V} (hx : x ≠ v) :
    removePotential (v := v) L e₀ x = 1 := by
  simp [removePotential, hx]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgeLabel_read {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
     (color : Bool)
    (hmono : MonochromaticVertex L v color)
    (e : RemovedEdge (V := V) e₀) :
    separatedMap (removeEdgeLabel L e₀ ha color hmono e) =
      (removePotential (v := v) L e₀ (allArrowSource e.1))⁻¹ *
        separatedMap (allArrowLabel L e.1) *
        removePotential (v := v) L e₀ (allArrowTarget e.1) := by
  classical
  let g₀ := allArrowLabel L e₀
  let l := allArrowLabel L e.1
  have hg : binarySumIndex (G := G) (H := H) g₀ = color := by
    exact hmono e₀ (Or.inl ha)
  by_cases hs : allArrowSource e.1 = v
  · have hl : binarySumIndex (G := G) (H := H) l = color :=
      hmono e.1 (Or.inl hs)
    by_cases ht : allArrowTarget e.1 = v
    · have hxy : binarySumIndex (G := G) (H := H)
          (factorWordInv g₀) = binarySumIndex (G := G) (H := H) l := by
        rw [binarySumIndex_factorWordInv, hl, hg]
      have hxy' : binarySumIndex (G := G) (H := H)
          (factorMul (factorWordInv g₀) l) =
            binarySumIndex (G := G) (H := H) g₀ := by
        rw [binarySumIndex_factorMul _ _ hxy,
          binarySumIndex_factorWordInv]
      rw [removeEdgeLabel_eq_source_target L e₀ ha color hmono e hs ht]
      rw [separatedMap_factorMul _ _ hxy', separatedMap_factorMul _ _ hxy]
      simp [removePotential, hs, ht, g₀, l, separatedMap_factorWordInv,
        mul_assoc]
    · have hxy : binarySumIndex (G := G) (H := H)
          (factorWordInv g₀) = binarySumIndex (G := G) (H := H) l := by
        rw [binarySumIndex_factorWordInv, hl, hg]
      rw [removeEdgeLabel_eq_source_only L e₀ ha color hmono e hs ht]
      rw [separatedMap_factorMul _ _ hxy]
      simp [removePotential, hs, ht, g₀, l, separatedMap_factorWordInv,
        ]
  · by_cases ht : allArrowTarget e.1 = v
    · have hl : binarySumIndex (G := G) (H := H) l = color :=
        hmono e.1 (Or.inr ht)
      have hxy : binarySumIndex (G := G) (H := H) l =
          binarySumIndex (G := G) (H := H) g₀ := by
        rw [hl, hg]
      rw [removeEdgeLabel_eq_target_only L e₀ ha color hmono e hs ht]
      rw [separatedMap_factorMul _ _ hxy]
      simp [removePotential, hs, ht, g₀, l]
    · rw [removeEdgeLabel_eq_neither L e₀ ha color hmono e hs ht]
      simp [removePotential, hs, ht]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeEdgePath_read {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
    (hn : allArrowTarget e₀ ≠ v) (color : Bool)
    (hmono : MonochromaticVertex L v color)
    {x y : V} (e : x ⟶ y) :
    (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
      (removeLabelling L e₀ ha hn color hmono) _ _
      (removeEdgePath e₀ ha hn e)) =
      (removePotential (v := v) L e₀ x)⁻¹ *
        separatedMap (L.label e) *
        removePotential (v := v) L e₀ y := by
  classical
  by_cases he₀ : allArrowOf e = e₀
  · have hs : x = v := by
      calc
        x = allArrowSource (allArrowOf e) := rfl
        _ = allArrowSource e₀ := congrArg allArrowSource he₀
        _ = v := ha
    have ht : y = allArrowTarget e₀ := by
      calc
        y = allArrowTarget (allArrowOf e) := rfl
        _ = allArrowTarget e₀ := congrArg allArrowTarget he₀
    have hty : y ≠ v := by simpa [ht] using hn
    have hlabel : L.label e = allArrowLabel L e₀ := by
      calc
        L.label e = allArrowLabel L (allArrowOf e) := rfl
        _ = allArrowLabel L e₀ := congrArg (allArrowLabel L) he₀
    have hpath :
        (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
          (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
          (removeLabelling L e₀ ha hn color hmono) _ _
          (removeEdgePath e₀ ha hn e)) = 1 := by
      simp [removeEdgePath, removeDeletedPath, removeDeletedPathForward,
        he₀, BinaryLabelling.pathRead_cast, BinaryLabelling.pathRead_nil]
    have hpx : removePotential (v := v) L e₀ x =
        separatedMap (allArrowLabel L e₀) := by
      rw [hs]
      simp
    have hpy : removePotential (v := v) L e₀ y = 1 :=
      removePotential_eq_one_of_ne L e₀ hty
    rw [hpath, hpx, hpy, hlabel]
    simp []
  · by_cases her : allArrowOf e = allArrowReverse e₀
    · have hs : x = allArrowTarget e₀ := by
        calc
          x = allArrowSource (allArrowOf e) := rfl
          _ = allArrowSource (allArrowReverse e₀) := congrArg allArrowSource her
          _ = allArrowTarget e₀ := by simp
      have ht : y = allArrowSource e₀ := by
        calc
          y = allArrowTarget (allArrowOf e) := rfl
          _ = allArrowTarget (allArrowReverse e₀) := congrArg allArrowTarget her
          _ = allArrowSource e₀ := by simp
      have hsx : x ≠ v := by simpa [hs] using hn
      have hneq : allArrowReverse e₀ ≠ e₀ := by
        intro h
        apply he₀
        exact her.trans h
      have hlabel : L.label e = factorWordInv (allArrowLabel L e₀) := by
        calc
          L.label e = allArrowLabel L (allArrowOf e) := rfl
          _ = allArrowLabel L (allArrowReverse e₀) :=
            congrArg (allArrowLabel L) her
          _ = factorWordInv (allArrowLabel L e₀) := by
            change L.label (Quiver.reverse (allArrowHom e₀)) =
              factorWordInv (L.label (allArrowHom e₀))
            exact L.reverse_label (allArrowHom e₀)
      have hpath :
          (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
            (removeLabelling L e₀ ha hn color hmono) _ _
            (removeEdgePath e₀ ha hn e)) = 1 := by
        simp [removeEdgePath, removeDeletedPath, removeDeletedPathBackward,
          her, hneq, BinaryLabelling.pathRead_cast,
          BinaryLabelling.pathRead_nil]
      have hpx : removePotential (v := v) L e₀ x = 1 :=
        removePotential_eq_one_of_ne L e₀ hsx
      have hpy : removePotential (v := v) L e₀ y =
          separatedMap (allArrowLabel L e₀) := by
        rw [ht, ha]
        simp
      rw [hpath, hpx, hpy, hlabel]
      simp [separatedMap_factorWordInv]
    · rw [removeEdgePath_of_retained e₀ ha hn e he₀ her]
      simp only [BinaryLabelling.pathRead_toPath]
      change separatedMap (removeEdgeLabel L e₀ ha color hmono
          ⟨allArrowOf e, he₀, her⟩) =
        (removePotential (v := v) L e₀ x)⁻¹ *
          separatedMap (L.label e) *
          removePotential (v := v) L e₀ y
      simpa only [allArrowLabel, allArrowSource_of, allArrowTarget_of,
        allArrowHom_of] using
        (removeEdgeLabel_read L e₀ ha color hmono
          ⟨allArrowOf e, he₀, her⟩)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removePath_read {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
    (hn : allArrowTarget e₀ ≠ v) (color : Bool)
    (hmono : MonochromaticVertex L v color)
    {x y : V} (p : @Quiver.Path V qV x y) :
    (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
      (removeLabelling L e₀ ha hn color hmono) _ _
      (removePath e₀ ha hn p)) =
      (removePotential (v := v) L e₀ x)⁻¹ *
        L.pathRead p *
        removePotential (v := v) L e₀ y := by
  classical
  induction p with
  | nil =>
      simp only [removePath, BinaryLabelling.pathRead_nil,
        L.pathRead_nil]
      simp []
  | @cons z y p e ih =>
      calc
        (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
            (removeLabelling L e₀ ha hn color hmono) _ _
            (removePath e₀ ha hn (Path.cons p e))) =
          (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
            (removeLabelling L e₀ ha hn color hmono) _ _
            (removePath e₀ ha hn p)) *
          (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
            (removeLabelling L e₀ ha hn color hmono) _ _
            (removeEdgePath e₀ ha hn e)) := by
              rw [removePath]
              exact @BinaryLabelling.pathRead_comp G H (RemovedVertex v)
                _ _ (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
                (removeLabelling L e₀ ha hn color hmono) _ _
                (removePath e₀ ha hn p) _
                (removeEdgePath e₀ ha hn e)
        _ = ((removePotential (v := v) L e₀ x)⁻¹ *
              L.pathRead p * removePotential (v := v) L e₀ z) *
            ((removePotential (v := v) L e₀ z)⁻¹ *
              separatedMap (L.label e) *
              removePotential (v := v) L e₀ y) := by
              rw [ih, removeEdgePath_read L e₀ ha hn color hmono]
        _ = (removePotential (v := v) L e₀ x)⁻¹ *
              L.pathRead (Path.cons p e) *
              removePotential (v := v) L e₀ y := by
              rw [← Path.comp_toPath_eq_cons, L.pathRead_comp,
                L.pathRead_toPath]
              simp [mul_assoc]

/-- The vertex map induced on symmetrized quivers by vertex removal. -/
def removeVertexMap {v : V} (e₀ : AllArrow (V := V))
     (hn : allArrowTarget e₀ ≠ v)
    (x : Symmetrify V) : Symmetrify (RemovedVertex v) :=
  removeEndpoint (removeAnchorTarget e₀ hn) (show V from x)

/-- The symmetrized replacement path for an edge under vertex removal. -/
def removeSymmEdgePath {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x y : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V)
      (@Quiver.symmetrifyQuiver V qV) x y) :
    @Quiver.Path (Symmetrify (RemovedVertex v))
      (@Quiver.symmetrifyQuiver (RemovedVertex v)
        (removeQuiver e₀ hn))
      (removeVertexMap e₀ hn x) (removeVertexMap e₀ hn y) := by
  cases e with
  | inl f =>
      exact @Prefunctor.mapPath (RemovedVertex v) (removeQuiver e₀ hn)
        (Symmetrify (RemovedVertex v))
        (@Quiver.symmetrifyQuiver (RemovedVertex v)
          (removeQuiver e₀ hn))
        (@Quiver.Symmetrify.of (RemovedVertex v)
          (removeQuiver e₀ hn)) _ _ (removeEdgePath e₀ ha hn f)
  | inr f =>
      exact @Prefunctor.mapPath (RemovedVertex v) (removeQuiver e₀ hn)
        (Symmetrify (RemovedVertex v))
        (@Quiver.symmetrifyQuiver (RemovedVertex v)
          (removeQuiver e₀ hn))
        (@Quiver.Symmetrify.of (RemovedVertex v)
          (removeQuiver e₀ hn)) _ _
        (removeEdgePath e₀ ha hn (Quiver.reverse f))

/-- Transports a symmetrized path through the vertex-removal construction. -/
def removeSymmPath {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v) :
    ∀ {x y : Symmetrify V},
      @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V qV) x y →
      @Quiver.Path (Symmetrify (RemovedVertex v))
        (@Quiver.symmetrifyQuiver (RemovedVertex v)
          (removeQuiver e₀ hn))
        (removeVertexMap e₀ hn x) (removeVertexMap e₀ hn y)
  | _, _, Path.nil =>
      @Quiver.Path.nil (Symmetrify (RemovedVertex v))
        (@Quiver.symmetrifyQuiver (RemovedVertex v)
          (removeQuiver e₀ hn)) _
  | _, _, Path.cons p e =>
      @Quiver.Path.comp (Symmetrify (RemovedVertex v))
        (@Quiver.symmetrifyQuiver (RemovedVertex v)
          (removeQuiver e₀ hn)) _ _ _
        (removeSymmPath e₀ ha hn p)
        (removeSymmEdgePath e₀ ha hn e)

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
@[simp]
theorem removeSymmPath_nil {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x : Symmetrify V} :
    removeSymmPath e₀ ha hn
        (@Quiver.Path.nil (Symmetrify V)
          (@Quiver.symmetrifyQuiver V qV) x) =
      @Quiver.Path.nil (Symmetrify (RemovedVertex v))
        (@Quiver.symmetrifyQuiver (RemovedVertex v)
          (removeQuiver e₀ hn)) _ := by
  simp only [removeSymmPath]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
@[simp]
theorem removeSymmPath_cons {v : V} (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = v) (hn : allArrowTarget e₀ ≠ v)
    {x y z : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V qV) x y)
    (e : @Quiver.Hom (Symmetrify V)
      (@Quiver.symmetrifyQuiver V qV) y z) :
    removeSymmPath e₀ ha hn (Path.cons p e) =
      @Quiver.Path.comp (Symmetrify (RemovedVertex v))
        (@Quiver.symmetrifyQuiver (RemovedVertex v)
          (removeQuiver e₀ hn)) _ _ _
        (removeSymmPath e₀ ha hn p)
        (removeSymmEdgePath e₀ ha hn e) := by
  simp only [removeSymmPath]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeSymmEdgePath_read {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
    (hn : allArrowTarget e₀ ≠ v) (color : Bool)
    (hmono : MonochromaticVertex L v color)
    {x y : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V)
      (@Quiver.symmetrifyQuiver V qV) x y) :
    (@BinaryLabelling.symmPathRead G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn)
      (removeHasReverse e₀ hn)
      (removeLabelling L e₀ ha hn color hmono) _ _
      (removeSymmEdgePath e₀ ha hn e)) =
      (removePotential (v := v) L e₀ (show V from x))⁻¹ *
        separatedMap (L.symmLabel e) *
        removePotential (v := v) L e₀ (show V from y) := by
  cases e with
  | inl f =>
      simp only [removeSymmEdgePath]
      have hmap :=
        @BinaryLabelling.symmPathRead_map_of G H (RemovedVertex v) _ _
          (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
          (removeLabelling L e₀ ha hn color hmono)
          _ _
          (removeEdgePath e₀ ha hn f)
      exact hmap.trans (removeEdgePath_read L e₀ ha hn color hmono f)
  | inr f =>
      simp only [removeSymmEdgePath]
      have hmap :=
        @BinaryLabelling.symmPathRead_map_of G H (RemovedVertex v) _ _
          (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
          (removeLabelling L e₀ ha hn color hmono)
          _ _
          (removeEdgePath e₀ ha hn (Quiver.reverse f))
      have h := removeEdgePath_read L e₀ ha hn color hmono
        (Quiver.reverse f)
      have hread :
          (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
            (removeLabelling L e₀ ha hn color hmono) _ _
            (removeEdgePath e₀ ha hn (Quiver.reverse f))) = _ := h
      exact hmap.trans (hread.trans
        (congrArg (fun z => (removePotential L e₀ x)⁻¹ * separatedMap z *
          removePotential L e₀ y) (L.reverse_label f)))

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removeSymmPath_read {v : V}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
    (hn : allArrowTarget e₀ ≠ v) (color : Bool)
    (hmono : MonochromaticVertex L v color)
    {x y : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V)
      (@Quiver.symmetrifyQuiver V qV) x y) :
    (@BinaryLabelling.symmPathRead G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn)
      (removeHasReverse e₀ hn)
      (removeLabelling L e₀ ha hn color hmono) _ _
      (removeSymmPath e₀ ha hn p)) =
      (removePotential (v := v) L e₀ (show V from x))⁻¹ *
        L.symmPathRead p *
        removePotential (v := v) L e₀ (show V from y) := by
  induction p with
  | nil =>
      simp only [removeSymmPath, BinaryLabelling.symmPathRead_nil,
        L.symmPathRead_nil]
      simp []
  | @cons z y p e ih =>
      calc
        (@BinaryLabelling.symmPathRead G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn)
            (removeHasReverse e₀ hn)
            (removeLabelling L e₀ ha hn color hmono) _ _
            (removeSymmPath e₀ ha hn (Path.cons p e))) =
          (@BinaryLabelling.symmPathRead G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn)
            (removeHasReverse e₀ hn)
            (removeLabelling L e₀ ha hn color hmono) _ _
            (removeSymmPath e₀ ha hn p)) *
          (@BinaryLabelling.symmPathRead G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn)
            (removeHasReverse e₀ hn)
            (removeLabelling L e₀ ha hn color hmono) _ _
            (removeSymmEdgePath e₀ ha hn e)) := by
              rw [removeSymmPath]
              exact @BinaryLabelling.symmPathRead_comp G H
                (RemovedVertex v) _ _
                (removeQuiver e₀ hn)
                (removeHasReverse e₀ hn)
                (removeLabelling L e₀ ha hn color hmono) _ _
                (removeSymmPath e₀ ha hn p) _
                (removeSymmEdgePath e₀ ha hn e)
        _ = ((removePotential (v := v) L e₀ (show V from x))⁻¹ *
              L.symmPathRead p *
              removePotential (v := v) L e₀ (show V from z)) *
            ((removePotential (v := v) L e₀ (show V from z))⁻¹ *
              separatedMap (L.symmLabel e) *
              removePotential (v := v) L e₀ (show V from y)) := by
              rw [ih, removeSymmEdgePath_read L e₀ ha hn color hmono]
        _ = (removePotential (v := v) L e₀ (show V from x))⁻¹ *
              L.symmPathRead (Path.cons p e) *
              removePotential (v := v) L e₀ (show V from y) := by
              rw [← Path.comp_toPath_eq_cons, L.symmPathRead_comp,
                L.symmPathRead_toPath]
              simp [mul_assoc]

/-! ### The contracted marked graph -/

/-- The marked graph obtained by removing a monochromatic vertex away from its base. -/
def removedMarkedGraph {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {v : V} (hbase : M.base ≠ v)
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
    (hn : allArrowTarget e₀ ≠ v) (color : Bool)
    (hmono : MonochromaticVertex M.labeling v color) :
    @MarkedBinaryGraph G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn) (removeHasReverse e₀ hn) n :=
  @MarkedBinaryGraph.mk G H (RemovedVertex v) _ _
    (removeQuiver e₀ hn) (removeHasReverse e₀ hn) n
    ⟨M.base, hbase⟩
    (removeLabelling M.labeling e₀ ha hn color hmono)
    (fun i =>
      @Quiver.Path.cast (RemovedVertex v) (removeQuiver e₀ hn)
        _ _ _ _
        (removeEndpoint_eq_of_ne (removeAnchorTarget e₀ hn) hbase)
        (removeEndpoint_eq_of_ne (removeAnchorTarget e₀ hn) hbase)
        (removePath e₀ ha hn (M.loops i)))

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removedMarkedGraph_read {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {v : V} (hbase : M.base ≠ v)
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
    (hn : allArrowTarget e₀ ≠ v) (color : Bool)
    (hmono : MonochromaticVertex M.labeling v color) :
    (@MarkedBinaryGraph.read n G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
      (removedMarkedGraph M hbase e₀ ha hn color hmono)) = M.read := by
  funext i
  change (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
      (removeLabelling M.labeling e₀ ha hn color hmono) _ _
      (@Quiver.Path.cast (RemovedVertex v) (removeQuiver e₀ hn)
        _ _ _ _
        (removeEndpoint_eq_of_ne (removeAnchorTarget e₀ hn) hbase)
        (removeEndpoint_eq_of_ne (removeAnchorTarget e₀ hn) hbase)
        (removePath e₀ ha hn (M.loops i)))) =
    M.labeling.pathRead (M.loops i)
  calc
    (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
        (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
        (removeLabelling M.labeling e₀ ha hn color hmono) _ _
        (@Quiver.Path.cast (RemovedVertex v) (removeQuiver e₀ hn)
          _ _ _ _
          (removeEndpoint_eq_of_ne (removeAnchorTarget e₀ hn) hbase)
          (removeEndpoint_eq_of_ne (removeAnchorTarget e₀ hn) hbase)
          (removePath e₀ ha hn (M.loops i)))) =
      (@BinaryLabelling.pathRead G H (RemovedVertex v) _ _
        (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
        (removeLabelling M.labeling e₀ ha hn color hmono) _ _
        (removePath e₀ ha hn (M.loops i))) :=
      @BinaryLabelling.pathRead_cast G H (RemovedVertex v) _ _
        (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
        (removeLabelling M.labeling e₀ ha hn color hmono) _ _ _ _
        (removeEndpoint_eq_of_ne (removeAnchorTarget e₀ hn) hbase)
        (removeEndpoint_eq_of_ne (removeAnchorTarget e₀ hn) hbase)
        (removePath e₀ ha hn (M.loops i))
    _ = (removePotential (v := v) M.labeling e₀ M.base)⁻¹ *
        M.labeling.pathRead (M.loops i) *
        removePotential (v := v) M.labeling e₀ M.base :=
      removePath_read M.labeling e₀ ha hn color hmono (M.loops i)
    _ = M.labeling.pathRead (M.loops i) := by
      simp [removePotential_eq_one_of_ne M.labeling e₀ hbase]

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removedMarkedGraph_isGenerating {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {v : V} (hbase : M.base ≠ v)
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
    (hn : allArrowTarget e₀ ≠ v) (color : Bool)
    (hmono : MonochromaticVertex M.labeling v color)
    (hM : M.IsGenerating) :
    @MarkedBinaryGraph.IsGenerating n G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
      (removedMarkedGraph M hbase e₀ ha hn color hmono) := by
  change Subgroup.closure (Set.range
    (@MarkedBinaryGraph.read n G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
      (removedMarkedGraph M hbase e₀ ha hn color hmono))) = ⊤
  rw [removedMarkedGraph_read M hbase e₀ ha hn color hmono]
  exact hM

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem removedMarkedGraph_weaklyConnected {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {v : V} (hbase : M.base ≠ v)
    (e₀ : AllArrow (V := V)) (ha : allArrowSource e₀ = v)
    (hn : allArrowTarget e₀ ≠ v) (color : Bool)
    (hmono : MonochromaticVertex M.labeling v color)
    (hM : M.WeaklyConnected) :
    @MarkedBinaryGraph.WeaklyConnected n G H (RemovedVertex v) _ _
      (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
      (removedMarkedGraph M hbase e₀ ha hn color hmono) := by
  intro w
  obtain ⟨p⟩ := hM w.1
  have hstart : removeVertexMap e₀ hn (show V from M.base) =
      (⟨M.base, hbase⟩ : RemovedVertex v) := by
    exact removeEndpoint_eq_of_ne _ hbase
  have hend : removeVertexMap e₀ hn (show V from w.1) = w := by
    apply Subtype.ext
    simp [removeVertexMap, removeEndpoint_eq_of_ne, w.property]
  exact ⟨@Quiver.Path.cast (Symmetrify (RemovedVertex v))
    (@Quiver.symmetrifyQuiver (RemovedVertex v)
      (removeQuiver e₀ hn)) _ _ _ _ hstart hend
      (removeSymmPath e₀ ha hn p)⟩

theorem removedMarkedGraph_euler_bound {n : ℕ}
    {v : V}
    (e₀ : AllArrow (V := V))
    (hn : allArrowTarget e₀ ≠ v) (hfree : ReverseFree (V := V))
    (hEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1)) :
    letI : Fintype (RemovedVertex v) := removedVertexFintype v
    letI : Quiver (RemovedVertex v) := removeQuiver e₀ hn
    letI : HasInvolutiveReverse (RemovedVertex v) :=
      removeHasReverse e₀ hn
    letI (x y : RemovedVertex v) :
        Fintype (@Quiver.Hom (RemovedVertex v)
          (removeQuiver e₀ hn) x y) :=
      removeQuiverHomFintype e₀ hn x y
    Fintype.card (@AllArrow (RemovedVertex v) (removeQuiver e₀ hn)) ≤
      2 * (n + Fintype.card (RemovedVertex v) - 1) := by
  let : Fintype (RemovedVertex v) := removedVertexFintype v
  let : Quiver (RemovedVertex v) := removeQuiver e₀ hn
  let : HasInvolutiveReverse (RemovedVertex v) :=
    removeHasReverse e₀ hn
  let (x y : RemovedVertex v) :
      Fintype (@Quiver.Hom (RemovedVertex v)
        (removeQuiver e₀ hn) x y) :=
    removeQuiverHomFintype e₀ hn x y
  have hcard := removeAllArrow_card_eq_removedEdge_card e₀ hn
  have hdel := deletedEdge_card_add_two_eq
    (AllArrow (V := V)) e₀ (allArrowReverse e₀) (hfree e₀).symm
  have hcard' :
      Fintype.card (@AllArrow (RemovedVertex v) (removeQuiver e₀ hn)) + 2 =
        Fintype.card (AllArrow (V := V)) := by
    rw [hcard]
    exact hdel
  have hvertex := removedVertex_card_add_one v
  omega

end GeneralGrushko
end MarshallHall
