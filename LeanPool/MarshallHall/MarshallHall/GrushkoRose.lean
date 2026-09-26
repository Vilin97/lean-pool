/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.GrushkoFoldStep


/-!
## The canonical subdivided rose

This file constructs the initial labelled graph for a finite tuple in a binary
free product.  Each tuple entry is represented by a path around its own
subdivided petal; all petal endpoints are the common base vertex.  The
construction is intentionally independent of the fold operation, so the
later induction can use it as a genuine finite marked graph rather than as a
picture of a word.
-/

@[expose] public section



open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u

variable {G H : Type u} [Group G] [Group H]

/-- The rose's common base vertex together with the internal letter positions of its petals. -/
abbrev RoseVertex {n : ℕ} (w : Fin n → List (Sum G H)) :=
  Option (Σ i : Fin n, Fin ((w i).length - 1))

/-- The vertex reached at a letter boundary on a rose petal, identifying both ends with the base. -/
def rosePosition {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) (k : Fin ((w i).length + 1)) : RoseVertex w :=
  if h0 : k.val = 0 then none
  else if hlast : k.val = (w i).length then none
  else some ⟨i, ⟨k.val - 1, by omega⟩⟩

omit [Group G] [Group H] in
theorem rosePosition_zero {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) :
    rosePosition w i ⟨0, by omega⟩ = none := by
  simp [rosePosition]

omit [Group G] [Group H] in
@[simp]
theorem rosePosition_last {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) :
    rosePosition w i ⟨(w i).length, by omega⟩ = none := by
  simp [rosePosition]

omit [Group G] [Group H] in
@[simp]
theorem rosePosition_interior {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) (k : Fin ((w i).length - 1)) :
    rosePosition w i ⟨k.val + 1, by omega⟩ = some ⟨i, k⟩ := by
  simp [rosePosition]
  omega

/-- An oriented letter edge on a specified petal of the rose. -/
structure RoseEdge {n : ℕ} (w : Fin n → List (Sum G H)) where
  /-- The petal containing the edge. -/
  i : Fin n
  /-- The letter position of the edge on its petal. -/
  k : Fin (w i).length
  /-- Whether the edge follows the forward reading direction of its petal. -/
  forward : Bool

/-- Reverses the orientation of a rose edge. -/
def RoseEdge.flip {n : ℕ} {w : Fin n → List (Sum G H)} :
    RoseEdge w → RoseEdge w
  | ⟨i, k, true⟩ => ⟨i, k, false⟩
  | ⟨i, k, false⟩ => ⟨i, k, true⟩

/-- The starting vertex of an oriented rose edge. -/
def roseEdgeSource {n : ℕ} {w : Fin n → List (Sum G H)} :
    RoseEdge w → RoseVertex w
  | ⟨i, k, true⟩ => rosePosition w i ⟨k.val, by omega⟩
  | ⟨i, k, false⟩ => rosePosition w i ⟨k.val + 1, by omega⟩

/-- The ending vertex of an oriented rose edge. -/
def roseEdgeTarget {n : ℕ} {w : Fin n → List (Sum G H)} :
    RoseEdge w → RoseVertex w
  | ⟨i, k, true⟩ => rosePosition w i ⟨k.val + 1, by omega⟩
  | ⟨i, k, false⟩ => rosePosition w i ⟨k.val, by omega⟩

omit [Group G] [Group H] in
theorem roseEdgeSource_flip {n : ℕ} {w : Fin n → List (Sum G H)}
    (e : RoseEdge w) :
    roseEdgeSource (RoseEdge.flip e) = roseEdgeTarget e := by
  cases e with
  | mk i k forward =>
      cases forward <;> rfl

omit [Group G] [Group H] in
theorem roseEdgeTarget_flip {n : ℕ} {w : Fin n → List (Sum G H)}
    (e : RoseEdge w) :
    roseEdgeTarget (RoseEdge.flip e) = roseEdgeSource e := by
  cases e with
  | mk i k forward =>
      cases forward <;> rfl

/-- The word letter carried by a rose edge, inverted when traversed backwards. -/
def roseEdgeLabel {n : ℕ} {w : Fin n → List (Sum G H)} :
    RoseEdge w → Sum G H
  | ⟨i, k, true⟩ => (w i).get k
  | ⟨i, k, false⟩ => factorWordInv ((w i).get k)

instance roseQuiver {n : ℕ} (w : Fin n → List (Sum G H)) :
    Quiver (RoseVertex w) where
  Hom a b := {e : RoseEdge w // roseEdgeSource e = a ∧ roseEdgeTarget e = b}

/-- Reverses an arrow in the rose quiver. -/
def roseReverseArrow {n : ℕ} {w : Fin n → List (Sum G H)}
    {a b : RoseVertex w} (e : a ⟶ b) : b ⟶ a :=
  ⟨RoseEdge.flip e.1, by rw [roseEdgeSource_flip, e.2.2],
    by rw [roseEdgeTarget_flip, e.2.1]⟩

instance roseHasReverse {n : ℕ} (w : Fin n → List (Sum G H)) :
    HasInvolutiveReverse (RoseVertex w) where
  reverse' := fun {_ _} e => roseReverseArrow (G := G) (H := H) e
  inv' := by
    intro a b e
    apply Subtype.ext
    change RoseEdge.flip (RoseEdge.flip e.1) = e.1
    cases e.1 with
    | mk i k forward =>
        cases forward <;> rfl

omit [Group G] [Group H] in
theorem rose_allArrow_reverse_ne {n : ℕ}
    (w : Fin n → List (Sum G H))
    (e : AllArrow (V := RoseVertex w)) :
    allArrowReverse e ≠ e := by
  rintro h
  cases e with
  | mk a be =>
    cases be with
    | mk b e =>
      cases e with
      | mk edge hsrc =>
        have hab : b = a := congrArg allArrowSource h
        subst b
        have hsnd : (⟨a, Quiver.reverse ⟨edge, hsrc⟩⟩ :
            Σ b : RoseVertex w, (a ⟶ b)) =
            ⟨a, ⟨edge, hsrc⟩⟩ := by
          injection h
        have hhom : (Quiver.reverse ⟨edge, hsrc⟩ : a ⟶ a) =
            ⟨edge, hsrc⟩ := by
          injection hsnd
        have hedge : RoseEdge.flip edge = edge := by
          have hedge' := congrArg Subtype.val hhom
          change RoseEdge.flip edge = edge at hedge'
          exact hedge'
        cases edge with
        | mk i k forward =>
          cases forward <;> simp [RoseEdge.flip] at hedge

/-- Labels the rose by the letters of the prescribed petal words. -/
def roseLabelling {n : ℕ} (w : Fin n → List (Sum G H)) :
    BinaryLabelling (G := G) (H := H) (V := RoseVertex w) where
  label := fun e => roseEdgeLabel e.1
  reverse_label := by
    intro a b e
    change roseEdgeLabel (RoseEdge.flip e.1) =
      factorWordInv (roseEdgeLabel e.1)
    cases e.1 with
    | mk i k forward =>
        cases forward
        · simpa [roseEdgeLabel, RoseEdge.flip, factorWordInv] using
            (factorWordInv_factorWordInv
              (G := G) (H := H) ((w i).get k)).symm
        · rfl

/-- The forward arrow at a specified letter position on a petal. -/
def roseForwardArrow {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) (k : Fin (w i).length) :
    rosePosition w i ⟨k.val, by omega⟩ ⟶
      rosePosition w i ⟨k.val + 1, by omega⟩ :=
  ⟨⟨i, k, true⟩, rfl, rfl⟩

/-- The initial segment of a petal traversing its first `k` letter edges. -/
def roseForwardPathAux {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) : ∀ (k : ℕ) (_hk : k ≤ (w i).length),
      @Quiver.Path (RoseVertex w) (roseQuiver w)
        none (rosePosition w i ⟨k, by omega⟩)
  | 0, hk => Path.nil
  | k + 1, hk =>
      let p := roseForwardPathAux w i k (by omega)
      let e := roseForwardArrow w i ⟨k, by omega⟩
      p.cons e

/-- The based loop traversing an entire rose petal in its forward direction. -/
def roseForwardPath {n : ℕ} (w : Fin n → List (Sum G H)) (i : Fin n) :
    @Quiver.Path (RoseVertex w) (roseQuiver w)
      (none : RoseVertex w) (none : RoseVertex w) :=
  (roseForwardPathAux w i (w i).length (le_rfl)).cast rfl
    (rosePosition_last w i)

theorem roseForwardPathAux_labels {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) :
    ∀ (k : ℕ) (hk : k ≤ (w i).length),
      (roseLabelling w).pathLabels
          (roseForwardPathAux w i k hk) = (w i).take k := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      rw [roseForwardPathAux]
      simp only [BinaryLabelling.pathLabels]
      rw [ih (by omega)]
      simp [roseLabelling, roseForwardArrow, roseEdgeLabel]

theorem roseForwardPath_labels {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) :
    (roseLabelling w).pathLabels (roseForwardPath w i) = w i := by
  unfold roseForwardPath
  have hcast :
      (roseLabelling w).pathLabels
          ((roseForwardPathAux w i (w i).length (le_rfl)).cast rfl
            (rosePosition_last w i)) =
        (roseLabelling w).pathLabels
          (roseForwardPathAux w i (w i).length (le_rfl)) := by
    exact BinaryLabelling.pathLabels_cast (L := roseLabelling w) rfl
      (rosePosition_last w i)
      (roseForwardPathAux w i (w i).length (le_rfl))
  rw [hcast]
  simpa using roseForwardPathAux_labels w i (w i).length (le_rfl)

theorem roseForwardPath_read {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) :
    (roseLabelling w).pathRead (roseForwardPath w i) = factorWordProd (w i) := by
  change factorWordProd ((roseLabelling w).pathLabels (roseForwardPath w i)) = _
  rw [roseForwardPath_labels]

noncomputable instance roseVertexFintype {n : ℕ} (w : Fin n → List (Sum G H)) :
    Fintype (RoseVertex w) := by
  dsimp [RoseVertex]
  infer_instance

/-- The rose marked by its forward petal loops and labelled by the given words. -/
def roseMarkedGraph {n : ℕ} (w : Fin n → List (Sum G H)) :
    MarkedBinaryGraph (G := G) (H := H) (V := RoseVertex w) n :=
  { base := none
    labeling := roseLabelling w
    loops := roseForwardPath w }

theorem roseMarkedGraph_read {n : ℕ} (w : Fin n → List (Sum G H)) :
    (roseMarkedGraph w).read = factorWordProd ∘ w := by
  funext i
  exact roseForwardPath_read w i

theorem roseMarkedGraph_weaklyConnected {n : ℕ}
    (w : Fin n → List (Sum G H)) :
    (roseMarkedGraph w).WeaklyConnected := by
  intro v
  cases v with
  | none =>
      exact ⟨Path.nil⟩
  | some q =>
      let i : Fin n := q.1
      let k : Fin ((w i).length - 1) := q.2
      have hp :
          @Quiver.Path (RoseVertex w) (roseQuiver w)
            none (rosePosition w i ⟨k.val + 1, by omega⟩) :=
        roseForwardPathAux w i (k.val + 1) (by omega)
      have htarget :
          rosePosition w i ⟨k.val + 1, by omega⟩ = some ⟨i, k⟩ :=
        rosePosition_interior w i k
      refine ⟨((Symmetrify.of (V := RoseVertex w)).mapPath hp).cast rfl htarget⟩

theorem binaryReducedLetters_length (x : G ∗ H) :
    (binaryReducedLetters (G := G) (H := H) x).length = factorWordLength x := by
  simpa [binaryReducedLetters, binaryReducedLength] using
    (factorWordLength_eq_binaryReducedLength (G := G) (H := H) x).symm

/-- The marked rose whose petals spell the reduced words of a tuple of group elements. -/
def reducedTupleRose {n : ℕ} (x : Fin n → G ∗ H) :
    MarkedBinaryGraph (G := G) (H := H)
      (V := RoseVertex (fun i => binaryReducedLetters (x i))) n :=
  roseMarkedGraph (fun i => binaryReducedLetters (x i))

theorem reducedTupleRose_read {n : ℕ} (x : Fin n → G ∗ H) :
    (reducedTupleRose x).read = x := by
  funext i
  change (roseMarkedGraph (fun i => binaryReducedLetters (x i))).read i = x i
  rw [roseMarkedGraph_read]
  exact factorWordProd_binaryReducedLetters (x i)

theorem reducedTupleRose_isGenerating {n : ℕ} (x : Fin n → G ∗ H)
    (hx : Subgroup.closure (Set.range x) = ⊤) :
    (reducedTupleRose x).IsGenerating := by
  change Subgroup.closure (Set.range (reducedTupleRose x).read) = ⊤
  rw [reducedTupleRose_read]
  exact hx

theorem reducedTupleRose_weaklyConnected {n : ℕ}
    (x : Fin n → G ∗ H) :
    (reducedTupleRose x).WeaklyConnected := by
  exact roseMarkedGraph_weaklyConnected
    (fun i => binaryReducedLetters (x i))

end GeneralGrushko
end MarshallHall
