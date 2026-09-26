/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.GrushkoUnfold
public import LeanPool.MarshallHall.MarshallHall.GrushkoRemove
public import LeanPool.MarshallHall.MarshallHall.GrushkoInvariant


/-!
## The unsafe-fold branch

The source-unfold construction creates a second copy of a monochromatic
source.  After the subsequent safe fold, the old copy remains a
monochromatic vertex and can be contracted explicitly.  This file contains
the bridge from that local construction to the removal operation.
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

/-! ### A quotient-class test for a vertex away from the fold pair -/

omit [Fintype V] [hV : Quiver.HasInvolutiveReverse V] [(a b : V) → Fintype (a ⟶ b)] in
omit [qV : Quiver V] in
theorem foldVertexMk_eq_of_not_eq {a b x y : V}
    (hxy : foldVertexMk (a := a) (b := b) x =
      foldVertexMk (a := a) (b := b) y)
    (hya : y ≠ a) (hyb : y ≠ b) :
    x = y := by
  have hcode : foldCode a b x = foldCode a b y := by
    have h := congrArg (foldCodeQuotient a b) hxy
    change foldCode a b x = foldCode a b y at h
    exact h
  have hyne : foldCode a b y ≠ none := by
    intro hy
    rcases (foldCode_eq_none_iff (a := a) (b := b) (v := y)).mp hy with
      rfl | rfl
    · exact hya rfl
    · exact hyb rfl
  cases hx : foldCode a b x with
  | none =>
      exfalso
      apply hyne
      rw [← hcode, hx]
  | some e =>
      have hye : foldCode a b y = some e := by
        rw [← hcode, hx]
      have hxe := (foldCode_eq_some_iff (a := a) (b := b)
        (v := x) e).mp hx
      have hye' := (foldCode_eq_some_iff (a := a) (b := b)
        (v := y) e).mp hye
      exact hxe.symm.trans hye'

/-! A connected path to a different vertex contains a non-loop edge at its
endpoint.  This lets the contraction choose its anchor from the graph's
actual connectivity, rather than from a special edge of the unfold. -/

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem exists_nonloop_incident_of_symm_path
    {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V qV) a b)
    (hab : (show V from a) ≠ (show V from b)) :
    ∃ e : AllArrow (V := V),
      (allArrowSource e = (show V from b) ∨
        allArrowTarget e = (show V from b)) ∧
      allArrowSource e ≠ allArrowTarget e := by
  revert hab
  induction p with
  | nil =>
      intro hab
      exact (hab rfl).elim
  | @cons a c p e ih =>
      intro hab
      let e' := symmOrientedArrow e
      by_cases hloop : allArrowSource e' = allArrowTarget e'
      · have hloop' :
            allArrowSource (symmOrientedArrow e) =
              allArrowTarget (symmOrientedArrow e) := by
          simpa [e'] using hloop
        have hac : (show V from a) = (show V from c) := by
          calc
            (show V from a) = allArrowSource (symmOrientedArrow e) :=
              (symmOrientedArrow_source e).symm
            _ = allArrowTarget (symmOrientedArrow e) := hloop'
            _ = (show V from c) := symmOrientedArrow_target e
        obtain ⟨f, hinc, hne⟩ := ih (by
          intro hstart
          apply hab
          exact hstart.trans hac)
        refine ⟨f, ?_, hne⟩
        rcases hinc with hs | ht
        · exact Or.inl (hs.trans hac)
        · exact Or.inr (ht.trans hac)
      · refine ⟨e', Or.inr (by simpa [e'] using
          (symmOrientedArrow_target e)), hloop⟩

/-- A generating connected marked graph admits the prescribed removal of a monochromatic vertex. -/
def HasRemovedMarkedGraph {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {v : V} (hbase : M.base ≠ v) (color : Bool)
    (hmono : MonochromaticVertex M.labeling v color) : Prop :=
  ∃ e₀ : AllArrow (V := V),
    ∃ ha : allArrowSource e₀ = v,
      ∃ hn : allArrowTarget e₀ ≠ v,
        letI : Fintype (RemovedVertex v) := removedVertexFintype v
        letI : Quiver (RemovedVertex v) := removeQuiver e₀ hn
        letI : HasInvolutiveReverse (RemovedVertex v) :=
          removeHasReverse e₀ hn
        letI (x y : RemovedVertex v) :
            Fintype (@Quiver.Hom (RemovedVertex v)
              (removeQuiver e₀ hn) x y) :=
          removeQuiverHomFintype e₀ hn x y
        @MarkedBinaryGraph.IsGenerating n G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
            (removedMarkedGraph M hbase e₀ ha hn color hmono) ∧
          @MarkedBinaryGraph.WeaklyConnected n G H (RemovedVertex v) _ _
            (removeQuiver e₀ hn) (removeHasReverse e₀ hn)
            (removedMarkedGraph M hbase e₀ ha hn color hmono) ∧
          ReverseFree (V := RemovedVertex v) ∧
          Fintype.card (@AllArrow (RemovedVertex v)
            (removeQuiver e₀ hn)) ≤
            2 * (n + Fintype.card (RemovedVertex v) - 1) ∧
          Fintype.card (RemovedVertex v) < Fintype.card V

theorem exists_removed_marked_graph_of_connected {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    {v : V} (hbase : M.base ≠ v) (color : Bool)
    (hmono : MonochromaticVertex M.labeling v color)
    (hgen : M.IsGenerating) (hconn : M.WeaklyConnected)
    (hfree : ReverseFree (V := V))
    (hEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1)) :
    HasRemovedMarkedGraph M hbase color hmono := by
  unfold HasRemovedMarkedGraph
  obtain ⟨p⟩ := hconn v
  obtain ⟨e₀, hinc, hne⟩ :=
    exists_nonloop_incident_of_symm_path p hbase
  have hexanchor : ∃ eₐ : AllArrow (V := V),
      allArrowSource eₐ = v ∧ allArrowTarget eₐ ≠ v := by
    rcases hinc with hs | ht
    · refine ⟨e₀, hs, ?_⟩
      intro ht'
      apply hne
      exact hs.trans ht'.symm
    · refine ⟨allArrowReverse e₀, ?_, ?_⟩
      · simpa using ht
      · intro hs'
        apply hne
        calc
          allArrowSource e₀ = allArrowTarget (allArrowReverse e₀) := by
            simp
          _ = v := hs'
          _ = allArrowSource (allArrowReverse e₀) := by
            simpa using ht.symm
          _ = allArrowTarget e₀ := by simp
  obtain ⟨eₐ, ha, hn⟩ := hexanchor
  refine ⟨eₐ, ha, hn, ?_⟩
  let : Fintype (RemovedVertex v) := removedVertexFintype v
  let : Quiver (RemovedVertex v) := removeQuiver eₐ hn
  let : HasInvolutiveReverse (RemovedVertex v) :=
    removeHasReverse eₐ hn
  let (x y : RemovedVertex v) :
      Fintype (@Quiver.Hom (RemovedVertex v)
        (removeQuiver eₐ hn) x y) :=
    removeQuiverHomFintype eₐ hn x y
  have hgen' := removedMarkedGraph_isGenerating
    M hbase eₐ ha hn color hmono hgen
  have hconn' := removedMarkedGraph_weaklyConnected
    M hbase eₐ ha hn color hmono hconn
  have hfree' : ReverseFree (V := RemovedVertex v) :=
    removeReverseFree eₐ hn hfree
  have hEuler' := removedMarkedGraph_euler_bound
    eₐ hn hfree hEuler
  have hcard' : Fintype.card (RemovedVertex v) < Fintype.card V := by
    have hcard := removedVertex_card_add_one v
    omega
  exact ⟨hgen', hconn', hfree', hEuler', hcard'⟩

/-! ### The old unfolded source stays monochromatic after a fold -/

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem foldedUnfoldOld_incident_color {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base)
    {b : Symmetrify V}
    (hb : (show V from b) ≠ allArrowSource e₀)
    (e₁ : @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver M.labeling e₀)) :
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) :=
      unfoldQuiver M.labeling e₀
    letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
      unfoldHasReverse M.labeling e₀
    ∀ (e : @AllArrow
      (foldVertex (unfoldNew (allArrowSource e₀))
        (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
          (show V from b) (unfoldEdgeColor M.labeling e₀)))
      (foldQuiver e₁)),
      e.1 = foldVertexMk (unfoldOld (allArrowSource e₀)) ∨
        e.2.1 = foldVertexMk (unfoldOld (allArrowSource e₀)) →
      binarySumIndex (G := G) (H := H)
          (@allArrowLabel
            (foldVertex (unfoldNew (allArrowSource e₀))
              (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
                (show V from b) (unfoldEdgeColor M.labeling e₀)))
            G H _ _ (foldQuiver e₁) (foldHasReverse e₁)
            (foldLabelling
              (unfoldedMarkedGraphNew M e₀ ha).labeling e₁) e) =
        unfoldEdgeColor M.labeling e₀ := by
  let : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver M.labeling e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse M.labeling e₀
  intro e hinc
  let a : UnfoldVertex (allArrowSource e₀) :=
    unfoldNew (allArrowSource e₀)
  let b₁ : UnfoldVertex (allArrowSource e₀) :=
    unfoldVertexAt M.labeling (allArrowSource e₀) e₀
      (show V from b) (unfoldEdgeColor M.labeling e₀)
  have hab : a ≠ b₁ := by
    dsimp [a, b₁]
    exact unfoldNew_ne_vertexAt_of_ne_source M.labeling e₀ hb
  have holda : unfoldOld (allArrowSource e₀) ≠ a := by
    exact unfoldOld_ne_new (allArrowSource e₀)
  have holdb : unfoldOld (allArrowSource e₀) ≠ b₁ := by
    dsimp [b₁]
    rw [unfoldVertexAt_of_ne M.labeling (show V from b)
      (unfoldEdgeColor M.labeling e₀) hb]
    intro h
    cases h
  rcases e with ⟨x, y, e⟩
  rcases e with ⟨edge, hs, ht⟩
  rcases hinc with hsrc_inc | htgt_inc
  · have hsrcfold :
        foldVertexMk (a := a) (b := b₁) (allArrowSource edge.1) =
          foldVertexMk (a := a) (b := b₁)
            (unfoldOld (allArrowSource e₀)) := by
      calc
        foldVertexMk (a := a) (b := b₁) (allArrowSource edge.1) =
            foldEdgeSource e₁ edge := rfl
        _ = x := hs
        _ = foldVertexMk (a := a) (b := b₁)
            (unfoldOld (allArrowSource e₀)) := hsrc_inc
    have hsrc : allArrowSource edge.1 =
        unfoldOld (allArrowSource e₀) := by
      exact foldVertexMk_eq_of_not_eq hsrcfold holda holdb
    have hincold : unfoldOldIncident M.labeling e₀ edge.1 :=
      Or.inl hsrc
    change binarySumIndex (G := G) (H := H)
        (unfoldEdgeLabel M.labeling e₀ edge.1.2.2.1) =
      unfoldEdgeColor M.labeling e₀
    exact unfold_old_incident_color M.labeling e₀ edge.1 hincold
  · have htgtfold :
        foldVertexMk (a := a) (b := b₁) (allArrowTarget edge.1) =
          foldVertexMk (a := a) (b := b₁)
            (unfoldOld (allArrowSource e₀)) := by
      calc
        foldVertexMk (a := a) (b := b₁) (allArrowTarget edge.1) =
            foldEdgeTarget e₁ edge := rfl
        _ = y := ht
        _ = foldVertexMk (a := a) (b := b₁)
            (unfoldOld (allArrowSource e₀)) := htgt_inc
    have htgt : allArrowTarget edge.1 =
        unfoldOld (allArrowSource e₀) := by
      exact foldVertexMk_eq_of_not_eq htgtfold holda holdb
    have hincold : unfoldOldIncident M.labeling e₀ edge.1 :=
      Or.inr htgt
    change binarySumIndex (G := G) (H := H)
        (unfoldEdgeLabel M.labeling e₀ edge.1.2.2.1) =
      unfoldEdgeColor M.labeling e₀
    exact unfold_old_incident_color M.labeling e₀ edge.1 hincold

/-! The fold produced by the unfold can now enter the generic contraction
branch. -/

omit [Fintype V] [(a b : V) → Fintype (a ⟶ b)] in
theorem unfoldOld_ne_vertexAt_of_ne_source
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {b : V} (hb : b ≠ allArrowSource e₀) :
    unfoldOld (allArrowSource e₀) ≠
      unfoldVertexAt L (allArrowSource e₀) e₀ b (unfoldEdgeColor L e₀) := by
  rw [unfoldVertexAt_of_ne L b (unfoldEdgeColor L e₀) hb]
  intro h
  cases h

theorem exists_removed_of_unfold_fold {n : ℕ}
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)
    (e₀ : AllArrow (V := V))
    (ha : allArrowSource e₀ = M.base)
    {b : Symmetrify V}
    (hb : (show V from b) ≠ allArrowSource e₀)
    (e₁ : @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver M.labeling e₀))
    (hfree : ReverseFree (V := V))
    (hEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1)) :
    letI : Fintype (UnfoldVertex (allArrowSource e₀)) :=
      unfoldVertexFintype (allArrowSource e₀)
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) :=
      unfoldQuiver M.labeling e₀
    letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
      unfoldHasReverse M.labeling e₀
    letI (x y : UnfoldVertex (allArrowSource e₀)) :
        Fintype (x ⟶ y) :=
      unfoldQuiverHomFintype M.labeling e₀ x y
    letI : Fintype (foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀))) :=
      foldVertexFintype (unfoldNew (allArrowSource e₀))
        (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
          (show V from b) (unfoldEdgeColor M.labeling e₀))
    letI : Quiver (foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀))) :=
      foldQuiver e₁
    letI : HasInvolutiveReverse (foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀))) :=
      foldHasReverse e₁
    letI (x y : foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀))) :
      Fintype (x ⟶ y) :=
      foldQuiverHomFintype e₁ x y
    ∀ (ha₁ : allArrowSource e₁ = unfoldNew (allArrowSource e₀))
    (q₁ : @Quiver.Path
      (Symmetrify (UnfoldVertex (allArrowSource e₀)))
      (@Quiver.symmetrifyQuiver (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver M.labeling e₀))
      ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver M.labeling e₀)).obj (allArrowTarget e₁))
      ((@Quiver.Symmetrify.of (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver M.labeling e₀)).obj
        (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
          (show V from b) (unfoldEdgeColor M.labeling e₀))))
    (hq₁ : foldSymmPathAvoid (qV := unfoldQuiver M.labeling e₀)
      e₁ q₁),
    let N : MarkedBinaryGraph (G := G) (H := H)
        (V := foldVertex (unfoldNew (allArrowSource e₀))
          (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
            (show V from b) (unfoldEdgeColor M.labeling e₀))) n :=
      foldedMarkedGraphSymm
        (unfoldedMarkedGraphNew M e₀ ha) e₁ ha₁ q₁ hq₁
    let holdb : unfoldOld (allArrowSource e₀) ≠
        unfoldVertexAt M.labeling (allArrowSource e₀) e₀
          (show V from b) (unfoldEdgeColor M.labeling e₀) :=
      unfoldOld_ne_vertexAt_of_ne_source M.labeling e₀ hb
    let hbaseN : N.base ≠ foldVertexMk (unfoldOld (allArrowSource e₀)) := by
      dsimp [N]
      intro h
      apply unfoldNew_ne_old (allArrowSource e₀)
      exact foldVertexMk_eq_of_not_eq h
        (unfoldOld_ne_new (allArrowSource e₀)) holdb
    let hmonoN : MonochromaticVertex N.labeling
        (foldVertexMk (unfoldOld (allArrowSource e₀)))
        (unfoldEdgeColor M.labeling e₀) := by
      intro e he
      dsimp [N]
      exact foldedUnfoldOld_incident_color M e₀ ha hb e₁ e he
    ∀ (_hgen₁ :
      @MarkedBinaryGraph.IsGenerating n G H
        (foldVertex (unfoldNew (allArrowSource e₀))
          (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
            (show V from b) (unfoldEdgeColor M.labeling e₀))) _ _
        (foldQuiver e₁) (foldHasReverse e₁) N)
    (_hconn₁ :
      @MarkedBinaryGraph.WeaklyConnected n G H
        (foldVertex (unfoldNew (allArrowSource e₀))
          (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
            (show V from b) (unfoldEdgeColor M.labeling e₀))) _ _
        (foldQuiver e₁) (foldHasReverse e₁) N),
      HasRemovedMarkedGraph N hbaseN (unfoldEdgeColor M.labeling e₀)
        hmonoN := by
  let : Fintype (UnfoldVertex (allArrowSource e₀)) :=
    unfoldVertexFintype (allArrowSource e₀)
  let : Quiver (UnfoldVertex (allArrowSource e₀)) :=
    unfoldQuiver M.labeling e₀
  let : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse M.labeling e₀
  let (x y : UnfoldVertex (allArrowSource e₀)) :
      Fintype (x ⟶ y) :=
    unfoldQuiverHomFintype M.labeling e₀ x y
  let : Fintype (foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀))) :=
    foldVertexFintype (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀))
  let : Quiver (foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀))) :=
    foldQuiver e₁
  let : HasInvolutiveReverse (foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀))) :=
    foldHasReverse e₁
  let (x y : foldVertex (unfoldNew (allArrowSource e₀))
      (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀))) :
      Fintype (x ⟶ y) :=
    foldQuiverHomFintype e₁ x y
  intro ha₁ q₁ hq₁
  dsimp only
  let N : MarkedBinaryGraph (G := G) (H := H)
      (V := foldVertex (unfoldNew (allArrowSource e₀))
        (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
          (show V from b) (unfoldEdgeColor M.labeling e₀))) n :=
    foldedMarkedGraphSymm
      (unfoldedMarkedGraphNew M e₀ ha) e₁ ha₁ q₁ hq₁
  let hab : unfoldNew (allArrowSource e₀) ≠
      unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀) :=
    unfoldNew_ne_vertexAt_of_ne_source M.labeling e₀ hb
  let holdb : unfoldOld (allArrowSource e₀) ≠
      unfoldVertexAt M.labeling (allArrowSource e₀) e₀
        (show V from b) (unfoldEdgeColor M.labeling e₀) :=
    unfoldOld_ne_vertexAt_of_ne_source M.labeling e₀ hb
  let hbaseN : N.base ≠ foldVertexMk (unfoldOld (allArrowSource e₀)) := by
    dsimp [N]
    intro h
    apply unfoldNew_ne_old (allArrowSource e₀)
    exact foldVertexMk_eq_of_not_eq h
      (unfoldOld_ne_new (allArrowSource e₀)) holdb
  let hmonoN : MonochromaticVertex N.labeling
      (foldVertexMk (unfoldOld (allArrowSource e₀)))
      (unfoldEdgeColor M.labeling e₀) := by
    intro e he
    dsimp [N]
    exact foldedUnfoldOld_incident_color M e₀ ha hb e₁ e he
  let hfreeU : ∀ e : @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver M.labeling e₀), allArrowReverse e ≠ e :=
    unfold_allArrow_reverse_ne M.labeling e₀ hfree
  let hfreeN : ReverseFree (V :=
      foldVertex (unfoldNew (allArrowSource e₀))
        (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
          (show V from b) (unfoldEdgeColor M.labeling e₀))) :=
    fold_allArrow_reverse_ne e₁ hfreeU
  let hEulerU :
      Fintype.card (@AllArrow (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver M.labeling e₀)) ≤
        2 * (n + Fintype.card (UnfoldVertex (allArrowSource e₀)) - 1) :=
    unfold_euler_bound M.labeling e₀ hEuler
  let hEulerN :
      Fintype.card (@AllArrow
        (foldVertex (unfoldNew (allArrowSource e₀))
          (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
            (show V from b) (unfoldEdgeColor M.labeling e₀)))
        (foldQuiver e₁)) ≤
        2 * (n + Fintype.card (foldVertex (unfoldNew (allArrowSource e₀))
          (unfoldVertexAt M.labeling (allArrowSource e₀) e₀
            (show V from b) (unfoldEdgeColor M.labeling e₀)) ) - 1) :=
    foldAllArrow_card_le_euler e₁ hab hfreeU hEulerU
  intro hgen₁ hconn₁
  exact exists_removed_marked_graph_of_connected N hbaseN
    (unfoldEdgeColor M.labeling e₀) hmonoN hgen₁ hconn₁ hfreeN hEulerN

end GeneralGrushko
end MarshallHall
