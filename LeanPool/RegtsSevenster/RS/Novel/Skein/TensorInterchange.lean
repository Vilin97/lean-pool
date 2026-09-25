/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorFragment
import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseRotate

/-!
# Interchange law of the skein category

The interchange law holds at the fragment level: tensoring two
composites is equivalent to composing the two tensors.  This file
constructs the `Fragment.Equiv` witnessing

  `(F₁ . G₁) ⊗ (F₂ . G₂) ≃ (F₁ ⊗ F₂) . (G₁ ⊗ G₂)`

by normalizing both sides to iterated gluing over the common
ambient `(F₁ ⊔ G₁) ⊔ (F₂ ⊔ G₂)` and meeting the label chains.
-/

namespace RS

namespace Fragment

variable {α β γ δ : Type}

/-- Four-summand exchange: `(W₁ ⊔ W₂) ⊔ (W₃ ⊔ W₄)` reshuffles
to `(W₁ ⊔ W₃) ⊔ (W₂ ⊔ W₄)` up to the `sumSumSumComm`
relabelling. -/
noncomputable def disjUnionExchange
    (W₁ : Fragment α) (W₂ : Fragment β)
    (W₃ : Fragment γ) (W₄ : Fragment δ) :
    ((W₁.disjUnion W₂).disjUnion (W₃.disjUnion W₄)).Equiv
      (((W₁.disjUnion W₃).disjUnion (W₂.disjUnion W₄)).relabel
        (_root_.Equiv.sumSumSumComm α γ β δ)) where
  flagEquiv := _root_.Equiv.sumSumSumComm
    W₁.Flag W₂.Flag W₃.Flag W₄.Flag
  vertexEquiv := _root_.Equiv.sumSumSumComm
    W₁.Vertex W₂.Vertex W₃.Vertex W₄.Vertex
  attach_comm := fun f => by
    rcases f with (f | f) | (f | f)
    · change (((W₁.attach f).map Sum.inl Sum.inl).map
          Sum.inl Sum.inl).map id
            (_root_.Equiv.sumSumSumComm α γ β δ) =
        (((W₁.attach f).map Sum.inl Sum.inl).map
          Sum.inl Sum.inl).map
          (_root_.Equiv.sumSumSumComm W₁.Vertex W₂.Vertex
            W₃.Vertex W₄.Vertex) id
      rcases W₁.attach f with v | ℓ <;> rfl
    · change (((W₂.attach f).map Sum.inl Sum.inl).map
          Sum.inr Sum.inr).map id
            (_root_.Equiv.sumSumSumComm α γ β δ) =
        (((W₂.attach f).map Sum.inr Sum.inr).map
          Sum.inl Sum.inl).map
          (_root_.Equiv.sumSumSumComm W₁.Vertex W₂.Vertex
            W₃.Vertex W₄.Vertex) id
      rcases W₂.attach f with v | ℓ <;> rfl
    · change (((W₃.attach f).map Sum.inr Sum.inr).map
          Sum.inl Sum.inl).map id
            (_root_.Equiv.sumSumSumComm α γ β δ) =
        (((W₃.attach f).map Sum.inl Sum.inl).map
          Sum.inr Sum.inr).map
          (_root_.Equiv.sumSumSumComm W₁.Vertex W₂.Vertex
            W₃.Vertex W₄.Vertex) id
      rcases W₃.attach f with v | ℓ <;> rfl
    · change (((W₄.attach f).map Sum.inr Sum.inr).map
          Sum.inr Sum.inr).map id
            (_root_.Equiv.sumSumSumComm α γ β δ) =
        (((W₄.attach f).map Sum.inr Sum.inr).map
          Sum.inr Sum.inr).map
          (_root_.Equiv.sumSumSumComm W₁.Vertex W₂.Vertex
            W₃.Vertex W₄.Vertex) id
      rcases W₄.attach f with v | ℓ <;> rfl
  pairing_comm := fun f => by
    rcases f with (f | f) | (f | f) <;> rfl
  circles_eq := by
    change W₁.circles + W₂.circles +
        (W₃.circles + W₄.circles) =
      W₁.circles + W₃.circles +
        (W₂.circles + W₄.circles)
    omega

end Fragment

/-! ### Interface pair splitting and ground computation -/

/-- The interface pairs of a sum split into the high block (second
factor) followed by the low block (first factor). -/
private theorem interchange_pairs_split
    (s₁ t₁ u₁ s₂ t₂ u₂ : ℕ) :
    interfacePairs (s₁+s₂) (t₁+t₂) (u₁+u₂) =
      (List.finRange t₂).reverse.map (fun k' =>
        ((Sum.inl ⟨(s₁+s₂) + (t₁ + k'.val),
            by have := k'.isLt; omega⟩ :
            Fin ((s₁+s₂) + (t₁+t₂)) ⊕
              Fin ((t₁+t₂) + (u₁+u₂))),
         Sum.inr ⟨t₁ + k'.val,
            by have := k'.isLt; omega⟩)) ++
      (List.finRange t₁).reverse.map (fun k =>
        ((Sum.inl ⟨(s₁+s₂) + k.val,
            by have := k.isLt; omega⟩ :
            Fin ((s₁+s₂) + (t₁+t₂)) ⊕
              Fin ((t₁+t₂) + (u₁+u₂))),
         Sum.inr ⟨k.val,
            by have := k.isLt; omega⟩)) := by
  unfold interfacePairs
  rw [List.map_reverse, List.map_reverse, List.map_reverse,
    ← List.reverse_append]
  refine congrArg List.reverse ?_
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map,
    List.ofFn_eq_map]
  exact congrArg₂ (· ++ ·)
    (List.map_congr_left fun i _ =>
      Prod.ext (congrArg Sum.inl (Fin.ext rfl))
        (congrArg Sum.inr (Fin.ext rfl)))
    (List.map_congr_left fun j _ =>
      Prod.ext (congrArg Sum.inl (Fin.ext rfl))
        (congrArg Sum.inr (Fin.ext rfl)))

/-- Transport of the low (first-factor) half through the
interchange shuffle: each pair maps to the corresponding
`inlPairs` pair. -/
private theorem interchange_ground_low_aux
    (s₁ t₁ u₁ s₂ t₂ u₂ : ℕ) :
    ∀ (l : List (Fin t₁)),
      Fragment.mapPairs
          ((_root_.Equiv.sumCongr
            (interleaveEquiv s₁ t₁ s₂ t₂)
            (interleaveEquiv t₁ u₁ t₂ u₂)).symm.trans
            (_root_.Equiv.sumSumSumComm
              (Fin (s₁+t₁)) (Fin (s₂+t₂))
              (Fin (t₁+u₁)) (Fin (t₂+u₂))))
          (l.map (fun k =>
            ((Sum.inl ⟨(s₁+s₂) + k.val,
                by have := k.isLt; omega⟩ :
                Fin ((s₁+s₂) + (t₁+t₂)) ⊕
                  Fin ((t₁+t₂) + (u₁+u₂))),
             Sum.inr ⟨k.val,
                by have := k.isLt; omega⟩))) =
        Fragment.inlPairs
          (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂))
          (l.map (fun k =>
            ((Sum.inl ⟨s₁ + k.val,
                by have := k.isLt; omega⟩ :
                Fin (s₁+t₁) ⊕ Fin (t₁+u₁)),
             Sum.inr ⟨k.val,
                by have := k.isLt; omega⟩)))
  | [] => rfl
  | k :: l => by
    simp only [List.map_cons, Fragment.mapPairs,
      Fragment.inlPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (interchange_ground_low_aux s₁ t₁ u₁ s₂ t₂ u₂ l)
    · change (_root_.Equiv.sumSumSumComm
            (Fin (s₁+t₁)) (Fin (s₂+t₂))
            (Fin (t₁+u₁)) (Fin (t₂+u₂)))
          (Sum.inl ((interleaveEquiv s₁ t₁ s₂ t₂).symm
            ⟨(s₁+s₂) + k.val,
              by have := k.isLt; omega⟩)) =
        Sum.inl (Sum.inl ⟨s₁ + k.val,
            by have := k.isLt; omega⟩)
      rw [show (⟨(s₁+s₂) + k.val, _⟩ :
            Fin ((s₁+s₂) + (t₁+t₂))) =
          Fin.natAdd (s₁+s₂) (Fin.castAdd t₂ k)
        from Fin.ext rfl,
        interleaveEquiv_symm_high_left]
      simp [_root_.Equiv.sumSumSumComm, Fin.ext_iff]
    · change (_root_.Equiv.sumSumSumComm
            (Fin (s₁+t₁)) (Fin (s₂+t₂))
            (Fin (t₁+u₁)) (Fin (t₂+u₂)))
          (Sum.inr ((interleaveEquiv t₁ u₁ t₂ u₂).symm
            ⟨k.val, by have := k.isLt; omega⟩)) =
        Sum.inl (Sum.inr ⟨k.val,
            by have := k.isLt; omega⟩)
      rw [show (⟨k.val, _⟩ :
            Fin ((t₁+t₂) + (u₁+u₂))) =
          Fin.castAdd (u₁+u₂) (Fin.castAdd t₂ k)
        from Fin.ext rfl,
        interleaveEquiv_symm_low_left]
      simp [_root_.Equiv.sumSumSumComm, Fin.ext_iff]

/-- Transport of the high (second-factor) half through the
interchange shuffle: each pair maps to the corresponding
`inrPairs` pair. -/
private theorem interchange_ground_high_aux
    (s₁ t₁ u₁ s₂ t₂ u₂ : ℕ) :
    ∀ (l : List (Fin t₂)),
      Fragment.mapPairs
          ((_root_.Equiv.sumCongr
            (interleaveEquiv s₁ t₁ s₂ t₂)
            (interleaveEquiv t₁ u₁ t₂ u₂)).symm.trans
            (_root_.Equiv.sumSumSumComm
              (Fin (s₁+t₁)) (Fin (s₂+t₂))
              (Fin (t₁+u₁)) (Fin (t₂+u₂))))
          (l.map (fun k' =>
            ((Sum.inl ⟨(s₁+s₂) + (t₁ + k'.val),
                by have := k'.isLt; omega⟩ :
                Fin ((s₁+s₂) + (t₁+t₂)) ⊕
                  Fin ((t₁+t₂) + (u₁+u₂))),
             Sum.inr ⟨t₁ + k'.val,
                by have := k'.isLt; omega⟩))) =
        Fragment.inrPairs
          (α := Fin (s₁+t₁) ⊕ Fin (t₁+u₁))
          (l.map (fun k' =>
            ((Sum.inl ⟨s₂ + k'.val,
                by have := k'.isLt; omega⟩ :
                Fin (s₂+t₂) ⊕ Fin (t₂+u₂)),
             Sum.inr ⟨k'.val,
                by have := k'.isLt; omega⟩)))
  | [] => rfl
  | k' :: l => by
    simp only [List.map_cons, Fragment.mapPairs,
      Fragment.inrPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (interchange_ground_high_aux s₁ t₁ u₁ s₂ t₂ u₂ l)
    · change (_root_.Equiv.sumSumSumComm
            (Fin (s₁+t₁)) (Fin (s₂+t₂))
            (Fin (t₁+u₁)) (Fin (t₂+u₂)))
          (Sum.inl ((interleaveEquiv s₁ t₁ s₂ t₂).symm
            ⟨(s₁+s₂) + (t₁ + k'.val),
              by have := k'.isLt; omega⟩)) =
        Sum.inr (Sum.inl ⟨s₂ + k'.val,
            by have := k'.isLt; omega⟩)
      rw [show (⟨(s₁+s₂) + (t₁ + k'.val), _⟩ :
            Fin ((s₁+s₂) + (t₁+t₂))) =
          Fin.natAdd (s₁+s₂) (Fin.natAdd t₁ k')
        from Fin.ext rfl,
        interleaveEquiv_symm_high_right]
      simp [_root_.Equiv.sumSumSumComm, Fin.ext_iff]
    · change (_root_.Equiv.sumSumSumComm
            (Fin (s₁+t₁)) (Fin (s₂+t₂))
            (Fin (t₁+u₁)) (Fin (t₂+u₂)))
          (Sum.inr ((interleaveEquiv t₁ u₁ t₂ u₂).symm
            ⟨t₁ + k'.val,
              by have := k'.isLt; omega⟩)) =
        Sum.inr (Sum.inr ⟨k'.val,
            by have := k'.isLt; omega⟩)
      rw [show (⟨t₁ + k'.val, _⟩ :
            Fin ((t₁+t₂) + (u₁+u₂))) =
          Fin.castAdd (u₁+u₂) (Fin.natAdd t₁ k')
        from Fin.ext rfl,
        interleaveEquiv_symm_low_right]
      simp [_root_.Equiv.sumSumSumComm, Fin.ext_iff]

/-- **Ground computation**: transporting the composition interface
pairs through the interchange shuffle yields the right-block
interface pairs followed by the left-block interface pairs. -/
theorem interchange_ground (s₁ t₁ u₁ s₂ t₂ u₂ : ℕ) :
    Fragment.mapPairs
        ((_root_.Equiv.sumCongr
          (interleaveEquiv s₁ t₁ s₂ t₂)
          (interleaveEquiv t₁ u₁ t₂ u₂)).symm.trans
          (_root_.Equiv.sumSumSumComm
            (Fin (s₁+t₁)) (Fin (s₂+t₂))
            (Fin (t₁+u₁)) (Fin (t₂+u₂))))
        (interfacePairs (s₁+s₂) (t₁+t₂) (u₁+u₂)) =
      Fragment.inrPairs
        (α := Fin (s₁+t₁) ⊕ Fin (t₁+u₁))
        (interfacePairs s₂ t₂ u₂) ++
      Fragment.inlPairs
        (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂))
        (interfacePairs s₁ t₁ u₁) := by
  rw [interchange_pairs_split s₁ t₁ u₁ s₂ t₂ u₂,
    mapPairs_append]
  unfold interfacePairs
  exact congrArg₂ (· ++ ·)
    (interchange_ground_high_aux s₁ t₁ u₁ s₂ t₂ u₂ _)
    (interchange_ground_low_aux s₁ t₁ u₁ s₂ t₂ u₂ _)

/-- The combined interface pairs of the interchange are
well-formed: the `inlPairs` block is all `Sum.inl` and the
`inrPairs` block is all `Sum.inr`, so they are disjoint. -/
theorem interchangePairs_wf (s₁ t₁ u₁ s₂ t₂ u₂ : ℕ) :
    Fragment.PairsWF
      (Fragment.inlPairs
          (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂))
          (interfacePairs s₁ t₁ u₁) ++
        Fragment.inrPairs
          (α := Fin (s₁+t₁) ⊕ Fin (t₁+u₁))
          (interfacePairs s₂ t₂ u₂)) := by
  unfold Fragment.PairsWF
  rw [List.flatMap_append]
  refine List.Nodup.append
    (Fragment.inlPairs_wf _ (interfacePairs_wf s₁ t₁ u₁))
    (Fragment.inrPairs_wf _ (interfacePairs_wf s₂ t₂ u₂))
    ?_
  intro x hx hy
  obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
  obtain ⟨q, hq, hyq⟩ := List.mem_flatMap.mp hy
  obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
  obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
  dsimp [Prod.map] at hxp hyq
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at hxp hyq
  rcases hxp with rfl | rfl <;>
    (rcases hyq with h | h <;> exact absurd h Sum.inl_ne_inr)

namespace Fragment

/-! ### LHS normalization -/

/-- **LHS chain**: `(F₁ . G₁) ⊗ (F₂ . G₂)` normalizes to
`(GL₁ ⊔ GL₂).relabel L_lhs` where `GL_i` is the glueing of
the `i`-th factor. -/
noncomputable def interchangeNormalLeft
    {s₁ t₁ u₁ s₂ t₂ u₂ : ℕ}
    (F₁ : Fragment (Fin (s₁ + t₁))) (G₁ : Fragment (Fin (t₁ + u₁)))
    (F₂ : Fragment (Fin (s₂ + t₂))) (G₂ : Fragment (Fin (t₂ + u₂))) :
    (tensorFragment (F₁.compose G₁) (F₂.compose G₂)).Equiv
      (((Fragment.glueList (F₁.disjUnion G₁)
            (interfacePairs s₁ t₁ u₁) (interfacePairs_wf s₁ t₁ u₁)).disjUnion
          (Fragment.glueList (F₂.disjUnion G₂)
            (interfacePairs s₂ t₂ u₂) (interfacePairs_wf s₂ t₂ u₂))).relabel
        ((_root_.Equiv.sumCongr
          ((interfaceSurvEquiv s₁ t₁ u₁).trans finSumFinEquiv)
          ((interfaceSurvEquiv s₂ t₂ u₂).trans finSumFinEquiv)).trans
          (interleaveEquiv s₁ u₁ s₂ u₂))) := by
  let GL₁ := glueList (F₁.disjUnion G₁)
    (interfacePairs s₁ t₁ u₁) (interfacePairs_wf s₁ t₁ u₁)
  let GL₂ := glueList (F₂.disjUnion G₂)
    (interfacePairs s₂ t₂ u₂) (interfacePairs_wf s₂ t₂ u₂)
  let surv₁ := (interfaceSurvEquiv s₁ t₁ u₁).trans finSumFinEquiv
  let surv₂ := (interfaceSurvEquiv s₂ t₂ u₂).trans finSumFinEquiv
  -- C0: composeNormal in each factor
  refine (tensorFragmentCongr
    (composeNormal F₁ G₁) (composeNormal F₂ G₂)).trans ?_
  -- Peel relabels, compose, flatten
  exact (Equiv.relabelCongr
      ((relabelDisjUnionLeft GL₁ (GL₂.relabel surv₂) surv₁).trans
        ((Equiv.relabelCongr
            (relabelDisjUnionRight GL₁ GL₂ surv₂)
            (_root_.Equiv.sumCongr surv₁
              (_root_.Equiv.refl _))).trans
          ((Equiv.relabelTrans (GL₁.disjUnion GL₂)
            (_root_.Equiv.sumCongr (_root_.Equiv.refl _) surv₂)
            (_root_.Equiv.sumCongr surv₁
              (_root_.Equiv.refl _))).trans
            (Equiv.relabelEq (GL₁.disjUnion GL₂)
              (_root_.Equiv.ext fun x => by
                cases x <;> rfl)))))
      (interleaveEquiv s₁ u₁ s₂ u₂)).trans
    (Equiv.relabelTrans (GL₁.disjUnion GL₂)
      (_root_.Equiv.sumCongr surv₁ surv₂)
      (interleaveEquiv s₁ u₁ s₂ u₂))

/-! ### Helper: liftPairs of inlPairs/inrPairs -/

/-- Lifting `inrPairs qs` through `inlPairs ps` equals mapping
through the inverse of `inlFoldEquiv`. -/
private theorem liftPairs_inlPairs_inrPairs
    {α β : Type}
    (ps : List (α × α)) :
    ∀ (qs : List (β × β))
      (h : PairsSepAll (inlPairs (β := β) ps)
        (inrPairs (α := α) qs)),
    liftPairs (inlPairs ps) (inrPairs qs) h =
      Fragment.mapPairs (inlFoldEquiv (β := β) ps).symm
        (inrPairs (α := FoldSurviving α ps) qs)
  | [], _ => rfl
  | q :: qs, h => by
    simp only [inrPairs, List.map_cons, liftPairs,
      Fragment.mapPairs, Prod.map]
    exact congrArg₂ List.cons
      (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
      (liftPairs_inlPairs_inrPairs ps qs _)

/-! ### RHS normalization -/

section InterchangeSurvivor

variable
    {s₁ t₁ u₁ s₂ t₂ u₂ : ℕ}
    (g : (FoldSurviving (Fin (s₁ + t₁) ⊕ Fin (t₁ + u₁))
        (interfacePairs s₁ t₁ u₁) ⊕
      FoldSurviving (Fin (s₂ + t₂) ⊕ Fin (t₂ + u₂))
        (interfacePairs s₂ t₂ u₂)) ≃
      FoldSurviving (Fin ((s₁ + s₂) + (t₁ + t₂)) ⊕ Fin ((t₁ + t₂) + (u₁ + u₂)))
        (interfacePairs (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)))
    (hg : ∀ x, (g x).val =
      ((_root_.Equiv.sumSumSumComm (Fin (s₁ + t₁)) (Fin (t₁ + u₁))
        (Fin (s₂ + t₂)) (Fin (t₂ + u₂))).trans
        (_root_.Equiv.sumCongr (interleaveEquiv s₁ t₁ s₂ t₂)
          (interleaveEquiv t₁ u₁ t₂ u₂))) (Sum.map Subtype.val Subtype.val x))

include hg

private theorem interchange_survivor_relabel_inl
    (fs₁ : FoldSurviving (Fin (s₁ + t₁) ⊕ Fin (t₁ + u₁))
      (interfacePairs s₁ t₁ u₁)) :
    (g.trans ((interfaceSurvEquiv (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)).trans
      finSumFinEquiv)) (Sum.inl fs₁) =
      ((_root_.Equiv.sumCongr
        ((interfaceSurvEquiv s₁ t₁ u₁).trans finSumFinEquiv)
        ((interfaceSurvEquiv s₂ t₂ u₂).trans finSumFinEquiv)).trans
        (interleaveEquiv s₁ u₁ s₂ u₂)) (Sum.inl fs₁) := by
  let ieF := interleaveEquiv s₁ t₁ s₂ t₂
  let ieG := interleaveEquiv t₁ u₁ t₂ u₂
  let E := (_root_.Equiv.sumSumSumComm
    (Fin (s₁+t₁)) (Fin (t₁+u₁)) (Fin (s₂+t₂)) (Fin (t₂+u₂))).trans
    (_root_.Equiv.sumCongr ieF ieG)
  cases hxv : fs₁.val with
  | inl a =>
    have ha : a.val < s₁ := by
      by_contra hge
      exact (forall_ne_iff_not_mem_flat _ _).mp fs₁.prop
        ((mem_interfacePairs_flat s₁ t₁ u₁ _).mpr
          (Or.inl ⟨a, hxv, by omega⟩))
    have hie_val : (ieF (Sum.inl a)).val = a.val := by
      change (interleaveEquiv s₁ t₁ s₂ t₂
        (Sum.inl a)).val = a.val
      conv_lhs => rw [show a = Fin.castAdd t₁
          ⟨a.val, ha⟩ from Fin.ext rfl,
        interleaveEquiv_inl_low]
      rfl
    rw [_root_.Equiv.trans_apply]
    conv_rhs =>
      rw [_root_.Equiv.trans_apply,
        _root_.Equiv.sumCongr_apply, Sum.map_inl,
        _root_.Equiv.trans_apply,
        interfaceSurvEquiv_inl s₁ t₁ u₁ fs₁ a hxv ha,
        finSumFinEquiv_apply_left,
        interleaveEquiv_inl_low s₁ u₁ s₂ u₂
          ⟨a.val, ha⟩]
    rw [_root_.Equiv.trans_apply]
    refine (congrArg finSumFinEquiv
      (interfaceSurvEquiv_inl (s₁+s₂) (t₁+t₂) (u₁+u₂)
        _ (ieF (Sum.inl a))
        (by
          rw [hg]
          change E (Sum.inl fs₁.val) = _
          rw [hxv]
          rfl)
        (by rw [hie_val]; omega))).trans ?_
    rw [finSumFinEquiv_apply_left]
    exact congrArg (Fin.castAdd (u₁+u₂))
      (Fin.ext hie_val)
  | inr b =>
    have hb : t₁ ≤ b.val := by
      by_contra hlt
      exact (forall_ne_iff_not_mem_flat _ _).mp fs₁.prop
        ((mem_interfacePairs_flat s₁ t₁ u₁ _).mpr
          (Or.inr ⟨b, hxv, by omega⟩))
    have hie_val : (ieG (Sum.inl b)).val =
        (t₁ + t₂) + (b.val - t₁) := by
      change (interleaveEquiv t₁ u₁ t₂ u₂
        (Sum.inl b)).val = _
      conv_lhs => rw [show b = Fin.natAdd t₁
          ⟨b.val - t₁, by
            have := b.isLt
            omega⟩ from Fin.ext (by
          change b.val = t₁ + (b.val - t₁)
          omega),
        interleaveEquiv_inl_high]
      rfl
    rw [_root_.Equiv.trans_apply]
    conv_rhs =>
      rw [_root_.Equiv.trans_apply,
        _root_.Equiv.sumCongr_apply, Sum.map_inl,
        _root_.Equiv.trans_apply,
        interfaceSurvEquiv_inr s₁ t₁ u₁ fs₁ b hxv hb,
        finSumFinEquiv_apply_right,
        interleaveEquiv_inl_high s₁ u₁ s₂ u₂
          ⟨b.val - t₁, by have := b.isLt; omega⟩]
    rw [_root_.Equiv.trans_apply]
    refine (congrArg finSumFinEquiv
      (interfaceSurvEquiv_inr (s₁+s₂) (t₁+t₂) (u₁+u₂)
        _ (ieG (Sum.inl b))
        (by
          rw [hg]
          change E (Sum.inl fs₁.val) = _
          rw [hxv]
          rfl)
        (by rw [hie_val]; omega))).trans ?_
    rw [finSumFinEquiv_apply_right]
    exact congrArg (Fin.natAdd (s₁+s₂))
      (Fin.ext (by
        change (ieG (Sum.inl b)).val - (t₁ + t₂) =
          b.val - t₁
        rw [hie_val]
        omega))

private theorem interchange_survivor_relabel_inr
    (fs₂ : FoldSurviving (Fin (s₂ + t₂) ⊕ Fin (t₂ + u₂))
      (interfacePairs s₂ t₂ u₂)) :
    (g.trans ((interfaceSurvEquiv (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)).trans
      finSumFinEquiv)) (Sum.inr fs₂) =
      ((_root_.Equiv.sumCongr
        ((interfaceSurvEquiv s₁ t₁ u₁).trans finSumFinEquiv)
        ((interfaceSurvEquiv s₂ t₂ u₂).trans finSumFinEquiv)).trans
        (interleaveEquiv s₁ u₁ s₂ u₂)) (Sum.inr fs₂) := by
  let ieF := interleaveEquiv s₁ t₁ s₂ t₂
  let ieG := interleaveEquiv t₁ u₁ t₂ u₂
  let E := (_root_.Equiv.sumSumSumComm
    (Fin (s₁+t₁)) (Fin (t₁+u₁)) (Fin (s₂+t₂)) (Fin (t₂+u₂))).trans
    (_root_.Equiv.sumCongr ieF ieG)
  cases hxv : fs₂.val with
  | inl c =>
    have hc : c.val < s₂ := by
      by_contra hge
      exact (forall_ne_iff_not_mem_flat _ _).mp fs₂.prop
        ((mem_interfacePairs_flat s₂ t₂ u₂ _).mpr
          (Or.inl ⟨c, hxv, by omega⟩))
    have hie_val : (ieF (Sum.inr c)).val =
        s₁ + c.val := by
      change (interleaveEquiv s₁ t₁ s₂ t₂
        (Sum.inr c)).val = _
      conv_lhs => rw [show c = Fin.castAdd t₂
          ⟨c.val, hc⟩ from Fin.ext rfl,
        interleaveEquiv_inr_low]
      rfl
    rw [_root_.Equiv.trans_apply]
    conv_rhs =>
      rw [_root_.Equiv.trans_apply,
        _root_.Equiv.sumCongr_apply, Sum.map_inr,
        _root_.Equiv.trans_apply,
        interfaceSurvEquiv_inl s₂ t₂ u₂ fs₂ c hxv hc,
        finSumFinEquiv_apply_left,
        interleaveEquiv_inr_low s₁ u₁ s₂ u₂
          ⟨c.val, hc⟩]
    rw [_root_.Equiv.trans_apply]
    refine (congrArg finSumFinEquiv
      (interfaceSurvEquiv_inl (s₁+s₂) (t₁+t₂) (u₁+u₂)
        _ (ieF (Sum.inr c))
        (by
          rw [hg]
          change E (Sum.inr fs₂.val) = _
          rw [hxv]
          rfl)
        (by rw [hie_val]; omega))).trans ?_
    rw [finSumFinEquiv_apply_left]
    exact congrArg (Fin.castAdd (u₁+u₂))
      (Fin.ext hie_val)
  | inr d =>
    have hd : t₂ ≤ d.val := by
      by_contra hlt
      exact (forall_ne_iff_not_mem_flat _ _).mp fs₂.prop
        ((mem_interfacePairs_flat s₂ t₂ u₂ _).mpr
          (Or.inr ⟨d, hxv, by omega⟩))
    have hie_val : (ieG (Sum.inr d)).val =
        (t₁ + t₂) + (u₁ + (d.val - t₂)) := by
      change (interleaveEquiv t₁ u₁ t₂ u₂
        (Sum.inr d)).val = _
      conv_lhs => rw [show d = Fin.natAdd t₂
          ⟨d.val - t₂, by
            have := d.isLt
            omega⟩ from Fin.ext (by
          change d.val = t₂ + (d.val - t₂)
          omega),
        interleaveEquiv_inr_high]
      rfl
    rw [_root_.Equiv.trans_apply]
    conv_rhs =>
      rw [_root_.Equiv.trans_apply,
        _root_.Equiv.sumCongr_apply, Sum.map_inr,
        _root_.Equiv.trans_apply,
        interfaceSurvEquiv_inr s₂ t₂ u₂ fs₂ d hxv hd,
        finSumFinEquiv_apply_right,
        interleaveEquiv_inr_high s₁ u₁ s₂ u₂
          ⟨d.val - t₂, by have := d.isLt; omega⟩]
    rw [_root_.Equiv.trans_apply]
    refine (congrArg finSumFinEquiv
      (interfaceSurvEquiv_inr (s₁+s₂) (t₁+t₂) (u₁+u₂)
        _ (ieG (Sum.inr d))
        (by
          rw [hg]
          change E (Sum.inr fs₂.val) = _
          rw [hxv]
          rfl)
        (by rw [hie_val]; omega))).trans ?_
    rw [finSumFinEquiv_apply_right]
    exact congrArg (Fin.natAdd (s₁+s₂))
      (Fin.ext (by
        change (ieG (Sum.inr d)).val - (t₁ + t₂) =
          u₁ + (d.val - t₂)
        rw [hie_val]
        omega))

private theorem interchange_survivor_relabel_eq :
    g.trans ((interfaceSurvEquiv (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)).trans
      finSumFinEquiv) =
      (_root_.Equiv.sumCongr
        ((interfaceSurvEquiv s₁ t₁ u₁).trans finSumFinEquiv)
        ((interfaceSurvEquiv s₂ t₂ u₂).trans finSumFinEquiv)).trans
        (interleaveEquiv s₁ u₁ s₂ u₂) := by
  apply _root_.Equiv.ext
  intro x
  cases x with
  | inl fs₁ => exact interchange_survivor_relabel_inl g hg fs₁
  | inr fs₂ => exact interchange_survivor_relabel_inr g hg fs₂

end InterchangeSurvivor

/-- **RHS chain**: `(F₁ ⊗ F₂) . (G₁ ⊗ G₂)` normalizes to
`(GL₁ ⊔ GL₂).relabel L_rhs`.

The chain goes through composeNormal, ambient peel (exchange +
relabel_disjUnion), relabel peel (glueListRelabel +
mapPairs_symm_cancel), ground computation
(interchange_ground), pair permutation (glueListPerm),
append split (glueListAppend), and two-sided localization
(glueListDisjUnionLeft + glueListDisjUnionRight). -/
noncomputable def interchangeNormalRight
    {s₁ t₁ u₁ s₂ t₂ u₂ : ℕ}
    (F₁ : Fragment (Fin (s₁ + t₁))) (G₁ : Fragment (Fin (t₁ + u₁)))
    (F₂ : Fragment (Fin (s₂ + t₂))) (G₂ : Fragment (Fin (t₂ + u₂))) :
    ((tensorFragment F₁ F₂).compose (tensorFragment G₁ G₂)).Equiv
      (((glueList (F₁.disjUnion G₁)
            (interfacePairs s₁ t₁ u₁) (interfacePairs_wf s₁ t₁ u₁)).disjUnion
          (glueList (F₂.disjUnion G₂)
            (interfacePairs s₂ t₂ u₂) (interfacePairs_wf s₂ t₂ u₂))).relabel
        ((_root_.Equiv.sumCongr
          ((interfaceSurvEquiv s₁ t₁ u₁).trans finSumFinEquiv)
          ((interfaceSurvEquiv s₂ t₂ u₂).trans finSumFinEquiv)).trans
          (interleaveEquiv s₁ u₁ s₂ u₂))) := by
  -- ═══════ SETUP: the two component folds and the interfaces ═══════
  let GL₁ := glueList (F₁.disjUnion G₁)
    (interfacePairs s₁ t₁ u₁) (interfacePairs_wf s₁ t₁ u₁)
  let GL₂ := glueList (F₂.disjUnion G₂)
    (interfacePairs s₂ t₂ u₂) (interfacePairs_wf s₂ t₂ u₂)
  let A := (F₁.disjUnion G₁).disjUnion (F₂.disjUnion G₂)
  let ieF := interleaveEquiv s₁ t₁ s₂ t₂
  let ieG := interleaveEquiv t₁ u₁ t₂ u₂
  let E := (_root_.Equiv.sumSumSumComm
    (Fin (s₁+t₁)) (Fin (t₁+u₁))
    (Fin (s₂+t₂)) (Fin (t₂+u₂))).trans
    (_root_.Equiv.sumCongr ieF ieG)
  let ips_c := interfacePairs (s₁+s₂) (t₁+t₂) (u₁+u₂)
  let wf_c := interfacePairs_wf (s₁+s₂) (t₁+t₂) (u₁+u₂)
  let surv_c := (interfaceSurvEquiv (s₁+s₂) (t₁+t₂) (u₁+u₂)).trans
    finSumFinEquiv
  let surv₁ := (interfaceSurvEquiv s₁ t₁ u₁).trans finSumFinEquiv
  let surv₂ := (interfaceSurvEquiv s₂ t₂ u₂).trans finSumFinEquiv
  let ips₁ := interfacePairs s₁ t₁ u₁
  let ips₂ := interfacePairs s₂ t₂ u₂
  let wf₁ := interfacePairs_wf s₁ t₁ u₁
  let wf₂ := interfacePairs_wf s₂ t₂ u₂
  -- ═══════ STAGE 1: THE AMBIENT EXCHANGE ═══════
  -- AMB: peel relabels from the tensor disjoint union via exchange
  have AMB : ((tensorFragment F₁ F₂).disjUnion
      (tensorFragment G₁ G₂)).Equiv (A.relabel E) :=
    (relabelDisjUnionLeft (F₁.disjUnion F₂)
        (tensorFragment G₁ G₂) ieF).trans
      ((Equiv.relabelCongr
          (relabelDisjUnionRight (F₁.disjUnion F₂)
            (G₁.disjUnion G₂) ieG)
          (_root_.Equiv.sumCongr ieF
            (_root_.Equiv.refl _))).trans
        ((Equiv.relabelTrans _ _ _).trans
          ((Equiv.relabelEq _
            (_root_.Equiv.ext fun x => by
              cases x <;> rfl)).trans
            ((Equiv.relabelCongr
              (disjUnionExchange F₁ F₂ G₁ G₂)
              (_root_.Equiv.sumCongr ieF ieG)).trans
              (Equiv.relabelTrans _ _ _)))))
  -- Peeled pair list and well-formedness
  let qs := Fragment.mapPairs E.symm ips_c
  have wfqs : PairsWF qs :=
    Fragment.mapPairs_wf E.symm _ wf_c
  -- rl / lr: reversed and canonical order of the decomposed pairs
  let rl := inrPairs (α := Fin (s₁+t₁) ⊕ Fin (t₁+u₁)) ips₂ ++
    inlPairs (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂)) ips₁
  let lr := inlPairs (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂)) ips₁ ++
    inrPairs (α := Fin (s₁+t₁) ⊕ Fin (t₁+u₁)) ips₂
  have wf_lr : PairsWF lr := interchangePairs_wf s₁ t₁ u₁ s₂ t₂ u₂
  have wf_rl : PairsWF rl := wf_lr.perm List.perm_append_comm
  -- ═══════ STAGE 2: PEELING THE COMPOSITE INTERFACE ═══════
  -- The single interface of the composite is pulled back along the
  -- exchange to the two components' interfaces, one relabel at a time.
  -- C5: bridge peeled pairs qs to decomposed pairs rl
  have C5 := Equiv.relabelFlip'
    (glueListEqEquiv A
      (interchange_ground s₁ t₁ u₁ s₂ t₂ u₂) wfqs wf_rl
      (List.Perm.of_eq (interchange_ground s₁ t₁ u₁ s₂ t₂ u₂)))
  -- C3: peel relabel E through glueList
  have C3 := (glueListRelabel A E qs wfqs).trans
    ((Equiv.relabelCongr C5
      (foldSurvivingMapEquiv E qs)).trans
    (Equiv.relabelTrans _ _ _))
  -- C2: bridge the composite pairs ips_c through mapPairs_symm_cancel
  have C2 := (Equiv.relabelFlip'
    (glueListEqEquiv (A.relabel E)
      (mapPairs_symm_cancel E ips_c).symm
      wf_c (Fragment.mapPairs_wf E _ wfqs)
      (List.Perm.of_eq
        (mapPairs_symm_cancel E ips_c).symm))).trans
    ((Equiv.relabelCongr C3
      (foldSurvivingPermEquiv
        ((mapPairs_symm_cancel E ips_c).symm ▸
          List.Perm.refl _)).symm).trans
    (Equiv.relabelTrans _ _ _))
  -- C1: composeNormal + AMB transport + peel
  have C1 := (glueListCongr AMB ips_c wf_c).trans C2
  -- ═══════ STAGE 3: REORDERING AND SPLITTING THE INTERFACE ═══════
  -- PM: permute rl → lr
  have PM := glueListPerm A
    (List.perm_append_comm
      (l₁ := inrPairs (α := Fin (s₁+t₁) ⊕ Fin (t₁+u₁)) ips₂)
      (l₂ := inlPairs (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂)) ips₁))
    wf_rl
  -- APP: append split lr = inlPairs ips₁ ++ inrPairs ips₂
  have APP := glueListAppend A
    (inlPairs (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂)) ips₁)
    (inrPairs (α := Fin (s₁+t₁) ⊕ Fin (t₁+u₁)) ips₂)
    wf_lr
  -- ═══════ STAGE 4: LOCALIZING THE FIRST COMPONENT ═══════
  -- L1: first localization — glue inlPairs ips₁ in A localizes
  -- to GL₁ ⊔ (F₂⊔G₂)
  have L1 := glueListDisjUnionLeft
    (F₁.disjUnion G₁) (F₂.disjUnion G₂) ips₁ wf₁
  -- L1G: transport second stage across L1
  have L1G := glueListCongr L1
    (liftPairs
      (inlPairs (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂)) ips₁)
      (inrPairs (α := Fin (s₁+t₁) ⊕ Fin (t₁+u₁)) ips₂)
      wf_lr.append_sep)
    (liftPairs_wf
      (inlPairs (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂)) ips₁)
      (inrPairs (α := Fin (s₁+t₁) ⊕ Fin (t₁+u₁)) ips₂)
      wf_lr.append_right wf_lr.append_sep)
  -- ═══════ STAGE 5: LOCALIZING THE SECOND COMPONENT ═══════
  -- L2B: bridge liftPairs → mapPairs via helper lemma
  let e_l := (inlFoldEquiv
    (β := Fin (s₂+t₂) ⊕ Fin (t₂+u₂)) ips₁).symm
  have L2B := Equiv.relabelFlip'
    (glueListEqEquiv
      ((GL₁.disjUnion (F₂.disjUnion G₂)).relabel e_l)
      (liftPairs_inlPairs_inrPairs ips₁ ips₂ wf_lr.append_sep)
      (liftPairs_wf _ _ wf_lr.append_right wf_lr.append_sep)
      (Fragment.mapPairs_wf e_l _
        (inrPairs_wf ips₂ wf₂))
      (List.Perm.of_eq
        (liftPairs_inlPairs_inrPairs ips₁ ips₂
          wf_lr.append_sep)))
  -- L2R: peel e_l through second-stage glueList
  have L2R := glueListRelabel
    (GL₁.disjUnion (F₂.disjUnion G₂)) e_l
    (inrPairs (α := FoldSurviving _  ips₁) ips₂)
    (inrPairs_wf ips₂ wf₂)
  -- L2D: second localization — glue inrPairs ips₂ in
  -- GL₁ ⊔ (F₂⊔G₂) localizes to GL₁ ⊔ GL₂
  have L2D := glueListDisjUnionRight GL₁
    (F₂.disjUnion G₂) ips₂ wf₂
  -- L2: compose the second-stage localization chain
  -- glueList (Y₁.relabel e_l) (liftPairs ...) ≃ (GL₁ ⊔ GL₂).relabel L_L2
  have L2 := L2B.trans
    ((Equiv.relabelCongr
      (L2R.trans
        ((Equiv.relabelCongr L2D
          (foldSurvivingMapEquiv e_l
            (inrPairs
              (α := FoldSurviving _ ips₁) ips₂))).trans
          (Equiv.relabelTrans _ _ _)))
      _).trans
      (Equiv.relabelTrans _ _ _))
  -- ═══════ ASSEMBLY ═══════
  -- C_total: compose the full inner chain
  -- glueList (TF⊔TG) ips_c wf_c ≃ (GL₁ ⊔ GL₂).relabel L_inner
  have C_total := C1.trans
    ((Equiv.relabelCongr (PM.trans
      ((Equiv.relabelCongr (APP.trans
        ((Equiv.relabelCongr (L1G.trans L2) _).trans
          (Equiv.relabelTrans _ _ _))) _).trans
        (Equiv.relabelTrans _ _ _))) _).trans
      (Equiv.relabelTrans _ _ _))
  -- Assemble: composeNormal → C_total → label meet
  exact (composeNormal (tensorFragment F₁ F₂)
    (tensorFragment G₁ G₂)).trans
    ((Equiv.relabelCongr C_total surv_c).trans
      ((Equiv.relabelTrans _ _ _).trans
        (Equiv.relabelEq _ (interchange_survivor_relabel_eq _
          (fun x => by cases x <;> rfl)))))

/-! ### Final assembly -/

/-- **Interchange law**: tensoring two composites is equivalent to
composing the two tensors. -/
noncomputable def tensorComposeInterchange
    {s₁ t₁ u₁ s₂ t₂ u₂ : ℕ}
    (F₁ : Fragment (Fin (s₁ + t₁))) (G₁ : Fragment (Fin (t₁ + u₁)))
    (F₂ : Fragment (Fin (s₂ + t₂))) (G₂ : Fragment (Fin (t₂ + u₂))) :
    (tensorFragment (F₁.compose G₁) (F₂.compose G₂)).Equiv
      ((tensorFragment F₁ F₂).compose (tensorFragment G₁ G₂)) :=
  (interchangeNormalLeft F₁ G₁ F₂ G₂).trans
    (interchangeNormalRight F₁ G₁ F₂ G₂).symm

end Fragment

end RS
