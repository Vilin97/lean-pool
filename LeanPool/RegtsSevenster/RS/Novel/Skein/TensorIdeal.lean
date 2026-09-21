/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorFragment
import LeanPool.RegtsSevenster.RS.Novel.Skein.PartialClose
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdeal

/-!
# The absorption of a tensor factor into the test fragment

The accompanying paper's Lemma 3.3(b), the geometric core: closing
a tensor
`x ⊗ z` against a test fragment `G` is closing `x` against the
partial closure `G_z = partialClose z G`.  Both sides normalize
to iterated gluing over the common ambient `(x ⊔ z) ⊔ G`: the
closure pairs split into the `z`-blocks and the `x`-blocks, the
`z`-blocks glue first (`glueListAppend`), localize to `z ⊔ G`
(`disjUnionAssoc` + `glueListDisjUnionRight`), and what
remains is the closure of `x` against the survivors — the
defining gluing of `partialClose`.
-/

namespace RS

/-! ### The four closure blocks over the common ambient -/

/-- The `v`-block: `z`'s high labels against the last block of
`G`. -/
def zvBlock (s t u v : ℕ) :
    List (((Fin (s + t) ⊕ Fin (u + v)) ⊕ Fin ((s + u) + (t + v))) ×
      ((Fin (s + t) ⊕ Fin (u + v)) ⊕ Fin ((s + u) + (t + v)))) :=
  (List.finRange v).reverse.map (fun l =>
    (Sum.inl (Sum.inr ⟨u + l.val, by have := l.isLt; omega⟩),
     Sum.inr ⟨(s + u) + (t + l.val), by have := l.isLt; omega⟩))

/-- The `t`-block: `x`'s high labels against the third block of
`G`. -/
def xtBlock (s t u v : ℕ) :
    List (((Fin (s + t) ⊕ Fin (u + v)) ⊕ Fin ((s + u) + (t + v))) ×
      ((Fin (s + t) ⊕ Fin (u + v)) ⊕ Fin ((s + u) + (t + v)))) :=
  (List.finRange t).reverse.map (fun k =>
    (Sum.inl (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩),
     Sum.inr ⟨(s + u) + k.val, by have := k.isLt; omega⟩))

/-- The `u`-block: `z`'s low labels against the second block of
`G`. -/
def zuBlock (s t u v : ℕ) :
    List (((Fin (s + t) ⊕ Fin (u + v)) ⊕ Fin ((s + u) + (t + v))) ×
      ((Fin (s + t) ⊕ Fin (u + v)) ⊕ Fin ((s + u) + (t + v)))) :=
  (List.finRange u).reverse.map (fun j =>
    (Sum.inl (Sum.inr ⟨j.val, by have := j.isLt; omega⟩),
     Sum.inr ⟨s + j.val, by have := j.isLt; omega⟩))

/-- The `s`-block: `x`'s low labels against the first block of
`G`. -/
def xsBlock (s t u v : ℕ) :
    List (((Fin (s + t) ⊕ Fin (u + v)) ⊕ Fin ((s + u) + (t + v))) ×
      ((Fin (s + t) ⊕ Fin (u + v)) ⊕ Fin ((s + u) + (t + v)))) :=
  (List.finRange s).reverse.map (fun i =>
    (Sum.inl (Sum.inl ⟨i.val, by have := i.isLt; omega⟩),
     Sum.inr ⟨i.val, by have := i.isLt; omega⟩))

/-! ### The four-way split of the closure interface -/

/-- The high closure half splits at `t`. -/
theorem ipHigh_split (s t u v : ℕ) :
    ipHigh (s + u) (t + v) =
      (List.finRange v).reverse.map (fun l =>
        ((Sum.inl ⟨(s + u) + (t + l.val),
            by have := l.isLt; omega⟩ :
          Fin (0 + ((s + u) + (t + v))) ⊕
            Fin ((s + u) + (t + v) + 0)),
         Sum.inr ⟨(s + u) + (t + l.val),
           by have := l.isLt; omega⟩)) ++
      (List.finRange t).reverse.map (fun k =>
        (Sum.inl ⟨(s + u) + k.val, by have := k.isLt; omega⟩,
         Sum.inr ⟨(s + u) + k.val, by have := k.isLt; omega⟩)) := by
  unfold ipHigh
  rw [List.map_reverse, List.map_reverse, List.map_reverse,
    ← List.reverse_append]
  refine congrArg List.reverse ?_
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map,
    List.ofFn_eq_map]
  refine congrArg₂ (· ++ ·)
    (List.map_congr_left fun k _ => ?_)
    (List.map_congr_left fun l _ => ?_)
  · refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_)) <;> rfl
  · refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_)) <;>
      · show (s + u) + (t + l.val) = (s + u) + (t + l.val)
        rfl

/-- The low closure half splits at `s`. -/
theorem ipLow_split (s t u v : ℕ) :
    ipLow (s + u) (t + v) =
      (List.finRange u).reverse.map (fun j =>
        ((Sum.inl ⟨s + j.val, by have := j.isLt; omega⟩ :
          Fin (0 + ((s + u) + (t + v))) ⊕
            Fin ((s + u) + (t + v) + 0)),
         Sum.inr ⟨s + j.val, by have := j.isLt; omega⟩)) ++
      (List.finRange s).reverse.map (fun i =>
        (Sum.inl ⟨i.val, by have := i.isLt; omega⟩,
         Sum.inr ⟨i.val, by have := i.isLt; omega⟩)) := by
  unfold ipLow
  rw [List.map_reverse, List.map_reverse, List.map_reverse,
    ← List.reverse_append]
  refine congrArg List.reverse ?_
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map,
    List.ofFn_eq_map]
  refine congrArg₂ (· ++ ·)
    (List.map_congr_left fun i _ => ?_)
    (List.map_congr_left fun j _ => ?_)
  · refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_)) <;> rfl
  · refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_)) <;> rfl

/-! ### The transported closure label -/

/-- The label equivalence of the left side: interleave the
tensor factors, then the closure casts. -/
noncomputable def tensorCloseLabel (s t u v : ℕ) :
    ((Fin (s + t) ⊕ Fin (u + v)) ⊕ Fin ((s + u) + (t + v))) ≃
      (Fin (0 + ((s + u) + (t + v))) ⊕
        Fin ((s + u) + (t + v) + 0)) :=
  _root_.Equiv.sumCongr
    ((interleaveEquiv s t u v).trans
      (finCongr (by omega :
        (s + u) + (t + v) = 0 + ((s + u) + (t + v)))))
    (finCongr (by omega :
      (s + u) + (t + v) = (s + u) + (t + v) + 0))

/-! ### The ground computation: transported pairs blockwise -/

private theorem tensor_ground_zv_aux (s t u v : ℕ) :
    ∀ (l : List (Fin v)),
      Fragment.mapPairs (tensorCloseLabel s t u v).symm
          (l.map (fun l' =>
            ((Sum.inl ⟨(s + u) + (t + l'.val),
                by have := l'.isLt; omega⟩ :
              Fin (0 + ((s + u) + (t + v))) ⊕
                Fin ((s + u) + (t + v) + 0)),
             Sum.inr ⟨(s + u) + (t + l'.val),
               by have := l'.isLt; omega⟩))) =
        l.map (fun l' =>
          (Sum.inl (Sum.inr ⟨u + l'.val, by have := l'.isLt; omega⟩),
           Sum.inr ⟨(s + u) + (t + l'.val),
             by have := l'.isLt; omega⟩))
  | [] => rfl
  | l' :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (tensor_ground_zv_aux s t u v l)
    · show Sum.inl ((interleaveEquiv s t u v).symm
        ⟨(s + u) + (t + l'.val), by have := l'.isLt; omega⟩) = _
      refine congrArg Sum.inl ?_
      rw [show (⟨(s + u) + (t + l'.val),
          by have := l'.isLt; omega⟩ :
            Fin ((s + u) + (t + v))) =
          Fin.natAdd (s + u) (Fin.natAdd t l') from Fin.ext rfl,
        interleaveEquiv_symm_high_right]
      exact congrArg Sum.inr (Fin.ext rfl)
    · show Sum.inr (⟨(s + u) + (t + l'.val),
          by have := l'.isLt; omega⟩ :
        Fin ((s + u) + (t + v))) = _
      rfl

private theorem tensor_ground_xt_aux (s t u v : ℕ) :
    ∀ (l : List (Fin t)),
      Fragment.mapPairs (tensorCloseLabel s t u v).symm
          (l.map (fun k =>
            ((Sum.inl ⟨(s + u) + k.val,
                by have := k.isLt; omega⟩ :
              Fin (0 + ((s + u) + (t + v))) ⊕
                Fin ((s + u) + (t + v) + 0)),
             Sum.inr ⟨(s + u) + k.val,
               by have := k.isLt; omega⟩))) =
        l.map (fun k =>
          (Sum.inl (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩),
           Sum.inr ⟨(s + u) + k.val, by have := k.isLt; omega⟩))
  | [] => rfl
  | k :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (tensor_ground_xt_aux s t u v l)
    · show Sum.inl ((interleaveEquiv s t u v).symm
        ⟨(s + u) + k.val, by have := k.isLt; omega⟩) = _
      refine congrArg Sum.inl ?_
      rw [show (⟨(s + u) + k.val, by have := k.isLt; omega⟩ :
            Fin ((s + u) + (t + v))) =
          Fin.natAdd (s + u) (Fin.castAdd v k) from Fin.ext rfl,
        interleaveEquiv_symm_high_left]
      exact congrArg Sum.inl (Fin.ext rfl)
    · show Sum.inr (⟨(s + u) + k.val, by have := k.isLt; omega⟩ :
        Fin ((s + u) + (t + v))) = _
      rfl

private theorem tensor_ground_zu_aux (s t u v : ℕ) :
    ∀ (l : List (Fin u)),
      Fragment.mapPairs (tensorCloseLabel s t u v).symm
          (l.map (fun j =>
            ((Sum.inl ⟨s + j.val, by have := j.isLt; omega⟩ :
              Fin (0 + ((s + u) + (t + v))) ⊕
                Fin ((s + u) + (t + v) + 0)),
             Sum.inr ⟨s + j.val, by have := j.isLt; omega⟩))) =
        l.map (fun j =>
          (Sum.inl (Sum.inr ⟨j.val, by have := j.isLt; omega⟩),
           Sum.inr ⟨s + j.val, by have := j.isLt; omega⟩))
  | [] => rfl
  | j :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (tensor_ground_zu_aux s t u v l)
    · show Sum.inl ((interleaveEquiv s t u v).symm
        ⟨s + j.val, by have := j.isLt; omega⟩) = _
      refine congrArg Sum.inl ?_
      rw [show (⟨s + j.val, by have := j.isLt; omega⟩ :
            Fin ((s + u) + (t + v))) =
          Fin.castAdd (t + v) (Fin.natAdd s j) from Fin.ext rfl,
        interleaveEquiv_symm_low_right]
      exact congrArg Sum.inr (Fin.ext rfl)
    · show Sum.inr (⟨s + j.val, by have := j.isLt; omega⟩ :
        Fin ((s + u) + (t + v))) = _
      rfl

private theorem tensor_ground_xs_aux (s t u v : ℕ) :
    ∀ (l : List (Fin s)),
      Fragment.mapPairs (tensorCloseLabel s t u v).symm
          (l.map (fun i =>
            ((Sum.inl ⟨i.val, by have := i.isLt; omega⟩ :
              Fin (0 + ((s + u) + (t + v))) ⊕
                Fin ((s + u) + (t + v) + 0)),
             Sum.inr ⟨i.val, by have := i.isLt; omega⟩))) =
        l.map (fun i =>
          (Sum.inl (Sum.inl ⟨i.val, by have := i.isLt; omega⟩),
           Sum.inr ⟨i.val, by have := i.isLt; omega⟩))
  | [] => rfl
  | i :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (tensor_ground_xs_aux s t u v l)
    · show Sum.inl ((interleaveEquiv s t u v).symm
        ⟨i.val, by have := i.isLt; omega⟩) = _
      refine congrArg Sum.inl ?_
      rw [show (⟨i.val, by have := i.isLt; omega⟩ :
            Fin ((s + u) + (t + v))) =
          Fin.castAdd (t + v) (Fin.castAdd u i) from Fin.ext rfl,
        interleaveEquiv_symm_low_left]
      exact congrArg Sum.inl (Fin.ext rfl)
    · show Sum.inr (⟨i.val, by have := i.isLt; omega⟩ :
        Fin ((s + u) + (t + v))) = _
      rfl

/-- The transported closure pairs of the tensor side: the four
blocks, in ground order. -/
theorem tensor_ground_pairs (s t u v : ℕ) :
    Fragment.mapPairs (tensorCloseLabel s t u v).symm
        (interfacePairs 0 ((s + u) + (t + v)) 0) =
      (zvBlock s t u v ++ xtBlock s t u v) ++
        (zuBlock s t u v ++ xsBlock s t u v) := by
  rw [interfacePairs_closure_split (s + u) (t + v),
    mapPairs_append, ipHigh_split, ipLow_split,
    mapPairs_append, mapPairs_append]
  unfold zvBlock xtBlock zuBlock xsBlock
  rw [tensor_ground_zv_aux, tensor_ground_xt_aux,
    tensor_ground_zu_aux, tensor_ground_xs_aux]

/-- Exchanging the middle blocks of a double append. -/
theorem perm_append_exchange {α : Type} (A B C D : List α) :
    ((A ++ B) ++ (C ++ D)).Perm ((A ++ C) ++ (B ++ D)) := by
  have h1 : (A ++ B) ++ (C ++ D) = A ++ (B ++ (C ++ D)) := by
    simp [List.append_assoc]
  have h2 : (A ++ C) ++ (B ++ D) = A ++ (C ++ (B ++ D)) := by
    simp [List.append_assoc]
  rw [h1, h2]
  refine List.Perm.append_left A ?_
  have h3 : B ++ (C ++ D) = (B ++ C) ++ D :=
    (List.append_assoc B C D).symm
  have h4 : C ++ (B ++ D) = (C ++ B) ++ D :=
    (List.append_assoc C B D).symm
  rw [h3, h4]
  exact List.perm_append_comm.append_right D

/-- The tensor-side closure pairs, reordered: `z`-blocks first. -/
theorem tensor_pairs_perm (s t u v : ℕ) :
    (Fragment.mapPairs (tensorCloseLabel s t u v).symm
        (interfacePairs 0 ((s + u) + (t + v)) 0)).Perm
      ((zvBlock s t u v ++ zuBlock s t u v) ++
        (xtBlock s t u v ++ xsBlock s t u v)) := by
  rw [tensor_ground_pairs]
  exact perm_append_exchange _ _ _ _

/-- The reordered tensor-side pairs are well-formed. -/
theorem tensorPairsL_wf (s t u v : ℕ) :
    Fragment.PairsWF
      ((zvBlock s t u v ++ zuBlock s t u v) ++
        (xtBlock s t u v ++ xsBlock s t u v)) :=
  (Fragment.mapPairs_wf (tensorCloseLabel s t u v).symm _
    (interfacePairs_wf 0 ((s + u) + (t + v)) 0)).perm
    (tensor_pairs_perm s t u v)

/-! ### The associated ambient: pairs localize -/

/-- The cross pairs: `x`'s labels against the surviving `x`-block
labels of `G`, inside the associated ambient. -/
def xCrossPairs (s t u v : ℕ) :
    List ((Fin (s + t) ⊕ (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))) ×
      (Fin (s + t) ⊕ (Fin (u + v) ⊕ Fin ((s + u) + (t + v))))) :=
  (List.finRange t).reverse.map (fun k =>
    (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
     Sum.inr (Sum.inr ⟨(s + u) + k.val,
       by have := k.isLt; omega⟩))) ++
  (List.finRange s).reverse.map (fun i =>
    (Sum.inl ⟨i.val, by have := i.isLt; omega⟩,
     Sum.inr (Sum.inr ⟨i.val, by have := i.isLt; omega⟩)))

/-- Under the sum association, the reordered tensor pairs are the
embedded `z`-gluing pairs followed by the cross pairs. -/
theorem tensor_pairs_assoc (s t u v : ℕ) :
    Fragment.mapPairs
        (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (u + v))
          (Fin ((s + u) + (t + v))))
        ((zvBlock s t u v ++ zuBlock s t u v) ++
          (xtBlock s t u v ++ xsBlock s t u v)) =
      Fragment.inrPairs (zClosePairs s t u v) ++
        xCrossPairs s t u v := by
  unfold Fragment.mapPairs zvBlock zuBlock xtBlock xsBlock
    zClosePairs Fragment.inrPairs xCrossPairs
  simp only [List.map_append, List.map_map]
  rfl

/-- The associated pair list is well-formed. -/
theorem tensorPairsA_wf (s t u v : ℕ) :
    Fragment.PairsWF
      (Fragment.inrPairs (zClosePairs s t u v) ++
        xCrossPairs s t u v) :=
  (tensor_pairs_assoc s t u v) ▸
    Fragment.mapPairs_wf
      (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (u + v))
        (Fin ((s + u) + (t + v)))) _ (tensorPairsL_wf s t u v)

/-! ### The lifted cross pairs -/

/-- A high `x`-block label of `G` survives the `z`-gluing. -/
theorem xtSurv (s t u v : ℕ) (k : Fin t) :
    ∀ p ∈ zClosePairs s t u v,
      (Sum.inr ⟨(s + u) + k.val, by have := k.isLt; omega⟩ :
        Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.1 ∧
      (Sum.inr ⟨(s + u) + k.val, by have := k.isLt; omega⟩ :
        Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.2 :=
  (forall_ne_iff_not_mem_flat _ _).mpr
    ((pcSurv_iff s t u v _).mpr
      (Or.inr ⟨by show (s + u) ≤ (s + u) + k.val; omega,
        by show (s + u) + k.val < (s + u) + t
           have := k.isLt; omega⟩))

/-- A low `x`-block label of `G` survives the `z`-gluing. -/
theorem xsSurv (s t u v : ℕ) (i : Fin s) :
    ∀ p ∈ zClosePairs s t u v,
      (Sum.inr ⟨i.val, by have := i.isLt; omega⟩ :
        Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.1 ∧
      (Sum.inr ⟨i.val, by have := i.isLt; omega⟩ :
        Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.2 :=
  (forall_ne_iff_not_mem_flat _ _).mpr
    ((pcSurv_iff s t u v _).mpr
      (Or.inl (show i.val < s from i.isLt)))

/-- The canonical cross pairs after the `z`-gluing: `x`'s labels
against the surviving `x`-block labels of `G`. -/
noncomputable def xLiftedPairs (s t u v : ℕ) :
    List ((Fin (s + t) ⊕
        Fragment.FoldSurviving
          (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))
          (zClosePairs s t u v)) ×
      (Fin (s + t) ⊕
        Fragment.FoldSurviving
          (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))
          (zClosePairs s t u v))) :=
  (List.finRange t).reverse.map (fun k =>
    (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
     Sum.inr ⟨Sum.inr ⟨(s + u) + k.val, by have := k.isLt; omega⟩,
       xtSurv s t u v k⟩)) ++
  (List.finRange s).reverse.map (fun i =>
    (Sum.inl ⟨i.val, by have := i.isLt; omega⟩,
     Sum.inr ⟨Sum.inr ⟨i.val, by have := i.isLt; omega⟩,
       xsSurv s t u v i⟩))

private theorem lift_pull_xt_aux (s t u v : ℕ) :
    ∀ (l : List (Fin t))
      (h : Fragment.PairsSepAll
        (Fragment.inrPairs (zClosePairs s t u v))
        (l.map (fun k =>
          ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
            Fin (s + t) ⊕
              (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))),
           Sum.inr (Sum.inr ⟨(s + u) + k.val,
             by have := k.isLt; omega⟩))))),
      Fragment.mapPairs
          (Fragment.inrFoldEquiv (α := Fin (s + t))
            (zClosePairs s t u v))
          (Fragment.liftPairs _ _ h) =
        l.map (fun k =>
          (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
           Sum.inr ⟨Sum.inr ⟨(s + u) + k.val,
             by have := k.isLt; omega⟩, xtSurv s t u v k⟩))
  | [], _ => rfl
  | k :: l, h => by
    simp only [List.map_cons, Fragment.liftPairs,
      Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (lift_pull_xt_aux s t u v l _)
    exact congrArg Sum.inr (Subtype.ext rfl)

private theorem lift_pull_xs_aux (s t u v : ℕ) :
    ∀ (l : List (Fin s))
      (h : Fragment.PairsSepAll
        (Fragment.inrPairs (zClosePairs s t u v))
        (l.map (fun i =>
          ((Sum.inl ⟨i.val, by have := i.isLt; omega⟩ :
            Fin (s + t) ⊕
              (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))),
           Sum.inr (Sum.inr ⟨i.val, by have := i.isLt; omega⟩))))),
      Fragment.mapPairs
          (Fragment.inrFoldEquiv (α := Fin (s + t))
            (zClosePairs s t u v))
          (Fragment.liftPairs _ _ h) =
        l.map (fun i =>
          (Sum.inl ⟨i.val, by have := i.isLt; omega⟩,
           Sum.inr ⟨Sum.inr ⟨i.val, by have := i.isLt; omega⟩,
             xsSurv s t u v i⟩))
  | [], _ => rfl
  | i :: l, h => by
    simp only [List.map_cons, Fragment.liftPairs,
      Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (lift_pull_xs_aux s t u v l _)
    exact congrArg Sum.inr (Subtype.ext rfl)

/-- Pulling the lifted cross pairs through the right-embedding
survivor equivalence gives the canonical cross pairs. -/
theorem lift_pull (s t u v : ℕ)
    (h : Fragment.PairsSepAll
      (Fragment.inrPairs (zClosePairs s t u v))
      (xCrossPairs s t u v)) :
    Fragment.mapPairs
        (Fragment.inrFoldEquiv (α := Fin (s + t))
          (zClosePairs s t u v))
        (Fragment.liftPairs _ _ h) =
      xLiftedPairs s t u v := by
  unfold xCrossPairs at h ⊢
  rw [liftPairs_append, mapPairs_append]
  unfold xLiftedPairs
  rw [lift_pull_xt_aux s t u v _ h.append_left',
    lift_pull_xs_aux s t u v _ h.append_right']

/-! ### The right side's transported closure label -/

/-- The label equivalence of the right side: the partial-closure
survivor identification, then the closure casts. -/
noncomputable def pcCloseLabel (s t u v : ℕ) :
    (Fin (s + t) ⊕
        Fragment.FoldSurviving
          (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))
          (zClosePairs s t u v)) ≃
      (Fin (0 + (s + t)) ⊕ Fin ((s + t) + 0)) :=
  _root_.Equiv.sumCongr
    (finCongr (by omega : s + t = 0 + (s + t)))
    ((pcSurvEquiv s t u v).trans
      (finCongr (by omega : s + t = (s + t) + 0)))

/-- The inverse survivor identification on high labels. -/
theorem pcSurvEquiv_symm_high_val (s t u v : ℕ) (k : Fin t)
    (h : s + k.val < s + t) :
    ((pcSurvEquiv s t u v).symm ⟨s + k.val, h⟩).val =
      Sum.inr (⟨(s + u) + k.val, by have := k.isLt; omega⟩ :
        Fin ((s + u) + (t + v))) := by
  show ((if hk : s + k.val < s then _ else _ :
    {x // pcSurvPred s t u v x})).val = _
  rw [dif_neg (show ¬ s + k.val < s by omega)]
  exact congrArg Sum.inr (Fin.ext (by
    show (s + u) + (s + k.val - s) = (s + u) + k.val
    omega))

/-- The inverse survivor identification on low labels. -/
theorem pcSurvEquiv_symm_low_val (s t u v : ℕ) (i : Fin s)
    (h : i.val < s + t) :
    ((pcSurvEquiv s t u v).symm ⟨i.val, h⟩).val =
      Sum.inr (⟨i.val, by have := i.isLt; omega⟩ :
        Fin ((s + u) + (t + v))) := by
  show ((if hk : i.val < s then _ else _ :
    {x // pcSurvPred s t u v x})).val = _
  rw [dif_pos (show i.val < s from i.isLt)]

/-! ### The right side's ground computation -/

private theorem rhs_ground_xt_aux (s t u v : ℕ) :
    ∀ (l : List (Fin t)),
      Fragment.mapPairs (pcCloseLabel s t u v).symm
          (l.map (fun k =>
            ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
              Fin (0 + (s + t)) ⊕ Fin ((s + t) + 0)),
             Sum.inr ⟨s + k.val, by have := k.isLt; omega⟩))) =
        l.map (fun k =>
          (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
           Sum.inr ⟨Sum.inr ⟨(s + u) + k.val,
             by have := k.isLt; omega⟩, xtSurv s t u v k⟩))
  | [] => rfl
  | k :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (rhs_ground_xt_aux s t u v l)
    show Sum.inr ((pcSurvEquiv s t u v).symm
      ⟨s + k.val, by have := k.isLt; omega⟩) = _
    refine congrArg Sum.inr (Subtype.ext ?_)
    rw [pcSurvEquiv_symm_high_val]

private theorem rhs_ground_xs_aux (s t u v : ℕ) :
    ∀ (l : List (Fin s)),
      Fragment.mapPairs (pcCloseLabel s t u v).symm
          (l.map (fun i =>
            ((Sum.inl ⟨i.val, by have := i.isLt; omega⟩ :
              Fin (0 + (s + t)) ⊕ Fin ((s + t) + 0)),
             Sum.inr ⟨i.val, by have := i.isLt; omega⟩))) =
        l.map (fun i =>
          (Sum.inl ⟨i.val, by have := i.isLt; omega⟩,
           Sum.inr ⟨Sum.inr ⟨i.val, by have := i.isLt; omega⟩,
             xsSurv s t u v i⟩))
  | [] => rfl
  | i :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (rhs_ground_xs_aux s t u v l)
    show Sum.inr ((pcSurvEquiv s t u v).symm
      ⟨i.val, by have := i.isLt; omega⟩) = _
    refine congrArg Sum.inr (Subtype.ext ?_)
    rw [pcSurvEquiv_symm_low_val]

/-- The right side's closure pairs are the canonical cross
pairs. -/
theorem rhs_ground_pairs (s t u v : ℕ) :
    Fragment.mapPairs (pcCloseLabel s t u v).symm
        (interfacePairs 0 (s + t) 0) =
      xLiftedPairs s t u v := by
  rw [interfacePairs_closure_split s t, mapPairs_append]
  unfold xLiftedPairs ipHigh ipLow
  rw [rhs_ground_xt_aux, rhs_ground_xs_aux]

/-- The right side's transported closure pairs. -/
noncomputable def absQsR (s t u v : ℕ) :=
  Fragment.mapPairs (pcCloseLabel s t u v).symm
    (interfacePairs 0 (s + t) 0)

/-- The canonical cross pairs are well-formed. -/
theorem xLiftedPairs_wf (s t u v : ℕ) :
    Fragment.PairsWF (xLiftedPairs s t u v) :=
  (rhs_ground_pairs s t u v) ▸
    Fragment.mapPairs_wf (pcCloseLabel s t u v).symm _
      (interfacePairs_wf 0 (s + t) 0)

/-! ### The right side, normalized -/

/-- The composed label identification of the right side. -/
noncomputable def absLabelR (s t u v : ℕ) :
    Fragment.FoldSurviving
        (Fin (s + t) ⊕
          Fragment.FoldSurviving
            (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))
            (zClosePairs s t u v))
        (xLiftedPairs s t u v) ≃ Fin (0 + 0) :=
  (Fragment.foldSurvivingPermEquiv
      ((rhs_ground_pairs s t u v) ▸ List.Perm.refl _)).symm.trans
    ((Fragment.foldSurvivingMapEquiv (pcCloseLabel s t u v)
        (absQsR s t u v)).trans
      ((Fragment.foldSurvivingPermEquiv
          ((mapPairs_symm_cancel (pcCloseLabel s t u v)
            (interfacePairs 0 (s + t) 0)).symm ▸
            List.Perm.refl _)).symm.trans
        ((interfaceSurvEquiv 0 (s + t) 0).trans finSumFinEquiv)))

/-- **The right side, normalized**: the closure of `x` against
the partial closure is iterated gluing of the canonical cross
pairs over `x ⊔ (glued z ⊔ G)`. -/
noncomputable def absNormalRight {s t u v : ℕ}
    (X : Fragment (Fin (s + t))) (z : Fragment (Fin (u + v)))
    (G : Fragment (Fin ((s + u) + (t + v)))) :
    (pairClose X (partialClose z G)).Equiv
      ((Fragment.glueList
          (X.disjUnion
            (Fragment.glueList (z.disjUnion G)
              (zClosePairs s t u v) (zClosePairs_wf s t u v)))
          (xLiftedPairs s t u v)
          (xLiftedPairs_wf s t u v)).relabel
        (absLabelR s t u v)) := by
  let σB := pcCloseLabel s t u v
  let qs0 := absQsR s t u v
  have wfqs0 : Fragment.PairsWF qs0 :=
    Fragment.mapPairs_wf σB.symm _ (interfacePairs_wf 0 (s + t) 0)
  let Zg := Fragment.glueList (z.disjUnion G)
    (zClosePairs s t u v) (zClosePairs_wf s t u v)
  let AmbR := X.disjUnion Zg
  -- C5: bridge the transported pairs to the canonical list.
  have C5 : (Fragment.glueList AmbR qs0 wfqs0).Equiv
      ((Fragment.glueList AmbR (xLiftedPairs s t u v)
          (xLiftedPairs_wf s t u v)).relabel
        (Fragment.foldSurvivingPermEquiv
          ((rhs_ground_pairs s t u v) ▸
            List.Perm.refl _)).symm) :=
    Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv AmbR (rhs_ground_pairs s t u v)
        wfqs0 (xLiftedPairs_wf s t u v)
        ((rhs_ground_pairs s t u v) ▸ List.Perm.refl _))
  -- C3: the fold-survivor relabelling stage.
  have C3 := (Fragment.glueListRelabel AmbR σB qs0 wfqs0).trans
    ((Fragment.Equiv.relabelCongr C5
      (Fragment.foldSurvivingMapEquiv σB qs0)).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C2: bridge the closure pairs.
  have C2 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (AmbR.relabel σB)
        (mapPairs_symm_cancel σB
          (interfacePairs 0 (s + t) 0)).symm
        (interfacePairs_wf 0 (s + t) 0)
        (Fragment.mapPairs_wf σB _ wfqs0)
        ((mapPairs_symm_cancel σB
          (interfacePairs 0 (s + t) 0)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr C3
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel σB
          (interfacePairs 0 (s + t) 0)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- E1R: peel the closure casts.
  have E1R : ((X.relabel
      (finCongr (by omega : s + t = 0 + (s + t)))).disjUnion
        ((partialClose z G).relabel
          (finCongr (by omega : s + t = (s + t) + 0)))).Equiv
      (AmbR.relabel σB) :=
    (Fragment.Equiv.disjUnionCongr
      (Fragment.Equiv.refl _)
      (Fragment.Equiv.relabelTrans Zg (pcSurvEquiv s t u v)
        (finCongr (by omega : s + t = (s + t) + 0)))).trans
    ((Fragment.relabelDisjUnionLeft X _
      (finCongr (by omega : s + t = 0 + (s + t)))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.relabelDisjUnionRight X Zg
        ((pcSurvEquiv s t u v).trans
          (finCongr (by omega : s + t = (s + t) + 0))))
      (_root_.Equiv.sumCongr
        (finCongr (by omega : s + t = 0 + (s + t)))
        (_root_.Equiv.refl _))).trans
    ((Fragment.Equiv.relabelTrans _ _ _).trans
    (Fragment.Equiv.relabelEq _
      (_root_.Equiv.ext (fun x => by cases x <;> rfl))))))
  -- C1: transport the closure gluing across E1R.
  have C1 := (Fragment.glueListCongr E1R
    (interfacePairs 0 (s + t) 0)
    (interfacePairs_wf 0 (s + t) 0)).trans C2
  -- Assemble.
  exact (composeNormal
      (X.relabel (finCongr (by omega : s + t = 0 + (s + t))))
      ((partialClose z G).relabel
        (finCongr (by omega : s + t = (s + t) + 0)))).trans
    ((Fragment.Equiv.relabelCongr C1
      ((interfaceSurvEquiv 0 (s + t) 0).trans
        finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

/-! ### The left side's derived pair lists -/

/-- The left side's transported closure pairs. -/
noncomputable def absQsL (s t u v : ℕ) :=
  Fragment.mapPairs (tensorCloseLabel s t u v).symm
    (interfacePairs 0 ((s + u) + (t + v)) 0)

/-- The reordered pairs, pulled back through the association. -/
noncomputable def absPs1 (s t u v : ℕ) :=
  Fragment.mapPairs
    (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (u + v))
      (Fin ((s + u) + (t + v)))).symm.symm
    ((zvBlock s t u v ++ zuBlock s t u v) ++
      (xtBlock s t u v ++ xsBlock s t u v))

/-- The pulled-back pairs are the localized pairs. -/
theorem abs_assoc' (s t u v : ℕ) :
    absPs1 s t u v =
      Fragment.inrPairs (zClosePairs s t u v) ++
        xCrossPairs s t u v := by
  unfold absPs1
  rw [_root_.Equiv.symm_symm]
  exact tensor_pairs_assoc s t u v

/-- The lifted cross pairs of the two-stage fold. -/
noncomputable def absQsLift (s t u v : ℕ) :=
  Fragment.liftPairs
    (Fragment.inrPairs (zClosePairs s t u v))
    (xCrossPairs s t u v)
    ((tensorPairsA_wf s t u v).append_sep)

/-- The lifted cross pairs, pulled back through the embedding
survivor equivalence. -/
noncomputable def absPs0 (s t u v : ℕ) :=
  Fragment.mapPairs
    (Fragment.inrFoldEquiv (α := Fin (s + t))
      (zClosePairs s t u v)).symm.symm
    (absQsLift s t u v)

/-- The pulled-back lifted pairs are the canonical cross pairs. -/
theorem abs_lift_pull (s t u v : ℕ) :
    absPs0 s t u v = xLiftedPairs s t u v := by
  unfold absPs0 absQsLift
  rw [_root_.Equiv.symm_symm]
  exact lift_pull s t u v _

/-! ### The left side, normalized -/

/-- The composed label identification of the left side. -/
noncomputable def absLabelL (s t u v : ℕ) :
    Fragment.FoldSurviving
        (Fin (s + t) ⊕
          Fragment.FoldSurviving
            (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))
            (zClosePairs s t u v))
        (xLiftedPairs s t u v) ≃ Fin (0 + 0) :=
  (Fragment.foldSurvivingPermEquiv
      ((abs_lift_pull s t u v) ▸ List.Perm.refl _)).symm.trans
  ((Fragment.foldSurvivingMapEquiv
      (Fragment.inrFoldEquiv (α := Fin (s + t))
        (zClosePairs s t u v)).symm (absPs0 s t u v)).trans
  ((Fragment.foldSurvivingPermEquiv
      ((mapPairs_symm_cancel
        (Fragment.inrFoldEquiv (α := Fin (s + t))
          (zClosePairs s t u v)).symm
        (absQsLift s t u v)).symm ▸
        List.Perm.refl _)).symm.trans
  ((Fragment.appendFlatten
      (Fragment.inrPairs (zClosePairs s t u v))
      (xCrossPairs s t u v)
      ((tensorPairsA_wf s t u v).append_sep)).trans
  ((Fragment.foldSurvivingPermEquiv
      ((abs_assoc' s t u v) ▸ List.Perm.refl _)).symm.trans
  ((Fragment.foldSurvivingMapEquiv
      (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (u + v))
        (Fin ((s + u) + (t + v)))).symm (absPs1 s t u v)).trans
  ((Fragment.foldSurvivingPermEquiv
      ((mapPairs_symm_cancel
        (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (u + v))
          (Fin ((s + u) + (t + v)))).symm
        ((zvBlock s t u v ++ zuBlock s t u v) ++
          (xtBlock s t u v ++ xsBlock s t u v))).symm ▸
        List.Perm.refl _)).symm.trans
  ((Fragment.foldSurvivingPermEquiv
      (tensor_pairs_perm s t u v)).symm.trans
  ((Fragment.foldSurvivingMapEquiv (tensorCloseLabel s t u v)
      (absQsL s t u v)).trans
  ((Fragment.foldSurvivingPermEquiv
      ((mapPairs_symm_cancel (tensorCloseLabel s t u v)
        (interfacePairs 0 ((s + u) + (t + v)) 0)).symm ▸
        List.Perm.refl _)).symm.trans
  ((interfaceSurvEquiv 0 ((s + u) + (t + v)) 0).trans
    finSumFinEquiv))))))))))

/-- **The left side, normalized**: the closure of the tensor
against `G` is iterated gluing of the canonical cross pairs over
`x ⊔ (glued z ⊔ G)`. -/
noncomputable def absNormalLeft {s t u v : ℕ}
    (X : Fragment (Fin (s + t))) (z : Fragment (Fin (u + v)))
    (G : Fragment (Fin ((s + u) + (t + v)))) :
    (pairClose (tensorFragment X z) G).Equiv
      ((Fragment.glueList
          (X.disjUnion
            (Fragment.glueList (z.disjUnion G)
              (zClosePairs s t u v) (zClosePairs_wf s t u v)))
          (xLiftedPairs s t u v)
          (xLiftedPairs_wf s t u v)).relabel
        (absLabelL s t u v)) := by
  -- ═══════ SETUP ═══════
  -- The three ambients (`AmbL`, `AmbA`, `AmbR`), the folds over them,
  -- and the well-formedness certificates of the four pair lists.
  let σA := tensorCloseLabel s t u v
  let aE := (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (u + v))
    (Fin ((s + u) + (t + v)))).symm
  let iM := Fragment.inrFoldEquiv (α := Fin (s + t))
    (zClosePairs s t u v)
  let pairsP := (zvBlock s t u v ++ zuBlock s t u v) ++
    (xtBlock s t u v ++ xsBlock s t u v)
  have wfqsL : Fragment.PairsWF (absQsL s t u v) :=
    Fragment.mapPairs_wf σA.symm _
      (interfacePairs_wf 0 ((s + u) + (t + v)) 0)
  have wfP : Fragment.PairsWF pairsP := tensorPairsL_wf s t u v
  have wfPs1 : Fragment.PairsWF (absPs1 s t u v) :=
    Fragment.mapPairs_wf aE.symm _ wfP
  have wfA : Fragment.PairsWF
      (Fragment.inrPairs (zClosePairs s t u v) ++
        xCrossPairs s t u v) := tensorPairsA_wf s t u v
  have wfLift : Fragment.PairsWF (absQsLift s t u v) :=
    Fragment.liftPairs_wf _ _ wfA.append_right wfA.append_sep
  have wfPs0 : Fragment.PairsWF (absPs0 s t u v) :=
    Fragment.mapPairs_wf iM.symm.symm _ wfLift
  let Zg := Fragment.glueList (z.disjUnion G)
    (zClosePairs s t u v) (zClosePairs_wf s t u v)
  let AmbL := (X.disjUnion z).disjUnion G
  let AmbA := X.disjUnion (z.disjUnion G)
  let AmbR := X.disjUnion Zg
  let Xf := Fragment.glueList AmbA
    (Fragment.inrPairs (zClosePairs s t u v)) wfA.append_left
  -- ═══════ STAGE 1: THE z-BLOCK, AS AN EMBEDDED FOLD ═══════
  -- K9: bridge the pulled-back lifted pairs to the canonical
  -- list.
  have K9 : (Fragment.glueList AmbR (absPs0 s t u v)
      wfPs0).Equiv
      ((Fragment.glueList AmbR (xLiftedPairs s t u v)
          (xLiftedPairs_wf s t u v)).relabel
        (Fragment.foldSurvivingPermEquiv
          ((abs_lift_pull s t u v) ▸
            List.Perm.refl _)).symm) :=
    Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv AmbR (abs_lift_pull s t u v)
        wfPs0 (xLiftedPairs_wf s t u v)
        ((abs_lift_pull s t u v) ▸ List.Perm.refl _))
  -- K8: the embedding-survivor relabelling stage.
  have K8 := (Fragment.glueListRelabel AmbR iM.symm
      (absPs0 s t u v) wfPs0).trans
    ((Fragment.Equiv.relabelCongr K9
      (Fragment.foldSurvivingMapEquiv iM.symm
        (absPs0 s t u v))).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- K7: bridge the lifted pairs.
  have K7 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (AmbR.relabel iM.symm)
        (mapPairs_symm_cancel iM.symm (absQsLift s t u v)).symm
        wfLift (Fragment.mapPairs_wf iM.symm _ wfPs0)
        ((mapPairs_symm_cancel iM.symm
          (absQsLift s t u v)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr K8
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel iM.symm
          (absQsLift s t u v)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- E4: the glued z-block is the embedded fold.
  have E4 : Xf.Equiv (AmbR.relabel iM.symm) :=
    Fragment.glueListDisjUnionRight X (z.disjUnion G)
      (zClosePairs s t u v) (zClosePairs_wf s t u v)
  -- K6: transport across E4.
  have K6 := (Fragment.glueListCongr E4 (absQsLift s t u v)
    wfLift).trans K7
  -- ═══════ STAGE 2: APPENDING AND REASSOCIATING THE AMBIENT ═══════
  -- K5: the append stage.
  have K5 := (Fragment.glueListAppend AmbA
      (Fragment.inrPairs (zClosePairs s t u v))
      (xCrossPairs s t u v) wfA).trans
    ((Fragment.Equiv.relabelCongr K6
      (Fragment.appendFlatten _ _ wfA.append_sep)).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- K4: bridge the localized pairs.
  have K4 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv AmbA (abs_assoc' s t u v)
        wfPs1 wfA
        ((abs_assoc' s t u v) ▸ List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr K5
      (Fragment.foldSurvivingPermEquiv
        ((abs_assoc' s t u v) ▸ List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- K3: the association relabelling stage.
  have K3 := (Fragment.glueListRelabel AmbA aE
      (absPs1 s t u v) wfPs1).trans
    ((Fragment.Equiv.relabelCongr K4
      (Fragment.foldSurvivingMapEquiv aE (absPs1 s t u v))).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- K2: bridge the reordered pairs.
  have K2 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (AmbA.relabel aE)
        (mapPairs_symm_cancel aE pairsP).symm
        wfP (Fragment.mapPairs_wf aE _ wfPs1)
        ((mapPairs_symm_cancel aE pairsP).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr K3
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel aE pairsP).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- KA: the association of the ambient.
  have KA := (Fragment.glueListCongr
    (Fragment.disjUnionAssoc X z G) pairsP wfP).trans K2
  -- ═══════ STAGE 3: REORDERING AND THE BOUNDARY RELABEL ═══════
  -- K1: the reordering stage.
  have K1 := (Fragment.glueListPerm AmbL
      (tensor_pairs_perm s t u v) wfqsL).trans
    ((Fragment.Equiv.relabelCongr KA
      (Fragment.foldSurvivingPermEquiv
        (tensor_pairs_perm s t u v)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- K0: the boundary relabelling stage.
  have K0 := (Fragment.glueListRelabel AmbL σA
      (absQsL s t u v) wfqsL).trans
    ((Fragment.Equiv.relabelCongr K1
      (Fragment.foldSurvivingMapEquiv σA (absQsL s t u v))).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- KB: bridge the closure pairs.
  have KB := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (AmbL.relabel σA)
        (mapPairs_symm_cancel σA
          (interfacePairs 0 ((s + u) + (t + v)) 0)).symm
        (interfacePairs_wf 0 ((s + u) + (t + v)) 0)
        (Fragment.mapPairs_wf σA _ wfqsL)
        ((mapPairs_symm_cancel σA
          (interfacePairs 0 ((s + u) + (t + v)) 0)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr K0
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel σA
          (interfacePairs 0 ((s + u) + (t + v)) 0)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- ═══════ STAGE 4: THE CLOSURE'S OWN INTERFACE ═══════
  -- E1L: peel the closure casts.
  have E1L : (((tensorFragment X z).relabel
      (finCongr (by omega :
        (s + u) + (t + v) = 0 + ((s + u) + (t + v))))).disjUnion
        (G.relabel (finCongr (by omega :
          (s + u) + (t + v) = (s + u) + (t + v) + 0)))).Equiv
      (AmbL.relabel σA) :=
    (Fragment.Equiv.disjUnionCongr
      (Fragment.Equiv.relabelTrans (X.disjUnion z)
        (interleaveEquiv s t u v)
        (finCongr (by omega :
          (s + u) + (t + v) = 0 + ((s + u) + (t + v)))))
      (Fragment.Equiv.refl _)).trans
    ((Fragment.relabelDisjUnionLeft (X.disjUnion z) _
      ((interleaveEquiv s t u v).trans
        (finCongr (by omega :
          (s + u) + (t + v) = 0 + ((s + u) + (t + v)))))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.relabelDisjUnionRight (X.disjUnion z) G
        (finCongr (by omega :
          (s + u) + (t + v) = (s + u) + (t + v) + 0)))
      (_root_.Equiv.sumCongr
        ((interleaveEquiv s t u v).trans
          (finCongr (by omega :
            (s + u) + (t + v) = 0 + ((s + u) + (t + v)))))
        (_root_.Equiv.refl _))).trans
    ((Fragment.Equiv.relabelTrans _ _ _).trans
    (Fragment.Equiv.relabelEq _
      (_root_.Equiv.ext (fun x => by cases x <;> rfl))))))
  -- KC: transport the closure gluing across E1L.
  have KC := (Fragment.glueListCongr E1L
    (interfacePairs 0 ((s + u) + (t + v)) 0)
    (interfacePairs_wf 0 ((s + u) + (t + v)) 0)).trans KB
  -- ═══════ ASSEMBLY ═══════
  exact (composeNormal
      ((tensorFragment X z).relabel
        (finCongr (by omega :
          (s + u) + (t + v) = 0 + ((s + u) + (t + v)))))
      (G.relabel (finCongr (by omega :
        (s + u) + (t + v) = (s + u) + (t + v) + 0)))).trans
    ((Fragment.Equiv.relabelCongr KC
      ((interfaceSurvEquiv 0 ((s + u) + (t + v)) 0).trans
        finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

/-! ### The meet: no label survives a full closure -/

/-- The canonical cross pairs glue every label: no survivor. -/
theorem absSurv_empty (s t u v : ℕ)
    (x : Fragment.FoldSurviving
      (Fin (s + t) ⊕
        Fragment.FoldSurviving
          (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))
          (zClosePairs s t u v))
      (xLiftedPairs s t u v)) : False := by
  obtain ⟨xv, hx⟩ := x
  rcases xv with a | b
  · by_cases ha : a.val < s
    · exact (hx _ (List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨⟨a.val, ha⟩,
          List.mem_reverse.mpr (List.mem_finRange _),
          rfl⟩)))).1 (congrArg Sum.inl (Fin.ext rfl))
    · have hk : a.val - s < t := by have := a.isLt; omega
      exact (hx _ (List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨⟨a.val - s, hk⟩,
          List.mem_reverse.mpr (List.mem_finRange _),
          rfl⟩)))).1 (congrArg Sum.inl (Fin.ext (by
            show a.val = s + (a.val - s)
            omega)))
  · obtain ⟨bv, hb⟩ := b
    have hpred : pcSurvPred s t u v bv :=
      (pcSurv_iff s t u v bv).mp
        ((forall_ne_iff_not_mem_flat _ bv).mp hb)
    rcases bv with a' | c
    · exact hpred
    · rcases hpred with hc | hc
      · exact (hx _ (List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨⟨c.val, hc⟩,
            List.mem_reverse.mpr (List.mem_finRange _),
            rfl⟩)))).2 (congrArg Sum.inr (Subtype.ext
              (congrArg Sum.inr (Fin.ext rfl))))
      · have hk : c.val - (s + u) < t := by omega
        exact (hx _ (List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨⟨c.val - (s + u), hk⟩,
            List.mem_reverse.mpr (List.mem_finRange _),
            rfl⟩)))).2 (congrArg Sum.inr (Subtype.ext
              (congrArg Sum.inr (Fin.ext (by
                show c.val = (s + u) + (c.val - (s + u))
                omega)))))

/-- **The absorption** (accompanying paper, Lemma 3.3(b), geometric
core): closing a tensor against a test fragment is closing the
first factor against the partial closure of the second. -/
noncomputable def pairCloseTensorAbsorb {s t u v : ℕ}
    (X : Fragment (Fin (s + t))) (z : Fragment (Fin (u + v)))
    (G : Fragment (Fin ((s + u) + (t + v)))) :
    (pairClose (tensorFragment X z) G).Equiv
      (pairClose X (partialClose z G)) :=
  (absNormalLeft X z G).trans
    ((Fragment.Equiv.relabelEq _
      (_root_.Equiv.ext (fun x =>
        absurd (absSurv_empty s t u v x) not_false))).trans
    (absNormalRight X z G).symm)

/-! ### The monoidal ideal (accompanying paper, Lemma 3.3(b)) -/

/-- The connection row of a tensor is a connection row of the
first factor at the partially closed test fragment. -/
theorem connectionPairing_tensor (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u v : ℕ} (X : Fragment (Fin (s + t)))
    (z : Fragment (Fin (u + v)))
    (G : Fragment (Fin ((s + u) + (t + v)))) :
    connectionPairing f ((s + u) + (t + v))
        (tensorFragment X z) G =
      connectionPairing f (s + t) X (partialClose z G) :=
  hf _ _ (pairCloseTensorAbsorb X z G)

/-- Bilinear tensor on the free modules of fragments. -/
noncomputable def tensorFinsupp (s t u v : ℕ) :
    (Fragment (Fin (s + t)) →₀ ℂ) →ₗ[ℂ]
      (Fragment (Fin (u + v)) →₀ ℂ) →ₗ[ℂ]
        (Fragment (Fin ((s + u) + (t + v))) →₀ ℂ) :=
  Finsupp.lift _ ℂ _ (fun F =>
    Finsupp.lift _ ℂ _ (fun z =>
      Finsupp.single (tensorFragment F z) (1 : ℂ)))

/-- Tensor of weighted single fragments. -/
theorem tensorFinsupp_single (s t u v : ℕ)
    (F : Fragment (Fin (s + t))) (c : ℂ)
    (z : Fragment (Fin (u + v))) (d : ℂ) :
    tensorFinsupp s t u v (Finsupp.single F c)
        (Finsupp.single z d) =
      Finsupp.single (tensorFragment F z) (c * d) := by
  unfold tensorFinsupp
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp),
    LinearMap.smul_apply, Finsupp.lift_apply,
    Finsupp.sum_single_index (by simp), Finsupp.smul_single,
    Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]

/-- The connection row of a single-fragment tensor, linearized in
the first slot. -/
theorem connectionMap_tensor_single (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u v : ℕ} (x : Fragment (Fin (s + t)) →₀ ℂ)
    (z : Fragment (Fin (u + v)))
    (K : Fragment (Fin ((s + u) + (t + v)))) :
    connectionMap f ((s + u) + (t + v))
        (tensorFinsupp s t u v x (Finsupp.single z 1)) K =
      connectionMap f (s + t) x (partialClose z K) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, LinearMap.zero_apply, map_zero]
    rfl
  | add y w hy hw =>
    rw [map_add, LinearMap.add_apply, map_add]
    show connectionMap f ((s + u) + (t + v)) _ K +
      connectionMap f ((s + u) + (t + v)) _ K = _
    rw [hy, hw, map_add]
    rfl
  | single F c =>
    rw [tensorFinsupp_single, mul_one, connectionMap_single,
      connectionMap_single, connectionPairing_tensor f hf]

/-- A kernel element tensored with a single fragment stays in the
kernel. -/
theorem tensorFinsupp_single_ker (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u v : ℕ} {x : Fragment (Fin (s + t)) →₀ ℂ}
    (hx : x ∈ LinearMap.ker (connectionMap f (s + t)))
    (z : Fragment (Fin (u + v))) :
    tensorFinsupp s t u v x (Finsupp.single z 1) ∈
      LinearMap.ker (connectionMap f ((s + u) + (t + v))) := by
  rw [LinearMap.mem_ker] at hx ⊢
  funext K
  rw [connectionMap_tensor_single f hf x z K, hx]
  rfl

/-- **The monoidal ideal** (accompanying paper, Lemma 3.3(b)): a
kernel element tensored with anything stays in the kernel. -/
theorem tensorFinsupp_ker_left (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {s t u v : ℕ} {x : Fragment (Fin (s + t)) →₀ ℂ}
    (hx : x ∈ LinearMap.ker (connectionMap f (s + t)))
    (y : Fragment (Fin (u + v)) →₀ ℂ) :
    tensorFinsupp s t u v x y ∈
      LinearMap.ker (connectionMap f ((s + u) + (t + v))) := by
  induction y using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add y w hy hw =>
    rw [map_add]
    exact Submodule.add_mem _ hy hw
  | single z c =>
    have h1 : tensorFinsupp s t u v x (Finsupp.single z c) =
        c • tensorFinsupp s t u v x (Finsupp.single z 1) := by
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1]
    exact Submodule.smul_mem _ c
      (tensorFinsupp_single_ker f hf hx z)

end RS
