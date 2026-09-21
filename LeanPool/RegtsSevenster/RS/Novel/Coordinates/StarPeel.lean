/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CircleScalar

/-!
# Peeling the multi-star into vertex stars

The block-sorted multi-star over a degree list is the iterated
tensor of vertex stars: `blockAssign` sends each slot to its
block, `starTensor` is the iterated tensor, and the peel
induction identifies them.
-/

namespace RS

/-- The block of a slot in a degree list. -/
def blockAssign : (ds : List ℕ) → Fin ds.sum → Fin ds.length
  | [], i => i.elim0
  | d :: ds, i =>
      if h : i.val < d then ⟨0, by simp⟩
      else (blockAssign ds ⟨i.val - d, by
        have := i.isLt
        simp only [List.sum_cons] at this
        omega⟩).succ

/-- The iterated tensor of vertex stars over a degree list. -/
noncomputable def starTensor : (ds : List ℕ) →
    Fragment (Fin ds.sum)
  | [] => emptyClosedFragment
  | d :: ds =>
      (tensorFragment
        ((vertexStar d).relabel (finCongr (by omega : d = 0 + d)))
        ((starTensor ds).relabel (finCongr
          (by omega : ds.sum = 0 + ds.sum)))).relabel
        (finCongr (by
          show (0 + 0) + (d + ds.sum) = (d :: ds).sum
          simp [List.sum_cons]))

/-- The empty multi-star is the empty fragment. -/
noncomputable def multiStarNil (c : ℕ) :
    (multiStar (blockAssign []) c).Equiv
      (addCircles (starTensor []) c) where
  flagEquiv :=
    haveI h1 : IsEmpty (multiStar (blockAssign []) c).Flag :=
      ⟨fun g => g.elim (fun i => i.elim0) (fun i => i.elim0)⟩
    haveI h2 : IsEmpty (addCircles (starTensor []) c).Flag :=
      inferInstanceAs (IsEmpty Empty)
    _root_.Equiv.equivOfIsEmpty _ _
  vertexEquiv :=
    haveI h1 : IsEmpty (multiStar (blockAssign []) c).Vertex :=
      ⟨fun i => i.elim0⟩
    haveI h2 : IsEmpty (addCircles (starTensor []) c).Vertex :=
      inferInstanceAs (IsEmpty Empty)
    _root_.Equiv.equivOfIsEmpty _ _
  attach_comm := fun g =>
    g.elim (fun i => i.elim0) (fun i => i.elim0)
  pairing_comm := fun g =>
    g.elim (fun i => i.elim0) (fun i => i.elim0)
  circles_eq := by
    show c = 0 + c
    omega

/-- The head-vertex splitting map. -/
def peelVertexFun (n : ℕ) (v : Fin (n + 1)) : Unit ⊕ Fin n :=
  if h : v.val = 0 then Sum.inl ()
  else Sum.inr ⟨v.val - 1, by have := v.isLt; omega⟩

/-- The head-vertex merging map. -/
def peelVertexInv (n : ℕ) : Unit ⊕ Fin n → Fin (n + 1)
  | Sum.inl _ => ⟨0, Nat.succ_pos n⟩
  | Sum.inr j => ⟨j.val + 1, by have := j.isLt; omega⟩

/-- The head-vertex split. -/
def peelVertexEquiv (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun := peelVertexFun n
  invFun := peelVertexInv n
  left_inv v := by
    by_cases h : v.val = 0
    · have h1 : peelVertexFun n v = Sum.inl () := dif_pos h
      rw [h1]
      exact Fin.ext h.symm
    · have h1 : peelVertexFun n v =
          Sum.inr ⟨v.val - 1, by have := v.isLt; omega⟩ :=
        dif_neg h
      rw [h1]
      exact Fin.ext (by
        show v.val - 1 + 1 = v.val
        omega)
  right_inv x := by
    rcases x with u | j
    · exact dif_pos rfl
    · have h1 : peelVertexFun n ⟨j.val + 1, by
          have := j.isLt
          omega⟩ = Sum.inr ⟨j.val + 1 - 1, by
          have := j.isLt
          omega⟩ :=
        dif_neg (show ¬ (j.val + 1 = 0) by omega)
      rw [show peelVertexInv n (Sum.inr j) =
        (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (n + 1))
        from rfl, h1]
      exact congrArg Sum.inr (Fin.ext (by
        show j.val + 1 - 1 = j.val
        omega))

/-- The peel splits off the first vertex. -/
theorem peelVertexEquiv_zero (n : ℕ) (h : 0 < n + 1) :
    peelVertexEquiv n ⟨0, h⟩ = Sum.inl () := by
  show peelVertexFun n ⟨0, h⟩ = Sum.inl ()
  exact dif_pos rfl

/-- And leaves the rest in order. -/
theorem peelVertexEquiv_succ (n : ℕ) (j : Fin n) :
    peelVertexEquiv n j.succ = Sum.inr j := by
  have h1 : peelVertexFun n j.succ =
      Sum.inr ⟨j.succ.val - 1, by
        show j.val + 1 - 1 < n
        have := j.isLt
        omega⟩ :=
    dif_neg (show ¬ (j.succ.val = 0) from by
      show ¬ (j.val + 1 = 0)
      omega)
  show peelVertexFun n j.succ = Sum.inr j
  rw [h1]
  exact congrArg Sum.inr (Fin.ext (by
    show j.val + 1 - 1 = j.val
    omega))

/-- The slot shuffle of the peel. -/
def peelFlagEquiv (d S : ℕ) :
    (Fin (d + S) ⊕ Fin (d + S)) ≃
      ((Fin d ⊕ Fin d) ⊕ (Fin S ⊕ Fin S)) :=
  (_root_.Equiv.sumCongr finSumFinEquiv.symm
    finSumFinEquiv.symm).trans
    (_root_.Equiv.sumSumSumComm (Fin d) (Fin S) (Fin d) (Fin S))

/-- On the left side, the first block's flags go to the peeled
star. -/
theorem peelFlagEquiv_inl_low (d S : ℕ) (i : Fin d) :
    peelFlagEquiv d S (Sum.inl (Fin.castAdd S i)) =
      Sum.inl (Sum.inl i) := by
  unfold peelFlagEquiv
  rw [_root_.Equiv.trans_apply, _root_.Equiv.sumCongr_apply,
    Sum.map_inl, finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- And the remaining left flags to the rest. -/
theorem peelFlagEquiv_inl_high (d S : ℕ) (j : Fin S) :
    peelFlagEquiv d S (Sum.inl (Fin.natAdd d j)) =
      Sum.inr (Sum.inl j) := by
  unfold peelFlagEquiv
  rw [_root_.Equiv.trans_apply, _root_.Equiv.sumCongr_apply,
    Sum.map_inl, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- On the right side, the first block's flags go to the peeled
star. -/
theorem peelFlagEquiv_inr_low (d S : ℕ) (i : Fin d) :
    peelFlagEquiv d S (Sum.inr (Fin.castAdd S i)) =
      Sum.inl (Sum.inr i) := by
  unfold peelFlagEquiv
  rw [_root_.Equiv.trans_apply, _root_.Equiv.sumCongr_apply,
    Sum.map_inr, finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- And the remaining right flags to the rest. -/
theorem peelFlagEquiv_inr_high (d S : ℕ) (j : Fin S) :
    peelFlagEquiv d S (Sum.inr (Fin.natAdd d j)) =
      Sum.inr (Sum.inr j) := by
  unfold peelFlagEquiv
  rw [_root_.Equiv.trans_apply, _root_.Equiv.sumCongr_apply,
    Sum.map_inr, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- **The peel step**, generically: a multi-star whose assignment
splits blockwise is the head vertex star tensored with the tail
multi-star. -/
noncomputable def multiStarPeel {n : ℕ} (d S c : ℕ)
    (rest : Fin S → Fin n) (a : Fin (d + S) → Fin (n + 1))
    (ha_low : ∀ i : Fin d,
      a (Fin.castAdd S i) = ⟨0, Nat.succ_pos n⟩)
    (ha_high : ∀ j : Fin S,
      a (Fin.natAdd d j) = (rest j).succ) :
    (multiStar a c).Equiv
      ((tensorFragment
        ((vertexStar d).relabel (finCongr (by omega : d = 0 + d)))
        ((multiStar rest c).relabel (finCongr
          (by omega : S = 0 + S)))).relabel
        (finCongr (by omega : (0 + 0) + (d + S) = d + S))) where
  flagEquiv := peelFlagEquiv d S
  vertexEquiv := peelVertexEquiv n
  -- ═══════ ATTACHMENT ═══════
  -- Flags below `d` sit on the peeled star, the rest on the
  -- remaining ones; each side keeps its own vertex.
  attach_comm := fun g => by
    rcases g with i | i
    · rcases Nat.lt_or_ge i.val d with hi | hi
      · rw [show i = Fin.castAdd S ⟨i.val, hi⟩ from Fin.ext rfl]
        erw [peelFlagEquiv_inl_low d S ⟨i.val, hi⟩]
        show (Sum.inl (Sum.inl ()) :
          ((Unit ⊕ Fin n) ⊕ Fin (d + S))) =
          Sum.map (peelVertexEquiv n) id
            (Sum.inl (a (Fin.castAdd S ⟨i.val, hi⟩)))
        rw [ha_low]
        show Sum.inl (Sum.inl ()) =
          Sum.inl (peelVertexEquiv n ⟨0, Nat.succ_pos n⟩)
        rw [peelVertexEquiv_zero]
      · rw [show i = Fin.natAdd d ⟨i.val - d, by
            have := i.isLt
            omega⟩ from Fin.ext (by
            show i.val = d + (i.val - d)
            omega)]
        erw [peelFlagEquiv_inl_high d S]
        show (Sum.inl (Sum.inr (rest ⟨i.val - d, by
            have := i.isLt
            omega⟩)) : ((Unit ⊕ Fin n) ⊕ Fin (d + S))) =
          Sum.map (peelVertexEquiv n) id
            (Sum.inl (a (Fin.natAdd d ⟨i.val - d, by
              have := i.isLt
              omega⟩)))
        rw [ha_high]
        show Sum.inl (Sum.inr (rest ⟨i.val - d, _⟩)) =
          Sum.inl (peelVertexEquiv n (rest ⟨i.val - d, _⟩).succ)
        rw [peelVertexEquiv_succ]
    · rcases Nat.lt_or_ge i.val d with hi | hi
      · rw [show i = Fin.castAdd S ⟨i.val, hi⟩ from Fin.ext rfl]
        erw [peelFlagEquiv_inr_low d S ⟨i.val, hi⟩]
        show Sum.inr (finCongr
          (by omega : (0 + 0) + (d + S) = d + S)
          (interleaveEquiv 0 d 0 S
            (Sum.inl (finCongr (by omega : d = 0 + d)
              ⟨i.val, hi⟩)))) =
          Sum.inr (Fin.castAdd S ⟨i.val, hi⟩)
        refine congrArg Sum.inr (Fin.ext ?_)
        rw [show (finCongr (by omega : d = 0 + d)
            (⟨i.val, hi⟩ : Fin d) : Fin (0 + d)) =
          Fin.natAdd 0 ⟨i.val, hi⟩ from Fin.ext (by
            show i.val = 0 + i.val
            omega),
          interleaveEquiv_inl_high]
        show (0 + 0) + i.val = i.val
        omega
      · rw [show i = Fin.natAdd d ⟨i.val - d, by
            have := i.isLt
            omega⟩ from Fin.ext (by
            show i.val = d + (i.val - d)
            omega)]
        erw [peelFlagEquiv_inr_high d S]
        show Sum.inr (finCongr
          (by omega : (0 + 0) + (d + S) = d + S)
          (interleaveEquiv 0 d 0 S
            (Sum.inr (finCongr (by omega : S = 0 + S)
              ⟨i.val - d, by have := i.isLt; omega⟩)))) =
          Sum.inr (Fin.natAdd d ⟨i.val - d, by
            have := i.isLt
            omega⟩)
        refine congrArg Sum.inr (Fin.ext ?_)
        rw [show (finCongr (by omega : S = 0 + S)
            (⟨i.val - d, by have := i.isLt; omega⟩ : Fin S) :
            Fin (0 + S)) =
          Fin.natAdd 0 ⟨i.val - d, by
            have := i.isLt
            omega⟩ from Fin.ext (by
            show i.val - d = 0 + (i.val - d)
            omega),
          interleaveEquiv_inr_high]
        show (0 + 0) + (d + (i.val - d)) = d + (i.val - d)
        omega
  -- ═══════ PAIRING ═══════
  -- The peel does not move any edge, so both sides read the same
  -- partner.
  pairing_comm := fun g => by
    rcases g with i | i
    · rcases Nat.lt_or_ge i.val d with hi | hi
      · rw [show i = Fin.castAdd S ⟨i.val, hi⟩ from Fin.ext rfl,
          show (multiStar a c).pairing
            (Sum.inl (Fin.castAdd S ⟨i.val, hi⟩)) =
          Sum.inr (Fin.castAdd S ⟨i.val, hi⟩) from rfl]
        erw [peelFlagEquiv_inr_low d S ⟨i.val, hi⟩,
          peelFlagEquiv_inl_low d S ⟨i.val, hi⟩]
        rfl
      · rw [show i = Fin.natAdd d ⟨i.val - d, by
            have := i.isLt
            omega⟩ from Fin.ext (by
            show i.val = d + (i.val - d)
            omega),
          show (multiStar a c).pairing
            (Sum.inl (Fin.natAdd d ⟨i.val - d, by
              have := i.isLt
              omega⟩)) =
          Sum.inr (Fin.natAdd d ⟨i.val - d, by
            have := i.isLt
            omega⟩) from rfl]
        erw [peelFlagEquiv_inr_high d S,
          peelFlagEquiv_inl_high d S]
        rfl
    · rcases Nat.lt_or_ge i.val d with hi | hi
      · rw [show i = Fin.castAdd S ⟨i.val, hi⟩ from Fin.ext rfl,
          show (multiStar a c).pairing
            (Sum.inr (Fin.castAdd S ⟨i.val, hi⟩)) =
          Sum.inl (Fin.castAdd S ⟨i.val, hi⟩) from rfl]
        erw [peelFlagEquiv_inl_low d S ⟨i.val, hi⟩,
          peelFlagEquiv_inr_low d S ⟨i.val, hi⟩]
        rfl
      · rw [show i = Fin.natAdd d ⟨i.val - d, by
            have := i.isLt
            omega⟩ from Fin.ext (by
            show i.val = d + (i.val - d)
            omega),
          show (multiStar a c).pairing
            (Sum.inr (Fin.natAdd d ⟨i.val - d, by
              have := i.isLt
              omega⟩)) =
          Sum.inl (Fin.natAdd d ⟨i.val - d, by
            have := i.isLt
            omega⟩) from rfl]
        erw [peelFlagEquiv_inl_high d S,
          peelFlagEquiv_inr_high d S]
        rfl
  circles_eq := by
    show c = 0 + c
    omega

/-- Circles migrate out of the second tensor factor. -/
noncomputable def tensorAddCirclesRight {s t u v : ℕ}
    (A : Fragment (Fin (s + t))) (B : Fragment (Fin (u + v)))
    (c : ℕ) :
    (tensorFragment A (addCircles B c)).Equiv
      (addCircles (tensorFragment A B) c) where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm := fun g => by
    rcases g with g | g
    · show ((A.attach g).map Sum.inl Sum.inl).map id _ =
        (((A.attach g).map Sum.inl Sum.inl).map id _).map
          (_root_.Equiv.refl _) id
      rcases A.attach g with x | x <;> rfl
    · show ((B.attach g).map Sum.inr Sum.inr).map id _ =
        (((B.attach g).map Sum.inr Sum.inr).map id _).map
          (_root_.Equiv.refl _) id
      rcases B.attach g with x | x <;> rfl
  pairing_comm := fun g => by
    rcases g with g | g <;> rfl
  circles_eq := by
    show A.circles + (B.circles + c) =
      (A.circles + B.circles) + c
    omega

/-- **The block factorization**: a block-sorted multi-star is the
iterated tensor of vertex stars with the circles split off. -/
noncomputable def multiStarBlocks :
    ∀ (ds : List ℕ) (c : ℕ),
      (multiStar (blockAssign ds) c).Equiv
        (addCircles (starTensor ds) c)
  | [], c => multiStarNil c
  | d :: ds, c => by
    refine (multiStarPeel d ds.sum c (blockAssign ds)
      (blockAssign (d :: ds))
      (fun i => dif_pos i.isLt)
      (fun j => by
        have h1 : ¬ ((Fin.natAdd d j :
            Fin (d + ds.sum)).val < d) := by
          show ¬ (d + j.val < d)
          omega
        refine (dif_neg h1).trans ?_
        refine congrArg Fin.succ
          (congrArg (blockAssign ds) (Fin.ext ?_))
        show d + j.val - d = j.val
        omega)).trans ?_
    refine (Fragment.Equiv.relabelCongr
      (tensorFragmentCongr (Fragment.Equiv.refl _)
        (Fragment.Equiv.relabelCongr
          (multiStarBlocks ds c) _)) _).trans ?_
    show ((tensorFragment
        ((vertexStar d).relabel (finCongr
          (by omega : d = 0 + d)))
        (addCircles ((starTensor ds).relabel (finCongr
          (by omega : ds.sum = 0 + ds.sum))) c)).relabel
        (finCongr (by omega :
          (0 + 0) + (d + ds.sum) = d + ds.sum))).Equiv
      (addCircles (starTensor (d :: ds)) c)
    exact Fragment.Equiv.relabelCongr
      (tensorAddCirclesRight
        ((vertexStar d).relabel (finCongr
          (by omega : d = 0 + d)))
        ((starTensor ds).relabel (finCongr
          (by omega : ds.sum = 0 + ds.sum))) c) _

end RS
