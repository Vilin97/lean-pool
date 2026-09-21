/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.MonoidalInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.PartialCloseCompose
import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseUnion

/-!
# The block splice

Partially closing an `(n, n)`-fragment against the block rotation on
`K + 2n` strands splices it into the block rotation on `K + n`
strands: the fragment is absorbed and the rotation drops one block.
This is the geometric step behind the block cycle trace, and the
reason a diagonal power of `g` closes to a power of its trace.

The proof identifies the two fragments flag by flag.  It runs through
the block rotation and its outer boundary permutation, the value
tables of the label maps they induce, and two bridges: the reshuffled
rotation as through-strands tensored with `K` cups, and the same
after the outer relabel is collapsed.
-/

namespace RS

open CategoryTheory

/-! ### The block rotation -/

/-- The block rotation: cyclically permute the first `a` and last `b`
elements of `Fin (a + b)`.  Value: `x < a ↦ b + x`, `x ≥ a ↦ x - a`. -/
noncomputable def blockRot (a b : ℕ) : Equiv.Perm (Fin (a + b)) :=
  (transposeEquiv a b).trans (finCongr (by omega : b + a = a + b))

/-- Forward value of `blockRot`. -/
theorem blockRot_val (a b : ℕ) (x : Fin (a + b)) :
    (blockRot a b x).val =
      if x.val < a then b + x.val else x.val - a := by
  unfold blockRot
  rw [_root_.Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  have hb := x.isLt
  by_cases h : x.val < a
  · conv_lhs =>
      rw [show x = (⟨x.val, hb⟩ : Fin (a + b)) from Fin.ext rfl]
    rw [transposeEquiv_low a b x.val h hb (by omega)]
    simp only [if_pos h]
  · conv_lhs =>
      rw [show x = (⟨a + (x.val - a), by omega⟩ : Fin (a + b)) from
        Fin.ext (by show x.val = a + (x.val - a); omega)]
    rw [transposeEquiv_high a b (x.val - a) (by omega) (by omega) (by omega)]
    simp only [if_neg h]

/-- Inverse value of `blockRot`. -/
private theorem blockRot_symm_val (a b : ℕ) (x : Fin (a + b)) :
    ((blockRot a b).symm x).val =
      if x.val < b then a + x.val else x.val - b := by
  set y := (blockRot a b).symm x
  have hfwd := blockRot_val a b y
  rw [Equiv.apply_symm_apply] at hfwd
  by_cases hya : y.val < a
  · rw [if_pos hya] at hfwd; rw [if_neg (by omega)]; omega
  · rw [if_neg hya] at hfwd; rw [if_pos (by omega)]; omega

/-! ### The outer boundary permutation -/

/-- The outer boundary permutation for the block splice:
`w < n ↦ (K+K+n)+w`, `w ≥ n ↦ w-n`.  At `K = 0` this is the
reversal `(finRotate (2n)).symm`. -/
private def blockOuterPerm (K n : ℕ) :
    Equiv.Perm (Fin ((K + n) + (K + n))) where
  toFun w :=
    if h : w.val < n then ⟨K + K + n + w.val, by have := w.isLt; omega⟩
    else ⟨w.val - n, by have := w.isLt; omega⟩
  invFun w :=
    if h : w.val < K + K + n then ⟨w.val + n, by omega⟩
    else ⟨w.val - (K + K + n), by have := w.isLt; omega⟩
  left_inv w := by
    dsimp only
    by_cases h : w.val < n
    · simp only [dif_pos h, Fin.val_mk]
      rw [dif_neg (show ¬ K + K + n + w.val < K + K + n by omega)]
      refine Fin.ext ?_; simp only []; omega
    · simp only [dif_neg h, Fin.val_mk]
      rw [dif_pos (show w.val - n < K + K + n by have := w.isLt; omega)]
      refine Fin.ext ?_; simp only []; omega
  right_inv w := by
    dsimp only
    by_cases h : w.val < K + K + n
    · simp only [dif_pos h, Fin.val_mk]
      rw [dif_neg (show ¬ w.val + n < n by omega)]
      refine Fin.ext ?_; simp only []; omega
    · simp only [dif_neg h, Fin.val_mk]
      rw [dif_pos (show w.val - (K + K + n) < n by have := w.isLt; omega)]
      refine Fin.ext ?_; simp only []; omega

/-- Value table of `blockOuterPerm`. -/
private theorem blockOuterPerm_val (K n : ℕ)
    (w : Fin ((K + n) + (K + n))) :
    (blockOuterPerm K n w).val =
      if w.val < n then K + K + n + w.val else w.val - n := by
  simp only [blockOuterPerm, Equiv.coe_fn_mk]; split_ifs <;> rfl

/-! ### The label map of the reshuffled rotation -/

/-- The value table of the reshuffled block rotation's label map, at
tensor arities `(s, t, u, v) = (K+n, K+n, n, n)`. -/
private theorem block_label_val (K n : ℕ)
    (ℓ : Fin ((K + n + n) + (K + n + n))) :
    (((permHighEquiv (blockRot (K + n) n).symm).trans
        (pcReshuffle (K + n) (K + n) n n)) ℓ).val =
      if ℓ.val < K + n then (n + n) + ℓ.val
      else if ℓ.val < K + n + n then ℓ.val - (K + n)
      else if ℓ.val < (K + n + n) + n then n + (ℓ.val - (K + n + n))
      else ℓ.val := by
  rw [_root_.Equiv.trans_apply]
  by_cases hlow : ℓ.val < K + n + n
  · -- Low half: permHighEquiv fixes
    have hfix : permHighEquiv (blockRot (K + n) n).symm ℓ = ℓ := by
      unfold permHighEquiv; exact dif_pos hlow
    rw [hfix]
    by_cases h1 : ℓ.val < K + n
    · -- x-low block
      have hform : ℓ = Fin.castAdd ((K + n) + n)
          (Fin.castAdd n (⟨ℓ.val, h1⟩ : Fin (K + n))) :=
        Fin.ext rfl
      rw [hform, pcReshuffle_xlow]
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      split_ifs <;> omega
    · -- z-low block
      have hform : ℓ = Fin.castAdd ((K + n) + n)
          (Fin.natAdd (K + n) (⟨ℓ.val - (K + n),
            by omega⟩ : Fin n)) :=
        Fin.ext (by simp [Fin.val_natAdd]; omega)
      rw [hform, pcReshuffle_zlow]
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      split_ifs <;> omega
  · -- High half: permHighEquiv applies π
    have hbound := ℓ.isLt
    have hk : ℓ.val - (K + n + n) < K + n + n := by omega
    have hrot : ((blockRot (K + n) n).symm
        (⟨ℓ.val - (K + n + n), hk⟩ : Fin (K + n + n))).val =
        if ℓ.val - (K + n + n) < n then (K + n) + (ℓ.val - (K + n + n))
        else ℓ.val - (K + n + n) - n :=
      blockRot_symm_val (K + n) n _
    have hstep : permHighEquiv (blockRot (K + n) n).symm ℓ =
        ⟨(K + n + n) + ((blockRot (K + n) n).symm
          (⟨ℓ.val - (K + n + n), hk⟩ : Fin (K + n + n))).val,
        by have := ((blockRot (K + n) n).symm
          (⟨ℓ.val - (K + n + n), hk⟩ : Fin (K + n + n))).isLt
           omega⟩ := by
      unfold permHighEquiv; exact dif_neg (by omega)
    rw [hstep]
    by_cases hk0 : ℓ.val - (K + n + n) < n
    · -- z-high block (k < n case)
      rw [if_pos hk0] at hrot
      have hform : (⟨(K + n + n) + ((blockRot (K + n) n).symm
            (⟨ℓ.val - (K + n + n), hk⟩ : Fin (K + n + n))).val,
            by have := ((blockRot (K + n) n).symm
              (⟨ℓ.val - (K + n + n), hk⟩ : Fin (K + n + n))).isLt
               omega⟩ : Fin ((K + n + n) + (K + n + n))) =
          Fin.natAdd ((K + n) + n)
            (Fin.natAdd (K + n) (⟨ℓ.val - (K + n + n),
              by omega⟩ : Fin n)) :=
        Fin.ext (by simp only [Fin.val_natAdd]; omega)
      rw [hform, pcReshuffle_zhigh]
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      split_ifs <;> omega
    · -- x-high block (k >= n case)
      rw [if_neg hk0] at hrot
      have hform : (⟨(K + n + n) + ((blockRot (K + n) n).symm
            (⟨ℓ.val - (K + n + n), hk⟩ : Fin (K + n + n))).val,
            by have := ((blockRot (K + n) n).symm
              (⟨ℓ.val - (K + n + n), hk⟩ : Fin (K + n + n))).isLt
               omega⟩ : Fin ((K + n + n) + (K + n + n))) =
          Fin.natAdd ((K + n) + n)
            (Fin.castAdd n (⟨ℓ.val - (K + n + n) - n,
              by omega⟩ : Fin (K + n))) :=
        Fin.ext (by simp only [Fin.val_natAdd, Fin.val_castAdd]; omega)
      rw [hform, pcReshuffle_xhigh]
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      split_ifs <;> omega

/-! ### The splice flag identification -/

/-- The flag identification of the block splice: wires 0..n-1 and
K+n..K+2n-1 are the 2n through-strands, wires n..K+n-1 are the K cups. -/
private def blockSpliceFlagEquiv (K n : ℕ) :
    (Fin (K + n + n) × Bool) ≃
      ((Fin (n + n) × Bool) ⊕ (Fin K × Bool)) where
  toFun p :=
    if hlo : p.1.val < n then
      Sum.inl (⟨n + p.1.val, by omega⟩, !p.2)
    else if hhi : p.1.val ≥ K + n then
      Sum.inl (⟨p.1.val - (K + n), by have := p.1.isLt; omega⟩, p.2)
    else
      Sum.inr (⟨p.1.val - n, by omega⟩, p.2)
  invFun := Sum.elim
    (fun q : Fin (n + n) × Bool =>
      if h : q.1.val < n then
        ((⟨K + n + q.1.val, by have := q.1.isLt; omega⟩ : Fin (K + n + n)), q.2)
      else
        ((⟨q.1.val - n, by have := q.1.isLt; omega⟩ : Fin (K + n + n)), !q.2))
    (fun q : Fin K × Bool =>
      (⟨q.1.val + n, by have := q.1.isLt; omega⟩, q.2))
  left_inv := by
    rintro ⟨i, b⟩; dsimp only
    by_cases hlo : i.val < n
    · rw [dif_pos hlo, Sum.elim_inl]
      rw [dif_neg (show ¬ (⟨n + i.val, by omega⟩ : Fin (n + n)).val < n by
        simp only []; omega)]
      exact Prod.ext (Fin.ext (by simp only []; omega)) (Bool.not_not b)
    · by_cases hhi : i.val ≥ K + n
      · rw [dif_neg hlo, dif_pos hhi, Sum.elim_inl]
        rw [dif_pos (show (⟨i.val - (K + n), by have := i.isLt; omega⟩ :
          Fin (n + n)).val < n by simp only []; have := i.isLt; omega)]
        exact Prod.ext (Fin.ext (by simp only []; omega)) rfl
      · rw [dif_neg hlo, dif_neg (show ¬ i.val ≥ K + n by omega), Sum.elim_inr]
        exact Prod.ext (Fin.ext (by simp only []; omega)) rfl
  right_inv := by
    rintro (⟨j, c⟩ | ⟨k, c⟩)
    · rw [Sum.elim_inl]; dsimp only
      by_cases hj : j.val < n
      · rw [dif_pos hj, dif_neg (show ¬ (⟨K + n + j.val,
            by have := j.isLt; omega⟩ : Fin (K + n + n)).val < n by
          simp only []; omega),
          dif_pos (show (⟨K + n + j.val,
            by have := j.isLt; omega⟩ : Fin (K + n + n)).val ≥ K + n by
          simp only []; omega)]
        exact congrArg Sum.inl
          (Prod.ext (Fin.ext (by simp only []; omega)) rfl)
      · rw [dif_neg hj, dif_pos (show (⟨j.val - n,
            by have := j.isLt; omega⟩ : Fin (K + n + n)).val < n by
          simp only []; have := j.isLt; omega)]
        exact congrArg Sum.inl
          (Prod.ext (Fin.ext (by simp only []; omega))
            (Bool.not_not c))
    · rw [Sum.elim_inr]; dsimp only
      rw [dif_neg (show ¬ (⟨k.val + n, by have := k.isLt; omega⟩ :
            Fin (K + n + n)).val < n by simp only []; omega),
        dif_neg (show ¬ (⟨k.val + n, by have := k.isLt; omega⟩ :
            Fin (K + n + n)).val ≥ K + n by
          simp only []; have := k.isLt; omega)]
      exact congrArg Sum.inr (Prod.ext (Fin.ext (by simp only []; omega)) rfl)

/-- The splice flag map anticommutes with strand flips. -/
private theorem blockSpliceFlagEquiv_pairing (K n : ℕ)
    (w : Fin (K + n + n)) (b : Bool) :
    blockSpliceFlagEquiv K n (w, !b) =
      Sum.map (fun q : Fin (n + n) × Bool => (q.1, !q.2))
        (fun q : Fin K × Bool => (q.1, !q.2))
        (blockSpliceFlagEquiv K n (w, b)) := by
  simp only [blockSpliceFlagEquiv, Equiv.coe_fn_mk]
  by_cases hlo : w.val < n
  · rw [dif_pos hlo, dif_pos hlo]; rfl
  · by_cases hhi : w.val ≥ K + n
    · rw [dif_neg hlo, dif_pos hhi, dif_neg hlo, dif_pos hhi]; rfl
    · rw [dif_neg hlo, dif_neg (by omega), dif_neg hlo, dif_neg (by omega)]; rfl

/-! ### The collapsed outer relabel and the rotated transpose -/

/-- Value of the collapsed outer relabel of the splice. -/
private theorem block_bigE_val (K n : ℕ)
    (x : Fin (0 + ((n + n) + (K + K)))) :
    ((((finCongr (by omega :
          0 + ((n + n) + (K + K)) = 0 + ((K + n) + (K + n)))).trans
        (outPermEquiv 0
          (blockOuterPerm K n))).trans
        (finCongr (by omega :
          0 + ((K + n) + (K + n)) = (K + n) + (K + n)))) x).val =
      if x.val < n then K + K + n + x.val else x.val - n := by
  rw [_root_.Equiv.trans_apply, _root_.Equiv.trans_apply]
  have hb := x.isLt
  have hform : ((finCongr (by omega :
      0 + ((n + n) + (K + K)) = 0 + ((K + n) + (K + n)))) x) =
      Fin.natAdd 0 (⟨x.val, by omega⟩ :
        Fin ((K + n) + (K + n))) :=
    Fin.ext (by simp only [finCongr_apply, Fin.val_cast,
      Fin.val_natAdd]; omega)
  rw [hform, outPermEquiv_high]
  simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd]
  rw [blockOuterPerm_val]
  simp only [Fin.val_mk]
  split_ifs <;> omega

/-- Value of the rotated-transpose relabel on the right side. -/
private theorem block_ER_val (K n : ℕ)
    (x : Fin ((K + n) + (K + n))) :
    (((transposeEquiv (K + n) (K + n)).trans
        (inPermEquiv
          ((blockRot K n).symm).symm (K + n))) x).val =
      if x.val < K + n then (K + n) + x.val
      else if x.val - (K + n) < K then n + (x.val - (K + n))
      else x.val - (K + n) - K := by
  rw [_root_.Equiv.trans_apply]
  have hb := x.isLt
  by_cases hlow : x.val < K + n
  · rw [show x = (⟨x.val, hb⟩ : Fin ((K + n) + (K + n))) from
      Fin.ext rfl]
    rw [transposeEquiv_low (K + n) (K + n) x.val hlow hb (by omega)]
    rw [show (⟨(K + n) + x.val, by omega⟩ :
        Fin ((K + n) + (K + n))) =
      Fin.natAdd (K + n) (⟨x.val, hlow⟩ : Fin (K + n)) from
      Fin.ext rfl]
    rw [inPermEquiv_high]
    simp only [Fin.val_natAdd]
    rw [if_pos hlow]
  · rw [show x = (⟨(K + n) + (x.val - (K + n)), by omega⟩ :
      Fin ((K + n) + (K + n))) from Fin.ext
        (by show x.val = (K + n) + (x.val - (K + n)); omega)]
    rw [transposeEquiv_high (K + n) (K + n) (x.val - (K + n))
      (by omega) (by omega) (by omega)]
    rw [show (⟨x.val - (K + n), by omega⟩ :
        Fin ((K + n) + (K + n))) =
      Fin.castAdd (K + n) (⟨x.val - (K + n), by omega⟩ :
        Fin (K + n)) from Fin.ext rfl]
    rw [inPermEquiv_low]
    -- Now we need the value of ((blockRot K n).symm).symm at x.val-(K+n)
    rw [_root_.Equiv.symm_symm]
    have hσ : (blockRot K n
        (⟨x.val - (K + n), by omega⟩ : Fin (K + n))).val =
        if x.val - (K + n) < K then n + (x.val - (K + n))
        else x.val - (K + n) - K := by
      rw [blockRot_val]
    simp only [Fin.val_castAdd, hσ]
    split_ifs <;> omega

/-! ### Collapsing a value-identity recast -/

/-- Collapse a value-identity recast. -/
private noncomputable def relabel_defeq_collapse {a : ℕ}
    (F : Fragment (Fin a)) (p : a = a) :
    (F.relabel (finCongr p)).Equiv F :=
  (Fragment.Equiv.relabelEq F
      (_root_.Equiv.ext (fun _ => Fin.ext rfl))).trans
    (Fragment.Equiv.relabelRefl F)

/-- Composition against an outer-boundary recast. -/
private noncomputable def compose_relabel_castOut
    {s t u u' : ℕ} (h : u = u')
    (F : Fragment (Fin (s + t))) (G : Fragment (Fin (t + u))) :
    (F.compose (G.relabel
        (finCongr (by rw [h] : t + u = t + u')))).Equiv
      ((F.compose G).relabel
        (finCongr (by rw [h] : s + u = s + u'))) := by
  cases h
  exact (Fragment.composeCongr (Fragment.Equiv.refl F)
      (relabel_defeq_collapse G _)).trans
    (relabel_defeq_collapse (F.compose G) _).symm

/-! ### The bridge: the rotation as through-strands and cups -/

/-- **The bridge**: the reshuffled big block rotation, as a
relabelled bundle, is the through-strands tensored with K cups,
up to the outer boundary permutation. -/
private noncomputable def block_bridge (K n : ℕ) :
    ((strandBundle (K + n + n)).relabel
        ((permHighEquiv (blockRot (K + n) n).symm).trans
          (pcReshuffle (K + n) (K + n) n n))).Equiv
      (((tensorFragment (s := n + n) (t := n + n) (u := 0) (v := K + K)
            (strandBundle (n + n))
            ((strandBundle K).relabel
              (finCongr (by omega : K + K = 0 + (K + K))))).relabel
          (finCongr (by omega :
            (n + n + 0) + (n + n + (K + K)) =
              (n + n) + ((K + n) + (K + n))))).relabel
        (outPermEquiv (n + n)
          (blockOuterPerm K n))) where
  flagEquiv := blockSpliceFlagEquiv K n
  vertexEquiv :=
    haveI : IsEmpty ((Empty ⊕ Empty : Type)) :=
      ⟨fun x => x.elim Empty.elim Empty.elim⟩
    show (Empty : Type) ≃ (Empty ⊕ Empty : Type) from
      _root_.Equiv.equivOfIsEmpty _ _
  attach_comm := fun f => by
    obtain ⟨w, b⟩ := f
    show (((tensorFragment (strandBundle (n + n))
              ((strandBundle K).relabel
                (finCongr (by omega : K + K = 0 + (K + K))))).relabel
            (finCongr (by omega :
              (n + n + 0) + (n + n + (K + K)) =
                (n + n) + ((K + n) + (K + n))))).relabel
          (outPermEquiv (n + n) (blockOuterPerm K n))).attach
        (blockSpliceFlagEquiv K n (w, b)) =
      Sum.map _ id
        (((strandBundle (K + n + n)).relabel
            ((permHighEquiv (blockRot (K + n) n).symm).trans
              (pcReshuffle (K + n) (K + n) n n))).attach (w, b))
    by_cases hlo : w.val < n
    -- ═══════ THE THROUGH STRANDS ═══════
    -- Wires below `n` and wires from `K+n` up are the two halves of
    -- the through-strand bundle; each end maps across unchanged.
    · -- Through-strand low block (wire w < n)
      rw [show blockSpliceFlagEquiv K n (w, b) =
          Sum.inl (⟨n + w.val, by omega⟩, !b) from by
        simp only [blockSpliceFlagEquiv, Equiv.coe_fn_mk]
        exact dif_pos hlo]
      cases b
      · -- in-end (b = false): wire w in-label -> through-strand n+w, out end
        dsimp only [tensorFragment, Fragment.relabel,
          Fragment.disjUnion, strandBundle, Sum.elim_inl,
          Sum.elim_inr, Sum.map_inr, Sum.map_inl,
          Bool.not_false]
        refine congrArg Sum.inr (Fin.ext ?_)
        simp only [Bool.not_false, Bool.not_true, reduceIte,
          Bool.false_eq_true, if_false, if_true, id_eq]
        rw [show (⟨(n + n) + (n + w.val), by omega⟩ :
            Fin ((n + n) + (n + n))) =
          Fin.natAdd (n + n) (⟨n + w.val, by omega⟩ : Fin (n + n)) from
          Fin.ext rfl]
        rw [interleaveEquiv_inl_high]
        rw [show ((finCongr (by omega :
              (n + n + 0) + (n + n + (K + K)) =
                (n + n) + ((K + n) + (K + n))))
            (Fin.natAdd (n + n + 0)
              (Fin.castAdd (K + K) (⟨n + w.val, by omega⟩ : Fin (n + n))))) =
          Fin.natAdd (n + n)
            (⟨n + w.val, by omega⟩ : Fin ((K + n) + (K + n))) from
          Fin.ext (by simp)]
        rw [outPermEquiv_high]
        rw [block_label_val]
        simp only [Fin.val_natAdd, Fin.val_castAdd]
        rw [blockOuterPerm_val]
        simp only [Fin.val_mk]
        split_ifs <;> omega
      · -- out-end (b = true): wire w out-label -> through-strand n+w, in end
        dsimp only [tensorFragment, Fragment.relabel,
          Fragment.disjUnion, strandBundle, Sum.elim_inl,
          Sum.elim_inr, Sum.map_inr, Sum.map_inl,
          Bool.not_true]
        refine congrArg Sum.inr (Fin.ext ?_)
        simp only [Bool.not_false, Bool.not_true, reduceIte,
          Bool.false_eq_true, if_false, if_true, id_eq]
        rw [show (⟨(n + w.val), by omega⟩ : Fin ((n + n) + (n + n))) =
          Fin.castAdd (n + n) (⟨n + w.val, by omega⟩ : Fin (n + n)) from
          Fin.ext rfl]
        rw [interleaveEquiv_inl_low]
        rw [show ((finCongr (by omega :
              (n + n + 0) + (n + n + (K + K)) =
                (n + n) + ((K + n) + (K + n))))
            (Fin.castAdd (n + n + (K + K))
              (Fin.castAdd 0 (⟨n + w.val, by omega⟩ : Fin (n + n))))) =
          Fin.castAdd ((K + n) + (K + n))
            (⟨n + w.val, by omega⟩ : Fin (n + n)) from
          Fin.ext (by simp)]
        rw [outPermEquiv_low]
        rw [block_label_val]
        simp only [Fin.val_castAdd]
        split_ifs <;> omega
    · by_cases hhi : w.val ≥ K + n
      · -- Through-strand high block (wire w >= K+n)
        rw [show blockSpliceFlagEquiv K n (w, b) =
            Sum.inl (⟨w.val - (K + n), by have := w.isLt; omega⟩, b) from by
          simp only [blockSpliceFlagEquiv, Equiv.coe_fn_mk]
          rw [dif_neg hlo, dif_pos hhi]]
        cases b
        · -- in-end: wire w in-label -> through-strand w-(K+n), in end
          dsimp only [tensorFragment, Fragment.relabel,
            Fragment.disjUnion, strandBundle, Sum.elim_inl,
            Sum.elim_inr, Sum.map_inr, Sum.map_inl]
          refine congrArg Sum.inr (Fin.ext ?_)
          simp only [Bool.not_false, Bool.not_true, reduceIte,
            Bool.false_eq_true, if_false, if_true, id_eq]
          rw [show (⟨w.val - (K + n), by have := w.isLt; omega⟩ :
              Fin ((n + n) + (n + n))) =
            Fin.castAdd (n + n)
              (⟨w.val - (K + n), by have := w.isLt; omega⟩ :
                Fin (n + n)) from Fin.ext rfl]
          rw [interleaveEquiv_inl_low]
          rw [show ((finCongr (by omega :
                (n + n + 0) + (n + n + (K + K)) =
                  (n + n) + ((K + n) + (K + n))))
              (Fin.castAdd (n + n + (K + K))
                (Fin.castAdd 0 (⟨w.val - (K + n),
                  by have := w.isLt; omega⟩ : Fin (n + n))))) =
            Fin.castAdd ((K + n) + (K + n))
              (⟨w.val - (K + n),
                by have := w.isLt; omega⟩ : Fin (n + n)) from
            Fin.ext (by simp)]
          rw [outPermEquiv_low]
          rw [block_label_val]
          simp only [Fin.val_castAdd]
          split_ifs <;> omega
        · -- out-end: wire w out-label -> through-strand w-(K+n), out end
          dsimp only [tensorFragment, Fragment.relabel,
            Fragment.disjUnion, strandBundle, Sum.elim_inl,
            Sum.elim_inr, Sum.map_inr, Sum.map_inl]
          refine congrArg Sum.inr (Fin.ext ?_)
          simp only [Bool.not_false, Bool.not_true, reduceIte,
            Bool.false_eq_true, if_false, if_true, id_eq]
          rw [show (⟨(n + n) + (w.val - (K + n)),
              by have := w.isLt; omega⟩ :
              Fin ((n + n) + (n + n))) =
            Fin.natAdd (n + n)
              (⟨w.val - (K + n),
                by have := w.isLt; omega⟩ : Fin (n + n)) from
            Fin.ext rfl]
          rw [interleaveEquiv_inl_high]
          rw [show ((finCongr (by omega :
                (n + n + 0) + (n + n + (K + K)) =
                  (n + n) + ((K + n) + (K + n))))
              (Fin.natAdd (n + n + 0)
                (Fin.castAdd (K + K)
                  (⟨w.val - (K + n),
                    by have := w.isLt; omega⟩ : Fin (n + n))))) =
            Fin.natAdd (n + n)
              (⟨w.val - (K + n),
                by have := w.isLt; omega⟩ :
                Fin ((K + n) + (K + n))) from
            Fin.ext (by simp)]
          rw [outPermEquiv_high]
          rw [block_label_val]
          simp only [Fin.val_natAdd, Fin.val_castAdd]
          rw [blockOuterPerm_val]
          simp only [Fin.val_mk]
          split_ifs <;> omega
      -- ═══════ THE CUPS ═══════
      -- The remaining wires are the `K` cups, indexed by `w - n`.
      · -- Pass wire: cup k := w - n
        have hpass : n ≤ w.val ∧ w.val < K + n := by omega
        rw [show blockSpliceFlagEquiv K n (w, b) =
            Sum.inr (⟨w.val - n, by omega⟩, b) from by
          simp only [blockSpliceFlagEquiv, Equiv.coe_fn_mk]
          rw [dif_neg hlo, dif_neg (by omega)]]
        cases b
        · -- in-end: pass wire -> cup, low end
          dsimp only [tensorFragment, Fragment.relabel,
            Fragment.disjUnion, strandBundle, Sum.elim_inl,
            Sum.elim_inr, Sum.map_inr, Sum.map_inl]
          refine congrArg Sum.inr (Fin.ext ?_)
          simp only [Bool.not_false, Bool.not_true, reduceIte,
            Bool.false_eq_true, if_false, if_true, id_eq]
          rw [show ((finCongr (by omega :
                K + K = 0 + (K + K)))
              (⟨w.val - n, by omega⟩ : Fin (K + K))) =
            Fin.natAdd 0 (⟨w.val - n, by omega⟩ :
              Fin (K + K)) from
            Fin.ext (by simp)]
          rw [interleaveEquiv_inr_high]
          rw [show ((finCongr (by omega :
                (n + n + 0) + (n + n + (K + K)) =
                  (n + n) + ((K + n) + (K + n))))
              (Fin.natAdd (n + n + 0)
                (Fin.natAdd (n + n) (⟨w.val - n,
                  by omega⟩ : Fin (K + K))))) =
            Fin.natAdd (n + n)
              (⟨(n + n) + (w.val - n),
                by omega⟩ :
                Fin ((K + n) + (K + n))) from
            Fin.ext (by simp)]
          rw [outPermEquiv_high]
          rw [block_label_val]
          simp only [Fin.val_natAdd, Fin.val_castAdd]
          rw [blockOuterPerm_val]
          simp only [Fin.val_mk]
          split_ifs <;> omega
        · -- out-end: pass wire -> cup, high end
          dsimp only [tensorFragment, Fragment.relabel,
            Fragment.disjUnion, strandBundle, Sum.elim_inl,
            Sum.elim_inr, Sum.map_inr, Sum.map_inl]
          refine congrArg Sum.inr (Fin.ext ?_)
          simp only [Bool.not_false, Bool.not_true, reduceIte,
            Bool.false_eq_true, if_false, if_true, id_eq]
          rw [show ((finCongr (by omega :
                K + K = 0 + (K + K)))
              (⟨K + (w.val - n), by omega⟩ : Fin (K + K))) =
            Fin.natAdd 0 (⟨K + (w.val - n), by omega⟩ :
              Fin (K + K)) from
            Fin.ext (by simp)]
          rw [interleaveEquiv_inr_high]
          rw [show ((finCongr (by omega :
                (n + n + 0) + (n + n + (K + K)) =
                  (n + n) + ((K + n) + (K + n))))
              (Fin.natAdd (n + n + 0)
                (Fin.natAdd (n + n) (⟨K + (w.val - n),
                  by omega⟩ : Fin (K + K))))) =
            Fin.natAdd (n + n)
              (⟨(n + n) + (K + (w.val - n)),
                by omega⟩ :
                Fin ((K + n) + (K + n))) from
            Fin.ext (by simp)]
          rw [outPermEquiv_high]
          rw [block_label_val]
          simp only [Fin.val_natAdd, Fin.val_castAdd]
          rw [blockOuterPerm_val]
          simp only [Fin.val_mk]
          split_ifs <;> omega
  pairing_comm := fun f =>
    blockSpliceFlagEquiv_pairing K n f.1 f.2
  circles_eq := rfl

/-! ### The reshuffle decomposition -/

/-- The reshuffle decomposition: the reshuffled big block rotation
is the through-strands tensored with K cups, up to the outer
boundary permutation. -/
private noncomputable def block_reshuffle_decomp (K n : ℕ) :
    ((permFragment (blockRot (K + n) n).symm).relabel
        (pcReshuffle (K + n) (K + n) n n)).Equiv
      (((tensorFragment (s := n + n) (t := n + n) (u := 0) (v := K + K)
            (strandBundle (n + n))
            ((strandBundle K).relabel
              (finCongr (by omega : K + K = 0 + (K + K))))).relabel
          (finCongr (by omega :
            (n + n + 0) + (n + n + (K + K)) =
              (n + n) + ((K + n) + (K + n))))).relabel
        (outPermEquiv (n + n)
          (blockOuterPerm K n))) :=
  (Fragment.Equiv.relabelCongr
      (permFragmentRelabelBundle (blockRot (K + n) n).symm)
      (pcReshuffle (K + n) (K + n) n n)).trans
    ((Fragment.Equiv.relabelTrans (strandBundle (K + n + n))
        (permHighEquiv (blockRot (K + n) n).symm)
        (pcReshuffle (K + n) (K + n) n n)).trans
      (block_bridge K n))

/-! ### The final flag map and bridge -/

/-- The flag map of the final comparison: the G-flags cross
sides, the cups flip into through-strands. -/
private def blockFinalFlagEquiv (K n : ℕ)
    (𝔊 : Fragment (Fin (n + n))) :
    (𝔊.Flag ⊕ (Fin K × Bool)) ≃ ((Fin K × Bool) ⊕ 𝔊.Flag) where
  toFun := Sum.elim (fun g : 𝔊.Flag => Sum.inr g)
    (fun q : Fin K × Bool => Sum.inl (q.1, !q.2))
  invFun := Sum.elim (fun q : Fin K × Bool =>
      Sum.inr (q.1, !q.2))
    (fun g : 𝔊.Flag => Sum.inl g)
  left_inv := by
    rintro (g | ⟨k, c⟩)
    · rfl
    · rw [Sum.elim_inr, Sum.elim_inl, Bool.not_not]
  right_inv := by
    rintro (⟨k, c⟩ | g)
    · rw [Sum.elim_inl, Sum.elim_inr, Bool.not_not]
    · rfl

/-- The last comparison of the block splice: the leg-extended
tensor against the rotated through-tensor. -/
private noncomputable def block_splice_bridge (K n : ℕ)
    (𝔊 : Fragment (Fin (n + n))) :
    ((tensorFragment (s := 0) (t := n + n) (u := 0) (v := K + K)
        (𝔊.relabel
          (finCongr (by omega : n + n = 0 + (n + n))))
        ((strandBundle K).relabel
          (finCongr (by omega : K + K = 0 + (K + K))))).relabel
      (((finCongr (by omega :
          0 + ((n + n) + (K + K)) = 0 + ((K + n) + (K + n)))).trans
        (outPermEquiv 0
          (blockOuterPerm K n))).trans
        (finCongr (by omega :
          0 + ((K + n) + (K + n)) = (K + n) + (K + n))))).Equiv
      ((tensorFragment (strandBundle K) 𝔊).relabel
        ((transposeEquiv (K + n) (K + n)).trans
          (inPermEquiv
            ((blockRot K n).symm).symm (K + n)))) where
  flagEquiv := blockFinalFlagEquiv K n 𝔊
  vertexEquiv :=
    show (𝔊.Vertex ⊕ (Empty : Type)) ≃
        ((Empty : Type) ⊕ 𝔊.Vertex) from
      _root_.Equiv.sumComm _ _
  attach_comm := by
    rintro (g | ⟨k, c⟩)
    -- ═══════ THE FRAGMENT'S OWN FLAGS ═══════
    · -- a G-flag crosses sides
      show Sum.map id
          (⇑((transposeEquiv (K + n) (K + n)).trans
            (inPermEquiv
              ((blockRot K n).symm).symm (K + n))))
          (Sum.map id
            (⇑(interleaveEquiv K K n n))
            ((𝔊.attach g).map Sum.inr Sum.inr)) =
        Sum.map _ id
          (Sum.map id
            (⇑(((finCongr (by omega :
                0 + ((n + n) + (K + K)) =
                  0 + ((K + n) + (K + n)))).trans
              (outPermEquiv 0
                (blockOuterPerm K n))).trans
              (finCongr (by omega :
                0 + ((K + n) + (K + n)) =
                  (K + n) + (K + n)))))
            (Sum.map id
              (⇑(interleaveEquiv 0 (n + n) 0 (K + K)))
              (((𝔊.attach g).map id
                  (⇑(finCongr (by omega :
                    n + n = 0 + (n + n))))).map
                Sum.inl Sum.inl)))
      rcases 𝔊.attach g with v | ℓ
      · rfl
      · simp only [Sum.map_inr]
        refine congrArg Sum.inr (Fin.ext ?_)
        -- Both sides reduce to value computations
        by_cases hv : ℓ.val < n
        · -- ℓ is a low label of 𝔊
          rw [show ℓ = Fin.castAdd n
            (⟨ℓ.val, hv⟩ : Fin n) from Fin.ext
              (by simp only [Fin.val_castAdd])]
          rw [interleaveEquiv_inr_low]
          rw [show ((finCongr (by omega :
                n + n = 0 + (n + n)))
              (Fin.castAdd n (⟨ℓ.val, hv⟩ : Fin n))) =
            Fin.natAdd 0 (⟨ℓ.val, by omega⟩ : Fin (n + n)) from
            Fin.ext (by simp [Fin.val_natAdd])]
          rw [interleaveEquiv_inl_high]
          rw [show (Fin.natAdd (0 + 0)
              (Fin.castAdd (K + K) (⟨ℓ.val, by omega⟩ :
                Fin (n + n)))) =
            (⟨ℓ.val, by omega⟩ :
              Fin (0 + ((n + n) + (K + K)))) from
            Fin.ext (by simp [Fin.val_natAdd, Fin.val_castAdd])]
          simp only [id_eq]
          rw [block_ER_val, block_bigE_val]
          simp only [Fin.val_castAdd, Fin.val_natAdd]
          split_ifs <;> omega
        · -- ℓ is a high label of 𝔊
          rw [show ℓ = Fin.natAdd n
            (⟨ℓ.val - n, by have := ℓ.isLt; omega⟩ : Fin n) from
            Fin.ext (by simp only [Fin.val_natAdd]; omega)]
          rw [interleaveEquiv_inr_high]
          rw [show ((finCongr (by omega :
                n + n = 0 + (n + n)))
              (Fin.natAdd n (⟨ℓ.val - n, by have := ℓ.isLt; omega⟩ :
                Fin n))) =
            Fin.natAdd 0 (⟨ℓ.val, by have := ℓ.isLt; omega⟩ :
              Fin (n + n)) from
            Fin.ext (by simp [Fin.val_natAdd]; omega)]
          rw [interleaveEquiv_inl_high]
          rw [show (Fin.natAdd (0 + 0)
              (Fin.castAdd (K + K) (⟨ℓ.val, by have := ℓ.isLt; omega⟩ :
                Fin (n + n)))) =
            (⟨ℓ.val, by have := ℓ.isLt; omega⟩ :
              Fin (0 + ((n + n) + (K + K)))) from
            Fin.ext (by simp [Fin.val_natAdd, Fin.val_castAdd])]
          simp only [id_eq]
          rw [block_ER_val, block_bigE_val]
          simp only [Fin.val_castAdd, Fin.val_natAdd]
          split_ifs <;> omega
    -- ═══════ THE CUP FLAGS ═══════
    · -- a cup flag flips into a through-strand
      show Sum.map id
          (⇑((transposeEquiv (K + n) (K + n)).trans
            (inPermEquiv
              ((blockRot K n).symm).symm (K + n))))
          (Sum.map id
            (⇑(interleaveEquiv K K n n))
            ((Sum.inr (if !c then
                (⟨K + k.val, by have := k.isLt; omega⟩ :
                  Fin (K + K))
              else ⟨k.val, by have := k.isLt; omega⟩)).map
              Sum.inl Sum.inl)) =
        Sum.map _ id
          (Sum.map id
            (⇑(((finCongr (by omega :
                0 + ((n + n) + (K + K)) =
                  0 + ((K + n) + (K + n)))).trans
              (outPermEquiv 0
                (blockOuterPerm K n))).trans
              (finCongr (by omega :
                0 + ((K + n) + (K + n)) =
                  (K + n) + (K + n)))))
            (Sum.map id
              (⇑(interleaveEquiv 0 (n + n) 0 (K + K)))
              (((Sum.inr ((finCongr (by omega :
                    K + K = 0 + (K + K)))
                  (if c then
                    (⟨K + k.val, by have := k.isLt; omega⟩ :
                      Fin (K + K))
                  else ⟨k.val,
                    by have := k.isLt; omega⟩))).map
                Sum.inr Sum.inr))))
      cases c
      · simp only [Bool.not_false, Sum.map_inl, Sum.map_inr,
          Bool.false_eq_true, if_false, if_true, reduceIte]
        refine congrArg Sum.inr (Fin.ext ?_)
        rw [show (⟨K + k.val, by have := k.isLt; omega⟩ :
            Fin (K + K)) =
          Fin.natAdd K (⟨k.val, k.isLt⟩ : Fin K) from
          Fin.ext rfl]
        rw [interleaveEquiv_inl_high]
        rw [show ((finCongr (by omega : K + K = 0 + (K + K)))
            (⟨k.val, by have := k.isLt; omega⟩ :
              Fin (K + K))) =
          Fin.natAdd 0 (⟨k.val,
            by have := k.isLt; omega⟩ : Fin (K + K)) from
          Fin.ext (by simp [Fin.val_natAdd])]
        rw [interleaveEquiv_inr_high]
        rw [show (Fin.natAdd (0 + 0) (Fin.natAdd (n + n)
            (⟨k.val, by have := k.isLt; omega⟩ :
              Fin (K + K)))) =
          (⟨(n + n) + k.val, by have := k.isLt; omega⟩ :
            Fin (0 + ((n + n) + (K + K)))) from
          Fin.ext (by simp [Fin.val_natAdd])]
        simp only [id_eq]
        rw [block_ER_val, block_bigE_val]
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        split_ifs <;> first
          | omega
          | (have hk := k.isLt; omega)
      · simp only [Bool.not_true, Sum.map_inl, Sum.map_inr,
          Bool.false_eq_true, if_false, if_true, reduceIte]
        refine congrArg Sum.inr (Fin.ext ?_)
        rw [show (⟨k.val, by have := k.isLt; omega⟩ :
            Fin (K + K)) =
          Fin.castAdd K (⟨k.val, k.isLt⟩ : Fin K) from
          Fin.ext rfl]
        rw [interleaveEquiv_inl_low]
        rw [show ((finCongr (by omega : K + K = 0 + (K + K)))
            (⟨K + k.val, by have := k.isLt; omega⟩ :
              Fin (K + K))) =
          Fin.natAdd 0 (⟨K + k.val,
            by have := k.isLt; omega⟩ : Fin (K + K)) from
          Fin.ext (by simp [Fin.val_natAdd])]
        rw [interleaveEquiv_inr_high]
        rw [show (Fin.natAdd (0 + 0) (Fin.natAdd (n + n)
            (⟨K + k.val, by have := k.isLt; omega⟩ :
              Fin (K + K)))) =
          (⟨(n + n) + (K + k.val), by have := k.isLt; omega⟩ :
            Fin (0 + ((n + n) + (K + K)))) from
          Fin.ext (by simp [Fin.val_natAdd])]
        simp only [id_eq]
        rw [block_ER_val, block_bigE_val]
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        split_ifs <;> first
          | omega
          | (have hk := k.isLt; omega)
  pairing_comm := by
    rintro (g | ⟨k, c⟩)
    · rfl
    · rfl
  circles_eq := by
    show 𝔊.circles + (strandBundle K).circles =
      (strandBundle K).circles + 𝔊.circles
    omega

/-! ### The splice -/

/-- **The block splice**: partially closing an `(n,n)`-fragment
against the block rotation on `K + 2n` strands splices it into
the block rotation on `K + n` strands. -/
noncomputable def partialCloseBlockSplice (K n : ℕ)
    (𝔊 : Fragment (Fin (n + n))) :
    (partialClose 𝔊
        (permFragment (blockRot (K + n) n).symm)).Equiv
      ((permFragment (blockRot K n).symm).compose
        ((tensorFragment (strandBundle K) 𝔊).relabel
          (transposeEquiv (K + n) (K + n)))) := by
  -- Step 1: partial closure to a composition
  refine (partialCloseEqCompose 𝔊
    (permFragment (blockRot (K + n) n).symm)).trans ?_
  -- Step 2: reshuffle decomposition
  refine (Fragment.Equiv.relabelCongr
    (Fragment.composeCongr
      (Fragment.Equiv.refl _)
      (block_reshuffle_decomp K n))
    (finCongr (by omega :
      0 + ((K + n) + (K + n)) = (K + n) + (K + n)))).trans ?_
  -- Step 3: composeRelabelOut (absorb outer perm into composition)
  refine (Fragment.Equiv.relabelCongr
    (composeRelabelOut
      (blockOuterPerm K n)
      (𝔊.relabel (finCongr (by omega : n + n = 0 + (n + n))))
      ((tensorFragment (s := n + n) (t := n + n) (u := 0) (v := K + K)
          (strandBundle (n + n))
          ((strandBundle K).relabel
            (finCongr (by omega : K + K = 0 + (K + K))))).relabel
        (finCongr (by omega :
          (n + n + 0) + (n + n + (K + K)) =
            (n + n) + ((K + n) + (K + n))))))
    (finCongr (by omega :
      0 + ((K + n) + (K + n)) = (K + n) + (K + n)))).trans ?_
  -- Step 4: compose_relabel_castOut (collapse the recast)
  refine (Fragment.Equiv.relabelCongr
    (Fragment.Equiv.relabelCongr
      (compose_relabel_castOut
        (by omega : (n + n) + (K + K) = (K + n) + (K + n))
        (𝔊.relabel (finCongr (by omega : n + n = 0 + (n + n))))
        (tensorFragment (s := n + n) (t := n + n) (u := 0) (v := K + K)
          (strandBundle (n + n))
          ((strandBundle K).relabel
            (finCongr (by omega : K + K = 0 + (K + K))))))
      (outPermEquiv 0 (blockOuterPerm K n)))
    (finCongr (by omega :
      0 + ((K + n) + (K + n)) = (K + n) + (K + n)))).trans ?_
  -- Step 5: tensorComposeInterchange + unit + strandBundle collapse
  have E5 : ((𝔊.relabel
      (finCongr (by omega : n + n = 0 + (n + n)))).compose
      (tensorFragment (s := n + n) (t := n + n) (u := 0) (v := K + K)
        (strandBundle (n + n))
        ((strandBundle K).relabel
          (finCongr (by omega : K + K = 0 + (K + K)))))).Equiv
      (tensorFragment (s := 0) (t := n + n) (u := 0) (v := K + K)
        (𝔊.relabel
          (finCongr (by omega : n + n = 0 + (n + n))))
        ((strandBundle K).relabel
          (finCongr (by omega : K + K = 0 + (K + K))))) :=
    (Fragment.composeCongr
        ((tensorFragmentUnitRight (𝔊.relabel
            (finCongr (by omega : n + n = 0 + (n + n))))).trans
          (relabel_defeq_collapse _ _)).symm
        (Fragment.Equiv.refl _)).trans
      ((Fragment.tensorComposeInterchange
          (𝔊.relabel
            (finCongr (by omega : n + n = 0 + (n + n))))
          (strandBundle (n + n))
          emptyClosedFragment
          ((strandBundle K).relabel
            (finCongr (by omega : K + K = 0 + (K + K))))).symm.trans
        (tensorFragmentCongr
          (composeStrandBundleRight 0 (n + n) _)
          ((Fragment.composeCongr
              strandBundleZeroEmpty.symm
              (Fragment.Equiv.refl _)).trans
            (composeStrandBundleLeft 0 (K + K) _))))
  refine (Fragment.Equiv.relabelCongr
    (Fragment.Equiv.relabelCongr
      (Fragment.Equiv.relabelCongr E5
        (finCongr (by omega :
          0 + ((n + n) + (K + K)) = 0 + ((K + n) + (K + n)))))
      (outPermEquiv 0 (blockOuterPerm K n)))
    (finCongr (by omega :
      0 + ((K + n) + (K + n)) = (K + n) + (K + n)))).trans ?_
  -- Step 6: collapse relabels
  refine (Fragment.Equiv.relabelCongr
    (Fragment.Equiv.relabelTrans _ _ _)
    (finCongr (by omega :
      0 + ((K + n) + (K + n)) = (K + n) + (K + n)))).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  -- Step 7: bridge to RHS
  refine Fragment.Equiv.trans ?_
    ((permFragmentComposeLeft
        ((blockRot K n).symm)
        ((tensorFragment (strandBundle K) 𝔊).relabel
          (transposeEquiv (K + n) (K + n)))).trans
      (Fragment.Equiv.relabelTrans _ _ _)).symm
  exact block_splice_bridge K n 𝔊

end RS
