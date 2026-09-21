/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorFragment
import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeAssoc

/-!
# Associativity of the fragment tensor

The two associations of a triple tensor carry the same
interleaved boundary up to the arithmetic cast: block order is
`s₁ s₂ s₃ | t₁ t₂ t₃` either way.  The label identity
(`assocLabel_eq`) is a six-block value chase through the
interleave value lemmas; the associator equivalence follows by
pure relabel algebra.
-/

namespace RS

variable (s₁ t₁ s₂ t₂ s₃ t₃ : ℕ)

/-- The associativity cast of interleaved boundaries. -/
noncomputable def tensorAssocCast :
    Fin ((s₁ + (s₂ + s₃)) + (t₁ + (t₂ + t₃))) ≃
      Fin (((s₁ + s₂) + s₃) + ((t₁ + t₂) + t₃)) :=
  finCongr (by omega)

/-- The left-association label composite. -/
noncomputable def assocLabelL :
    (Fin (s₁ + t₁) ⊕ (Fin (s₂ + t₂) ⊕ Fin (s₃ + t₃))) ≃
      Fin (((s₁ + s₂) + s₃) + ((t₁ + t₂) + t₃)) :=
  (_root_.Equiv.sumAssoc _ _ _).symm.trans
    ((_root_.Equiv.sumCongr (interleaveEquiv s₁ t₁ s₂ t₂)
      (_root_.Equiv.refl (Fin (s₃ + t₃)))).trans
      (interleaveEquiv (s₁ + s₂) (t₁ + t₂) s₃ t₃))

/-- The right-association label composite, cast. -/
noncomputable def assocLabelR :
    (Fin (s₁ + t₁) ⊕ (Fin (s₂ + t₂) ⊕ Fin (s₃ + t₃))) ≃
      Fin (((s₁ + s₂) + s₃) + ((t₁ + t₂) + t₃)) :=
  (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s₁ + t₁)))
      (interleaveEquiv s₂ t₂ s₃ t₃)).trans
    ((interleaveEquiv s₁ t₁ (s₂ + s₃) (t₂ + t₃)).trans
      (tensorAssocCast s₁ t₁ s₂ t₂ s₃ t₃))

/-- The two association composites agree. -/
theorem assocLabel_eq :
    assocLabelL s₁ t₁ s₂ t₂ s₃ t₃ =
      assocLabelR s₁ t₁ s₂ t₂ s₃ t₃ := by
  apply _root_.Equiv.ext
  intro x
  unfold assocLabelL assocLabelR tensorAssocCast
  simp only [_root_.Equiv.trans_apply,
    _root_.Equiv.sumCongr_apply]
  rcases x with a | (b | c)
  · simp only [_root_.Equiv.sumAssoc_symm_apply_inl,
      Sum.map_inl, _root_.Equiv.refl_apply]
    by_cases h : a.val < s₁
    · rw [show a = Fin.castAdd t₁ ⟨a.val, h⟩ from Fin.ext rfl,
        interleaveEquiv_inl_low, interleaveEquiv_inl_low,
        interleaveEquiv_inl_low]
      exact Fin.ext rfl
    · have hk : a.val - s₁ < t₁ := by have := a.isLt; omega
      rw [show a = Fin.natAdd s₁ ⟨a.val - s₁, hk⟩ from
          Fin.ext (by show a.val = s₁ + (a.val - s₁); omega),
        interleaveEquiv_inl_high, interleaveEquiv_inl_high,
        interleaveEquiv_inl_high]
      exact Fin.ext (by
        show ((s₁ + s₂) + s₃) + (a.val - s₁) =
          (s₁ + (s₂ + s₃)) + (a.val - s₁)
        omega)
  · simp only [_root_.Equiv.sumAssoc_symm_apply_inr_inl,
      Sum.map_inl, Sum.map_inr]
    by_cases h : b.val < s₂
    · rw [show b = Fin.castAdd t₂ ⟨b.val, h⟩ from Fin.ext rfl,
        interleaveEquiv_inr_low, interleaveEquiv_inl_low,
        interleaveEquiv_inl_low, interleaveEquiv_inr_low]
      exact Fin.ext rfl
    · have hk : b.val - s₂ < t₂ := by have := b.isLt; omega
      rw [show b = Fin.natAdd s₂ ⟨b.val - s₂, hk⟩ from
          Fin.ext (by show b.val = s₂ + (b.val - s₂); omega),
        interleaveEquiv_inr_high, interleaveEquiv_inl_high,
        interleaveEquiv_inl_high, interleaveEquiv_inr_high]
      exact Fin.ext (by
        show ((s₁ + s₂) + s₃) + (t₁ + (b.val - s₂)) =
          (s₁ + (s₂ + s₃)) + (t₁ + (b.val - s₂))
        omega)
  · simp only [_root_.Equiv.sumAssoc_symm_apply_inr_inr,
      Sum.map_inr, _root_.Equiv.refl_apply]
    by_cases h : c.val < s₃
    · rw [show c = Fin.castAdd t₃ ⟨c.val, h⟩ from Fin.ext rfl,
        interleaveEquiv_inr_low, interleaveEquiv_inr_low,
        interleaveEquiv_inr_low]
      exact Fin.ext (by
        show (s₁ + s₂) + c.val = s₁ + (s₂ + c.val)
        omega)
    · have hk : c.val - s₃ < t₃ := by have := c.isLt; omega
      rw [show c = Fin.natAdd s₃ ⟨c.val - s₃, hk⟩ from
          Fin.ext (by show c.val = s₃ + (c.val - s₃); omega),
        interleaveEquiv_inr_high, interleaveEquiv_inr_high,
        interleaveEquiv_inr_high]
      exact Fin.ext (by
        show ((s₁ + s₂) + s₃) + ((t₁ + t₂) + (c.val - s₃)) =
          (s₁ + (s₂ + s₃)) + (t₁ + (t₂ + (c.val - s₃)))
        omega)

/-- **Associativity of the fragment tensor**: the two
associations agree up to the arithmetic cast. -/
noncomputable def tensorFragmentAssoc
    (X : Fragment (Fin (s₁ + t₁))) (Y : Fragment (Fin (s₂ + t₂)))
    (Z : Fragment (Fin (s₃ + t₃))) :
    (tensorFragment (tensorFragment X Y) Z).Equiv
      ((tensorFragment X (tensorFragment Y Z)).relabel
        (tensorAssocCast s₁ t₁ s₂ t₂ s₃ t₃)) :=
  ((Fragment.Equiv.relabelCongr
      (Fragment.relabelDisjUnionLeft (X.disjUnion Y) Z
        (interleaveEquiv s₁ t₁ s₂ t₂))
      (interleaveEquiv (s₁ + s₂) (t₁ + t₂) s₃ t₃)).trans
    ((Fragment.Equiv.relabelTrans
        ((X.disjUnion Y).disjUnion Z) _ _).trans
      ((Fragment.Equiv.relabelCongr
          (Fragment.disjUnionAssoc X Y Z)
          ((_root_.Equiv.sumCongr (interleaveEquiv s₁ t₁ s₂ t₂)
            (_root_.Equiv.refl (Fin (s₃ + t₃)))).trans
            (interleaveEquiv (s₁ + s₂) (t₁ + t₂) s₃ t₃))).trans
        (Fragment.Equiv.relabelTrans
          (X.disjUnion (Y.disjUnion Z)) _ _)))).trans
  ((Fragment.Equiv.relabelEq _
      (assocLabel_eq s₁ t₁ s₂ t₂ s₃ t₃)).trans
    (((Fragment.Equiv.relabelCongr
        ((Fragment.Equiv.relabelCongr
          (Fragment.relabelDisjUnionRight X (Y.disjUnion Z)
            (interleaveEquiv s₂ t₂ s₃ t₃))
          (interleaveEquiv s₁ t₁ (s₂ + s₃) (t₂ + t₃))).trans
        (Fragment.Equiv.relabelTrans
          (X.disjUnion (Y.disjUnion Z)) _ _))
        (tensorAssocCast s₁ t₁ s₂ t₂ s₃ t₃)).trans
      (Fragment.Equiv.relabelTrans
        (X.disjUnion (Y.disjUnion Z)) _ _)).symm))

end RS
