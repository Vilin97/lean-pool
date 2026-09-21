/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PermFragment
import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceShift
import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLaw

/-!
# Composition of permutation fragments

The multiplication law of the symmetric-group generators
(accompanying paper §3.1): composing permutation fragments composes the
permutations, `Pσ ∘ Pτ ≃ P(τσ)`.  The proof is pure calculus:
a permutation fragment is the strand bundle with outgoing labels
permuted (`permFragmentRelabelOutPerm`), the outgoing
permutation crosses the interface by `interfaceShift`, the bare
bundle is absorbed by the identity law, and the residual incoming
permutation is traded for a strand re-indexing of the bundle
(`strandBundleRelabelBoth`), which is invisible up to
equivalence.
-/

namespace RS

/-- A permutation fragment is the strand bundle with its outgoing
labels permuted by `outPermEquiv`. -/
noncomputable def permFragmentRelabelOutPerm {t : ℕ}
    (σ : Equiv.Perm (Fin t)) :
    (permFragment σ).Equiv
      ((strandBundle t).relabel (outPermEquiv t σ)) where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm := fun f => by
    obtain ⟨k, b⟩ := f
    cases b
    · show Sum.inr (outPermEquiv t σ
          ⟨k.val, by have := k.isLt; omega⟩) =
        Sum.inr (⟨k.val, by have := k.isLt; omega⟩ : Fin (t + t))
      refine congrArg Sum.inr ?_
      rw [show (⟨k.val, by have := k.isLt; omega⟩ : Fin (t + t)) =
          Fin.castAdd t k from Fin.ext rfl, outPermEquiv_low]
    · show Sum.inr (outPermEquiv t σ
          ⟨t + k.val, by have := k.isLt; omega⟩) =
        Sum.inr (⟨t + (σ k).val,
          by have := (σ k).isLt; omega⟩ : Fin (t + t))
      refine congrArg Sum.inr ?_
      rw [show (⟨t + k.val, by have := k.isLt; omega⟩ :
          Fin (t + t)) = Fin.natAdd t k from Fin.ext rfl,
        outPermEquiv_high]
      exact Fin.ext rfl
  pairing_comm := fun _ => rfl
  circles_eq := rfl

/-- Re-indexing the strands of the bundle — permuting both ends
of each strand by the same permutation — is invisible up to
equivalence. -/
noncomputable def strandBundleRelabelBoth {t : ℕ}
    (δ : Equiv.Perm (Fin t)) :
    ((strandBundle t).relabel
      ((inPermEquiv δ t).trans (outPermEquiv t δ))).Equiv
      (strandBundle t) where
  flagEquiv := _root_.Equiv.prodCongr δ (_root_.Equiv.refl Bool)
  vertexEquiv := _root_.Equiv.refl _
  attach_comm := fun f => by
    obtain ⟨k, b⟩ := f
    cases b
    · show Sum.inr (⟨(δ k).val,
          by have := (δ k).isLt; omega⟩ : Fin (t + t)) =
        Sum.inr ((inPermEquiv δ t).trans (outPermEquiv t δ)
          ⟨k.val, by have := k.isLt; omega⟩)
      refine congrArg Sum.inr ?_
      rw [show (⟨k.val, by have := k.isLt; omega⟩ : Fin (t + t)) =
          Fin.castAdd t k from Fin.ext rfl,
        _root_.Equiv.trans_apply, inPermEquiv_low, outPermEquiv_low]
      exact Fin.ext rfl
    · show Sum.inr (⟨t + (δ k).val,
          by have := (δ k).isLt; omega⟩ : Fin (t + t)) =
        Sum.inr ((inPermEquiv δ t).trans (outPermEquiv t δ)
          ⟨t + k.val, by have := k.isLt; omega⟩)
      refine congrArg Sum.inr ?_
      rw [show (⟨t + k.val, by have := k.isLt; omega⟩ :
          Fin (t + t)) = Fin.natAdd t k from Fin.ext rfl,
        _root_.Equiv.trans_apply, inPermEquiv_high, outPermEquiv_high]
      exact Fin.ext rfl
  pairing_comm := fun _ => rfl
  circles_eq := rfl

/-- Label algebra: shifting the outgoing permutation `τ` across
the interface against `σ` re-associates into a strand re-indexing
by `σ⁻¹` followed by the outgoing composite permutation. -/
theorem outPerm_shift_both {t : ℕ} (σ τ : Equiv.Perm (Fin t)) :
    (outPermEquiv t τ).trans (inPermEquiv σ.symm t) =
      ((inPermEquiv σ.symm t).trans (outPermEquiv t σ.symm)).trans
        (outPermEquiv t (τ * σ)) := by
  apply _root_.Equiv.ext
  intro ℓ
  by_cases h : ℓ.val < t
  · rw [show ℓ = (Fin.castAdd t ⟨ℓ.val, h⟩ : Fin (t + t)) from
      Fin.ext rfl]
    simp only [_root_.Equiv.trans_apply, outPermEquiv_low,
      inPermEquiv_low]
  · rw [show ℓ = (Fin.natAdd t ⟨ℓ.val - t,
        by have := ℓ.isLt; omega⟩ : Fin (t + t)) from
      Fin.ext (by show ℓ.val = t + (ℓ.val - t); omega)]
    simp only [_root_.Equiv.trans_apply, outPermEquiv_high,
      inPermEquiv_high]
    refine congrArg (Fin.natAdd t) ?_
    simp [Equiv.Perm.mul_apply]

/-- **Permutation fragments compose** (accompanying paper §3.1): the
composition of the permutation fragments of `σ` and `τ` is the
permutation fragment of the composite `τ * σ` (first through
`σ`, then through `τ`). -/
noncomputable def permFragmentCompose {t : ℕ}
    (σ τ : Equiv.Perm (Fin t)) :
    ((permFragment σ).compose (permFragment τ)).Equiv
      (permFragment (τ * σ)) :=
  (Fragment.composeCongr (permFragmentRelabelOutPerm σ)
      (Fragment.Equiv.refl (permFragment τ))).trans
    ((interfaceShift σ (strandBundle t) (permFragment τ)).trans
      ((composeStrandBundleLeft t t
          ((permFragment τ).relabel (inPermEquiv σ.symm t))).trans
        ((Fragment.Equiv.relabelCongr
            (permFragmentRelabelOutPerm τ)
            (inPermEquiv σ.symm t)).trans
          ((Fragment.Equiv.relabelTrans (strandBundle t)
              (outPermEquiv t τ) (inPermEquiv σ.symm t)).trans
            ((Fragment.Equiv.relabelEq (strandBundle t)
                (outPerm_shift_both σ τ)).trans
              ((Fragment.Equiv.relabelTrans (strandBundle t)
                  ((inPermEquiv σ.symm t).trans
                    (outPermEquiv t σ.symm))
                  (outPermEquiv t (τ * σ))).symm.trans
                ((Fragment.Equiv.relabelCongr
                    (strandBundleRelabelBoth σ.symm)
                    (outPermEquiv t (τ * σ))).trans
                  (permFragmentRelabelOutPerm
                    (τ * σ)).symm)))))))

end RS
