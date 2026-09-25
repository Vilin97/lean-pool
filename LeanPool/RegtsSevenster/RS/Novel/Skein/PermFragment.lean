/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.StrandBundle

/-!
# Permutation fragments

The symmetric-group generators of the skein category: for a
permutation `σ` of `Fin t`, the fragment `permFragment σ` consists
of `t` disjoint strands, strand `k` joining incoming boundary label
`k` to outgoing boundary label `t + σ k`.  The identity permutation
gives the strand bundle.
-/

@[expose] public section

namespace RS

/-- The permutation fragment of `σ`: strand `k` joins incoming
label `k` to outgoing label `t + σ k`. -/
def permFragment {t : ℕ} (σ : Equiv.Perm (Fin t)) :
    Fragment (Fin (t + t)) where
  Flag := Fin t × Bool
  Vertex := Empty
  attach := fun f =>
    Sum.inr (if f.2 then
        ⟨t + (σ f.1).val, by have := (σ f.1).isLt; omega⟩
      else ⟨f.1.val, by have := f.1.isLt; omega⟩)
  pairing := fun f => (f.1, !f.2)
  pairing_invol := fun f => by simp
  pairing_ne := fun f h => by
    have hsnd := congrArg Prod.snd h
    simp at hsnd
  boundaryFlag := fun ℓ =>
    if h : ℓ.val < t then (⟨ℓ.val, h⟩, false)
    else (σ.symm ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩, true)
  attach_boundaryFlag := fun ℓ => by
    by_cases h : ℓ.val < t
    · rw [dite_eq_left h]
      exact congrArg Sum.inr (Fin.ext rfl)
    · rw [dite_eq_right h]
      refine congrArg Sum.inr (Fin.ext ?_)
      change t + (σ (σ.symm ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩)).val =
        ℓ.val
      rw [Equiv.apply_symm_apply]
      change t + (ℓ.val - t) = ℓ.val
      have := ℓ.isLt
      omega
  eq_boundaryFlag := fun ℓ f h => by
    obtain ⟨a, b⟩ := f
    have hℓ := (Sum.inr.inj h).symm
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hℓ
      subst hℓ
      rw [dite_eq_left a.isLt]
    · simp only [ite_true] at hℓ
      subst hℓ
      rw [dite_eq_right (show ¬ t + (σ a).val < t by omega)]
      refine Prod.ext_iff.mpr ⟨?_, rfl⟩
      change a = σ.symm ⟨t + (σ a).val - t,
        by have := (σ a).isLt; omega⟩
      rw [show (⟨t + (σ a).val - t,
          by have := (σ a).isLt; omega⟩ : Fin t) = σ a from
        Fin.ext (by change t + (σ a).val - t = (σ a).val; omega)]
      exact (σ.symm_apply_apply a).symm
  circles := 0

/-- The identity permutation gives the strand bundle. -/
theorem permFragment_one (t : ℕ) :
    permFragment (1 : Equiv.Perm (Fin t)) = strandBundle t := rfl

/-- The label re-indexing that fixes incoming labels and permutes
outgoing labels by `σ`. -/
def permHighEquiv {t : ℕ} (σ : Equiv.Perm (Fin t)) :
    Fin (t + t) ≃ Fin (t + t) where
  toFun ℓ :=
    if h : ℓ.val < t then ℓ
    else ⟨t + (σ ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩).val,
      by have := (σ ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩).isLt; omega⟩
  invFun ℓ :=
    if h : ℓ.val < t then ℓ
    else ⟨t + (σ.symm ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩).val,
      by have := (σ.symm ⟨ℓ.val - t,
        by have := ℓ.isLt; omega⟩).isLt; omega⟩
  left_inv ℓ := by
    dsimp only
    by_cases h : ℓ.val < t
    · simp only [dite_eq_left h]
    · rw [dite_eq_right h, dite_eq_right (by
        change ¬ t + (σ ⟨ℓ.val - t, _⟩).val < t
        omega)]
      refine Fin.ext ?_
      change t + (σ.symm ⟨t + (σ ⟨ℓ.val - t, _⟩).val - t, _⟩).val = ℓ.val
      rw [show (⟨t + (σ ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩).val - t,
          by have := (σ ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩).isLt
             omega⟩ : Fin t) =
        σ ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩ from Fin.ext (by
          change t + _ - t = _
          omega)]
      rw [Equiv.symm_apply_apply]
      change t + (ℓ.val - t) = ℓ.val
      omega
  right_inv ℓ := by
    dsimp only
    by_cases h : ℓ.val < t
    · simp only [dite_eq_left h]
    · rw [dite_eq_right h, dite_eq_right (by
        change ¬ t + (σ.symm ⟨ℓ.val - t, _⟩).val < t
        omega)]
      refine Fin.ext ?_
      change t + (σ ⟨t + (σ.symm ⟨ℓ.val - t, _⟩).val - t, _⟩).val = ℓ.val
      rw [show (⟨t + (σ.symm ⟨ℓ.val - t,
            by have := ℓ.isLt; omega⟩).val - t,
          by have := (σ.symm ⟨ℓ.val - t,
            by have := ℓ.isLt; omega⟩).isLt; omega⟩ : Fin t) =
        σ.symm ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩ from Fin.ext (by
          change t + _ - t = _
          omega)]
      rw [Equiv.apply_symm_apply]
      change t + (ℓ.val - t) = ℓ.val
      omega

/-- A permutation fragment is the strand bundle with its outgoing
labels re-indexed. -/
noncomputable def permFragmentRelabelBundle {t : ℕ}
    (σ : Equiv.Perm (Fin t)) :
    (permFragment σ).Equiv
      ((strandBundle t).relabel (permHighEquiv σ)) where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm := fun f => by
    obtain ⟨k, b⟩ := f
    cases b
    · change Sum.inr (permHighEquiv σ ⟨k.val, by have := k.isLt; omega⟩) =
        Sum.inr ⟨k.val, by have := k.isLt; omega⟩
      refine congrArg Sum.inr ?_
      unfold permHighEquiv
      change (if h : (⟨k.val, by have := k.isLt; omega⟩ :
          Fin (t + t)).val < t then _ else _) = _
      rw [dite_eq_left (show k.val < t from k.isLt)]
    · change Sum.inr (permHighEquiv σ ⟨t + k.val,
          by have := k.isLt; omega⟩) =
        Sum.inr ⟨t + (σ k).val, by have := (σ k).isLt; omega⟩
      refine congrArg Sum.inr ?_
      unfold permHighEquiv
      change (if h : (⟨t + k.val, by have := k.isLt; omega⟩ :
          Fin (t + t)).val < t then _ else _) = _
      rw [dite_eq_right (show ¬ t + k.val < t by omega)]
      refine Fin.ext ?_
      change t + (σ ⟨t + k.val - t, _⟩).val = t + (σ k).val
      rw [show (⟨t + k.val - t, by have := k.isLt; omega⟩ : Fin t) = k
        from Fin.ext (by change t + k.val - t = k.val; omega)]
  pairing_comm := fun _ => rfl
  circles_eq := rfl

end RS
