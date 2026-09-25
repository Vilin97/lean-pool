/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorFragment

/-!
# The strand bundle is a tensor of strand bundles

`strandBundle (a + b) ≃ strandBundle a ⊗ strandBundle b`: the
first `a` strands form the first factor, the rest the second.
This is the object-level compatibility of the identity fragments
with the monoidal product, the entry point for the trace
multiplicativity (Lemma 3.5(b)).
-/

namespace RS

/-- The strand split: strands below `a` to the left factor,
strands above to the right. -/
def bundleFlagEquiv (a b : ℕ) :
    (Fin (a + b) × Bool) ≃ ((Fin a × Bool) ⊕ (Fin b × Bool)) where
  toFun f :=
    if h : f.1.val < a then Sum.inl (⟨f.1.val, h⟩, f.2)
    else Sum.inr (⟨f.1.val - a, by have := f.1.isLt; omega⟩, f.2)
  invFun g :=
    match g with
    | Sum.inl (k, c) => (⟨k.val, by have := k.isLt; omega⟩, c)
    | Sum.inr (l, c) => (⟨a + l.val, by have := l.isLt; omega⟩, c)
  left_inv f := by
    by_cases h : f.1.val < a
    · simp only [dite_eq_left h]
    · simp only [dite_eq_right h]
      exact Prod.ext (Fin.ext (by
        change a + (f.1.val - a) = f.1.val
        omega)) rfl
  right_inv g := by
    rcases g with ⟨k, c⟩ | ⟨l, c⟩
    · simp only [dite_eq_left k.isLt]
    · simp only [dite_eq_right (show ¬ a + l.val < a by omega)]
      refine congrArg Sum.inr (Prod.ext (Fin.ext ?_) rfl)
      change a + l.val - a = l.val
      omega

/-- **The bundle splits**: the `(a + b)`-strand bundle is the
tensor of the `a`- and `b`-strand bundles. -/
noncomputable def strandBundleTensor (a b : ℕ) :
    (strandBundle (a + b)).Equiv
      (tensorFragment (strandBundle a) (strandBundle b)) where
  flagEquiv := bundleFlagEquiv a b
  vertexEquiv :=
    show Empty ≃ (Empty ⊕ Empty) from
      _root_.Equiv.equivOfIsEmpty _ _
  attach_comm := fun f => by
    obtain ⟨k, c⟩ := f
    by_cases h : k.val < a
    · have hbfe : bundleFlagEquiv a b (k, c) =
          Sum.inl (⟨k.val, h⟩, c) := dite_eq_left h
      change (tensorFragment (strandBundle a)
        (strandBundle b)).attach (bundleFlagEquiv a b (k, c)) = _
      rw [hbfe]
      rcases c with _ | _
      · change Sum.inr (interleaveEquiv a a b b
          (Sum.inl ⟨k.val, by omega⟩)) = Sum.inr ⟨k.val, by omega⟩
        rw [show (⟨k.val, by omega⟩ : Fin (a + a)) =
            Fin.castAdd a ⟨k.val, h⟩ from Fin.ext rfl,
          interleaveEquiv_inl_low]
        exact congrArg Sum.inr (Fin.ext rfl)
      · change Sum.inr (interleaveEquiv a a b b
          (Sum.inl ⟨a + k.val, by omega⟩)) =
          Sum.inr ⟨(a + b) + k.val, by have := k.isLt; omega⟩
        rw [show (⟨a + k.val, by omega⟩ : Fin (a + a)) =
            Fin.natAdd a ⟨k.val, h⟩ from Fin.ext rfl,
          interleaveEquiv_inl_high]
        exact congrArg Sum.inr (Fin.ext rfl)
    · have hbfe : bundleFlagEquiv a b (k, c) =
          Sum.inr (⟨k.val - a, by have := k.isLt; omega⟩, c) :=
        dite_eq_right h
      change (tensorFragment (strandBundle a)
        (strandBundle b)).attach (bundleFlagEquiv a b (k, c)) = _
      rw [hbfe]
      rcases c with _ | _
      · change Sum.inr (interleaveEquiv a a b b
          (Sum.inr ⟨k.val - a, by have := k.isLt; omega⟩)) =
          Sum.inr ⟨k.val, by omega⟩
        rw [show (⟨k.val - a, by have := k.isLt; omega⟩ :
            Fin (b + b)) =
            Fin.castAdd b ⟨k.val - a, by have := k.isLt; omega⟩
          from Fin.ext rfl, interleaveEquiv_inr_low]
        exact congrArg Sum.inr (Fin.ext (by
          change a + (k.val - a) = k.val
          omega))
      · change Sum.inr (interleaveEquiv a a b b
          (Sum.inr ⟨b + (k.val - a), by have := k.isLt; omega⟩)) =
          Sum.inr ⟨(a + b) + k.val, by have := k.isLt; omega⟩
        rw [show (⟨b + (k.val - a), by have := k.isLt; omega⟩ :
            Fin (b + b)) =
            Fin.natAdd b ⟨k.val - a, by have := k.isLt; omega⟩
          from Fin.ext rfl, interleaveEquiv_inr_high]
        exact congrArg Sum.inr (Fin.ext (by
          change (a + b) + (a + (k.val - a)) = (a + b) + k.val
          omega))
  pairing_comm := fun f => by
    obtain ⟨k, c⟩ := f
    by_cases h : k.val < a
    · have h1 : bundleFlagEquiv a b (k, !c) =
          Sum.inl (⟨k.val, h⟩, !c) := dite_eq_left h
      have h2 : bundleFlagEquiv a b (k, c) =
          Sum.inl (⟨k.val, h⟩, c) := dite_eq_left h
      change bundleFlagEquiv a b (k, !c) = _
      rw [h1]
      change _ = (tensorFragment (strandBundle a)
        (strandBundle b)).pairing (bundleFlagEquiv a b (k, c))
      rw [h2]
      rfl
    · have h1 : bundleFlagEquiv a b (k, !c) =
          Sum.inr (⟨k.val - a, by have := k.isLt; omega⟩, !c) :=
        dite_eq_right h
      have h2 : bundleFlagEquiv a b (k, c) =
          Sum.inr (⟨k.val - a, by have := k.isLt; omega⟩, c) :=
        dite_eq_right h
      change bundleFlagEquiv a b (k, !c) = _
      rw [h1]
      change _ = (tensorFragment (strandBundle a)
        (strandBundle b)).pairing (bundleFlagEquiv a b (k, c))
      rw [h2]
      rfl
  circles_eq := rfl

end RS
