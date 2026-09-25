/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorFragment

/-!
# Units of the fragment tensor

Tensoring with the empty closed fragment is a relabel by the
arithmetic cast, on either side.  These power the unitors of the
monoidal skein category.
-/

namespace RS

/-- The interleave against an empty left factor is the cast. -/
theorem interleave_unit_left (s t : ℕ) (ℓ : Fin (s + t)) :
    interleaveEquiv 0 0 s t (Sum.inr ℓ) =
      finCongr (by omega : s + t = (0 + s) + (0 + t)) ℓ := by
  by_cases hl : ℓ.val < s
  · rw [show ℓ = Fin.castAdd t ⟨ℓ.val, hl⟩ from Fin.ext rfl,
      interleaveEquiv_inr_low]
    exact Fin.ext (by change 0 + ℓ.val = ℓ.val; omega)
  · have hk : ℓ.val - s < t := by have := ℓ.isLt; omega
    rw [show ℓ = Fin.natAdd s ⟨ℓ.val - s, hk⟩ from
        Fin.ext (by change ℓ.val = s + (ℓ.val - s); omega),
      interleaveEquiv_inr_high]
    exact Fin.ext (by
      change (0 + s) + (0 + (ℓ.val - s)) = s + (ℓ.val - s)
      omega)

/-- The interleave against an empty right factor is the cast. -/
theorem interleave_unit_right (s t : ℕ) (ℓ : Fin (s + t)) :
    interleaveEquiv s t 0 0 (Sum.inl ℓ) =
      finCongr (by omega : s + t = (s + 0) + (t + 0)) ℓ := by
  by_cases hl : ℓ.val < s
  · rw [show ℓ = Fin.castAdd t ⟨ℓ.val, hl⟩ from Fin.ext rfl,
      interleaveEquiv_inl_low]
    exact Fin.ext rfl
  · have hk : ℓ.val - s < t := by have := ℓ.isLt; omega
    rw [show ℓ = Fin.natAdd s ⟨ℓ.val - s, hk⟩ from
        Fin.ext (by change ℓ.val = s + (ℓ.val - s); omega),
      interleaveEquiv_inl_high]
    exact Fin.ext (by
      change (s + 0) + (ℓ.val - s) = s + (ℓ.val - s)
      omega)

/-- **The left unit**: the empty fragment tensors away. -/
noncomputable def tensorFragmentUnitLeft {s t : ℕ}
    (X : Fragment (Fin (s + t))) :
    (tensorFragment emptyClosedFragment X).Equiv
      (X.relabel (finCongr
        (by omega : s + t = (0 + s) + (0 + t)))) where
  flagEquiv :=
    show (Empty ⊕ X.Flag) ≃ X.Flag from
      _root_.Equiv.emptySum Empty X.Flag
  vertexEquiv :=
    show (Empty ⊕ X.Vertex) ≃ X.Vertex from
      _root_.Equiv.emptySum Empty X.Vertex
  attach_comm := fun f => by
    rcases f with f | f
    · exact f.elim
    · change (X.attach f).map id
        (finCongr (by omega : s + t = (0 + s) + (0 + t))) =
        Sum.map (show (Empty ⊕ X.Vertex) ≃ X.Vertex from
          _root_.Equiv.emptySum Empty X.Vertex) id
          (Sum.map id (interleaveEquiv 0 0 s t)
            (Sum.map Sum.inr Sum.inr (X.attach f)))
      rcases ha : X.attach f with v | ℓ
      · rfl
      · exact congrArg Sum.inr (interleave_unit_left s t ℓ).symm
  pairing_comm := fun f => by
    rcases f with f | f
    · exact f.elim
    · rfl
  circles_eq := by
    change 0 + X.circles = X.circles
    omega

/-- **The right unit**: the empty fragment tensors away. -/
noncomputable def tensorFragmentUnitRight {s t : ℕ}
    (X : Fragment (Fin (s + t))) :
    (tensorFragment X emptyClosedFragment).Equiv
      (X.relabel (finCongr
        (by omega : s + t = (s + 0) + (t + 0)))) where
  flagEquiv :=
    show (X.Flag ⊕ Empty) ≃ X.Flag from
      _root_.Equiv.sumEmpty X.Flag Empty
  vertexEquiv :=
    show (X.Vertex ⊕ Empty) ≃ X.Vertex from
      _root_.Equiv.sumEmpty X.Vertex Empty
  attach_comm := fun f => by
    rcases f with f | f
    · change (X.attach f).map id
        (finCongr (by omega : s + t = (s + 0) + (t + 0))) =
        Sum.map (show (X.Vertex ⊕ Empty) ≃ X.Vertex from
          _root_.Equiv.sumEmpty X.Vertex Empty) id
          (Sum.map id (interleaveEquiv s t 0 0)
            (Sum.map Sum.inl Sum.inl (X.attach f)))
      rcases ha : X.attach f with v | ℓ
      · rfl
      · exact congrArg Sum.inr (interleave_unit_right s t ℓ).symm
    · exact f.elim
  pairing_comm := fun f => by
    rcases f with f | f
    · rfl
    · exact f.elim
  circles_eq := by
    change X.circles + 0 = X.circles
    omega

end RS
