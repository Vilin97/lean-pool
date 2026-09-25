/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.CompositionEquiv

/-!
# The tensor product of fragments

The monoidal product of the skein category on representatives:
the tensor of an `(s, t)`-fragment and a `(u, v)`-fragment is
their disjoint union with interleaved boundary — the two low
blocks side by side, then the two high blocks
(`interleaveEquiv`).  The four value lemmas locate each block of
the interleaving, and `tensorFragmentCongr` shows the tensor
respects fragment equivalence in both slots.
-/

@[expose] public section

namespace RS

/-- The interleaving of two `(low, high)` boundaries: low block
of the first, low block of the second, high block of the first,
high block of the second. -/
def interleaveEquiv (s t u v : ℕ) :
    (Fin (s + t) ⊕ Fin (u + v)) ≃ Fin ((s + u) + (t + v)) :=
  ((_root_.Equiv.sumCongr finSumFinEquiv.symm
      finSumFinEquiv.symm).trans
    ((_root_.Equiv.sumSumSumComm (Fin s) (Fin t)
        (Fin u) (Fin v)).trans
      (_root_.Equiv.sumCongr finSumFinEquiv
        finSumFinEquiv))).trans
    finSumFinEquiv

/-- The low block of the first factor sits first. -/
theorem interleaveEquiv_inl_low (s t u v : ℕ) (i : Fin s) :
    interleaveEquiv s t u v (Sum.inl (Fin.castAdd t i)) =
      Fin.castAdd (t + v) (Fin.castAdd u i) := by
  unfold interleaveEquiv
  simp [_root_.Equiv.sumSumSumComm,
    finSumFinEquiv_symm_apply_castAdd]

/-- The low block of the second factor sits second. -/
theorem interleaveEquiv_inr_low (s t u v : ℕ) (j : Fin u) :
    interleaveEquiv s t u v (Sum.inr (Fin.castAdd v j)) =
      Fin.castAdd (t + v) (Fin.natAdd s j) := by
  unfold interleaveEquiv
  simp [_root_.Equiv.sumSumSumComm,
    finSumFinEquiv_symm_apply_castAdd]

/-- The high block of the first factor sits third. -/
theorem interleaveEquiv_inl_high (s t u v : ℕ) (k : Fin t) :
    interleaveEquiv s t u v (Sum.inl (Fin.natAdd s k)) =
      Fin.natAdd (s + u) (Fin.castAdd v k) := by
  unfold interleaveEquiv
  simp [_root_.Equiv.sumSumSumComm,
    finSumFinEquiv_symm_apply_natAdd]

/-- The high block of the second factor sits last. -/
theorem interleaveEquiv_inr_high (s t u v : ℕ) (l : Fin v) :
    interleaveEquiv s t u v (Sum.inr (Fin.natAdd u l)) =
      Fin.natAdd (s + u) (Fin.natAdd t l) := by
  unfold interleaveEquiv
  simp [_root_.Equiv.sumSumSumComm,
    finSumFinEquiv_symm_apply_natAdd]

/-- The inverse interleaving on the first block. -/
theorem interleaveEquiv_symm_low_left (s t u v : ℕ) (i : Fin s) :
    (interleaveEquiv s t u v).symm
        (Fin.castAdd (t + v) (Fin.castAdd u i)) =
      Sum.inl (Fin.castAdd t i) :=
  (_root_.Equiv.symm_apply_eq _).mpr
    (interleaveEquiv_inl_low s t u v i).symm

/-- The inverse interleaving on the second block. -/
theorem interleaveEquiv_symm_low_right (s t u v : ℕ) (j : Fin u) :
    (interleaveEquiv s t u v).symm
        (Fin.castAdd (t + v) (Fin.natAdd s j)) =
      Sum.inr (Fin.castAdd v j) :=
  (_root_.Equiv.symm_apply_eq _).mpr
    (interleaveEquiv_inr_low s t u v j).symm

/-- The inverse interleaving on the third block. -/
theorem interleaveEquiv_symm_high_left (s t u v : ℕ) (k : Fin t) :
    (interleaveEquiv s t u v).symm
        (Fin.natAdd (s + u) (Fin.castAdd v k)) =
      Sum.inl (Fin.natAdd s k) :=
  (_root_.Equiv.symm_apply_eq _).mpr
    (interleaveEquiv_inl_high s t u v k).symm

/-- The inverse interleaving on the last block. -/
theorem interleaveEquiv_symm_high_right (s t u v : ℕ) (l : Fin v) :
    (interleaveEquiv s t u v).symm
        (Fin.natAdd (s + u) (Fin.natAdd t l)) =
      Sum.inr (Fin.natAdd u l) :=
  (_root_.Equiv.symm_apply_eq _).mpr
    (interleaveEquiv_inr_high s t u v l).symm

/-- The tensor product of fragments: disjoint union with
interleaved boundary. -/
noncomputable def tensorFragment {s t u v : ℕ}
    (x : Fragment (Fin (s + t))) (z : Fragment (Fin (u + v))) :
    Fragment (Fin ((s + u) + (t + v))) :=
  (x.disjUnion z).relabel (interleaveEquiv s t u v)

/-- The tensor respects fragment equivalence in both slots. -/
noncomputable def tensorFragmentCongr {s t u v : ℕ}
    {x₁ x₂ : Fragment (Fin (s + t))}
    {z₁ z₂ : Fragment (Fin (u + v))}
    (hx : x₁.Equiv x₂) (hz : z₁.Equiv z₂) :
    (tensorFragment x₁ z₁).Equiv (tensorFragment x₂ z₂) :=
  Fragment.Equiv.relabelCongr
    (Fragment.Equiv.disjUnionCongr hx hz)
    (interleaveEquiv s t u v)

end RS
