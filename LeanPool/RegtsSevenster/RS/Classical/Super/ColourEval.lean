/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPower

/-!
# Evaluating a colour tensor

The function tensor on a pure tensor is the pointwise product, and
the colouring of a product index splits into its two factors — the
computation rules the standard super model's coordinates use.
-/

@[expose] public section

open scoped TensorProduct

namespace RS

/-- The function tensor on a pure tensor is the pointwise
product. -/
theorem funTensorFun_tmul {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : ι → ℂ) (g : κ → ℂ) (p : ι × κ) :
    funTensorFun ι κ (f ⊗ₜ[ℂ] g) p = f p.1 * g p.2 := by
  obtain ⟨a, b⟩ := p
  simp [funTensorFun, LinearEquiv.trans_apply]

/-- Rejoining, at an early slot. -/
theorem colouringSplit_symm_castSucc {k ℓ d : ℕ}
    (c₀ : MixedColouring k ℓ d) (x : Fin k ⊕ Fin (2 * ℓ))
    (i : Fin d) :
    (colouringSplit k ℓ d).symm (c₀, x) i.castSucc = c₀ i := by
  simp [colouringSplit]

/-- At the last slot. -/
theorem colouringSplit_symm_last {k ℓ d : ℕ}
    (c₀ : MixedColouring k ℓ d) (x : Fin k ⊕ Fin (2 * ℓ)) :
    (colouringSplit k ℓ d).symm (c₀, x) (Fin.last d) = x := by
  simp [colouringSplit]

/-- The inverse even split on an even-tail/even-colour pair. -/
theorem evenSplitEquiv_symm_inl {k ℓ d : ℕ}
    (c₀ : {c : MixedColouring k ℓ d // c.IsEven}) (a : Fin k) :
    ((evenSplitEquiv k ℓ d).symm (Sum.inl (c₀, a))).val =
      (colouringSplit k ℓ d).symm (c₀.val, Sum.inl a) := rfl

/-- The inverse even split on an odd-tail/odd-colour pair. -/
theorem evenSplitEquiv_symm_inr {k ℓ d : ℕ}
    (c₀ : {c : MixedColouring k ℓ d // ¬ c.IsEven})
    (b : Fin (2 * ℓ)) :
    ((evenSplitEquiv k ℓ d).symm (Sum.inr (c₀, b))).val =
      (colouringSplit k ℓ d).symm (c₀.val, Sum.inr b) := rfl

/-- The inverse odd split on an odd-tail/even-colour pair. -/
theorem oddSplitEquiv_symm_inl {k ℓ d : ℕ}
    (c₀ : {c : MixedColouring k ℓ d // ¬ c.IsEven}) (a : Fin k) :
    ((oddSplitEquiv k ℓ d).symm (Sum.inl (c₀, a))).val =
      (colouringSplit k ℓ d).symm (c₀.val, Sum.inl a) := rfl

/-- The inverse odd split on an even-tail/odd-colour pair. -/
theorem oddSplitEquiv_symm_inr {k ℓ d : ℕ}
    (c₀ : {c : MixedColouring k ℓ d // c.IsEven})
    (b : Fin (2 * ℓ)) :
    ((oddSplitEquiv k ℓ d).symm (Sum.inr (c₀, b))).val =
      (colouringSplit k ℓ d).symm (c₀.val, Sum.inr b) := rfl

end RS
