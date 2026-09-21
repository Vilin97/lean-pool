/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TwoBasis
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TopBraidMerge

/-!
# The colour action of the top braiding, base case

The two-strand braid conjugated into the colouring model is the
Koszul-signed adjacent swap: coordinate evaluation of the braid
on the block structure, one encoding context throughout.
-/

namespace RS

open CategoryTheory MonoidalCategory
open scoped TensorProduct

variable {k ℓ : ℕ}

/-- Subsingleton-module tensors vanish. -/
private theorem subsingleton_tmul_eq_zero {P M : Type*}
    [AddCommGroup P] [Module ℂ P] [Subsingleton P]
    [AddCommGroup M] [Module ℂ M]
    (t : P ⊗[ℂ] M) : t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => rfl
  | tmul p m =>
    rw [Subsingleton.elim p 0, TensorProduct.zero_tmul]
  | add s t hs ht => rw [hs, ht, add_zero]

/-! ### Arity-one evaluations on general pads -/

private theorem eval1_even_inl (r : ℂ)
    (x : (stdSuperPair k ℓ).even)
    (c₁ : MixedColouring k ℓ 1) (h₁ : c₁.IsEven)
    (i : Fin k) (hi : c₁ (Fin.last 0) = Sum.inl i) :
    (colourPowerEquiv k ℓ 1).evenEquiv
      (evenPair r x) ⟨c₁, h₁⟩ = r * x i := by
  show (colourPowerStep k ℓ 0).evenEquiv
    ((TensorProduct.congr
        (colourPowerEquiv k ℓ 0).evenEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even))
      ((r ⊗ₜ[ℂ] x :
        (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
          (stdSuperPair k ℓ).even)),
      (TensorProduct.congr
        (colourPowerEquiv k ℓ 0).oddEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd)) 0)
    ⟨c₁, h₁⟩ = r * x i
  have hcongr : (TensorProduct.congr
      (colourPowerEquiv k ℓ 0).evenEquiv
      (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even))
      ((r ⊗ₜ[ℂ] x :
        (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
          (stdSuperPair k ℓ).even)) =
    ((colourPowerEquiv k ℓ 0).evenEquiv r) ⊗ₜ[ℂ] x :=
    Eq.trans (TensorProduct.congr_tmul _ _ _ _) (by rfl)
  rw [hcongr, map_zero]
  show Sum.elim
    (fun p => funTensorFun _ _
      (((colourPowerEquiv k ℓ 0).evenEquiv r) ⊗ₜ[ℂ]
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even x)) p)
    (fun q => funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) q)
    (evenSplitEquiv k ℓ 0 ⟨c₁, h₁⟩) = r * x i
  rw [evenSplitD_inl c₁ h₁ i hi, Sum.elim_inl]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 0).evenEquiv r)
      (⟨MixedColouring.tail c₁,
        (c₁.isEven_succ_left i hi).mp h₁⟩,
      i).1 = r from rfl]
  rfl

private theorem eval1_even_zero (r : ℂ)
    (x : (stdSuperPair k ℓ).even)
    (c₁ : MixedColouring k ℓ 1) (h₁ : c₁.IsEven)
    (b : Fin (2 * ℓ)) (hb : c₁ (Fin.last 0) = Sum.inr b) :
    (colourPowerEquiv k ℓ 1).evenEquiv
      (evenPair r x) ⟨c₁, h₁⟩ = 0 := by
  show (colourPowerStep k ℓ 0).evenEquiv
    ((TensorProduct.congr
        (colourPowerEquiv k ℓ 0).evenEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even))
      ((r ⊗ₜ[ℂ] x :
        (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
          (stdSuperPair k ℓ).even)),
      (TensorProduct.congr
        (colourPowerEquiv k ℓ 0).oddEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd)) 0)
    ⟨c₁, h₁⟩ = 0
  have hcongr : (TensorProduct.congr
      (colourPowerEquiv k ℓ 0).evenEquiv
      (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even))
      ((r ⊗ₜ[ℂ] x :
        (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
          (stdSuperPair k ℓ).even)) =
    ((colourPowerEquiv k ℓ 0).evenEquiv r) ⊗ₜ[ℂ] x :=
    Eq.trans (TensorProduct.congr_tmul _ _ _ _) (by rfl)
  rw [hcongr, map_zero]
  show Sum.elim
    (fun p => funTensorFun _ _
      (((colourPowerEquiv k ℓ 0).evenEquiv r) ⊗ₜ[ℂ]
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even x)) p)
    (fun q => funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) q)
    (evenSplitEquiv k ℓ 0 ⟨c₁, h₁⟩) = 0
  rw [evenSplitD_inr c₁ h₁ b hb, Sum.elim_inr]
  rw [show funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) _ = 0 from by
    rw [map_zero]; rfl]

private theorem eval1_odd_inr (r : ℂ)
    (w : (stdSuperPair k ℓ).odd)
    (c₁ : MixedColouring k ℓ 1) (h₁ : ¬ c₁.IsEven)
    (a : Fin (2 * ℓ)) (ha : c₁ (Fin.last 0) = Sum.inr a) :
    (colourPowerEquiv k ℓ 1).oddEquiv
      (((r ⊗ₜ[ℂ] w, 0) :
        (superPow (stdSuperPair k ℓ) 1).odd)) ⟨c₁, h₁⟩ =
      r * w a := by
  show (colourPowerStep k ℓ 0).oddEquiv
    ((TensorProduct.congr
        (colourPowerEquiv k ℓ 0).evenEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd))
      ((r ⊗ₜ[ℂ] w :
        (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd)),
      (TensorProduct.congr
        (colourPowerEquiv k ℓ 0).oddEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even)) 0)
    ⟨c₁, h₁⟩ = r * w a
  have hcongr : (TensorProduct.congr
      (colourPowerEquiv k ℓ 0).evenEquiv
      (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd))
      ((r ⊗ₜ[ℂ] w :
        (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd)) =
    ((colourPowerEquiv k ℓ 0).evenEquiv r) ⊗ₜ[ℂ] w :=
    Eq.trans (TensorProduct.congr_tmul _ _ _ _) (by rfl)
  rw [hcongr, map_zero]
  show Sum.elim
    (fun p => funTensorFun _ _
      (((colourPowerEquiv k ℓ 0).evenEquiv r) ⊗ₜ[ℂ]
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd w)) p)
    (fun q => funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin k → ℂ)) q)
    ((Equiv.sumComm _ _).symm (oddSplitEquiv k ℓ 0 ⟨c₁, h₁⟩))
    = r * w a
  rw [oddSplitD_inr c₁ h₁ a ha]
  rw [show ((Equiv.sumComm
      ({c : MixedColouring k ℓ 0 // c.IsEven} ×
        Fin (2 * ℓ))
      ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} ×
        Fin k)).symm
      (Sum.inr (⟨MixedColouring.tail c₁, by
        by_contra hcontra
        exact h₁ ((c₁.isEven_succ_right a ha).mpr
          hcontra)⟩, a))) =
    Sum.inl (⟨MixedColouring.tail c₁, by
      by_contra hcontra
      exact h₁ ((c₁.isEven_succ_right a ha).mpr
        hcontra)⟩, a) from rfl]
  rw [Sum.elim_inl]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 0).evenEquiv r)
      (⟨MixedColouring.tail c₁, by
        by_contra hcontra
        exact h₁ ((c₁.isEven_succ_right a ha).mpr
          hcontra)⟩, a).1 = r from rfl]
  rfl

private theorem eval1_odd_zero (r : ℂ)
    (w : (stdSuperPair k ℓ).odd)
    (c₁ : MixedColouring k ℓ 1) (h₁ : ¬ c₁.IsEven)
    (i : Fin k) (hi : c₁ (Fin.last 0) = Sum.inl i) :
    (colourPowerEquiv k ℓ 1).oddEquiv
      (((r ⊗ₜ[ℂ] w, 0) :
        (superPow (stdSuperPair k ℓ) 1).odd)) ⟨c₁, h₁⟩ = 0 := by
  show (colourPowerStep k ℓ 0).oddEquiv
    ((TensorProduct.congr
        (colourPowerEquiv k ℓ 0).evenEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd))
      ((r ⊗ₜ[ℂ] w :
        (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd)),
      (TensorProduct.congr
        (colourPowerEquiv k ℓ 0).oddEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even)) 0)
    ⟨c₁, h₁⟩ = 0
  have hcongr : (TensorProduct.congr
      (colourPowerEquiv k ℓ 0).evenEquiv
      (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd))
      ((r ⊗ₜ[ℂ] w :
        (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd)) =
    ((colourPowerEquiv k ℓ 0).evenEquiv r) ⊗ₜ[ℂ] w :=
    Eq.trans (TensorProduct.congr_tmul _ _ _ _) (by rfl)
  rw [hcongr, map_zero]
  show Sum.elim
    (fun p => funTensorFun _ _
      (((colourPowerEquiv k ℓ 0).evenEquiv r) ⊗ₜ[ℂ]
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd w)) p)
    (fun q => funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin k → ℂ)) q)
    ((Equiv.sumComm _ _).symm (oddSplitEquiv k ℓ 0 ⟨c₁, h₁⟩))
    = 0
  rw [oddSplitD_inl c₁ h₁ i hi]
  rw [show ((Equiv.sumComm
      ({c : MixedColouring k ℓ 0 // c.IsEven} ×
        Fin (2 * ℓ))
      ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} ×
        Fin k)).symm
      (Sum.inl (⟨MixedColouring.tail c₁, by
        intro hcontra
        exact h₁ ((c₁.isEven_succ_left i hi).mpr
          hcontra)⟩, i))) =
    Sum.inr (⟨MixedColouring.tail c₁, by
      intro hcontra
      exact h₁ ((c₁.isEven_succ_left i hi).mpr
        hcontra)⟩, i) from rfl]
  rw [Sum.elim_inr]
  rw [show funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 0 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin k → ℂ)) _ = 0 from by
    rw [map_zero]; rfl]

/-! ### Arity-two evaluations on general pads, even component -/

private theorem eval2_ee (r : ℂ) (x y : (stdSuperPair k ℓ).even)
    (c : MixedColouring k ℓ 2) (hc : c.IsEven) :
    (colourPowerEquiv k ℓ 2).evenEquiv
      (evenPair (evenPair r x) y) ⟨c, hc⟩ =
    Sum.elim
      (fun p => funTensorFun _ _
        (((colourPowerEquiv k ℓ 1).evenEquiv
            (evenPair r x)) ⊗ₜ[ℂ]
          (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even y)) p)
      (fun q => funTensorFun _ _
        (0 : ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} → ℂ)
          ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) q)
      (evenSplitEquiv k ℓ 1 ⟨c, hc⟩) := by
  show (colourPowerStep k ℓ 1).evenEquiv
    ((TensorProduct.congr
        (colourPowerEquiv k ℓ 1).evenEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even))
      (((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y :
        (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even)),
      (TensorProduct.congr
        (colourPowerEquiv k ℓ 1).oddEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd)) 0)
    ⟨c, hc⟩ = _
  have hcongr : (TensorProduct.congr
      (colourPowerEquiv k ℓ 1).evenEquiv
      (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even))
      (((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y :
        (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even)) =
    ((colourPowerEquiv k ℓ 1).evenEquiv
      (evenPair r x)) ⊗ₜ[ℂ] y :=
    Eq.trans (TensorProduct.congr_tmul _ _ _ _) (by rfl)
  rw [hcongr, map_zero]
  rfl

private theorem eval2_ee_val (r : ℂ)
    (x y : (stdSuperPair k ℓ).even)
    (c : MixedColouring k ℓ 2) (hc : c.IsEven)
    (i j : Fin k)
    (h0 : c 0 = Sum.inl i) (h1 : c (Fin.last 1) = Sum.inl j) :
    (colourPowerEquiv k ℓ 2).evenEquiv
      (evenPair (evenPair r x) y) ⟨c, hc⟩ =
    r * x i * y j := by
  rw [eval2_ee r x y c hc]
  rw [evenSplitD_inl c hc j h1, Sum.elim_inl]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 1).evenEquiv
      (evenPair r x))
      (⟨MixedColouring.tail c,
        (c.isEven_succ_left j h1).mp hc⟩, j).1 =
    r * x i from eval1_even_inl r x _ _ i
      (show MixedColouring.tail c (Fin.last 0) =
        Sum.inl i from h0)]
  rfl

private theorem eval2_ee_zero_right (r : ℂ)
    (x y : (stdSuperPair k ℓ).even)
    (c : MixedColouring k ℓ 2) (hc : c.IsEven)
    (b : Fin (2 * ℓ)) (h1 : c (Fin.last 1) = Sum.inr b) :
    (colourPowerEquiv k ℓ 2).evenEquiv
      (evenPair (evenPair r x) y) ⟨c, hc⟩ = 0 := by
  rw [eval2_ee r x y c hc]
  rw [evenSplitD_inr c hc b h1, Sum.elim_inr]
  rw [show funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) _ = 0 from by
    rw [map_zero]; rfl]

private theorem eval2_ee_zero_left (r : ℂ)
    (x y : (stdSuperPair k ℓ).even)
    (c : MixedColouring k ℓ 2) (hc : c.IsEven)
    (j : Fin k) (a : Fin (2 * ℓ))
    (h0 : c 0 = Sum.inr a) (h1 : c (Fin.last 1) = Sum.inl j) :
    (colourPowerEquiv k ℓ 2).evenEquiv
      (evenPair (evenPair r x) y) ⟨c, hc⟩ = 0 := by
  rw [eval2_ee r x y c hc]
  rw [evenSplitD_inl c hc j h1, Sum.elim_inl]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 1).evenEquiv
      (evenPair r x))
      (⟨MixedColouring.tail c,
        (c.isEven_succ_left j h1).mp hc⟩, j).1 =
    0 from eval1_even_zero r x _ _ a
      (show MixedColouring.tail c (Fin.last 0) =
        Sum.inr a from h0)]
  exact zero_mul _

private theorem eval2_oo (r : ℂ)
    (w z : (stdSuperPair k ℓ).odd)
    (c : MixedColouring k ℓ 2) (hc : c.IsEven) :
    (colourPowerEquiv k ℓ 2).evenEquiv
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even),
        ((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
        (superPow (stdSuperPair k ℓ) 2).even) ⟨c, hc⟩ =
    Sum.elim
      (fun p => funTensorFun _ _
        (0 : ({c : MixedColouring k ℓ 1 // c.IsEven} → ℂ)
          ⊗[ℂ] (Fin k → ℂ)) p)
      (fun q => funTensorFun _ _
        (((colourPowerEquiv k ℓ 1).oddEquiv
            (((r ⊗ₜ[ℂ] w, 0) :
              (superPow (stdSuperPair k ℓ) 1).odd))) ⊗ₜ[ℂ]
          (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd z)) q)
      (evenSplitEquiv k ℓ 1 ⟨c, hc⟩) := by
  show (colourPowerStep k ℓ 1).evenEquiv
    ((TensorProduct.congr
        (colourPowerEquiv k ℓ 1).evenEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even))
      (0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
        (stdSuperPair k ℓ).even),
      (TensorProduct.congr
        (colourPowerEquiv k ℓ 1).oddEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd))
      ((((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z :
        (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).odd)))
    ⟨c, hc⟩ = _
  have hcongr : (TensorProduct.congr
      (colourPowerEquiv k ℓ 1).oddEquiv
      (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd))
      ((((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z :
        (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).odd)) =
    ((colourPowerEquiv k ℓ 1).oddEquiv
      (((r ⊗ₜ[ℂ] w, 0) :
        (superPow (stdSuperPair k ℓ) 1).odd))) ⊗ₜ[ℂ] z :=
    Eq.trans (TensorProduct.congr_tmul _ _ _ _) (by rfl)
  rw [hcongr, map_zero]
  rfl

private theorem eval2_oo_val (r : ℂ)
    (w z : (stdSuperPair k ℓ).odd)
    (c : MixedColouring k ℓ 2) (hc : c.IsEven)
    (a b : Fin (2 * ℓ))
    (h0 : c 0 = Sum.inr a) (h1 : c (Fin.last 1) = Sum.inr b) :
    (colourPowerEquiv k ℓ 2).evenEquiv
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even),
        ((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
        (superPow (stdSuperPair k ℓ) 2).even) ⟨c, hc⟩ =
    r * w a * z b := by
  rw [eval2_oo r w z c hc]
  rw [evenSplitD_inr c hc b h1, Sum.elim_inr]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 1).oddEquiv
      (((r ⊗ₜ[ℂ] w, 0) :
        (superPow (stdSuperPair k ℓ) 1).odd)))
      (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact ((c.isEven_succ_right b h1).mp hc) hcontra⟩,
      b).1 =
    r * w a from eval1_odd_inr r w _ _ a
      (show MixedColouring.tail c (Fin.last 0) =
        Sum.inr a from h0)]
  rfl

private theorem eval2_oo_zero_right (r : ℂ)
    (w z : (stdSuperPair k ℓ).odd)
    (c : MixedColouring k ℓ 2) (hc : c.IsEven)
    (j : Fin k) (h1 : c (Fin.last 1) = Sum.inl j) :
    (colourPowerEquiv k ℓ 2).evenEquiv
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even),
        ((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
        (superPow (stdSuperPair k ℓ) 2).even) ⟨c, hc⟩ = 0 := by
  rw [eval2_oo r w z c hc]
  rw [evenSplitD_inl c hc j h1, Sum.elim_inl]
  rw [show funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 1 // c.IsEven} → ℂ)
        ⊗[ℂ] (Fin k → ℂ)) _ = 0 from by
    rw [map_zero]; rfl]

private theorem eval2_oo_zero_left (r : ℂ)
    (w z : (stdSuperPair k ℓ).odd)
    (c : MixedColouring k ℓ 2) (hc : c.IsEven)
    (i : Fin k) (b : Fin (2 * ℓ))
    (h0 : c 0 = Sum.inl i) (h1 : c (Fin.last 1) = Sum.inr b) :
    (colourPowerEquiv k ℓ 2).evenEquiv
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even),
        ((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
        (superPow (stdSuperPair k ℓ) 2).even) ⟨c, hc⟩ = 0 := by
  rw [eval2_oo r w z c hc]
  rw [evenSplitD_inr c hc b h1, Sum.elim_inr]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 1).oddEquiv
      (((r ⊗ₜ[ℂ] w, 0) :
        (superPow (stdSuperPair k ℓ) 1).odd)))
      (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact ((c.isEven_succ_right b h1).mp hc) hcontra⟩,
      b).1 =
    0 from eval1_odd_zero r w _ _ i
      (show MixedColouring.tail c (Fin.last 0) =
        Sum.inl i from h0)]
  exact zero_mul _

/-! ### The braid values, in-file encodings -/

private theorem whisker_unit_even' {V W : SuperVect}
    (g : SuperVect.Hom V W) (r : ℂ) (z : V.even) :
    (SuperVect.tensorHom
        (SuperVect.Hom.id SuperVect.tensorUnit) g).evenMap
      ((r ⊗ₜ[ℂ] z, (0 : SuperVect.tensorUnit.odd ⊗[ℂ]
        V.odd))) =
      ((r ⊗ₜ[ℂ] g.evenMap z,
        (0 : SuperVect.tensorUnit.odd ⊗[ℂ] W.odd))) := by
  show (TensorProduct.map
      (SuperVect.Hom.id SuperVect.tensorUnit).evenMap
      g.evenMap (r ⊗ₜ[ℂ] z),
    TensorProduct.map
      (SuperVect.Hom.id SuperVect.tensorUnit).oddMap
      g.oddMap 0) = _
  rw [TensorProduct.map_tmul, map_zero]
  rfl

private theorem neg_pack' {V : SuperVect} (r : ℂ)
    (t : V.odd ⊗[ℂ] V.odd) :
    ((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.even), -t) :
        (SuperVect.tensorObj V V).even)),
      (0 : SuperVect.tensorUnit.odd ⊗[ℂ]
        (SuperVect.tensorObj V V).odd)) =
    -((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.even), t) :
        (SuperVect.tensorObj V V).even)),
      (0 : SuperVect.tensorUnit.odd ⊗[ℂ]
        (SuperVect.tensorObj V V).odd)) := by
  rw [show (((0 : V.even ⊗[ℂ] V.even), -t) :
      (SuperVect.tensorObj V V).even) =
    -(((0 : V.even ⊗[ℂ] V.even), t) :
      (SuperVect.tensorObj V V).even) from by
    rw [Prod.neg_mk, neg_zero]]
  rw [TensorProduct.tmul_neg]
  rw [Prod.neg_mk, neg_zero]

private theorem braid_ee (r : ℂ) (x y : (stdSuperPair k ℓ).even) :
    ((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).evenMap
      (evenPair (evenPair r x) y) =
      evenPair (evenPair r y) x := by
  have hfun : ((topBraid (stdSuperPair k ℓ) 0) :
      SuperVect.Hom _ _).evenMap
      (evenPair (evenPair r x) y) =
    (((α_ (superPow (stdSuperPair k ℓ) 0) (stdSuperPair k ℓ)
        (stdSuperPair k ℓ)).inv : _ ⟶ _) :
        SuperVect.Hom _ _).evenMap
      ((((superPow (stdSuperPair k ℓ) 0) ◁
          (β_ (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom : _ ⟶ _) :
          SuperVect.Hom _ _).evenMap
        ((((α_ (superPow (stdSuperPair k ℓ) 0) (stdSuperPair k ℓ)
            (stdSuperPair k ℓ)).hom : _ ⟶ _) :
            SuperVect.Hom _ _).evenMap
          (evenPair (evenPair r x) y))) := rfl
  rw [hfun]
  refine Eq.trans (congrArg (((α_ (superPow (stdSuperPair k ℓ) 0)
      (stdSuperPair k ℓ) (stdSuperPair k ℓ)).inv : _ ⟶ _) :
      SuperVect.Hom _ _).evenMap
    (Eq.trans (congrArg ((((superPow (stdSuperPair k ℓ) 0) ◁
        (β_ (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom : _ ⟶ _) :
        SuperVect.Hom _ _).evenMap)
      (SuperVect.assoc_unit_ee r x y))
      (Eq.trans (whisker_unit_even'
        (SuperVect.koszulBraiding (stdSuperPair k ℓ)
          (stdSuperPair k ℓ)) r _)
        (congrArg (fun z => (r ⊗ₜ[ℂ] z, 0)) (SuperVect.koszul_ee x y))))) ?_
  exact SuperVect.assoc_unit_inv_ee r y x

private theorem braid_oo (r : ℂ) (w z : (stdSuperPair k ℓ).odd) :
    ((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).evenMap
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even),
        ((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
        (superPow (stdSuperPair k ℓ) 2).even) =
      -((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even),
        ((r ⊗ₜ[ℂ] z, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] w)) :
        (superPow (stdSuperPair k ℓ) 2).even) := by
  have hfun : ((topBraid (stdSuperPair k ℓ) 0) :
      SuperVect.Hom _ _).evenMap
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even),
        ((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
        (superPow (stdSuperPair k ℓ) 2).even) =
    (((α_ (superPow (stdSuperPair k ℓ) 0) (stdSuperPair k ℓ)
        (stdSuperPair k ℓ)).inv : _ ⟶ _) :
        SuperVect.Hom _ _).evenMap
      ((((superPow (stdSuperPair k ℓ) 0) ◁
          (β_ (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom : _ ⟶ _) :
          SuperVect.Hom _ _).evenMap
        ((((α_ (superPow (stdSuperPair k ℓ) 0) (stdSuperPair k ℓ)
            (stdSuperPair k ℓ)).hom : _ ⟶ _) :
            SuperVect.Hom _ _).evenMap
          ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
              (stdSuperPair k ℓ).even),
            ((r ⊗ₜ[ℂ] w, 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
            (superPow (stdSuperPair k ℓ) 2).even))) := rfl
  rw [hfun]
  refine Eq.trans (congrArg (((α_ (superPow (stdSuperPair k ℓ) 0)
      (stdSuperPair k ℓ) (stdSuperPair k ℓ)).inv : _ ⟶ _) :
      SuperVect.Hom _ _).evenMap
    (Eq.trans (congrArg ((((superPow (stdSuperPair k ℓ) 0) ◁
        (β_ (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom : _ ⟶ _) :
        SuperVect.Hom _ _).evenMap)
      (SuperVect.assoc_unit_oo r w z))
      (Eq.trans
        (Eq.trans (whisker_unit_even'
          (SuperVect.koszulBraiding (stdSuperPair k ℓ)
            (stdSuperPair k ℓ)) r _)
          (by rw [SuperVect.koszul_oo]; rfl))
        (neg_pack' r (z ⊗ₜ[ℂ] w))))) ?_
  refine Eq.trans (map_neg _ _) ?_
  exact congrArg Neg.neg
    (SuperVect.assoc_unit_inv_oo r z w)

/-- Pointwise sum on colour functions. -/
private theorem colourFun_add_apply {n : ℕ}
    (F G : (colourPower k ℓ n).even)
    (p : {c : MixedColouring k ℓ n // c.IsEven}) :
    (F + G) p = F p + G p := rfl

/-- Pointwise negation on colour functions. -/
private theorem colourFun_neg_apply {n : ℕ}
    (F : (colourPower k ℓ n).even)
    (p : {c : MixedColouring k ℓ n // c.IsEven}) :
    (-F) p = -(F p) := rfl

/-! ### The even-component coordinate identity -/

-- Raised budget: one coordinate of the Koszul braiding at two
-- strands, elaborated through the colouring equivalence and both
-- tensor decompositions; the term is large, the search is not.
private theorem braid_coord_even
    (c' : MixedColouring k ℓ 2) (hc' : c'.IsEven)
    (v : (superPow (stdSuperPair k ℓ) 2).even) :
    (colourPowerEquiv k ℓ 2).evenEquiv
      (((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).evenMap v) ⟨c', hc'⟩ =
    adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ *
      (colourPowerEquiv k ℓ 2).evenEquiv v
        ⟨c' ∘ _root_.Equiv.swap (⟨0, by omega⟩ : Fin 2)
          ⟨1, by omega⟩, hc'.comp _⟩ := by
  haveI : Subsingleton SuperVect.tensorUnit.odd :=
    inferInstanceAs (Subsingleton PUnit)
  haveI : Subsingleton (superPow (stdSuperPair k ℓ) 0).odd :=
    inferInstanceAs (Subsingleton PUnit)
  -- ═══════ THE PREDICATE, PROVED ADDITIVELY ═══════
  set P : (superPow (stdSuperPair k ℓ) 2).even → Prop :=
    fun u =>
      (colourPowerEquiv k ℓ 2).evenEquiv
        (((topBraid (stdSuperPair k ℓ) 0) :
          SuperVect.Hom _ _).evenMap u) ⟨c', hc'⟩ =
      adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ *
        (colourPowerEquiv k ℓ 2).evenEquiv u
          ⟨c' ∘ _root_.Equiv.swap (⟨0, by omega⟩ : Fin 2)
            ⟨1, by omega⟩, hc'.comp _⟩ with hP
  show P v
  have hswap0 : (c' ∘ _root_.Equiv.swap
      (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩) 0 =
      c' (Fin.last 1) :=
    congrArg c' (_root_.Equiv.swap_apply_left _ _)
  have hswap1 : (c' ∘ _root_.Equiv.swap
      (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩) (Fin.last 1) =
      c' 0 :=
    congrArg c' (_root_.Equiv.swap_apply_right _ _)
  have hP0 : P 0 := by
    rw [hP]
    beta_reduce
    rw [map_zero, map_zero]
    show (0 : ℂ) = _ * (0 : {c : MixedColouring k ℓ 2 //
      c.IsEven} → ℂ) ⟨c' ∘ _root_.Equiv.swap
        (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩, hc'.comp _⟩
    rw [show (0 : {c : MixedColouring k ℓ 2 //
        c.IsEven} → ℂ) ⟨c' ∘ _root_.Equiv.swap
          (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩,
        hc'.comp _⟩ = 0 from rfl]
    rw [mul_zero]
  have hPadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂) := by
    intro u₁ u₂ h₁ h₂
    rw [hP] at h₁ h₂ ⊢
    beta_reduce at h₁ h₂ ⊢
    rw [map_add, map_add, colourFun_add_apply, map_add,
      colourFun_add_apply, h₁, h₂, mul_add]
  -- ═══════ THE EVEN⊗EVEN GENERATORS ═══════
  have hee : ∀ (r : ℂ) (x y : (stdSuperPair k ℓ).even),
      P ((((r ⊗ₜ[ℂ] x, 0) :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y,
        (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).odd))) := by
    intro r x y
    rw [hP]
    beta_reduce
    refine Eq.trans (congrArg
      (fun t => (colourPowerEquiv k ℓ 2).evenEquiv t
        ⟨c', hc'⟩) (braid_ee r x y)) ?_
    rcases hl0 : c' 0 with i | a <;>
      rcases hl1 : c' (Fin.last 1) with j | b
    · refine Eq.trans (eval2_ee_val r y x c' hc' i j
        hl0 hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_ee_val r x y _ (hc'.comp _) j i
          (hswap0.trans hl1) (hswap1.trans hl0)).symm))
      rw [show adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ =
          (1 : ℂ) from if_neg (fun hA => by
        rw [show c' ⟨0, by omega⟩ = Sum.inl i from hl0] at hA
        exact Bool.noConfusion hA.1)]
      ring
    · refine Eq.trans (eval2_ee_zero_right r y x c' hc' b
        hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_ee_zero_left r x y _ (hc'.comp _) i b
          (hswap0.trans hl1) (hswap1.trans hl0)).symm))
      exact (mul_zero _).symm
    · refine Eq.trans (eval2_ee_zero_left r y x c' hc' j a
        hl0 hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_ee_zero_right r x y _ (hc'.comp _) a
          (hswap1.trans hl0)).symm))
      exact (mul_zero _).symm
    · refine Eq.trans (eval2_ee_zero_right r y x c' hc' b
        hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_ee_zero_right r x y _ (hc'.comp _) a
          (hswap1.trans hl0)).symm))
      exact (mul_zero _).symm
  -- ═══════ THE ODD⊗ODD GENERATORS ═══════
  have hoo : ∀ (r : ℂ) (w z : (stdSuperPair k ℓ).odd),
      P (((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).even),
        ((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) := by
    intro r w z
    rw [hP]
    beta_reduce
    refine Eq.trans (congrArg
      (fun t => (colourPowerEquiv k ℓ 2).evenEquiv t
        ⟨c', hc'⟩) (braid_oo r w z)) ?_
    refine Eq.trans (congrArg (fun F => F ⟨c', hc'⟩)
      (map_neg ((colourPowerEquiv k ℓ 2).evenEquiv) _)) ?_
    refine Eq.trans (colourFun_neg_apply _ _) ?_
    rcases hl0 : c' 0 with i | a <;>
      rcases hl1 : c' (Fin.last 1) with j | b
    · refine Eq.trans (congrArg Neg.neg
        (eval2_oo_zero_right r z w c' hc' j hl1))
        (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_oo_zero_right r w z _ (hc'.comp _) i
          (hswap1.trans hl0)).symm))
      rw [mul_zero, neg_zero]
    · refine Eq.trans (congrArg Neg.neg
        (eval2_oo_zero_left r z w c' hc' i b hl0 hl1))
        (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_oo_zero_right r w z _ (hc'.comp _) i
          (hswap1.trans hl0)).symm))
      rw [mul_zero, neg_zero]
    · refine Eq.trans (congrArg Neg.neg
        (eval2_oo_zero_right r z w c' hc' j hl1))
        (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_oo_zero_left r w z _ (hc'.comp _) j a
          (hswap0.trans hl1) (hswap1.trans hl0)).symm))
      rw [mul_zero, neg_zero]
    · refine Eq.trans (congrArg Neg.neg
        (eval2_oo_val r z w c' hc' a b hl0 hl1))
        (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_oo_val r w z _ (hc'.comp _) b a
          (hswap0.trans hl1) (hswap1.trans hl0)).symm))
      rw [show adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ =
          (-1 : ℂ) from if_pos ⟨(by
        rw [show c' ⟨0, by omega⟩ = Sum.inr a from hl0]
        rfl), (by
        rw [show c' ⟨1, by omega⟩ = Sum.inr b from hl1]
        rfl)⟩]
      ring
  -- Assemble by block decomposition and tensor induction.
  obtain ⟨v₁, v₂⟩ := v
  rw [show ((v₁, v₂) : (superPow (stdSuperPair k ℓ) 2).even) =
    (v₁, 0) + (0, v₂) from by
    rw [Prod.mk_add_mk, add_zero, zero_add]]
  refine hPadd _ _ ?_ ?_
  · -- The even-even block.
    induction v₁ using TensorProduct.induction_on with
    | zero => exact hP0
    | add s t hs ht =>
      rw [show ((s + t, 0) :
          (superPow (stdSuperPair k ℓ) 2).even) =
        (s, 0) + (t, 0) from by
        rw [Prod.mk_add_mk, add_zero]]
      exact hPadd _ _ hs ht
    | tmul a y =>
      obtain ⟨a₁, a₂⟩ := a
      have helem : ((((a₁, a₂) :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y,
          0) : (superPow (stdSuperPair k ℓ) 2).even) =
        (((((a₁, 0) :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y, 0)) :
          (superPow (stdSuperPair k ℓ) 2).even) +
        (((((0, a₂) :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y, 0)) :
          (superPow (stdSuperPair k ℓ) 2).even)
        := by
        refine Eq.trans (congrArg (fun t =>
          ((t, (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
            (stdSuperPair k ℓ).odd)) :
            (superPow (stdSuperPair k ℓ) 2).even))
          (Eq.trans (congrArg (fun s =>
              s ⊗ₜ[ℂ] y)
            (show ((a₁, a₂) :
                (superPow (stdSuperPair k ℓ) 1).even) =
              ((a₁, 0) : (superPow (stdSuperPair k ℓ) 1).even) +
              ((0, a₂) : (superPow (stdSuperPair k ℓ) 1).even)
              from by rw [Prod.mk_add_mk, add_zero,
                zero_add]))
            (TensorProduct.add_tmul
              (((a₁, 0) :
                (superPow (stdSuperPair k ℓ) 1).even))
              (((0, a₂) :
                (superPow (stdSuperPair k ℓ) 1).even)) y))) ?_
        exact Prod.ext_iff.mpr ⟨rfl, (add_zero 0).symm⟩
      refine Eq.mpr (congrArg P helem) (hPadd _ _ ?_ ?_)
      · clear helem
        induction a₁ using TensorProduct.induction_on with
        | zero =>
          have h0elem : (((((0 :
              (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
              (stdSuperPair k ℓ).even), 0) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y,
              0) : (superPow (stdSuperPair k ℓ) 2).even) =
              0 := by
            refine Eq.trans (congrArg (fun t =>
              ((t, (0 : (superPow (stdSuperPair k ℓ) 1).odd
                ⊗[ℂ] (stdSuperPair k ℓ).odd)) :
                (superPow (stdSuperPair k ℓ) 2).even))
              (show ((((0 :
                  (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                  (stdSuperPair k ℓ).even), 0) :
                (superPow (stdSuperPair k ℓ) 1).even))
                ⊗ₜ[ℂ] y = 0 from
                TensorProduct.zero_tmul _ y)) ?_
            exact Prod.ext_iff.mpr ⟨rfl, rfl⟩
          exact Eq.mpr (congrArg P h0elem) hP0
        | add s t hs ht =>
          have helem : (((((s + t :
              (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
              (stdSuperPair k ℓ).even), 0) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y,
              0) : (superPow (stdSuperPair k ℓ) 2).even) =
            ((((s, 0) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y,
              0) : (superPow (stdSuperPair k ℓ) 2).even) +
            (((((t, 0) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y,
              0)) : (superPow (stdSuperPair k ℓ) 2).even) := by
            refine Eq.trans (congrArg (fun u =>
              ((u, (0 : (superPow (stdSuperPair k ℓ) 1).odd
                ⊗[ℂ] (stdSuperPair k ℓ).odd)) :
                (superPow (stdSuperPair k ℓ) 2).even))
              (Eq.trans (congrArg (fun w => w ⊗ₜ[ℂ] y)
                (show (((s + t :
                    (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                    (stdSuperPair k ℓ).even), 0) :
                  (superPow (stdSuperPair k ℓ) 1).even) =
                  ((s, 0) :
                    (superPow (stdSuperPair k ℓ) 1).even) +
                  ((t, 0) :
                    (superPow (stdSuperPair k ℓ) 1).even)
                  from by rw [Prod.mk_add_mk, add_zero]))
                (TensorProduct.add_tmul
                  (((s, 0) :
                    (superPow (stdSuperPair k ℓ) 1).even))
                  (((t, 0) :
                    (superPow (stdSuperPair k ℓ) 1).even))
                  y))) ?_
            exact Prod.ext_iff.mpr ⟨rfl, (add_zero 0).symm⟩
          exact Eq.mpr (congrArg P helem) (hPadd _ _ hs ht)
        | tmul r x => exact hee r x y
      · have h0elem : (((((0 :
            (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
            (stdSuperPair k ℓ).even), a₂) :
            (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y,
            0) : (superPow (stdSuperPair k ℓ) 2).even) =
            0 := by
          refine Eq.trans (congrArg (fun t =>
            ((((((0 : (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                (stdSuperPair k ℓ).even), t) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] y),
              (0 : (superPow (stdSuperPair k ℓ) 1).odd
                ⊗[ℂ] (stdSuperPair k ℓ).odd)) :
              (superPow (stdSuperPair k ℓ) 2).even))
            (subsingleton_tmul_eq_zero a₂)) ?_
          refine Eq.trans (congrArg (fun t =>
            ((t, (0 : (superPow (stdSuperPair k ℓ) 1).odd
              ⊗[ℂ] (stdSuperPair k ℓ).odd)) :
              (superPow (stdSuperPair k ℓ) 2).even))
            (show ((((0 :
                (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                (stdSuperPair k ℓ).even), (0 :
                (superPow (stdSuperPair k ℓ) 0).odd ⊗[ℂ]
                (stdSuperPair k ℓ).odd)) :
              (superPow (stdSuperPair k ℓ) 1).even))
              ⊗ₜ[ℂ] y = 0 from
              TensorProduct.zero_tmul _ y)) ?_
          exact Prod.ext_iff.mpr ⟨rfl, rfl⟩
        exact Eq.mpr (congrArg P h0elem) hP0
  · -- The odd-odd block.
    induction v₂ using TensorProduct.induction_on with
    | zero => exact hP0
    | add s t hs ht =>
      rw [show ((0, s + t) :
          (superPow (stdSuperPair k ℓ) 2).even) =
        (0, s) + (0, t) from by
        rw [Prod.mk_add_mk, add_zero]]
      exact hPadd _ _ hs ht
    | tmul b z =>
      obtain ⟨b₁, b₂⟩ := b
      have helem : ((0, (((b₁, b₂) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
          (superPow (stdSuperPair k ℓ) 2).even) =
        (((0, (((b₁, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z))) :
          (superPow (stdSuperPair k ℓ) 2).even) +
        (((0, (((0, b₂) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z))) :
          (superPow (stdSuperPair k ℓ) 2).even)
        := by
        refine Eq.trans (congrArg (fun t =>
          (((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
            (stdSuperPair k ℓ).even), t) :
            (superPow (stdSuperPair k ℓ) 2).even))
          (Eq.trans (congrArg (fun s =>
              s ⊗ₜ[ℂ] z)
            (show ((b₁, b₂) :
                (superPow (stdSuperPair k ℓ) 1).odd) =
              ((b₁, 0) : (superPow (stdSuperPair k ℓ) 1).odd) +
              ((0, b₂) : (superPow (stdSuperPair k ℓ) 1).odd)
              from by rw [Prod.mk_add_mk, add_zero,
                zero_add]))
            (TensorProduct.add_tmul
              (((b₁, 0) :
                (superPow (stdSuperPair k ℓ) 1).odd))
              (((0, b₂) :
                (superPow (stdSuperPair k ℓ) 1).odd)) z))) ?_
        exact Prod.ext_iff.mpr ⟨(add_zero 0).symm, rfl⟩
      refine Eq.mpr (congrArg P helem) (hPadd _ _ ?_ ?_)
      · clear helem
        induction b₁ using TensorProduct.induction_on with
        | zero =>
          have h0elem : ((0, ((((0 :
              (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
              (stdSuperPair k ℓ).odd), 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
              (superPow (stdSuperPair k ℓ) 2).even) = 0 := by
            refine Eq.trans (congrArg (fun t =>
              (((0 : (superPow (stdSuperPair k ℓ) 1).even
                ⊗[ℂ] (stdSuperPair k ℓ).even), t) :
                (superPow (stdSuperPair k ℓ) 2).even))
              (show ((((0 :
                  (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                  (stdSuperPair k ℓ).odd), 0) :
                (superPow (stdSuperPair k ℓ) 1).odd))
                ⊗ₜ[ℂ] z = 0 from
                TensorProduct.zero_tmul _ z)) ?_
            exact Prod.ext_iff.mpr ⟨rfl, rfl⟩
          exact Eq.mpr (congrArg P h0elem) hP0
        | add s t hs ht =>
          have helem : ((0, ((((s + t :
              (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
              (stdSuperPair k ℓ).odd), 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
              (superPow (stdSuperPair k ℓ) 2).even) =
            (((0, (((s, 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z))) :
              (superPow (stdSuperPair k ℓ) 2).even) +
            (((0, (((t, 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z))) :
              (superPow (stdSuperPair k ℓ) 2).even)
            := by
            refine Eq.trans (congrArg (fun u =>
              (((0 : (superPow (stdSuperPair k ℓ) 1).even
                ⊗[ℂ] (stdSuperPair k ℓ).even), u) :
                (superPow (stdSuperPair k ℓ) 2).even))
              (Eq.trans (congrArg (fun w =>
                  w ⊗ₜ[ℂ] z)
                (show (((s + t :
                    (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                    (stdSuperPair k ℓ).odd), 0) :
                  (superPow (stdSuperPair k ℓ) 1).odd) =
                  ((s, 0) :
                    (superPow (stdSuperPair k ℓ) 1).odd) +
                  ((t, 0) :
                    (superPow (stdSuperPair k ℓ) 1).odd)
                  from by rw [Prod.mk_add_mk, add_zero]))
                (TensorProduct.add_tmul
                  (((s, 0) :
                    (superPow (stdSuperPair k ℓ) 1).odd))
                  (((t, 0) :
                    (superPow (stdSuperPair k ℓ) 1).odd))
                  z))) ?_
            exact Prod.ext_iff.mpr ⟨(add_zero 0).symm, rfl⟩
          exact Eq.mpr (congrArg P helem) (hPadd _ _ hs ht)
        | tmul r w => exact hoo r w z
      · have h0elem : ((0, ((((0 :
            (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
            (stdSuperPair k ℓ).odd), b₂) :
            (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
            (superPow (stdSuperPair k ℓ) 2).even) = 0 := by
          refine Eq.trans (congrArg (fun t =>
            (((0 : (superPow (stdSuperPair k ℓ) 1).even
              ⊗[ℂ] (stdSuperPair k ℓ).even),
              ((((0 : (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                (stdSuperPair k ℓ).odd), t) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] z)) :
              (superPow (stdSuperPair k ℓ) 2).even))
            (subsingleton_tmul_eq_zero b₂)) ?_
          refine Eq.trans (congrArg (fun t =>
            (((0 : (superPow (stdSuperPair k ℓ) 1).even
              ⊗[ℂ] (stdSuperPair k ℓ).even), t) :
              (superPow (stdSuperPair k ℓ) 2).even))
            (show ((((0 :
                (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                (stdSuperPair k ℓ).odd), (0 :
                (superPow (stdSuperPair k ℓ) 0).odd ⊗[ℂ]
                (stdSuperPair k ℓ).even)) :
              (superPow (stdSuperPair k ℓ) 1).odd))
              ⊗ₜ[ℂ] z = 0 from
              TensorProduct.zero_tmul _ z)) ?_
          exact Prod.ext_iff.mpr ⟨rfl, rfl⟩
        exact Eq.mpr (congrArg P h0elem) hP0

/-! ### Arity-two evaluations, odd component -/

private theorem eval2_eo (r : ℂ) (x : (stdSuperPair k ℓ).even)
    (w : (stdSuperPair k ℓ).odd)
    (c : MixedColouring k ℓ 2) (hc : ¬ c.IsEven) :
    (colourPowerEquiv k ℓ 2).oddEquiv
      ((((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
        (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even))) :
        (superPow (stdSuperPair k ℓ) 2).odd) ⟨c, hc⟩ =
    Sum.elim
      (fun p => funTensorFun _ _
        (((colourPowerEquiv k ℓ 1).evenEquiv
            (evenPair r x)) ⊗ₜ[ℂ]
          (LinearEquiv.refl ℂ (Fin (2 * ℓ) → ℂ) w)) p)
      (fun q => funTensorFun _ _
        (0 : ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} → ℂ)
          ⊗[ℂ] (Fin k → ℂ)) q)
      ((Equiv.sumComm _ _).symm
        (oddSplitEquiv k ℓ 1 ⟨c, hc⟩)) := by
  show (colourPowerStep k ℓ 1).oddEquiv
    ((TensorProduct.congr
        (colourPowerEquiv k ℓ 1).evenEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd))
      (((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w :
        (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd)),
      (TensorProduct.congr
        (colourPowerEquiv k ℓ 1).oddEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even)) 0)
    ⟨c, hc⟩ = _
  have hcongr : (TensorProduct.congr
      (colourPowerEquiv k ℓ 1).evenEquiv
      (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd))
      (((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w :
        (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd)) =
    ((colourPowerEquiv k ℓ 1).evenEquiv
      (evenPair r x)) ⊗ₜ[ℂ] w :=
    Eq.trans (TensorProduct.congr_tmul _ _ _ _) (by rfl)
  rw [hcongr, map_zero]
  rfl

private theorem eval2_eo_val (r : ℂ)
    (x : (stdSuperPair k ℓ).even) (w : (stdSuperPair k ℓ).odd)
    (c : MixedColouring k ℓ 2) (hc : ¬ c.IsEven)
    (i : Fin k) (b : Fin (2 * ℓ))
    (h0 : c 0 = Sum.inl i) (h1 : c (Fin.last 1) = Sum.inr b) :
    (colourPowerEquiv k ℓ 2).oddEquiv
      ((((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
        (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even))) :
        (superPow (stdSuperPair k ℓ) 2).odd) ⟨c, hc⟩ =
    r * x i * w b := by
  rw [eval2_eo r x w c hc]
  rw [oddSplitD_inr c hc b h1]
  rw [show ((Equiv.sumComm
      ({c : MixedColouring k ℓ 1 // c.IsEven} ×
        Fin (2 * ℓ))
      ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} ×
        Fin k)).symm
      (Sum.inr (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact hc ((c.isEven_succ_right b h1).mpr
          hcontra)⟩, b))) =
    Sum.inl (⟨MixedColouring.tail c, by
      by_contra hcontra
      exact hc ((c.isEven_succ_right b h1).mpr
        hcontra)⟩, b) from rfl]
  rw [Sum.elim_inl]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 1).evenEquiv
      (evenPair r x))
      (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact hc ((c.isEven_succ_right b h1).mpr
          hcontra)⟩, b).1 =
    r * x i from eval1_even_inl r x _ _ i
      (show MixedColouring.tail c (Fin.last 0) =
        Sum.inl i from h0)]
  rfl

private theorem eval2_eo_zero_right (r : ℂ)
    (x : (stdSuperPair k ℓ).even) (w : (stdSuperPair k ℓ).odd)
    (c : MixedColouring k ℓ 2) (hc : ¬ c.IsEven)
    (j : Fin k) (h1 : c (Fin.last 1) = Sum.inl j) :
    (colourPowerEquiv k ℓ 2).oddEquiv
      ((((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
        (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even))) :
        (superPow (stdSuperPair k ℓ) 2).odd) ⟨c, hc⟩ = 0 := by
  rw [eval2_eo r x w c hc]
  rw [oddSplitD_inl c hc j h1]
  rw [show ((Equiv.sumComm
      ({c : MixedColouring k ℓ 1 // c.IsEven} ×
        Fin (2 * ℓ))
      ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} ×
        Fin k)).symm
      (Sum.inl (⟨MixedColouring.tail c, by
        intro hcontra
        exact hc ((c.isEven_succ_left j h1).mpr
          hcontra)⟩, j))) =
    Sum.inr (⟨MixedColouring.tail c, by
      intro hcontra
      exact hc ((c.isEven_succ_left j h1).mpr
        hcontra)⟩, j) from rfl]
  rw [Sum.elim_inr]
  rw [show funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} → ℂ)
        ⊗[ℂ] (Fin k → ℂ)) _ = 0 from by
    rw [map_zero]; rfl]

private theorem eval2_eo_zero_left (r : ℂ)
    (x : (stdSuperPair k ℓ).even) (w : (stdSuperPair k ℓ).odd)
    (c : MixedColouring k ℓ 2) (hc : ¬ c.IsEven)
    (a b : Fin (2 * ℓ))
    (h0 : c 0 = Sum.inr a) (h1 : c (Fin.last 1) = Sum.inr b) :
    (colourPowerEquiv k ℓ 2).oddEquiv
      ((((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
        (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even))) :
        (superPow (stdSuperPair k ℓ) 2).odd) ⟨c, hc⟩ = 0 := by
  rw [eval2_eo r x w c hc]
  rw [oddSplitD_inr c hc b h1]
  rw [show ((Equiv.sumComm
      ({c : MixedColouring k ℓ 1 // c.IsEven} ×
        Fin (2 * ℓ))
      ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} ×
        Fin k)).symm
      (Sum.inr (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact hc ((c.isEven_succ_right b h1).mpr
          hcontra)⟩, b))) =
    Sum.inl (⟨MixedColouring.tail c, by
      by_contra hcontra
      exact hc ((c.isEven_succ_right b h1).mpr
        hcontra)⟩, b) from rfl]
  rw [Sum.elim_inl]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 1).evenEquiv
      (evenPair r x))
      (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact hc ((c.isEven_succ_right b h1).mpr
          hcontra)⟩, b).1 =
    0 from eval1_even_zero r x _ _ a
      (show MixedColouring.tail c (Fin.last 0) =
        Sum.inr a from h0)]
  exact zero_mul _

private theorem eval2_oe (r : ℂ) (u : (stdSuperPair k ℓ).odd)
    (y : (stdSuperPair k ℓ).even)
    (c : MixedColouring k ℓ 2) (hc : ¬ c.IsEven) :
    (colourPowerEquiv k ℓ 2).oddEquiv
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd),
        ((r ⊗ₜ[ℂ] u, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
        (superPow (stdSuperPair k ℓ) 2).odd) ⟨c, hc⟩ =
    Sum.elim
      (fun p => funTensorFun _ _
        (0 : ({c : MixedColouring k ℓ 1 // c.IsEven} → ℂ)
          ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) p)
      (fun q => funTensorFun _ _
        (((colourPowerEquiv k ℓ 1).oddEquiv
            (((r ⊗ₜ[ℂ] u, 0) :
              (superPow (stdSuperPair k ℓ) 1).odd))) ⊗ₜ[ℂ]
          (LinearEquiv.refl ℂ (Fin k → ℂ) y)) q)
      ((Equiv.sumComm _ _).symm
        (oddSplitEquiv k ℓ 1 ⟨c, hc⟩)) := by
  show (colourPowerStep k ℓ 1).oddEquiv
    ((TensorProduct.congr
        (colourPowerEquiv k ℓ 1).evenEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).odd))
      (0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
        (stdSuperPair k ℓ).odd),
      (TensorProduct.congr
        (colourPowerEquiv k ℓ 1).oddEquiv
        (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even))
      ((((r ⊗ₜ[ℂ] u, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y :
        (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even)))
    ⟨c, hc⟩ = _
  have hcongr : (TensorProduct.congr
      (colourPowerEquiv k ℓ 1).oddEquiv
      (LinearEquiv.refl ℂ (stdSuperPair k ℓ).even))
      ((((r ⊗ₜ[ℂ] u, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y :
        (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even)) =
    ((colourPowerEquiv k ℓ 1).oddEquiv
      (((r ⊗ₜ[ℂ] u, 0) :
        (superPow (stdSuperPair k ℓ) 1).odd))) ⊗ₜ[ℂ] y :=
    Eq.trans (TensorProduct.congr_tmul _ _ _ _) (by rfl)
  rw [hcongr, map_zero]
  rfl

private theorem eval2_oe_val (r : ℂ)
    (u : (stdSuperPair k ℓ).odd) (y : (stdSuperPair k ℓ).even)
    (c : MixedColouring k ℓ 2) (hc : ¬ c.IsEven)
    (a : Fin (2 * ℓ)) (j : Fin k)
    (h0 : c 0 = Sum.inr a) (h1 : c (Fin.last 1) = Sum.inl j) :
    (colourPowerEquiv k ℓ 2).oddEquiv
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd),
        ((r ⊗ₜ[ℂ] u, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
        (superPow (stdSuperPair k ℓ) 2).odd) ⟨c, hc⟩ =
    r * u a * y j := by
  rw [eval2_oe r u y c hc]
  rw [oddSplitD_inl c hc j h1]
  rw [show ((Equiv.sumComm
      ({c : MixedColouring k ℓ 1 // c.IsEven} ×
        Fin (2 * ℓ))
      ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} ×
        Fin k)).symm
      (Sum.inl (⟨MixedColouring.tail c, by
        intro hcontra
        exact hc ((c.isEven_succ_left j h1).mpr
          hcontra)⟩, j))) =
    Sum.inr (⟨MixedColouring.tail c, by
      intro hcontra
      exact hc ((c.isEven_succ_left j h1).mpr
        hcontra)⟩, j) from rfl]
  rw [Sum.elim_inr]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 1).oddEquiv
      (((r ⊗ₜ[ℂ] u, 0) :
        (superPow (stdSuperPair k ℓ) 1).odd)))
      (⟨MixedColouring.tail c, by
        intro hcontra
        exact hc ((c.isEven_succ_left j h1).mpr
          hcontra)⟩, j).1 =
    r * u a from eval1_odd_inr r u _ _ a
      (show MixedColouring.tail c (Fin.last 0) =
        Sum.inr a from h0)]
  rfl

private theorem eval2_oe_zero_right (r : ℂ)
    (u : (stdSuperPair k ℓ).odd) (y : (stdSuperPair k ℓ).even)
    (c : MixedColouring k ℓ 2) (hc : ¬ c.IsEven)
    (b : Fin (2 * ℓ)) (h1 : c (Fin.last 1) = Sum.inr b) :
    (colourPowerEquiv k ℓ 2).oddEquiv
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd),
        ((r ⊗ₜ[ℂ] u, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
        (superPow (stdSuperPair k ℓ) 2).odd) ⟨c, hc⟩ = 0 := by
  rw [eval2_oe r u y c hc]
  rw [oddSplitD_inr c hc b h1]
  rw [show ((Equiv.sumComm
      ({c : MixedColouring k ℓ 1 // c.IsEven} ×
        Fin (2 * ℓ))
      ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} ×
        Fin k)).symm
      (Sum.inr (⟨MixedColouring.tail c, by
        by_contra hcontra
        exact hc ((c.isEven_succ_right b h1).mpr
          hcontra)⟩, b))) =
    Sum.inl (⟨MixedColouring.tail c, by
      by_contra hcontra
      exact hc ((c.isEven_succ_right b h1).mpr
        hcontra)⟩, b) from rfl]
  rw [Sum.elim_inl]
  rw [show funTensorFun _ _
      (0 : ({c : MixedColouring k ℓ 1 // c.IsEven} → ℂ)
        ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) _ = 0 from by
    rw [map_zero]; rfl]

private theorem eval2_oe_zero_left (r : ℂ)
    (u : (stdSuperPair k ℓ).odd) (y : (stdSuperPair k ℓ).even)
    (c : MixedColouring k ℓ 2) (hc : ¬ c.IsEven)
    (i j : Fin k)
    (h0 : c 0 = Sum.inl i) (h1 : c (Fin.last 1) = Sum.inl j) :
    (colourPowerEquiv k ℓ 2).oddEquiv
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd),
        ((r ⊗ₜ[ℂ] u, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
        (superPow (stdSuperPair k ℓ) 2).odd) ⟨c, hc⟩ = 0 := by
  rw [eval2_oe r u y c hc]
  rw [oddSplitD_inl c hc j h1]
  rw [show ((Equiv.sumComm
      ({c : MixedColouring k ℓ 1 // c.IsEven} ×
        Fin (2 * ℓ))
      ({c : MixedColouring k ℓ 1 // ¬ c.IsEven} ×
        Fin k)).symm
      (Sum.inl (⟨MixedColouring.tail c, by
        intro hcontra
        exact hc ((c.isEven_succ_left j h1).mpr
          hcontra)⟩, j))) =
    Sum.inr (⟨MixedColouring.tail c, by
      intro hcontra
      exact hc ((c.isEven_succ_left j h1).mpr
        hcontra)⟩, j) from rfl]
  rw [Sum.elim_inr]
  refine Eq.trans (funTensorFun_tmul _ _ _) ?_
  rw [show ((colourPowerEquiv k ℓ 1).oddEquiv
      (((r ⊗ₜ[ℂ] u, 0) :
        (superPow (stdSuperPair k ℓ) 1).odd)))
      (⟨MixedColouring.tail c, by
        intro hcontra
        exact hc ((c.isEven_succ_left j h1).mpr
          hcontra)⟩, j).1 =
    0 from eval1_odd_zero r u _ _ i
      (show MixedColouring.tail c (Fin.last 0) =
        Sum.inl i from h0)]
  exact zero_mul _

/-! ### The odd braid values and coordinate identity -/

private theorem whisker_unit_odd' {V W : SuperVect}
    (g : SuperVect.Hom V W) (r : ℂ) (z : V.odd) :
    (SuperVect.tensorHom
        (SuperVect.Hom.id SuperVect.tensorUnit) g).oddMap
      ((r ⊗ₜ[ℂ] z, (0 : SuperVect.tensorUnit.odd ⊗[ℂ]
        V.even))) =
      ((r ⊗ₜ[ℂ] g.oddMap z,
        (0 : SuperVect.tensorUnit.odd ⊗[ℂ] W.even))) := by
  show (TensorProduct.map
      (SuperVect.Hom.id SuperVect.tensorUnit).evenMap
      g.oddMap (r ⊗ₜ[ℂ] z),
    TensorProduct.map
      (SuperVect.Hom.id SuperVect.tensorUnit).oddMap
      g.evenMap 0) = _
  rw [TensorProduct.map_tmul, map_zero]
  rfl

private theorem braid_eo (r : ℂ) (x : (stdSuperPair k ℓ).even)
    (w : (stdSuperPair k ℓ).odd) :
    ((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).oddMap
      ((((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
        (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even))) :
        (superPow (stdSuperPair k ℓ) 2).odd) =
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd),
        ((r ⊗ₜ[ℂ] w, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] x)) :
        (superPow (stdSuperPair k ℓ) 2).odd) := by
  have hfun : ((topBraid (stdSuperPair k ℓ) 0) :
      SuperVect.Hom _ _).oddMap
      ((((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
        (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even))) :
        (superPow (stdSuperPair k ℓ) 2).odd) =
    (((α_ (superPow (stdSuperPair k ℓ) 0) (stdSuperPair k ℓ)
        (stdSuperPair k ℓ)).inv : _ ⟶ _) :
        SuperVect.Hom _ _).oddMap
      ((((superPow (stdSuperPair k ℓ) 0) ◁
          (β_ (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom : _ ⟶ _) :
          SuperVect.Hom _ _).oddMap
        ((((α_ (superPow (stdSuperPair k ℓ) 0) (stdSuperPair k ℓ)
            (stdSuperPair k ℓ)).hom : _ ⟶ _) :
            SuperVect.Hom _ _).oddMap
          ((((evenPair r x :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
            (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
              (stdSuperPair k ℓ).even))) :
            (superPow (stdSuperPair k ℓ) 2).odd))) := rfl
  rw [hfun]
  refine Eq.trans (congrArg (((α_ (superPow (stdSuperPair k ℓ) 0)
      (stdSuperPair k ℓ) (stdSuperPair k ℓ)).inv : _ ⟶ _) :
      SuperVect.Hom _ _).oddMap
    (Eq.trans (congrArg ((((superPow (stdSuperPair k ℓ) 0) ◁
        (β_ (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom : _ ⟶ _) :
        SuperVect.Hom _ _).oddMap)
      (SuperVect.assoc_unit_eo r x w))
      (Eq.trans (whisker_unit_odd'
        (SuperVect.koszulBraiding (stdSuperPair k ℓ)
          (stdSuperPair k ℓ)) r _)
        (congrArg (fun z => (r ⊗ₜ[ℂ] z, 0)) (SuperVect.koszul_eo x w))))) ?_
  exact SuperVect.assoc_unit_inv_oe r w x

private theorem braid_oe (r : ℂ) (u : (stdSuperPair k ℓ).odd)
    (y : (stdSuperPair k ℓ).even) :
    ((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).oddMap
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd),
        ((r ⊗ₜ[ℂ] u, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
        (superPow (stdSuperPair k ℓ) 2).odd) =
      ((((evenPair r y :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] u,
        (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even))) :
        (superPow (stdSuperPair k ℓ) 2).odd) := by
  have hfun : ((topBraid (stdSuperPair k ℓ) 0) :
      SuperVect.Hom _ _).oddMap
      ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd),
        ((r ⊗ₜ[ℂ] u, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
        (superPow (stdSuperPair k ℓ) 2).odd) =
    (((α_ (superPow (stdSuperPair k ℓ) 0) (stdSuperPair k ℓ)
        (stdSuperPair k ℓ)).inv : _ ⟶ _) :
        SuperVect.Hom _ _).oddMap
      ((((superPow (stdSuperPair k ℓ) 0) ◁
          (β_ (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom : _ ⟶ _) :
          SuperVect.Hom _ _).oddMap
        ((((α_ (superPow (stdSuperPair k ℓ) 0) (stdSuperPair k ℓ)
            (stdSuperPair k ℓ)).hom : _ ⟶ _) :
            SuperVect.Hom _ _).oddMap
          ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
              (stdSuperPair k ℓ).odd),
            ((r ⊗ₜ[ℂ] u, 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
            (superPow (stdSuperPair k ℓ) 2).odd))) := rfl
  rw [hfun]
  refine Eq.trans (congrArg (((α_ (superPow (stdSuperPair k ℓ) 0)
      (stdSuperPair k ℓ) (stdSuperPair k ℓ)).inv : _ ⟶ _) :
      SuperVect.Hom _ _).oddMap
    (Eq.trans (congrArg ((((superPow (stdSuperPair k ℓ) 0) ◁
        (β_ (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom : _ ⟶ _) :
        SuperVect.Hom _ _).oddMap)
      (SuperVect.assoc_unit_oe r u y))
      (Eq.trans (whisker_unit_odd'
        (SuperVect.koszulBraiding (stdSuperPair k ℓ)
          (stdSuperPair k ℓ)) r _)
        (congrArg (fun z => (r ⊗ₜ[ℂ] z, 0)) (SuperVect.koszul_oe u y))))) ?_
  exact SuperVect.assoc_unit_inv_eo r y u

/-- Pointwise sum on odd colour functions. -/
private theorem colourFunO_add_apply {n : ℕ}
    (F G : (colourPower k ℓ n).odd)
    (p : {c : MixedColouring k ℓ n // ¬ c.IsEven}) :
    (F + G) p = F p + G p := rfl

-- As for the even component: the same two-strand coordinate
-- elaborated through the odd half of the colouring equivalence.
private theorem braid_coord_odd
    (c' : MixedColouring k ℓ 2) (hc' : ¬ c'.IsEven)
    (v : (superPow (stdSuperPair k ℓ) 2).odd) :
    (colourPowerEquiv k ℓ 2).oddEquiv
      (((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).oddMap v) ⟨c', hc'⟩ =
    adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ *
      (colourPowerEquiv k ℓ 2).oddEquiv v
        ⟨c' ∘ _root_.Equiv.swap (⟨0, by omega⟩ : Fin 2)
          ⟨1, by omega⟩,
        MixedColouring.not_isEven_comp hc' _⟩ := by
  haveI : Subsingleton SuperVect.tensorUnit.odd :=
    inferInstanceAs (Subsingleton PUnit)
  haveI : Subsingleton (superPow (stdSuperPair k ℓ) 0).odd :=
    inferInstanceAs (Subsingleton PUnit)
  -- ═══════ THE PREDICATE, PROVED ADDITIVELY ═══════
  set P : (superPow (stdSuperPair k ℓ) 2).odd → Prop :=
    fun u =>
      (colourPowerEquiv k ℓ 2).oddEquiv
        (((topBraid (stdSuperPair k ℓ) 0) :
          SuperVect.Hom _ _).oddMap u) ⟨c', hc'⟩ =
      adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ *
        (colourPowerEquiv k ℓ 2).oddEquiv u
          ⟨c' ∘ _root_.Equiv.swap (⟨0, by omega⟩ : Fin 2)
            ⟨1, by omega⟩,
          MixedColouring.not_isEven_comp hc' _⟩ with hP
  show P v
  have hswap0 : (c' ∘ _root_.Equiv.swap
      (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩) 0 =
      c' (Fin.last 1) :=
    congrArg c' (_root_.Equiv.swap_apply_left _ _)
  have hswap1 : (c' ∘ _root_.Equiv.swap
      (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩) (Fin.last 1) =
      c' 0 :=
    congrArg c' (_root_.Equiv.swap_apply_right _ _)
  have hP0 : P 0 := by
    rw [hP]
    beta_reduce
    rw [map_zero, map_zero]
    show (0 : ℂ) = _ * (0 : {c : MixedColouring k ℓ 2 //
      ¬ c.IsEven} → ℂ) ⟨c' ∘ _root_.Equiv.swap
        (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩,
      MixedColouring.not_isEven_comp hc' _⟩
    rw [show (0 : {c : MixedColouring k ℓ 2 //
        ¬ c.IsEven} → ℂ) ⟨c' ∘ _root_.Equiv.swap
          (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩,
        MixedColouring.not_isEven_comp hc' _⟩ = 0 from rfl]
    rw [mul_zero]
  have hPadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂) := by
    intro u₁ u₂ h₁ h₂
    rw [hP] at h₁ h₂ ⊢
    beta_reduce at h₁ h₂ ⊢
    rw [map_add, map_add, colourFunO_add_apply, map_add,
      colourFunO_add_apply, h₁, h₂, mul_add]
  -- ═══════ THE EVEN⊗ODD GENERATORS ═══════
  have heo : ∀ (r : ℂ) (x : (stdSuperPair k ℓ).even)
      (w : (stdSuperPair k ℓ).odd),
      P ((((evenPair r x :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
        (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even)))) := by
    intro r x w
    rw [hP]
    beta_reduce
    refine Eq.trans (congrArg
      (fun t => (colourPowerEquiv k ℓ 2).oddEquiv t
        ⟨c', hc'⟩) (braid_eo r x w)) ?_
    rcases hl0 : c' 0 with i | a <;>
      rcases hl1 : c' (Fin.last 1) with j | b
    · refine Eq.trans (eval2_oe_zero_left r w x c' hc' i j
        hl0 hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_eo_zero_right r x w _
          (MixedColouring.not_isEven_comp hc' _) i
          (hswap1.trans hl0)).symm))
      exact (mul_zero _).symm
    · refine Eq.trans (eval2_oe_zero_right r w x c' hc' b
        hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_eo_zero_right r x w _
          (MixedColouring.not_isEven_comp hc' _) i
          (hswap1.trans hl0)).symm))
      exact (mul_zero _).symm
    · refine Eq.trans (eval2_oe_val r w x c' hc' a j
        hl0 hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_eo_val r x w _
          (MixedColouring.not_isEven_comp hc' _) j a
          (hswap0.trans hl1) (hswap1.trans hl0)).symm))
      rw [show adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ =
          (1 : ℂ) from if_neg (fun hA => by
        rw [show c' ⟨1, by omega⟩ = Sum.inl j from hl1] at hA
        exact Bool.noConfusion hA.2)]
      ring
    · refine Eq.trans (eval2_oe_zero_right r w x c' hc' b
        hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_eo_zero_left r x w _
          (MixedColouring.not_isEven_comp hc' _) b a
          (hswap0.trans hl1) (hswap1.trans hl0)).symm))
      exact (mul_zero _).symm
  -- ═══════ THE ODD⊗EVEN GENERATORS ═══════
  have hoe : ∀ (r : ℂ) (u : (stdSuperPair k ℓ).odd)
      (y : (stdSuperPair k ℓ).even),
      P ((((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd),
        ((r ⊗ₜ[ℂ] u, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y))) := by
    intro r u y
    rw [hP]
    beta_reduce
    refine Eq.trans (congrArg
      (fun t => (colourPowerEquiv k ℓ 2).oddEquiv t
        ⟨c', hc'⟩) (braid_oe r u y)) ?_
    rcases hl0 : c' 0 with i | a <;>
      rcases hl1 : c' (Fin.last 1) with j | b
    · refine Eq.trans (eval2_eo_zero_right r y u c' hc' j
        hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_oe_zero_left r u y _
          (MixedColouring.not_isEven_comp hc' _) j i
          (hswap0.trans hl1) (hswap1.trans hl0)).symm))
      exact (mul_zero _).symm
    · refine Eq.trans (eval2_eo_val r y u c' hc' i b
        hl0 hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_oe_val r u y _
          (MixedColouring.not_isEven_comp hc' _) b i
          (hswap0.trans hl1) (hswap1.trans hl0)).symm))
      rw [show adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ =
          (1 : ℂ) from if_neg (fun hA => by
        rw [show c' ⟨0, by omega⟩ = Sum.inl i from hl0] at hA
        exact Bool.noConfusion hA.1)]
      ring
    · refine Eq.trans (eval2_eo_zero_right r y u c' hc' j
        hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_oe_zero_right r u y _
          (MixedColouring.not_isEven_comp hc' _) a
          (hswap1.trans hl0)).symm))
      exact (mul_zero _).symm
    · refine Eq.trans (eval2_eo_zero_left r y u c' hc' a b
        hl0 hl1) (Eq.trans ?_ (congrArg
        (fun t => adjSign c' ⟨0, by omega⟩ ⟨1, by omega⟩ * t)
        (eval2_oe_zero_right r u y _
          (MixedColouring.not_isEven_comp hc' _) a
          (hswap1.trans hl0)).symm))
      exact (mul_zero _).symm
  -- Assemble by block decomposition and tensor induction.
  obtain ⟨v₁, v₂⟩ := v
  rw [show ((v₁, v₂) : (superPow (stdSuperPair k ℓ) 2).odd) =
    (v₁, 0) + (0, v₂) from by
    rw [Prod.mk_add_mk, add_zero, zero_add]]
  refine hPadd _ _ ?_ ?_
  · -- The even-odd block.
    induction v₁ using TensorProduct.induction_on with
    | zero => exact hP0
    | add s t hs ht =>
      rw [show ((s + t, 0) :
          (superPow (stdSuperPair k ℓ) 2).odd) =
        (s, 0) + (t, 0) from by
        rw [Prod.mk_add_mk, add_zero]]
      exact hPadd _ _ hs ht
    | tmul a w =>
      obtain ⟨a₁, a₂⟩ := a
      have helem : ((((a₁, a₂) :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
          0) : (superPow (stdSuperPair k ℓ) 2).odd) =
        (((((a₁, 0) :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w, 0)) :
          (superPow (stdSuperPair k ℓ) 2).odd) +
        (((((0, a₂) :
          (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w, 0)) :
          (superPow (stdSuperPair k ℓ) 2).odd)
        := by
        refine Eq.trans (congrArg (fun t =>
          ((t, (0 : (superPow (stdSuperPair k ℓ) 1).odd ⊗[ℂ]
            (stdSuperPair k ℓ).even)) :
            (superPow (stdSuperPair k ℓ) 2).odd))
          (Eq.trans (congrArg (fun s =>
              s ⊗ₜ[ℂ] w)
            (show ((a₁, a₂) :
                (superPow (stdSuperPair k ℓ) 1).even) =
              ((a₁, 0) : (superPow (stdSuperPair k ℓ) 1).even) +
              ((0, a₂) : (superPow (stdSuperPair k ℓ) 1).even)
              from by rw [Prod.mk_add_mk, add_zero,
                zero_add]))
            (TensorProduct.add_tmul
              (((a₁, 0) :
                (superPow (stdSuperPair k ℓ) 1).even))
              (((0, a₂) :
                (superPow (stdSuperPair k ℓ) 1).even)) w))) ?_
        exact Prod.ext_iff.mpr ⟨rfl, (add_zero 0).symm⟩
      refine Eq.mpr (congrArg P helem) (hPadd _ _ ?_ ?_)
      · clear helem
        induction a₁ using TensorProduct.induction_on with
        | zero =>
          have h0elem : (((((0 :
              (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
              (stdSuperPair k ℓ).even), 0) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
              0) : (superPow (stdSuperPair k ℓ) 2).odd) =
              0 := by
            refine Eq.trans (congrArg (fun t =>
              ((t, (0 : (superPow (stdSuperPair k ℓ) 1).odd
                ⊗[ℂ] (stdSuperPair k ℓ).even)) :
                (superPow (stdSuperPair k ℓ) 2).odd))
              (show ((((0 :
                  (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                  (stdSuperPair k ℓ).even), 0) :
                (superPow (stdSuperPair k ℓ) 1).even))
                ⊗ₜ[ℂ] w = 0 from
                TensorProduct.zero_tmul _ w)) ?_
            exact Prod.ext_iff.mpr ⟨rfl, rfl⟩
          exact Eq.mpr (congrArg P h0elem) hP0
        | add s t hs ht =>
          have helem : (((((s + t :
              (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
              (stdSuperPair k ℓ).even), 0) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
              0) : (superPow (stdSuperPair k ℓ) 2).odd) =
            ((((s, 0) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
              0) : (superPow (stdSuperPair k ℓ) 2).odd) +
            (((((t, 0) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
              0)) : (superPow (stdSuperPair k ℓ) 2).odd) := by
            refine Eq.trans (congrArg (fun u =>
              ((u, (0 : (superPow (stdSuperPair k ℓ) 1).odd
                ⊗[ℂ] (stdSuperPair k ℓ).even)) :
                (superPow (stdSuperPair k ℓ) 2).odd))
              (Eq.trans (congrArg (fun q => q ⊗ₜ[ℂ] w)
                (show (((s + t :
                    (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                    (stdSuperPair k ℓ).even), 0) :
                  (superPow (stdSuperPair k ℓ) 1).even) =
                  ((s, 0) :
                    (superPow (stdSuperPair k ℓ) 1).even) +
                  ((t, 0) :
                    (superPow (stdSuperPair k ℓ) 1).even)
                  from by rw [Prod.mk_add_mk, add_zero]))
                (TensorProduct.add_tmul
                  (((s, 0) :
                    (superPow (stdSuperPair k ℓ) 1).even))
                  (((t, 0) :
                    (superPow (stdSuperPair k ℓ) 1).even))
                  w))) ?_
            exact Prod.ext_iff.mpr ⟨rfl, (add_zero 0).symm⟩
          exact Eq.mpr (congrArg P helem) (hPadd _ _ hs ht)
        | tmul r x => exact heo r x w
      · have h0elem : (((((0 :
            (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
            (stdSuperPair k ℓ).even), a₂) :
            (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w,
            0) : (superPow (stdSuperPair k ℓ) 2).odd) =
            0 := by
          refine Eq.trans (congrArg (fun t =>
            ((((((0 : (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                (stdSuperPair k ℓ).even), t) :
              (superPow (stdSuperPair k ℓ) 1).even) ⊗ₜ[ℂ] w),
              (0 : (superPow (stdSuperPair k ℓ) 1).odd
                ⊗[ℂ] (stdSuperPair k ℓ).even)) :
              (superPow (stdSuperPair k ℓ) 2).odd))
            (subsingleton_tmul_eq_zero a₂)) ?_
          refine Eq.trans (congrArg (fun t =>
            ((t, (0 : (superPow (stdSuperPair k ℓ) 1).odd
              ⊗[ℂ] (stdSuperPair k ℓ).even)) :
              (superPow (stdSuperPair k ℓ) 2).odd))
            (show ((((0 :
                (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                (stdSuperPair k ℓ).even), (0 :
                (superPow (stdSuperPair k ℓ) 0).odd ⊗[ℂ]
                (stdSuperPair k ℓ).odd)) :
              (superPow (stdSuperPair k ℓ) 1).even))
              ⊗ₜ[ℂ] w = 0 from
              TensorProduct.zero_tmul _ w)) ?_
          exact Prod.ext_iff.mpr ⟨rfl, rfl⟩
        exact Eq.mpr (congrArg P h0elem) hP0
  · -- The odd-even block.
    induction v₂ using TensorProduct.induction_on with
    | zero => exact hP0
    | add s t hs ht =>
      rw [show ((0, s + t) :
          (superPow (stdSuperPair k ℓ) 2).odd) =
        (0, s) + (0, t) from by
        rw [Prod.mk_add_mk, add_zero]]
      exact hPadd _ _ hs ht
    | tmul b y =>
      obtain ⟨b₁, b₂⟩ := b
      have helem : ((0, (((b₁, b₂) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
          (superPow (stdSuperPair k ℓ) 2).odd) =
        (((0, (((b₁, 0) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y))) :
          (superPow (stdSuperPair k ℓ) 2).odd) +
        (((0, (((0, b₂) :
          (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y))) :
          (superPow (stdSuperPair k ℓ) 2).odd)
        := by
        refine Eq.trans (congrArg (fun t =>
          (((0 : (superPow (stdSuperPair k ℓ) 1).even ⊗[ℂ]
            (stdSuperPair k ℓ).odd), t) :
            (superPow (stdSuperPair k ℓ) 2).odd))
          (Eq.trans (congrArg (fun s =>
              s ⊗ₜ[ℂ] y)
            (show ((b₁, b₂) :
                (superPow (stdSuperPair k ℓ) 1).odd) =
              ((b₁, 0) : (superPow (stdSuperPair k ℓ) 1).odd) +
              ((0, b₂) : (superPow (stdSuperPair k ℓ) 1).odd)
              from by rw [Prod.mk_add_mk, add_zero,
                zero_add]))
            (TensorProduct.add_tmul
              (((b₁, 0) :
                (superPow (stdSuperPair k ℓ) 1).odd))
              (((0, b₂) :
                (superPow (stdSuperPair k ℓ) 1).odd)) y))) ?_
        exact Prod.ext_iff.mpr ⟨(add_zero 0).symm, rfl⟩
      refine Eq.mpr (congrArg P helem) (hPadd _ _ ?_ ?_)
      · clear helem
        induction b₁ using TensorProduct.induction_on with
        | zero =>
          have h0elem : ((0, ((((0 :
              (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
              (stdSuperPair k ℓ).odd), 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
              (superPow (stdSuperPair k ℓ) 2).odd) = 0 := by
            refine Eq.trans (congrArg (fun t =>
              (((0 : (superPow (stdSuperPair k ℓ) 1).even
                ⊗[ℂ] (stdSuperPair k ℓ).odd), t) :
                (superPow (stdSuperPair k ℓ) 2).odd))
              (show ((((0 :
                  (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                  (stdSuperPair k ℓ).odd), 0) :
                (superPow (stdSuperPair k ℓ) 1).odd))
                ⊗ₜ[ℂ] y = 0 from
                TensorProduct.zero_tmul _ y)) ?_
            exact Prod.ext_iff.mpr ⟨rfl, rfl⟩
          exact Eq.mpr (congrArg P h0elem) hP0
        | add s t hs ht =>
          have helem : ((0, ((((s + t :
              (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
              (stdSuperPair k ℓ).odd), 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
              (superPow (stdSuperPair k ℓ) 2).odd) =
            (((0, (((s, 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y))) :
              (superPow (stdSuperPair k ℓ) 2).odd) +
            (((0, (((t, 0) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y))) :
              (superPow (stdSuperPair k ℓ) 2).odd)
            := by
            refine Eq.trans (congrArg (fun u =>
              (((0 : (superPow (stdSuperPair k ℓ) 1).even
                ⊗[ℂ] (stdSuperPair k ℓ).odd), u) :
                (superPow (stdSuperPair k ℓ) 2).odd))
              (Eq.trans (congrArg (fun q => q ⊗ₜ[ℂ] y)
                (show (((s + t :
                    (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                    (stdSuperPair k ℓ).odd), 0) :
                  (superPow (stdSuperPair k ℓ) 1).odd) =
                  ((s, 0) :
                    (superPow (stdSuperPair k ℓ) 1).odd) +
                  ((t, 0) :
                    (superPow (stdSuperPair k ℓ) 1).odd)
                  from by rw [Prod.mk_add_mk, add_zero]))
                (TensorProduct.add_tmul
                  (((s, 0) :
                    (superPow (stdSuperPair k ℓ) 1).odd))
                  (((t, 0) :
                    (superPow (stdSuperPair k ℓ) 1).odd))
                  y))) ?_
            exact Prod.ext_iff.mpr ⟨(add_zero 0).symm, rfl⟩
          exact Eq.mpr (congrArg P helem) (hPadd _ _ hs ht)
        | tmul r u => exact hoe r u y
      · have h0elem : ((0, ((((0 :
            (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
            (stdSuperPair k ℓ).odd), b₂) :
            (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
            (superPow (stdSuperPair k ℓ) 2).odd) = 0 := by
          refine Eq.trans (congrArg (fun t =>
            (((0 : (superPow (stdSuperPair k ℓ) 1).even
              ⊗[ℂ] (stdSuperPair k ℓ).odd),
              ((((0 : (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                (stdSuperPair k ℓ).odd), t) :
              (superPow (stdSuperPair k ℓ) 1).odd) ⊗ₜ[ℂ] y)) :
              (superPow (stdSuperPair k ℓ) 2).odd))
            (subsingleton_tmul_eq_zero b₂)) ?_
          refine Eq.trans (congrArg (fun t =>
            (((0 : (superPow (stdSuperPair k ℓ) 1).even
              ⊗[ℂ] (stdSuperPair k ℓ).odd), t) :
              (superPow (stdSuperPair k ℓ) 2).odd))
            (show ((((0 :
                (superPow (stdSuperPair k ℓ) 0).even ⊗[ℂ]
                (stdSuperPair k ℓ).odd), (0 :
                (superPow (stdSuperPair k ℓ) 0).odd ⊗[ℂ]
                (stdSuperPair k ℓ).even)) :
              (superPow (stdSuperPair k ℓ) 1).odd))
              ⊗ₜ[ℂ] y = 0 from
              TensorProduct.zero_tmul _ y)) ?_
          exact Prod.ext_iff.mpr ⟨rfl, rfl⟩
        exact Eq.mpr (congrArg P h0elem) hP0

/-! ### The top swap on halves -/

private theorem firstHalf_swapTop (n : ℕ)
    (c : MixedColouring k ℓ (n + 2)) :
    MixedColouring.firstHalf (a := n) (b := 2)
      (c ∘ _root_.Equiv.swap
        (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩) =
    MixedColouring.firstHalf (a := n) (b := 2) c := by
  funext i
  show c (_root_.Equiv.swap
    (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩
    (Fin.castAdd 2 i)) = c (Fin.castAdd 2 i)
  refine congrArg c (_root_.Equiv.swap_apply_of_ne_of_ne ?_ ?_)
  · exact Fin.ne_of_val_ne (show i.val ≠ n from by
      have := i.isLt; omega)
  · exact Fin.ne_of_val_ne (show i.val ≠ n + 1 from by
      have := i.isLt; omega)

private theorem secondHalf_swapTop (n : ℕ)
    (c : MixedColouring k ℓ (n + 2)) :
    MixedColouring.secondHalf (a := n) (b := 2)
      (c ∘ _root_.Equiv.swap
        (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩) =
    (MixedColouring.secondHalf (a := n) (b := 2) c) ∘
      _root_.Equiv.swap (⟨0, by omega⟩ : Fin 2)
        ⟨1, by omega⟩ := by
  funext j
  show c (_root_.Equiv.swap
    (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩
    (Fin.natAdd n j)) =
    c (Fin.natAdd n (_root_.Equiv.swap
      (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩ j))
  refine congrArg c ?_
  rcases j with ⟨jv, hj⟩
  interval_cases jv
  · rw [show Fin.natAdd n (⟨0, hj⟩ : Fin 2) =
      (⟨n, by omega⟩ : Fin (n + 2)) from Fin.ext (by
        show n + 0 = n; omega)]
    rw [_root_.Equiv.swap_apply_left]
    rw [show (⟨0, hj⟩ : Fin 2) = ⟨0, by omega⟩ from rfl]
    rw [_root_.Equiv.swap_apply_left]
    exact Fin.ext (by show n + 1 = n + 1; rfl)
  · rw [show Fin.natAdd n (⟨1, hj⟩ : Fin 2) =
      (⟨n + 1, by omega⟩ : Fin (n + 2)) from Fin.ext rfl]
    rw [_root_.Equiv.swap_apply_right]
    rw [show (⟨1, hj⟩ : Fin 2) = ⟨1, by omega⟩ from rfl]
    rw [_root_.Equiv.swap_apply_right]
    exact Fin.ext (by show n = n + 0; omega)

private theorem adjSign_secondHalf (n : ℕ)
    (c : MixedColouring k ℓ (n + 2)) :
    adjSign (MixedColouring.secondHalf (a := n) (b := 2) c)
      ⟨0, by omega⟩ ⟨1, by omega⟩ =
    adjSign c ⟨n, by omega⟩ ⟨n + 1, by omega⟩ := by
  unfold adjSign
  rw [show MixedColouring.secondHalf (a := n) (b := 2) c
      ⟨0, by omega⟩ = c ⟨n, by omega⟩ from
    congrArg c (Fin.ext (by show n + 0 = n; omega))]
  rw [show MixedColouring.secondHalf (a := n) (b := 2) c
      ⟨1, by omega⟩ = c ⟨n + 1, by omega⟩ from
    congrArg c (Fin.ext rfl)]

/-! ### The general even coordinate identity -/

-- Raised budget: the two-strand coordinate transported over `n`
-- leading positions, so the merge equivalence at arity `n` enters
-- the elaborated term alongside the braiding.
private theorem braidN_coord_even (n : ℕ)
    (c : MixedColouring k ℓ (n + 2)) (hc : c.IsEven)
    (v : (superPow (stdSuperPair k ℓ) (n + 2)).even) :
    (colourPowerEquiv k ℓ (n + 2)).evenEquiv
      (((topBraid (stdSuperPair k ℓ) n) :
        SuperVect.Hom _ _).evenMap v) ⟨c, hc⟩ =
    adjSign c ⟨n, by omega⟩ ⟨n + 1, by omega⟩ *
      (colourPowerEquiv k ℓ (n + 2)).evenEquiv v
        ⟨c ∘ _root_.Equiv.swap
          (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩,
        hc.comp _⟩ := by
  obtain ⟨w, rfl⟩ :=
    powMerge_evenMap_surjective (stdSuperPair k ℓ) n 2 v
  -- ═══════ THE BRAIDING COMMUTES PAST THE LEADING BLOCK ═══════
  have hcomm := (congrArg (fun z :
      (superPow (stdSuperPair k ℓ) n ⊗
        superPow (stdSuperPair k ℓ) 2 ⟶
        superPow (stdSuperPair k ℓ) (n + 2)) =>
    (z : SuperVect.Hom _ _).evenMap w)
    (powMerge_topBraid (stdSuperPair k ℓ) n)).symm
  refine Eq.trans (congrArg
    (fun t => (colourPowerEquiv k ℓ (n + 2)).evenEquiv t
      ⟨c, hc⟩) hcomm) ?_
  clear hcomm
  -- ═══════ THE PREDICATE, PROVED ADDITIVELY ═══════
  set P : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) n)
      (superPow (stdSuperPair k ℓ) 2)).even → Prop := fun u =>
    (colourPowerEquiv k ℓ (n + 2)).evenEquiv
      (((powMerge (stdSuperPair k ℓ) n 2) :
        SuperVect.Hom _ _).evenMap
        ((((superPow (stdSuperPair k ℓ) n) ◁
            topBraid (stdSuperPair k ℓ) 0 : _ ⟶ _) :
          SuperVect.Hom _ _).evenMap u)) ⟨c, hc⟩ =
    adjSign c ⟨n, by omega⟩ ⟨n + 1, by omega⟩ *
      (colourPowerEquiv k ℓ (n + 2)).evenEquiv
        (((powMerge (stdSuperPair k ℓ) n 2) :
          SuperVect.Hom _ _).evenMap u)
        ⟨c ∘ _root_.Equiv.swap
          (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩,
        hc.comp _⟩ with hP
  show P w
  have hP0 : P 0 := by
    rw [hP]
    beta_reduce
    simp only [map_zero]
    show (0 : ℂ) = adjSign c ⟨n, by omega⟩
      ⟨n + 1, by omega⟩ * (0 : ℂ)
    rw [mul_zero]
  have hPadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂) := by
    intro u₁ u₂ h₁ h₂
    rw [hP] at h₁ h₂ ⊢
    beta_reduce at h₁ h₂ ⊢
    rw [map_add, map_add, map_add, colourFun_add_apply,
      map_add, map_add, colourFun_add_apply, h₁, h₂, mul_add]
  -- ═══════ THE EVEN LEADING BLOCK ═══════
  have hblock1 : ∀ (p : (superPow (stdSuperPair k ℓ) n).even)
      (q : (superPow (stdSuperPair k ℓ) 2).even),
      P (evenPair p q) := by
    intro p q
    rw [hP]
    beta_reduce
    refine Eq.trans (congrArg (fun t =>
      (colourPowerEquiv k ℓ (n + 2)).evenEquiv
        (((powMerge (stdSuperPair k ℓ) n 2) :
          SuperVect.Hom _ _).evenMap t) ⟨c, hc⟩)
      (tensorHom_evenPair (SuperVect.Hom.id _)
        ((topBraid (stdSuperPair k ℓ) 0) :
          SuperVect.Hom _ _) p q)) ?_
    refine Eq.trans (colourMerge_coord n 2 p
      (((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).evenMap q) c hc) ?_
    refine Eq.trans ?_ (congrArg
      (fun t => adjSign c ⟨n, by omega⟩ ⟨n + 1, by omega⟩ * t)
      (colourMerge_coord n 2 p q _ (hc.comp _)).symm)
    by_cases hfh : MixedColouring.IsEven
        (MixedColouring.firstHalf (a := n) (b := 2) c)
    · rw [dif_pos hfh]
      rw [dif_pos (show MixedColouring.IsEven
          (MixedColouring.firstHalf (a := n) (b := 2)
            (c ∘ _root_.Equiv.swap
              (⟨n, by omega⟩ : Fin (n + 2))
              ⟨n + 1, by omega⟩)) from
        (firstHalf_swapTop n c).symm ▸ hfh)]
      refine Eq.trans (congrArg
        (fun t => (colourPowerEquiv k ℓ n).evenEquiv p
          ⟨MixedColouring.firstHalf c, hfh⟩ * t)
        (braid_coord_even
          (MixedColouring.secondHalf (a := n) (b := 2) c)
          (c.secondHalf_isEven hc hfh) q)) ?_
      rw [show (⟨MixedColouring.firstHalf (a := n) (b := 2)
          (c ∘ _root_.Equiv.swap
            (⟨n, by omega⟩ : Fin (n + 2))
            ⟨n + 1, by omega⟩), _⟩ :
          {c : MixedColouring k ℓ n // c.IsEven}) =
        ⟨MixedColouring.firstHalf (a := n) (b := 2) c,
          hfh⟩ from Subtype.ext (firstHalf_swapTop n c)]
      rw [show (⟨MixedColouring.secondHalf (a := n) (b := 2)
          (c ∘ _root_.Equiv.swap
            (⟨n, by omega⟩ : Fin (n + 2))
            ⟨n + 1, by omega⟩), _⟩ :
          {c : MixedColouring k ℓ 2 // c.IsEven}) =
        ⟨(MixedColouring.secondHalf (a := n) (b := 2) c) ∘
          _root_.Equiv.swap (⟨0, by omega⟩ : Fin 2)
            ⟨1, by omega⟩,
          (c.secondHalf_isEven hc hfh).comp _⟩ from
        Subtype.ext (secondHalf_swapTop n c)]
      rw [adjSign_secondHalf n c]
      ring
    · rw [dif_neg hfh]
      rw [dif_neg (show ¬ MixedColouring.IsEven
          (MixedColouring.firstHalf (a := n) (b := 2)
            (c ∘ _root_.Equiv.swap
              (⟨n, by omega⟩ : Fin (n + 2))
              ⟨n + 1, by omega⟩)) from
        fun h' => hfh ((firstHalf_swapTop n c) ▸ h'))]
      rw [mul_zero]
  -- ═══════ THE ODD LEADING BLOCK ═══════
  have hblock2 : ∀ (p : (superPow (stdSuperPair k ℓ) n).odd)
      (q : (superPow (stdSuperPair k ℓ) 2).odd),
      P (((0 : (superPow (stdSuperPair k ℓ) n).even ⊗[ℂ]
          (superPow (stdSuperPair k ℓ) 2).even),
        p ⊗ₜ[ℂ] q)) := by
    intro p q
    rw [hP]
    beta_reduce
    refine Eq.trans (congrArg (fun t =>
      (colourPowerEquiv k ℓ (n + 2)).evenEquiv
        (((powMerge (stdSuperPair k ℓ) n 2) :
          SuperVect.Hom _ _).evenMap t) ⟨c, hc⟩)
      (tensorHom_oddPair (SuperVect.Hom.id _)
        ((topBraid (stdSuperPair k ℓ) 0) :
          SuperVect.Hom _ _) p q)) ?_
    refine Eq.trans (colourMerge_coord_oddPair n 2 p
      (((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).oddMap q) c hc) ?_
    refine Eq.trans ?_ (congrArg
      (fun t => adjSign c ⟨n, by omega⟩ ⟨n + 1, by omega⟩ * t)
      (colourMerge_coord_oddPair n 2 p q _ (hc.comp _)).symm)
    by_cases hfh : MixedColouring.IsEven
        (MixedColouring.firstHalf (a := n) (b := 2) c)
    · rw [dif_pos hfh]
      rw [dif_pos (show MixedColouring.IsEven
          (MixedColouring.firstHalf (a := n) (b := 2)
            (c ∘ _root_.Equiv.swap
              (⟨n, by omega⟩ : Fin (n + 2))
              ⟨n + 1, by omega⟩)) from
        (firstHalf_swapTop n c).symm ▸ hfh)]
      rw [mul_zero]
    · rw [dif_neg hfh]
      rw [dif_neg (show ¬ MixedColouring.IsEven
          (MixedColouring.firstHalf (a := n) (b := 2)
            (c ∘ _root_.Equiv.swap
              (⟨n, by omega⟩ : Fin (n + 2))
              ⟨n + 1, by omega⟩)) from
        fun h' => hfh ((firstHalf_swapTop n c) ▸ h'))]
      refine Eq.trans (congrArg
        (fun t => (colourPowerEquiv k ℓ n).oddEquiv p
          ⟨MixedColouring.firstHalf c, hfh⟩ * t)
        (braid_coord_odd
          (MixedColouring.secondHalf (a := n) (b := 2) c)
          (c.secondHalf_not_isEven' hc hfh) q)) ?_
      rw [show (⟨MixedColouring.firstHalf (a := n) (b := 2)
          (c ∘ _root_.Equiv.swap
            (⟨n, by omega⟩ : Fin (n + 2))
            ⟨n + 1, by omega⟩), _⟩ :
          {c : MixedColouring k ℓ n // ¬ c.IsEven}) =
        ⟨MixedColouring.firstHalf (a := n) (b := 2) c,
          hfh⟩ from Subtype.ext (firstHalf_swapTop n c)]
      rw [show (⟨MixedColouring.secondHalf (a := n) (b := 2)
          (c ∘ _root_.Equiv.swap
            (⟨n, by omega⟩ : Fin (n + 2))
            ⟨n + 1, by omega⟩), _⟩ :
          {c : MixedColouring k ℓ 2 // ¬ c.IsEven}) =
        ⟨(MixedColouring.secondHalf (a := n) (b := 2) c) ∘
          _root_.Equiv.swap (⟨0, by omega⟩ : Fin 2)
            ⟨1, by omega⟩,
          MixedColouring.not_isEven_comp
            (c.secondHalf_not_isEven' hc hfh) _⟩ from
        Subtype.ext (secondHalf_swapTop n c)]
      rw [adjSign_secondHalf n c]
      ring
  obtain ⟨w₁, w₂⟩ := w
  rw [show ((w₁, w₂) :
      (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) n)
        (superPow (stdSuperPair k ℓ) 2)).even) =
    (w₁, 0) + (0, w₂) from by
    rw [Prod.mk_add_mk, add_zero, zero_add]]
  refine hPadd _ _ ?_ ?_
  · induction w₁ using TensorProduct.induction_on with
    | zero => exact hP0
    | add s t hs ht =>
      rw [show ((s + t, 0) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) n)
            (superPow (stdSuperPair k ℓ) 2)).even) =
        (s, 0) + (t, 0) from by
        rw [Prod.mk_add_mk, add_zero]]
      exact hPadd _ _ hs ht
    | tmul p q => exact hblock1 p q
  · induction w₂ using TensorProduct.induction_on with
    | zero => exact hP0
    | add s t hs ht =>
      rw [show ((0, s + t) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) n)
            (superPow (stdSuperPair k ℓ) 2)).even) =
        (0, s) + (0, t) from by
        rw [Prod.mk_add_mk, add_zero]]
      exact hPadd _ _ hs ht
    | tmul p q => exact hblock2 p q

/-! ### The general odd coordinate identity and main theorem -/

private theorem tensorHom_oddFst {V₁ V₂ W₁ W₂ : SuperVect}
    (e₁ : SuperVect.Hom V₁ W₁) (e₂ : SuperVect.Hom V₂ W₂)
    (v : V₁.even) (u : V₂.odd) :
    (SuperVect.tensorHom e₁ e₂).oddMap
      ((v ⊗ₜ[ℂ] u, (0 : V₁.odd ⊗[ℂ] V₂.even))) =
      ((e₁.evenMap v ⊗ₜ[ℂ] e₂.oddMap u,
        (0 : W₁.odd ⊗[ℂ] W₂.even))) := by
  show (TensorProduct.map e₁.evenMap e₂.oddMap (v ⊗ₜ[ℂ] u),
    TensorProduct.map e₁.oddMap e₂.evenMap 0) = _
  rw [TensorProduct.map_tmul, map_zero]

private theorem tensorHom_oddSnd {V₁ V₂ W₁ W₂ : SuperVect}
    (e₁ : SuperVect.Hom V₁ W₁) (e₂ : SuperVect.Hom V₂ W₂)
    (v : V₁.odd) (u : V₂.even) :
    (SuperVect.tensorHom e₁ e₂).oddMap
      (((0 : V₁.even ⊗[ℂ] V₂.odd), v ⊗ₜ[ℂ] u)) =
      (((0 : W₁.even ⊗[ℂ] W₂.odd),
        e₁.oddMap v ⊗ₜ[ℂ] e₂.evenMap u)) := by
  show (TensorProduct.map e₁.evenMap e₂.oddMap 0,
    TensorProduct.map e₁.oddMap e₂.evenMap (v ⊗ₜ[ℂ] u)) = _
  rw [TensorProduct.map_tmul, map_zero]

private theorem secondHalf_even_of_odd_odd {a b : ℕ}
    {c : MixedColouring k ℓ (a + b)} (hc : ¬ c.IsEven)
    (h : ¬ MixedColouring.IsEven
      (MixedColouring.firstHalf (a := a) (b := b) c)) :
    MixedColouring.IsEven
      (MixedColouring.secondHalf (a := a) (b := b) c) := by
  by_contra hsh
  refine hc ?_
  rw [MixedColouring.IsEven, MixedColouring.oddSet_card_split]
  rw [MixedColouring.IsEven] at h hsh
  exact Nat.even_add.mpr ⟨fun hA => absurd hA h,
    fun hB => absurd hB hsh⟩

-- As for the even component, on the odd half.
private theorem braidN_coord_odd (n : ℕ)
    (c : MixedColouring k ℓ (n + 2)) (hc : ¬ c.IsEven)
    (v : (superPow (stdSuperPair k ℓ) (n + 2)).odd) :
    (colourPowerEquiv k ℓ (n + 2)).oddEquiv
      (((topBraid (stdSuperPair k ℓ) n) :
        SuperVect.Hom _ _).oddMap v) ⟨c, hc⟩ =
    adjSign c ⟨n, by omega⟩ ⟨n + 1, by omega⟩ *
      (colourPowerEquiv k ℓ (n + 2)).oddEquiv v
        ⟨c ∘ _root_.Equiv.swap
          (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩,
        MixedColouring.not_isEven_comp hc _⟩ := by
  obtain ⟨w, rfl⟩ :=
    powMerge_oddMap_surjective (stdSuperPair k ℓ) n 2 v
  have hcomm := (congrArg (fun z :
      (superPow (stdSuperPair k ℓ) n ⊗
        superPow (stdSuperPair k ℓ) 2 ⟶
        superPow (stdSuperPair k ℓ) (n + 2)) =>
    (z : SuperVect.Hom _ _).oddMap w)
    (powMerge_topBraid (stdSuperPair k ℓ) n)).symm
  refine Eq.trans (congrArg
    (fun t => (colourPowerEquiv k ℓ (n + 2)).oddEquiv t
      ⟨c, hc⟩) hcomm) ?_
  clear hcomm
  -- ═══════ THE PREDICATE, PROVED ADDITIVELY ═══════
  set P : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) n)
      (superPow (stdSuperPair k ℓ) 2)).odd → Prop := fun u =>
    (colourPowerEquiv k ℓ (n + 2)).oddEquiv
      (((powMerge (stdSuperPair k ℓ) n 2) :
        SuperVect.Hom _ _).oddMap
        ((((superPow (stdSuperPair k ℓ) n) ◁
            topBraid (stdSuperPair k ℓ) 0 : _ ⟶ _) :
          SuperVect.Hom _ _).oddMap u)) ⟨c, hc⟩ =
    adjSign c ⟨n, by omega⟩ ⟨n + 1, by omega⟩ *
      (colourPowerEquiv k ℓ (n + 2)).oddEquiv
        (((powMerge (stdSuperPair k ℓ) n 2) :
          SuperVect.Hom _ _).oddMap u)
        ⟨c ∘ _root_.Equiv.swap
          (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩,
        MixedColouring.not_isEven_comp hc _⟩ with hP
  show P w
  have hP0 : P 0 := by
    rw [hP]
    beta_reduce
    simp only [map_zero]
    show (0 : ℂ) = adjSign c ⟨n, by omega⟩
      ⟨n + 1, by omega⟩ * (0 : ℂ)
    rw [mul_zero]
  have hPadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂) := by
    intro u₁ u₂ h₁ h₂
    rw [hP] at h₁ h₂ ⊢
    beta_reduce at h₁ h₂ ⊢
    rw [map_add, map_add, map_add, colourFunO_add_apply,
      map_add, map_add, colourFunO_add_apply, h₁, h₂,
      mul_add]
  -- ═══════ THE EVEN LEADING BLOCK ═══════
  have hblock1 : ∀ (p : (superPow (stdSuperPair k ℓ) n).even)
      (q : (superPow (stdSuperPair k ℓ) 2).odd),
      P ((p ⊗ₜ[ℂ] q,
        (0 : (superPow (stdSuperPair k ℓ) n).odd ⊗[ℂ]
          (superPow (stdSuperPair k ℓ) 2).even))) := by
    intro p q
    rw [hP]
    beta_reduce
    refine Eq.trans (congrArg (fun t =>
      (colourPowerEquiv k ℓ (n + 2)).oddEquiv
        (((powMerge (stdSuperPair k ℓ) n 2) :
          SuperVect.Hom _ _).oddMap t) ⟨c, hc⟩)
      (tensorHom_oddFst (SuperVect.Hom.id _)
        ((topBraid (stdSuperPair k ℓ) 0) :
          SuperVect.Hom _ _) p q)) ?_
    refine Eq.trans (colourMerge_coord_evenOdd n 2 p
      (((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).oddMap q) c hc) ?_
    refine Eq.trans ?_ (congrArg
      (fun t => adjSign c ⟨n, by omega⟩ ⟨n + 1, by omega⟩ * t)
      (colourMerge_coord_evenOdd n 2 p q _
        (MixedColouring.not_isEven_comp hc _)).symm)
    by_cases hfh : MixedColouring.IsEven
        (MixedColouring.firstHalf (a := n) (b := 2) c)
    · rw [dif_pos hfh]
      rw [dif_pos (show MixedColouring.IsEven
          (MixedColouring.firstHalf (a := n) (b := 2)
            (c ∘ _root_.Equiv.swap
              (⟨n, by omega⟩ : Fin (n + 2))
              ⟨n + 1, by omega⟩)) from
        (firstHalf_swapTop n c).symm ▸ hfh)]
      refine Eq.trans (congrArg
        (fun t => (colourPowerEquiv k ℓ n).evenEquiv p
          ⟨MixedColouring.firstHalf c, hfh⟩ * t)
        (braid_coord_odd
          (MixedColouring.secondHalf (a := n) (b := 2) c)
          (c.secondHalf_not_isEven hc hfh) q)) ?_
      rw [show (⟨MixedColouring.firstHalf (a := n) (b := 2)
          (c ∘ _root_.Equiv.swap
            (⟨n, by omega⟩ : Fin (n + 2))
            ⟨n + 1, by omega⟩), _⟩ :
          {c : MixedColouring k ℓ n // c.IsEven}) =
        ⟨MixedColouring.firstHalf (a := n) (b := 2) c,
          hfh⟩ from Subtype.ext (firstHalf_swapTop n c)]
      rw [show (⟨MixedColouring.secondHalf (a := n) (b := 2)
          (c ∘ _root_.Equiv.swap
            (⟨n, by omega⟩ : Fin (n + 2))
            ⟨n + 1, by omega⟩), _⟩ :
          {c : MixedColouring k ℓ 2 // ¬ c.IsEven}) =
        ⟨(MixedColouring.secondHalf (a := n) (b := 2) c) ∘
          _root_.Equiv.swap (⟨0, by omega⟩ : Fin 2)
            ⟨1, by omega⟩,
          MixedColouring.not_isEven_comp
            (c.secondHalf_not_isEven hc hfh) _⟩ from
        Subtype.ext (secondHalf_swapTop n c)]
      rw [adjSign_secondHalf n c]
      ring
    · rw [dif_neg hfh]
      rw [dif_neg (show ¬ MixedColouring.IsEven
          (MixedColouring.firstHalf (a := n) (b := 2)
            (c ∘ _root_.Equiv.swap
              (⟨n, by omega⟩ : Fin (n + 2))
              ⟨n + 1, by omega⟩)) from
        fun h' => hfh ((firstHalf_swapTop n c) ▸ h'))]
      rw [mul_zero]
  -- ═══════ THE ODD LEADING BLOCK ═══════
  have hblock2 : ∀ (p : (superPow (stdSuperPair k ℓ) n).odd)
      (q : (superPow (stdSuperPair k ℓ) 2).even),
      P (((0 : (superPow (stdSuperPair k ℓ) n).even ⊗[ℂ]
          (superPow (stdSuperPair k ℓ) 2).odd),
        p ⊗ₜ[ℂ] q)) := by
    intro p q
    rw [hP]
    beta_reduce
    refine Eq.trans (congrArg (fun t =>
      (colourPowerEquiv k ℓ (n + 2)).oddEquiv
        (((powMerge (stdSuperPair k ℓ) n 2) :
          SuperVect.Hom _ _).oddMap t) ⟨c, hc⟩)
      (tensorHom_oddSnd (SuperVect.Hom.id _)
        ((topBraid (stdSuperPair k ℓ) 0) :
          SuperVect.Hom _ _) p q)) ?_
    refine Eq.trans (colourMerge_coord_odd n 2 p
      (((topBraid (stdSuperPair k ℓ) 0) :
        SuperVect.Hom _ _).evenMap q) c hc) ?_
    refine Eq.trans ?_ (congrArg
      (fun t => adjSign c ⟨n, by omega⟩ ⟨n + 1, by omega⟩ * t)
      (colourMerge_coord_odd n 2 p q _
        (MixedColouring.not_isEven_comp hc _)).symm)
    by_cases hfh : MixedColouring.IsEven
        (MixedColouring.firstHalf (a := n) (b := 2) c)
    · rw [dif_pos hfh]
      rw [dif_pos (show MixedColouring.IsEven
          (MixedColouring.firstHalf (a := n) (b := 2)
            (c ∘ _root_.Equiv.swap
              (⟨n, by omega⟩ : Fin (n + 2))
              ⟨n + 1, by omega⟩)) from
        (firstHalf_swapTop n c).symm ▸ hfh)]
      rw [mul_zero]
    · rw [dif_neg hfh]
      rw [dif_neg (show ¬ MixedColouring.IsEven
          (MixedColouring.firstHalf (a := n) (b := 2)
            (c ∘ _root_.Equiv.swap
              (⟨n, by omega⟩ : Fin (n + 2))
              ⟨n + 1, by omega⟩)) from
        fun h' => hfh ((firstHalf_swapTop n c) ▸ h'))]
      refine Eq.trans (congrArg
        (fun t => (colourPowerEquiv k ℓ n).oddEquiv p
          ⟨MixedColouring.firstHalf c, hfh⟩ * t)
        (braid_coord_even
          (MixedColouring.secondHalf (a := n) (b := 2) c)
          (secondHalf_even_of_odd_odd hc hfh) q)) ?_
      rw [show (⟨MixedColouring.firstHalf (a := n) (b := 2)
          (c ∘ _root_.Equiv.swap
            (⟨n, by omega⟩ : Fin (n + 2))
            ⟨n + 1, by omega⟩), _⟩ :
          {c : MixedColouring k ℓ n // ¬ c.IsEven}) =
        ⟨MixedColouring.firstHalf (a := n) (b := 2) c,
          hfh⟩ from Subtype.ext (firstHalf_swapTop n c)]
      rw [show (⟨MixedColouring.secondHalf (a := n) (b := 2)
          (c ∘ _root_.Equiv.swap
            (⟨n, by omega⟩ : Fin (n + 2))
            ⟨n + 1, by omega⟩), _⟩ :
          {c : MixedColouring k ℓ 2 // c.IsEven}) =
        ⟨(MixedColouring.secondHalf (a := n) (b := 2) c) ∘
          _root_.Equiv.swap (⟨0, by omega⟩ : Fin 2)
            ⟨1, by omega⟩,
          (secondHalf_even_of_odd_odd hc hfh).comp _⟩ from
        Subtype.ext (secondHalf_swapTop n c)]
      rw [adjSign_secondHalf n c]
      ring
  obtain ⟨w₁, w₂⟩ := w
  rw [show ((w₁, w₂) :
      (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) n)
        (superPow (stdSuperPair k ℓ) 2)).odd) =
    (w₁, 0) + (0, w₂) from by
    rw [Prod.mk_add_mk, add_zero, zero_add]]
  refine hPadd _ _ ?_ ?_
  · induction w₁ using TensorProduct.induction_on with
    | zero => exact hP0
    | add s t hs ht =>
      rw [show ((s + t, 0) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) n)
            (superPow (stdSuperPair k ℓ) 2)).odd) =
        (s, 0) + (t, 0) from by
        rw [Prod.mk_add_mk, add_zero]]
      exact hPadd _ _ hs ht
    | tmul p q => exact hblock1 p q
  · induction w₂ using TensorProduct.induction_on with
    | zero => exact hP0
    | add s t hs ht =>
      rw [show ((0, s + t) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) n)
            (superPow (stdSuperPair k ℓ) 2)).odd) =
        (0, s) + (0, t) from by
        rw [Prod.mk_add_mk, add_zero]]
      exact hPadd _ _ hs ht
    | tmul p q => exact hblock2 p q

-- Raised budget: assembling the two coordinate formulas into an
-- equality of super morphisms unfolds the colouring equivalence on
-- both components once more.
/-- **The colour action of the top braiding.** -/
theorem toColour_topBraid (n : ℕ) :
    toColour (k := k) (ℓ := ℓ) (n + 2)
        (topBraid (stdSuperPair k ℓ) n) =
      colourSwap k ℓ (n + 2) n (by omega) := by
  refine SuperVect.Hom.ext ?_ ?_
  · refine LinearMap.ext (fun F => ?_)
    funext c'
    obtain ⟨c', hc'⟩ := c'
    refine Eq.trans (braidN_coord_even n c' hc'
      ((colourPowerEquiv k ℓ (n + 2)).evenEquiv.symm F)) ?_
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · refine LinearMap.ext (fun F => ?_)
    funext c'
    obtain ⟨c', hc'⟩ := c'
    refine Eq.trans (braidN_coord_odd n c' hc'
      ((colourPowerEquiv k ℓ (n + 2)).oddEquiv.symm F)) ?_
    rw [LinearEquiv.apply_symm_apply]
    rfl

end RS
