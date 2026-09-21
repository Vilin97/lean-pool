/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PowMerge
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourEval

/-!
# The merge coordinate product rule

Coordinates of a merged even pair multiply over the halves,
vanishing when the halves have odd parity.
-/

open scoped TensorProduct

namespace RS

open CategoryTheory MonoidalCategory

/-! ### First and second halves of a colouring -/

/-- The first half of a colouring of a sum. -/
def MixedColouring.firstHalf {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + b)) : MixedColouring k ℓ a :=
  fun i => c (Fin.castAdd b i)

/-- The second half of a colouring of a sum. -/
def MixedColouring.secondHalf {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + b)) : MixedColouring k ℓ b :=
  fun j => c (Fin.natAdd a j)

/-- The odd count splits over the halves. -/
theorem MixedColouring.oddSet_card_split {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + b)) :
    c.oddSet.card = (MixedColouring.oddSet c.firstHalf).card +
      (MixedColouring.oddSet c.secondHalf).card := by
  unfold oddSet firstHalf secondHalf
  simp only [Finset.card_filter]
  exact (Equiv.sum_comp finSumFinEquiv _).symm.trans
    (Fintype.sum_sum_type _)

/-! ### Helper lemmas -/

/-- The first half at `b = 0` is the colouring itself. -/
theorem MixedColouring.firstHalf_zero {k ℓ a : ℕ}
    (c : MixedColouring k ℓ (a + 0)) :
    c.firstHalf = c := by
  funext i; show c (Fin.castAdd 0 i) = c i; congr 1

/-- The first half of a tail equals the first half. -/
theorem MixedColouring.firstHalf_tail {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + (b + 1))) :
    (MixedColouring.tail c).firstHalf = c.firstHalf := by
  funext i
  show c (Fin.castAdd b i).castSucc = c (Fin.castAdd (b + 1) i)
  congr 1

/-- The second half of a tail equals the tail of the second half. -/
theorem MixedColouring.secondHalf_tail {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + (b + 1))) :
    (MixedColouring.tail c).secondHalf =
      MixedColouring.tail (c.secondHalf) := by
  funext j
  show c (Fin.natAdd a j).castSucc = c (Fin.natAdd a j.castSucc)
  congr 1

/-- Parity of the halves is linked when the whole is even. -/
theorem MixedColouring.isEven_half_iff {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven) :
    c.firstHalf.IsEven ↔ c.secondHalf.IsEven := by
  unfold IsEven at hc ⊢
  rw [oddSet_card_split] at hc
  exact Nat.even_add.mp hc

/-- When the whole is even and the first half is even,
the second half is even. -/
theorem MixedColouring.secondHalf_isEven {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven)
    (h : c.firstHalf.IsEven) : c.secondHalf.IsEven :=
  (c.isEven_half_iff hc).mp h

/-- When the whole is odd and the first half is even,
the second half is odd. -/
theorem MixedColouring.secondHalf_not_isEven {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + b)) (hc : ¬ c.IsEven)
    (h : c.firstHalf.IsEven) : ¬ c.secondHalf.IsEven := by
  intro hs
  unfold IsEven at hc
  rw [oddSet_card_split] at hc
  exact hc (Nat.even_add.mpr (Iff.intro (fun _ => hs) (fun _ => h)))

/-- The last colour of `c` equals the last colour of the
second half. -/
theorem MixedColouring.secondHalf_last {k ℓ a b : ℕ}
    (c : MixedColouring k ℓ (a + (b + 1))) :
    c.secondHalf (Fin.last b) = c (Fin.last (a + b)) := by
  show c (Fin.natAdd a (Fin.last b)) = c (Fin.last (a + b))
  congr 1

/-! ### Forward computation of evenSplitEquiv -/

/-- Compute `evenSplitEquiv` forward via its inverse, last colour
even. -/
theorem evenSplitEquiv_inl {k ℓ d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (hc : c.IsEven)
    (a' : Fin k) (ha : c (Fin.last d) = Sum.inl a') :
    evenSplitEquiv k ℓ d ⟨c, hc⟩ =
      Sum.inl (⟨MixedColouring.tail c,
        (c.isEven_succ_left a' ha).mp hc⟩, a') := by
  have inv : (evenSplitEquiv k ℓ d).symm
      (Sum.inl (⟨MixedColouring.tail c,
        (c.isEven_succ_left a' ha).mp hc⟩, a')) = ⟨c, hc⟩ := by
    apply Subtype.ext; rw [evenSplitEquiv_symm_inl]; funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (colouringSplit_symm_last _ _).trans ha.symm
    · exact colouringSplit_symm_castSucc _ _ _
  rw [← inv, Equiv.apply_symm_apply]

/-- Compute `evenSplitEquiv` forward via its inverse, last colour
odd. -/
theorem evenSplitEquiv_inr {k ℓ d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (hc : c.IsEven)
    (b' : Fin (2 * ℓ)) (hb : c (Fin.last d) = Sum.inr b') :
    evenSplitEquiv k ℓ d ⟨c, hc⟩ =
      Sum.inr (⟨MixedColouring.tail c,
        (c.isEven_succ_right b' hb).mp hc⟩, b') := by
  have inv : (evenSplitEquiv k ℓ d).symm
      (Sum.inr (⟨MixedColouring.tail c,
        (c.isEven_succ_right b' hb).mp hc⟩, b')) = ⟨c, hc⟩ := by
    apply Subtype.ext; rw [evenSplitEquiv_symm_inr]; funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (colouringSplit_symm_last _ _).trans hb.symm
    · exact colouringSplit_symm_castSucc _ _ _
  rw [← inv, Equiv.apply_symm_apply]

/-! ### Forward computation of oddSplitEquiv -/

/-- Compute `oddSplitEquiv` forward via its inverse, last colour
even. -/
theorem oddSplitEquiv_inl {k ℓ d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (hc : ¬ c.IsEven)
    (a' : Fin k) (ha : c (Fin.last d) = Sum.inl a') :
    oddSplitEquiv k ℓ d ⟨c, hc⟩ =
      Sum.inl (⟨MixedColouring.tail c,
        (c.isEven_succ_left a' ha).not.mp hc⟩, a') := by
  have inv : (oddSplitEquiv k ℓ d).symm
      (Sum.inl (⟨MixedColouring.tail c,
        (c.isEven_succ_left a' ha).not.mp hc⟩, a')) = ⟨c, hc⟩ := by
    apply Subtype.ext; rw [oddSplitEquiv_symm_inl]; funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (colouringSplit_symm_last _ _).trans ha.symm
    · exact colouringSplit_symm_castSucc _ _ _
  rw [← inv, Equiv.apply_symm_apply]

/-- Compute `oddSplitEquiv` forward via its inverse, last colour
odd. -/
theorem oddSplitEquiv_inr {k ℓ d : ℕ}
    (c : MixedColouring k ℓ (d + 1)) (hc : ¬ c.IsEven)
    (b' : Fin (2 * ℓ)) (hb : c (Fin.last d) = Sum.inr b') :
    oddSplitEquiv k ℓ d ⟨c, hc⟩ =
      Sum.inr (⟨MixedColouring.tail c,
        Decidable.not_not.mp ((c.isEven_succ_right b' hb).not.mp hc)⟩,
        b') := by
  have inv : (oddSplitEquiv k ℓ d).symm
      (Sum.inr (⟨MixedColouring.tail c,
        Decidable.not_not.mp ((c.isEven_succ_right b' hb).not.mp hc)⟩,
        b')) = ⟨c, hc⟩ := by
    apply Subtype.ext; rw [oddSplitEquiv_symm_inr]; funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (colouringSplit_symm_last _ _).trans hb.symm
    · exact colouringSplit_symm_castSucc _ _ _
  rw [← inv, Equiv.apply_symm_apply]

/-! ### ColourPowerStep evaluation -/

/-- `colourPowerStep.evenEquiv` at a colouring whose last colour
is even: the value comes from the even-even channel. -/
theorem cps_even_at_inl {k ℓ d : ℕ}
    (z₁ : ({c : MixedColouring k ℓ d // c.IsEven} → ℂ) ⊗[ℂ]
      (Fin k → ℂ))
    (z₂ : ({c : MixedColouring k ℓ d // ¬ c.IsEven} → ℂ) ⊗[ℂ]
      (Fin (2 * ℓ) → ℂ))
    (c : MixedColouring k ℓ (d + 1)) (hc : c.IsEven)
    (a' : Fin k) (ha : c (Fin.last d) = Sum.inl a') :
    (colourPowerStep k ℓ d).evenEquiv (z₁, z₂) ⟨c, hc⟩ =
      funTensorFun _ _ z₁
        (⟨MixedColouring.tail c,
          (c.isEven_succ_left a' ha).mp hc⟩, a') := by
  show Sum.elim (fun p => funTensorFun _ _ z₁ p)
    (fun q => funTensorFun _ _ z₂ q)
    (evenSplitEquiv k ℓ d ⟨c, hc⟩) = _
  simp only [evenSplitEquiv_inl c hc a' ha, Sum.elim_inl]

/-- `colourPowerStep.evenEquiv` at a colouring whose last colour
is odd: the value comes from the odd-odd channel. -/
theorem cps_even_at_inr {k ℓ d : ℕ}
    (z₁ : ({c : MixedColouring k ℓ d // c.IsEven} → ℂ) ⊗[ℂ]
      (Fin k → ℂ))
    (z₂ : ({c : MixedColouring k ℓ d // ¬ c.IsEven} → ℂ) ⊗[ℂ]
      (Fin (2 * ℓ) → ℂ))
    (c : MixedColouring k ℓ (d + 1)) (hc : c.IsEven)
    (b' : Fin (2 * ℓ)) (hb : c (Fin.last d) = Sum.inr b') :
    (colourPowerStep k ℓ d).evenEquiv (z₁, z₂) ⟨c, hc⟩ =
      funTensorFun _ _ z₂
        (⟨MixedColouring.tail c,
          (c.isEven_succ_right b' hb).mp hc⟩, b') := by
  show Sum.elim (fun p => funTensorFun _ _ z₁ p)
    (fun q => funTensorFun _ _ z₂ q)
    (evenSplitEquiv k ℓ d ⟨c, hc⟩) = _
  simp only [evenSplitEquiv_inr c hc b' hb, Sum.elim_inr]

/-- `colourPowerStep.oddEquiv` at a colouring whose last colour
is even: the value comes from the odd-even channel. -/
theorem cps_odd_at_inl {k ℓ d : ℕ}
    (z₁ : ({c : MixedColouring k ℓ d // c.IsEven} → ℂ) ⊗[ℂ]
      (Fin (2 * ℓ) → ℂ))
    (z₂ : ({c : MixedColouring k ℓ d // ¬ c.IsEven} → ℂ) ⊗[ℂ]
      (Fin k → ℂ))
    (c : MixedColouring k ℓ (d + 1)) (hc : ¬ c.IsEven)
    (a' : Fin k) (ha : c (Fin.last d) = Sum.inl a') :
    (colourPowerStep k ℓ d).oddEquiv (z₁, z₂) ⟨c, hc⟩ =
      funTensorFun _ _ z₂
        (⟨MixedColouring.tail c,
          (c.isEven_succ_left a' ha).not.mp hc⟩, a') := by
  -- cps.oddEquiv = (prodCongr ftf ftf).trans (sumArrow.symm.trans (piCongrLeft'
  --   sumComm.trans piCongrLeft' oddSplit.symm))
  -- At oddSplit(c,hc) = inl(⟨tail c, ¬ tail.IsEven⟩, a'):
  -- piCongrLeft' oddSplit.symm precomposes with oddSplit, giving oddSplit(c,hc)
  --   = inl(...)
  -- piCongrLeft' sumComm precomposes with sumComm, so inl -> inr via
  --   sumComm.symm
  --   Wait no. piCongrLeft' is PRECOMPOSITION.
  --   Let f = piCongrLeft' oddSplit.symm, g = piCongrLeft' sumComm.
  --   Then (g.trans f) sends φ to φ ∘ oddSplit.symm ∘ sumComm.symm.
  --   No: (f.trans g)(x) = g(f(x)).
  --   f(x) = x ∘ sumComm.symm
  --   g(y) = y ∘ oddSplit.symm
  -- So (sumArrow.symm.trans f.trans g)(x) at ⟨c,hc⟩ = (sumArrow.symm x) ∘
  --   sumComm.symm ∘ oddSplit.symm at ⟨c,hc⟩
  --   Wait, let me look at the definition more carefully.
  -- The oddEquiv definition is:
  --   (prodCongr ftf_eo ftf_oe).trans
  -- (sumArrow.symm.trans ((piCongrLeft' sumComm).trans (piCongrLeft'
  --   oddSplit.symm)))
  -- So for input (z₁, z₂):
  --   Step 1: prodCongr ftf_eo ftf_oe (z₁, z₂) = (ftf z₁, ftf z₂)
  --   Step 2: sumArrow.symm (ftf z₁, ftf z₂) = Sum.elim (ftf z₁) (ftf z₂)
  --   Step 3: piCongrLeft' sumComm: precompose with sumComm.symm
  --     At Sum.inl(c₀_odd, a'): sumComm.symm(Sum.inl x) = Sum.inr x
  --       so the value is Sum.elim (ftf z₁) (ftf z₂) (Sum.inr(c₀_odd, a'))
  --       = ftf z₂ (c₀_odd, a')
  --     At Sum.inr(c₀_even, b'): sumComm.symm(Sum.inr x) = Sum.inl x
  --       so the value is ftf z₁ (c₀_even, b')
  --   Step 4: piCongrLeft' oddSplit.symm: precompose with oddSplit
  --     At ⟨c, hc⟩: oddSplit(⟨c, hc⟩) = Sum.inl(⟨tail c, ¬ tail.IsEven⟩, a')
  --       so the value from Step 3 is ftf z₂ (⟨tail c, ht⟩, a')
  show (Sum.elim (funTensorFun _ _ z₁) (funTensorFun _ _ z₂))
    ((Equiv.sumComm _ _).symm
      (oddSplitEquiv k ℓ d ⟨c, hc⟩)) = _
  simp only [oddSplitEquiv_inl c hc a' ha, Equiv.sumComm_symm,
    Equiv.sumComm_apply, Sum.swap_inl, Sum.elim_inr]

/-- `colourPowerStep.oddEquiv` at a colouring whose last colour
is odd: the value comes from the even-odd channel. -/
theorem cps_odd_at_inr {k ℓ d : ℕ}
    (z₁ : ({c : MixedColouring k ℓ d // c.IsEven} → ℂ) ⊗[ℂ]
      (Fin (2 * ℓ) → ℂ))
    (z₂ : ({c : MixedColouring k ℓ d // ¬ c.IsEven} → ℂ) ⊗[ℂ]
      (Fin k → ℂ))
    (c : MixedColouring k ℓ (d + 1)) (hc : ¬ c.IsEven)
    (b' : Fin (2 * ℓ)) (hb : c (Fin.last d) = Sum.inr b') :
    (colourPowerStep k ℓ d).oddEquiv (z₁, z₂) ⟨c, hc⟩ =
      funTensorFun _ _ z₁
        (⟨MixedColouring.tail c,
          Decidable.not_not.mp
            ((c.isEven_succ_right b' hb).not.mp hc)⟩, b') := by
  show (Sum.elim (funTensorFun _ _ z₁) (funTensorFun _ _ z₂))
    ((Equiv.sumComm _ _).symm
      (oddSplitEquiv k ℓ d ⟨c, hc⟩)) = _
  simp only [oddSplitEquiv_inr c hc b' hb, Equiv.sumComm_symm,
    Equiv.sumComm_apply, Sum.swap_inr, Sum.elim_inl]

/-! ### Chain computation helpers -/

/-- The associator inverse on a pure ee tensor. -/
private theorem assoc_inv_ee_tmul {k ℓ a b : ℕ}
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (w₁ : (superPow (stdSuperPair k ℓ) b).even)
    (x₁ : (stdSuperPair k ℓ).even) :
    (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).evenMap
      (evenPair v ((w₁ ⊗ₜ[ℂ] x₁,
        (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ] (stdSuperPair k ℓ).odd)) :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
          (stdSuperPair k ℓ)).even)))
          =
    (((evenPair v w₁) ⊗ₜ[ℂ] x₁,
      (0 : ((SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)).odd ⊗[ℂ] (stdSuperPair k ℓ).odd))) :
      (SuperVect.tensorObj (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)) (stdSuperPair k ℓ)).even) := by
  show (SuperVect.assocAux _ _ _ _ _ _).symm
      ((v ⊗ₜ[ℂ] ((w₁ ⊗ₜ[ℂ] x₁, (0 : _)) : _), (0 : _)) : _) = _
  exact SuperVect.assocAux_symm_ee v w₁ x₁

/-- The associator inverse on a pure eo tensor. -/
private theorem assoc_inv_eo_tmul {k ℓ a b : ℕ}
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (w₂ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).evenMap
      (evenPair v (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
        (stdSuperPair k ℓ).even), w₂ ⊗ₜ[ℂ] x₂) :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
          (stdSuperPair k ℓ)).even)))
          =
    (((0 : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)).even ⊗[ℂ] (stdSuperPair k ℓ).even),
      ((v ⊗ₜ[ℂ] w₂, (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
        (superPow (stdSuperPair k ℓ) b).even)) ⊗ₜ[ℂ] x₂)) :
      (SuperVect.tensorObj (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)) (stdSuperPair k ℓ)).even) := by
  show (SuperVect.assocAux _ _ _ _ _ _).symm
      ((v ⊗ₜ[ℂ] (((0 : _), w₂ ⊗ₜ[ℂ] x₂) : _), (0 : _)) : _) = _
  exact SuperVect.assocAux_symm_eo v w₂ x₂

/-- The associator inverse oddMap on a pure eo tensor. -/
private theorem assoc_inv_odd_eo_tmul {k ℓ a b : ℕ}
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (w₂ : (superPow (stdSuperPair k ℓ) b).even)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).oddMap
      ((v ⊗ₜ[ℂ] ((w₂ ⊗ₜ[ℂ] x₂,
        (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even)) :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
          (stdSuperPair k ℓ)).odd),
      (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
          (stdSuperPair k ℓ)).even))
          :
      (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
          (stdSuperPair k ℓ))).odd))
          =
    (((evenPair v w₂) ⊗ₜ[ℂ] x₂,
      (0 : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)).odd ⊗[ℂ] (stdSuperPair k ℓ).even)) :
      (SuperVect.tensorObj (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)) (stdSuperPair k ℓ)).odd) := by
  show (SuperVect.assocAux _ _ _ _ _ _).symm
      ((v ⊗ₜ[ℂ] ((w₂ ⊗ₜ[ℂ] x₂, (0 : _)) : _), (0 : _)) : _) = _
  exact SuperVect.assocAux_symm_ee v w₂ x₂

/-- The associator inverse oddMap on a pure oe tensor. -/
private theorem assoc_inv_odd_oe_tmul {k ℓ a b : ℕ}
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (w₁ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₁ : (stdSuperPair k ℓ).even) :
    (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
        (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).oddMap
      ((v ⊗ₜ[ℂ] (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd), w₁ ⊗ₜ[ℂ] x₁) :
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
          (stdSuperPair k ℓ)).odd),
      (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
          (stdSuperPair k ℓ)).even))
          :
      (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
          (stdSuperPair k ℓ))).odd))
          =
    (((0 : (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)).even ⊗[ℂ] (stdSuperPair k ℓ).odd),
      ((v ⊗ₜ[ℂ] w₁, (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
        (superPow (stdSuperPair k ℓ) b).even)) ⊗ₜ[ℂ] x₁)) :
      (SuperVect.tensorObj (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b)) (stdSuperPair k ℓ)).odd) := by
  show (SuperVect.assocAux _ _ _ _ _ _).symm
      ((v ⊗ₜ[ℂ] (((0 : _), w₁ ⊗ₜ[ℂ] x₁) : _), (0 : _)) : _) = _
  exact SuperVect.assocAux_symm_eo v w₁ x₁

/-! ### Full chain reduction on pure tensor generators -/

-- Raised budget: the merge, the colouring equivalence at arity
-- `a + (b+1)` and the tensor step all unfold on a single pure
-- tensor; four such chains, one per parity pattern.
/-- The full chain on a pure ee tensor: the LHS of the inductive
step reduces to `cps` applied to the IH tensor. -/
private theorem chain_even_ee {k ℓ a b : ℕ}
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (w₁ : (superPow (stdSuperPair k ℓ) b).even)
    (x₁ : (stdSuperPair k ℓ).even) :
    (colourPowerEquiv k ℓ (a + (b + 1))).evenEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).evenMap
          (evenPair v ((w₁ ⊗ₜ[ℂ] x₁,
            (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
              (stdSuperPair k ℓ).odd)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
              (stdSuperPair k ℓ)).even)))) =
      (colourPowerStep k ℓ (a + b)).evenEquiv
        (((colourPowerEquiv k ℓ (a + b)).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a b :
              SuperVect.Hom _ _).evenMap
              (evenPair v w₁))) ⊗ₜ[ℂ] x₁,
          (0 : ({c : MixedColouring k ℓ (a + b) // ¬ c.IsEven} → ℂ)
            ⊗[ℂ] (Fin (2 * ℓ) → ℂ)))) := by
  -- Unfold cpe(a+(b+1)) = cps ∘ tc and pm(a,b+1) = (pm ▷ V) ∘ α⁻¹
  show (colourPowerStep k ℓ (a + b)).evenEquiv
      ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ (a + b))
          (SuperLinearEquiv.refl (stdSuperPair k ℓ))).evenEquiv
        ((powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ :
          SuperVect.Hom _ _).evenMap
          (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).evenMap
            (evenPair v ((w₁ ⊗ₜ[ℂ] x₁, (0 : _)) : _))))) = _
  refine congr_arg (colourPowerStep k ℓ (a + b)).evenEquiv ?_
  rw [assoc_inv_ee_tmul v w₁ x₁]
  have hid_e : (SuperVect.Hom.id (stdSuperPair k ℓ)).evenMap =
      LinearMap.id := rfl
  simp only [MonoidalCategoryStruct.whiskerRight,
    SuperVect.tensorHom_evenMap, hid_e]
  show LinearEquiv.prodCongr
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).evenEquiv
      (LinearEquiv.refl ℂ _))
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).oddEquiv
      (LinearEquiv.refl ℂ _))
    (((powMerge (stdSuperPair k ℓ) a b : SuperVect.Hom _ _).evenMap
        (evenPair v w₁) ⊗ₜ[ℂ] x₁, (0 : _))) = _
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

-- As for the ee generator, with the odd second factor.
/-- The full chain on a pure eo tensor: the LHS reduces to `cps`
applied to the odd-IH tensor. -/
private theorem chain_even_eo {k ℓ a b : ℕ}
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (w₂ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (colourPowerEquiv k ℓ (a + (b + 1))).evenEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).evenMap
          (evenPair v (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
              (stdSuperPair k ℓ).even),
            w₂ ⊗ₜ[ℂ] x₂) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
              (stdSuperPair k ℓ)).even)))) =
      (colourPowerStep k ℓ (a + b)).evenEquiv
        (((0 : ({c : MixedColouring k ℓ (a + b) // c.IsEven} → ℂ)
            ⊗[ℂ] (Fin k → ℂ)),
          (colourPowerEquiv k ℓ (a + b)).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a b :
              SuperVect.Hom _ _).oddMap
              ((v ⊗ₜ[ℂ] w₂,
                (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).even)) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).odd))
              ) ⊗ₜ[ℂ] x₂)) := by
  -- Unfold cpe(a+(b+1)) = cps ∘ tc and pm(a,b+1) = (pm ▷ V) ∘ α⁻¹
  show (colourPowerStep k ℓ (a + b)).evenEquiv
      ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ (a + b))
          (SuperLinearEquiv.refl (stdSuperPair k ℓ))).evenEquiv
        ((powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ :
          SuperVect.Hom _ _).evenMap
          (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).evenMap
            (evenPair v (((0 : _), w₂ ⊗ₜ[ℂ] x₂) : _))))) = _
  refine congr_arg (colourPowerStep k ℓ (a + b)).evenEquiv ?_
  rw [assoc_inv_eo_tmul v w₂ x₂]
  have hid_o : (SuperVect.Hom.id (stdSuperPair k ℓ)).oddMap =
      LinearMap.id := rfl
  simp only [MonoidalCategoryStruct.whiskerRight,
    SuperVect.tensorHom_evenMap, hid_o]
  show LinearEquiv.prodCongr
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).evenEquiv
      (LinearEquiv.refl ℂ _))
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).oddEquiv
      (LinearEquiv.refl ℂ _))
    (((0 : _),
      ((powMerge (stdSuperPair k ℓ) a b : SuperVect.Hom _ _).oddMap
        ((v ⊗ₜ[ℂ] w₂, (0 : _)) : _)) ⊗ₜ[ℂ] x₂)) = _
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

/-- The RHS chain on a pure ee tensor: `cpe(b+1)` on `(t ⊗ₜ x, 0)`
reduces to `cps` applied to the transported tensor. -/
theorem rhs_even_ee {k ℓ b : ℕ}
    (w₁ : (superPow (stdSuperPair k ℓ) b).even)
    (x₁ : (stdSuperPair k ℓ).even) :
    (colourPowerEquiv k ℓ (b + 1)).evenEquiv
        ((w₁ ⊗ₜ[ℂ] x₁,
          (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
            (stdSuperPair k ℓ).odd)) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).even) =
      (colourPowerStep k ℓ b).evenEquiv
        (((colourPowerEquiv k ℓ b).evenEquiv w₁ ⊗ₜ[ℂ] x₁,
          (0 : ({c : MixedColouring k ℓ b // ¬ c.IsEven} → ℂ)
            ⊗[ℂ] (Fin (2 * ℓ) → ℂ)))) := by
  show (colourPowerStep k ℓ b).evenEquiv
      (LinearEquiv.prodCongr
        (TensorProduct.congr (colourPowerEquiv k ℓ b).evenEquiv
          (LinearEquiv.refl ℂ _))
        (TensorProduct.congr (colourPowerEquiv k ℓ b).oddEquiv
          (LinearEquiv.refl ℂ _))
        ((w₁ ⊗ₜ[ℂ] x₁, (0 : _)))) = _
  refine congr_arg (colourPowerStep k ℓ b).evenEquiv ?_
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

/-- The RHS chain on a pure oo tensor: `cpe(b+1)` on `(0, s ⊗ₜ x)`
reduces to `cps` applied to the transported tensor. -/
theorem rhs_even_oo {k ℓ b : ℕ}
    (w₂ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (colourPowerEquiv k ℓ (b + 1)).evenEquiv
        (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
            (stdSuperPair k ℓ).even),
          w₂ ⊗ₜ[ℂ] x₂) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).even) =
      (colourPowerStep k ℓ b).evenEquiv
        (((0 : ({c : MixedColouring k ℓ b // c.IsEven} → ℂ)
            ⊗[ℂ] (Fin k → ℂ)),
          (colourPowerEquiv k ℓ b).oddEquiv w₂ ⊗ₜ[ℂ] x₂)) := by
  show (colourPowerStep k ℓ b).evenEquiv
      (LinearEquiv.prodCongr
        (TensorProduct.congr (colourPowerEquiv k ℓ b).evenEquiv
          (LinearEquiv.refl ℂ _))
        (TensorProduct.congr (colourPowerEquiv k ℓ b).oddEquiv
          (LinearEquiv.refl ℂ _))
        (((0 : _), w₂ ⊗ₜ[ℂ] x₂))) = _
  refine congr_arg (colourPowerStep k ℓ b).evenEquiv ?_
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

-- As for the even chains, on the odd component.
/-- Full chain (odd, eo generator): the LHS on a pure `(t ⊗ x, 0)` odd tensor
reduces to `cps ∘ cpe ∘ powMerge` on the even pair. -/
private theorem chain_odd_eo {k ℓ a b : ℕ}
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (w₂ : (superPow (stdSuperPair k ℓ) b).even)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (colourPowerEquiv k ℓ (a + (b + 1))).oddEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).oddMap
          ((v ⊗ₜ[ℂ] ((w₂ ⊗ₜ[ℂ] x₂,
            (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
              (stdSuperPair k ℓ).even)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
              (stdSuperPair k ℓ)).odd),
          (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
              (stdSuperPair k ℓ)).even)) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
            (superPow (stdSuperPair k ℓ) (b + 1))).odd))) =
      (colourPowerStep k ℓ (a + b)).oddEquiv
        (((colourPowerEquiv k ℓ (a + b)).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a b :
              SuperVect.Hom _ _).evenMap
              (evenPair v w₂))) ⊗ₜ[ℂ] x₂,
          (0 : ({c : MixedColouring k ℓ (a + b) // ¬ c.IsEven} → ℂ)
            ⊗[ℂ] (Fin k → ℂ)))) := by
  show (colourPowerStep k ℓ (a + b)).oddEquiv
      ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ (a + b))
          (SuperLinearEquiv.refl (stdSuperPair k ℓ))).oddEquiv
        ((powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ :
          SuperVect.Hom _ _).oddMap
          (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).oddMap
            ((v ⊗ₜ[ℂ] ((w₂ ⊗ₜ[ℂ] x₂,
              (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
                (stdSuperPair k ℓ).even)) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).odd),
            (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).even)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ))).odd)))) = _
  refine congr_arg (colourPowerStep k ℓ (a + b)).oddEquiv ?_
  erw [assoc_inv_odd_eo_tmul v w₂ x₂]
  have hid_o : (SuperVect.Hom.id (stdSuperPair k ℓ)).oddMap =
      LinearMap.id := rfl
  have hid_e : (SuperVect.Hom.id (stdSuperPair k ℓ)).evenMap =
      LinearMap.id := rfl
  simp only [MonoidalCategoryStruct.whiskerRight,
    SuperVect.tensorHom_oddMap, hid_o, hid_e]
  show LinearEquiv.prodCongr
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).evenEquiv
      (LinearEquiv.refl ℂ _))
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).oddEquiv
      (LinearEquiv.refl ℂ _))
    (((powMerge (stdSuperPair k ℓ) a b : SuperVect.Hom _ _).evenMap
        (evenPair v w₂) ⊗ₜ[ℂ] x₂, (0 : _))) = _
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

-- As for the even chains, on the odd component.
/-- Full chain (odd, oe generator): the LHS on a pure `(0, s ⊗ x)` odd tensor
reduces to `cps ∘ cpe ∘ powMerge` on the odd pair. -/
private theorem chain_odd_oe {k ℓ a b : ℕ}
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (w₁ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₁ : (stdSuperPair k ℓ).even) :
    (colourPowerEquiv k ℓ (a + (b + 1))).oddEquiv
        (((powMerge (stdSuperPair k ℓ) a (b + 1) :
          SuperVect.Hom _ _).oddMap
          ((v ⊗ₜ[ℂ] (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
              (stdSuperPair k ℓ).odd),
            w₁ ⊗ₜ[ℂ] x₁) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
              (stdSuperPair k ℓ)).odd),
          (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
              (stdSuperPair k ℓ)).even)) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
            (superPow (stdSuperPair k ℓ) (b + 1))).odd))) =
      (colourPowerStep k ℓ (a + b)).oddEquiv
        (((0 : ({c : MixedColouring k ℓ (a + b) // c.IsEven} → ℂ)
            ⊗[ℂ] (Fin (2 * ℓ) → ℂ)),
          (colourPowerEquiv k ℓ (a + b)).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a b :
              SuperVect.Hom _ _).oddMap
              ((v ⊗ₜ[ℂ] w₁,
                (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
                  (superPow (stdSuperPair k ℓ) b).even)) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).odd)))
            ⊗ₜ[ℂ] x₁)) := by
  show (colourPowerStep k ℓ (a + b)).oddEquiv
      ((SuperLinearEquiv.tensorCongr (colourPowerEquiv k ℓ (a + b))
          (SuperLinearEquiv.refl (stdSuperPair k ℓ))).oddEquiv
        ((powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ :
          SuperVect.Hom _ _).oddMap
          (((α_ (superPow (stdSuperPair k ℓ) a) (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).inv : SuperVect.Hom _ _).oddMap
            ((v ⊗ₜ[ℂ] (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
                (stdSuperPair k ℓ).odd),
              w₁ ⊗ₜ[ℂ] x₁) :
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).odd),
            (0 : (superPow (stdSuperPair k ℓ) a).odd ⊗[ℂ]
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ)).even)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
                (stdSuperPair k ℓ))).odd)))) = _
  refine congr_arg (colourPowerStep k ℓ (a + b)).oddEquiv ?_
  erw [assoc_inv_odd_oe_tmul v w₁ x₁]
  have hid_o : (SuperVect.Hom.id (stdSuperPair k ℓ)).oddMap =
      LinearMap.id := rfl
  have hid_e : (SuperVect.Hom.id (stdSuperPair k ℓ)).evenMap =
      LinearMap.id := rfl
  simp only [MonoidalCategoryStruct.whiskerRight,
    SuperVect.tensorHom_oddMap, hid_o, hid_e]
  show LinearEquiv.prodCongr
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).evenEquiv
      (LinearEquiv.refl ℂ _))
    (TensorProduct.congr (colourPowerEquiv k ℓ (a + b)).oddEquiv
      (LinearEquiv.refl ℂ _))
    (((0 : _),
      ((powMerge (stdSuperPair k ℓ) a b : SuperVect.Hom _ _).oddMap
        ((v ⊗ₜ[ℂ] w₁, (0 : _)) : _)) ⊗ₜ[ℂ] x₁)) = _
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

/-- The RHS chain on a pure eo tensor (odd part): `cpe(b+1)` on
`(t ⊗ₜ x, 0)` reduces to `cps` applied to the transported tensor. -/
theorem rhs_odd_eo {k ℓ b : ℕ}
    (w₂ : (superPow (stdSuperPair k ℓ) b).even)
    (x₂ : (stdSuperPair k ℓ).odd) :
    (colourPowerEquiv k ℓ (b + 1)).oddEquiv
        ((w₂ ⊗ₜ[ℂ] x₂,
          (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
            (stdSuperPair k ℓ).even)) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).odd) =
      (colourPowerStep k ℓ b).oddEquiv
        (((colourPowerEquiv k ℓ b).evenEquiv w₂ ⊗ₜ[ℂ] x₂,
          (0 : ({c : MixedColouring k ℓ b // ¬ c.IsEven} → ℂ)
            ⊗[ℂ] (Fin k → ℂ)))) := by
  show (colourPowerStep k ℓ b).oddEquiv
      (LinearEquiv.prodCongr
        (TensorProduct.congr (colourPowerEquiv k ℓ b).evenEquiv
          (LinearEquiv.refl ℂ _))
        (TensorProduct.congr (colourPowerEquiv k ℓ b).oddEquiv
          (LinearEquiv.refl ℂ _))
        ((w₂ ⊗ₜ[ℂ] x₂, (0 : _)))) = _
  refine congr_arg (colourPowerStep k ℓ b).oddEquiv ?_
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

/-- The RHS chain on a pure oe tensor (odd part): `cpe(b+1)` on
`(0, s ⊗ₜ x)` reduces to `cps` applied to the transported tensor. -/
theorem rhs_odd_oe {k ℓ b : ℕ}
    (w₁ : (superPow (stdSuperPair k ℓ) b).odd)
    (x₁ : (stdSuperPair k ℓ).even) :
    (colourPowerEquiv k ℓ (b + 1)).oddEquiv
        (((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
            (stdSuperPair k ℓ).odd),
          w₁ ⊗ₜ[ℂ] x₁) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) b)
            (stdSuperPair k ℓ)).odd) =
      (colourPowerStep k ℓ b).oddEquiv
        (((0 : ({c : MixedColouring k ℓ b // c.IsEven} → ℂ)
            ⊗[ℂ] (Fin (2 * ℓ) → ℂ)),
          (colourPowerEquiv k ℓ b).oddEquiv w₁ ⊗ₜ[ℂ] x₁)) := by
  show (colourPowerStep k ℓ b).oddEquiv
      (LinearEquiv.prodCongr
        (TensorProduct.congr (colourPowerEquiv k ℓ b).evenEquiv
          (LinearEquiv.refl ℂ _))
        (TensorProduct.congr (colourPowerEquiv k ℓ b).oddEquiv
          (LinearEquiv.refl ℂ _))
        (((0 : _), w₁ ⊗ₜ[ℂ] x₁))) = _
  refine congr_arg (colourPowerStep k ℓ b).oddEquiv ?_
  simp only [LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, map_zero]
  rfl

/-! ### The merge coordinate product rule -/

-- Raised budget: the even and odd coordinate formulas are proved
-- by one mutual induction, so both statements and all four chain
-- lemmas are elaborated in a single declaration.
/-- Combined even and odd merge coordinate formulas, proved by
mutual induction on `b`. -/
private theorem colourMerge_pair {k ℓ : ℕ} (a : ℕ)
    (v : (superPow (stdSuperPair k ℓ) a).even) :
    ∀ (b : ℕ),
    (∀ (w : (superPow (stdSuperPair k ℓ) b).even)
        (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven),
        (colourPowerEquiv k ℓ (a + b)).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a b) :
              SuperVect.Hom _ _).evenMap (evenPair v w)) ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then
            (colourPowerEquiv k ℓ a).evenEquiv v ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ b).evenEquiv w ⟨c.secondHalf,
              c.secondHalf_isEven hc h⟩
          else 0)
    ∧
    (∀ (u : (superPow (stdSuperPair k ℓ) b).odd)
        (c : MixedColouring k ℓ (a + b)) (hc : ¬ c.IsEven),
        (colourPowerEquiv k ℓ (a + b)).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a b) :
              SuperVect.Hom _ _).oddMap
              ((v ⊗ₜ[ℂ] u, 0) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) b)).odd))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then
            (colourPowerEquiv k ℓ a).evenEquiv v ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ b).oddEquiv u ⟨c.secondHalf,
              c.secondHalf_not_isEven hc h⟩
          else 0)
  | 0 => by
    constructor
    · -- ═══════ b = 0, EVEN COMPONENT ═══════
      intro w c hc
      set w' : ℂ := w with hw'
      have hpow : ((powMerge (stdSuperPair k ℓ) a 0 :
          SuperVect.Hom _ _).evenMap (evenPair v w')) = w' • v := by
        change ((SuperVect.rightUnitor
            (superPow (stdSuperPair k ℓ) a)).hom).evenMap
          (v ⊗ₜ[ℂ] w', 0) = _
        rw [SuperVect.rightUnitor_hom_evenMap]
        change (TensorProduct.rid ℂ _) (v ⊗ₜ[ℂ] w') = w' • v
        exact TensorProduct.rid_tmul v w'
      have hfh : c.firstHalf = c := c.firstHalf_zero
      have hfe : c.firstHalf.IsEven := hfh ▸ hc
      have h0 : (colourPowerEquiv k ℓ 0).evenEquiv w
          ⟨c.secondHalf, c.secondHalf_isEven hc hfe⟩ = w' := by
        show (LinearEquiv.funUnique
          {c : MixedColouring k ℓ 0 // c.IsEven} ℂ ℂ).symm w' _ = w'
        rfl
      simp only [hpow, LinearEquiv.map_smul,
        dif_pos hfe,
        show (⟨c.firstHalf, hfe⟩ :
          {c : MixedColouring k ℓ a // c.IsEven}) = ⟨c, hc⟩ from
          Subtype.ext hfh]
      change w' * (colourPowerEquiv k ℓ (a + 0)).evenEquiv v ⟨c, hc⟩ =
        (colourPowerEquiv k ℓ a).evenEquiv v ⟨c, hc⟩ *
        (colourPowerEquiv k ℓ 0).evenEquiv w' ⟨c.secondHalf,
          c.secondHalf_isEven hc hfe⟩
      rw [h0, mul_comm]; rfl
    · -- ═══════ b = 0, ODD COMPONENT ═══════
      -- The odd component of `superPow _ 0` is `PUnit`, so the whole
      -- odd side vanishes.
      intro u c hc
      have hfe : ¬ c.firstHalf.IsEven := c.firstHalf_zero ▸ hc
      simp only [dif_neg hfe]
      -- pm(a,0) = right unitor; its oddMap sends (v ⊗ₜ u, 0) to 0
      have hzero : ((powMerge (stdSuperPair k ℓ) a 0 :
          SuperVect.Hom _ _).oddMap
          ((v ⊗ₜ[ℂ] u, 0) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) 0)).odd)) = 0 := by
        change ((SuperVect.rightUnitor
            (superPow (stdSuperPair k ℓ) a)).hom).oddMap
          (v ⊗ₜ[ℂ] u, 0) = 0
        rw [SuperVect.rightUnitor_hom_oddMap]; rfl
      rw [hzero, map_zero]; rfl
  | b + 1 => by
    obtain ⟨ih_even, ih_odd⟩ := colourMerge_pair a v b
    constructor
    · -- ═══════ b + 1, EVEN COMPONENT ═══════
      intro w c hc
      obtain ⟨w_ee, w_oo⟩ := w
      -- Both sides are additive in w; decompose and reduce to generators.
      -- Helper: evenPair distributes over addition
      have ep_add : ∀ (w₁ w₂ : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even),
          evenPair v (w₁ + w₂) = evenPair v w₁ + evenPair v w₂ :=
        fun w₁ w₂ => Prod.ext (TensorProduct.tmul_add v w₁ w₂)
          (add_zero 0).symm
      -- Helper for zero pair
      have ep_zero : evenPair v (0 : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even) = (0 : _) :=
        Prod.ext (TensorProduct.tmul_zero _ v) rfl
      -- Abbreviate the goal predicate for w
      set Goal := fun (w : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even) =>
        (colourPowerEquiv k ℓ (a + (b + 1))).evenEquiv
            (((powMerge (stdSuperPair k ℓ) a (b + 1) :
              SuperVect.Hom _ _).evenMap (evenPair v w))) ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then
            (colourPowerEquiv k ℓ a).evenEquiv v ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ (b + 1)).evenEquiv w ⟨c.secondHalf,
              c.secondHalf_isEven hc h⟩
          else 0 with hGoal
      change Goal (w_ee, w_oo)
      -- Additivity: Goal(w₁ + w₂) follows from Goal(w₁) and Goal(w₂)
      have Goal_add : ∀ (w₁ w₂ : _), Goal w₁ → Goal w₂ → Goal (w₁ + w₂) := by
        intro w₁ w₂ h₁ h₂
        simp only [hGoal] at h₁ h₂ ⊢
        erw [ep_add w₁ w₂, map_add, LinearEquiv.map_add, Pi.add_apply, h₁, h₂]
        split_ifs with h
        · erw [← mul_add]; congr 1
          erw [LinearEquiv.map_add, Pi.add_apply]
        · exact add_zero 0
      -- Prove for (t, 0) by TensorProduct.induction_on
      have h_ee : ∀ t, Goal (t, (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
          (stdSuperPair k ℓ).odd)) := by
        intro t; induction t using TensorProduct.induction_on with
        | zero =>
          simp only [hGoal]
          erw [ep_zero, map_zero, LinearEquiv.map_zero, Pi.zero_apply]
          split_ifs with h
          · exact (mul_zero _).symm
          · rfl
        | tmul w₁ x₁ =>
          simp only [hGoal]
          -- Case split on the last colour of c
          rcases hcl : c (Fin.last (a + b)) with a' | b'
          · -- Last colour even: chain + cps_even_at_inl on LHS
            erw [(congr_fun (chain_even_ee v w₁ x₁) ⟨c, hc⟩).trans
              (cps_even_at_inl _ _ c hc a' hcl), funTensorFun_tmul]
            have hcl_sh : c.secondHalf (Fin.last b) = Sum.inl a' :=
              c.secondHalf_last.symm ▸ hcl
            erw [ih_even w₁ (MixedColouring.tail c)
              ((c.isEven_succ_left a' hcl).mp hc)]
            simp only [MixedColouring.firstHalf_tail,
              MixedColouring.secondHalf_tail]
            split_ifs with h
            · -- c.firstHalf.IsEven: chain + cps_even_at_inl on RHS
              erw [(congr_fun (rhs_even_ee w₁ x₁)
                  ⟨c.secondHalf, c.secondHalf_isEven hc h⟩).trans
                (cps_even_at_inl _ _ c.secondHalf
                  (c.secondHalf_isEven hc h) a' hcl_sh),
                funTensorFun_tmul]
              ring
            · -- ¬ c.firstHalf.IsEven
              simp [zero_mul]
          · -- Last colour odd: both sides vanish
            erw [(congr_fun (chain_even_ee v w₁ x₁) ⟨c, hc⟩).trans
              (cps_even_at_inr _ _ c hc b' hcl)]
            simp only [map_zero, Pi.zero_apply]
            split_ifs with h
            · have hcl_sh : c.secondHalf (Fin.last b) = Sum.inr b' :=
                c.secondHalf_last.symm ▸ hcl
              erw [(congr_fun (rhs_even_ee w₁ x₁)
                  ⟨c.secondHalf, c.secondHalf_isEven hc h⟩).trans
                (cps_even_at_inr _ _ c.secondHalf
                  (c.secondHalf_isEven hc h) b' hcl_sh)]
              simp [map_zero, mul_zero]
            · rfl
        | add t₁ t₂ ih₁ ih₂ =>
          have : ((t₁ + t₂, (0 : _)) : (SuperVect.tensorObj
              (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even) =
            ((t₁, (0 : _)) : _) + ((t₂, (0 : _)) : _) :=
            Prod.ext rfl (add_zero 0).symm
          rw [this]; exact Goal_add _ _ ih₁ ih₂
      -- Prove for (0, s) by TensorProduct.induction_on
      have h_oo : ∀ s, Goal ((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
          (stdSuperPair k ℓ).even), s) := by
        intro s; induction s using TensorProduct.induction_on with
        | zero =>
          simp only [hGoal]
          erw [ep_zero, map_zero, LinearEquiv.map_zero, Pi.zero_apply]
          split_ifs with h
          · exact (mul_zero _).symm
          · rfl
        | tmul w₂ x₂ =>
          simp only [hGoal]
          -- Case split on the last colour of c
          rcases hcl : c (Fin.last (a + b)) with a' | b'
          · -- Last colour even: both sides vanish
            erw [(congr_fun (chain_even_eo v w₂ x₂) ⟨c, hc⟩).trans
              (cps_even_at_inl _ _ c hc a' hcl)]
            simp only [map_zero, Pi.zero_apply]
            split_ifs with h
            · have hcl_sh : c.secondHalf (Fin.last b) = Sum.inl a' :=
                c.secondHalf_last.symm ▸ hcl
              erw [(congr_fun (rhs_even_oo w₂ x₂)
                  ⟨c.secondHalf, c.secondHalf_isEven hc h⟩).trans
                (cps_even_at_inl _ _ c.secondHalf
                  (c.secondHalf_isEven hc h) a' hcl_sh)]
              simp [map_zero, mul_zero]
            · rfl
          · -- Last colour odd: chain + cps_even_at_inr on LHS
            erw [(congr_fun (chain_even_eo v w₂ x₂) ⟨c, hc⟩).trans
              (cps_even_at_inr _ _ c hc b' hcl), funTensorFun_tmul]
            have hcl_sh : c.secondHalf (Fin.last b) = Sum.inr b' :=
              c.secondHalf_last.symm ▸ hcl
            erw [ih_odd w₂ (MixedColouring.tail c)
              ((c.isEven_succ_right b' hcl).mp hc)]
            simp only [MixedColouring.firstHalf_tail,
              MixedColouring.secondHalf_tail]
            split_ifs with h
            · -- c.firstHalf.IsEven: chain + cps_even_at_inr on RHS
              erw [(congr_fun (rhs_even_oo w₂ x₂)
                  ⟨c.secondHalf, c.secondHalf_isEven hc h⟩).trans
                (cps_even_at_inr _ _ c.secondHalf
                  (c.secondHalf_isEven hc h) b' hcl_sh),
                funTensorFun_tmul]
              ring
            · -- ¬ c.firstHalf.IsEven
              simp [zero_mul]
        | add s₁ s₂ ih₁ ih₂ =>
          have : (((0 : _), s₁ + s₂) : (SuperVect.tensorObj
              (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even) =
            (((0 : _), s₁) : _) + (((0 : _), s₂) : _) :=
            Prod.ext (add_zero 0).symm rfl
          rw [this]; exact Goal_add _ _ ih₁ ih₂
      -- Combine: (w_ee, w_oo) = (w_ee, 0) + (0, w_oo)
      have hw : ((w_ee, w_oo) : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).even) =
        ((w_ee, (0 : _)) : _) + (((0 : _), w_oo) : _) :=
        Prod.ext (add_zero w_ee).symm (zero_add w_oo).symm
      rw [hw]; exact Goal_add _ _ (h_ee w_ee) (h_oo w_oo)
    · -- ═══════ b + 1, ODD COMPONENT ═══════
      intro u c hc
      obtain ⟨u_eo, u_oe⟩ := u
      -- Both sides are additive in u; decompose and reduce to generators.
      -- Helper: (v ⊗ₜ ·, 0) distributes over addition
      have op_add : ∀ (u₁ u₂ : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd),
          ((v ⊗ₜ[ℂ] (u₁ + u₂), (0 : _)) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) (b + 1))).odd) =
          ((v ⊗ₜ[ℂ] u₁, (0 : _)) : _) + ((v ⊗ₜ[ℂ] u₂, (0 : _)) : _) :=
        fun u₁ u₂ => Prod.ext (TensorProduct.tmul_add v u₁ u₂)
          (add_zero 0).symm
      -- Helper for zero pair
      have op_zero : ((v ⊗ₜ[ℂ] (0 : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd), (0 : _)) :
          (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
            (superPow (stdSuperPair k ℓ) (b + 1))).odd) = (0 : _) :=
        Prod.ext (TensorProduct.tmul_zero _ v) rfl
      -- Abbreviate the goal predicate for u
      set Goal := fun (u : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd) =>
        (colourPowerEquiv k ℓ (a + (b + 1))).oddEquiv
            (((powMerge (stdSuperPair k ℓ) a (b + 1) :
              SuperVect.Hom _ _).oddMap
              ((v ⊗ₜ[ℂ] u, 0) :
                (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
                  (superPow (stdSuperPair k ℓ) (b + 1))).odd)))
            ⟨c, hc⟩ =
          if h : MixedColouring.IsEven c.firstHalf then
            (colourPowerEquiv k ℓ a).evenEquiv v ⟨c.firstHalf, h⟩ *
            (colourPowerEquiv k ℓ (b + 1)).oddEquiv u ⟨c.secondHalf,
              c.secondHalf_not_isEven hc h⟩
          else 0 with hGoal
      change Goal (u_eo, u_oe)
      -- Additivity: Goal(u₁ + u₂) follows from Goal(u₁) and Goal(u₂)
      have Goal_add : ∀ (u₁ u₂ : _), Goal u₁ → Goal u₂ → Goal (u₁ + u₂) := by
        intro u₁ u₂ h₁ h₂
        simp only [hGoal] at h₁ h₂ ⊢
        erw [op_add u₁ u₂, map_add, LinearEquiv.map_add, Pi.add_apply, h₁, h₂]
        split_ifs with h
        · erw [← mul_add]; congr 1
          erw [LinearEquiv.map_add, Pi.add_apply]
        · exact add_zero 0
      -- Prove for (t, 0) by TensorProduct.induction_on
      have h_eo : ∀ t, Goal (t, (0 : (superPow (stdSuperPair k ℓ) b).odd ⊗[ℂ]
          (stdSuperPair k ℓ).even)) := by
        intro t; induction t using TensorProduct.induction_on with
        | zero =>
          simp only [hGoal]
          erw [op_zero, map_zero, LinearEquiv.map_zero, Pi.zero_apply]
          split_ifs with h
          · exact (mul_zero _).symm
          · rfl
        | tmul w₂ x₂ =>
          simp only [hGoal]
          rcases hcl : c (Fin.last (a + b)) with a' | b'
          · -- Last colour even: both sides vanish
            erw [(congr_fun (chain_odd_eo v w₂ x₂) ⟨c, hc⟩).trans
              (cps_odd_at_inl _ _ c hc a' hcl)]
            simp only [map_zero, Pi.zero_apply]
            split_ifs with h
            · have hcl_sh : c.secondHalf (Fin.last b) = Sum.inl a' :=
                c.secondHalf_last.symm ▸ hcl
              erw [(congr_fun (rhs_odd_eo w₂ x₂)
                  ⟨c.secondHalf, c.secondHalf_not_isEven hc h⟩).trans
                (cps_odd_at_inl _ _ c.secondHalf
                  (c.secondHalf_not_isEven hc h) a' hcl_sh)]
              simp [map_zero, mul_zero]
            · rfl
          · -- Last colour odd: chain + cps_odd_at_inr + IH
            erw [(congr_fun (chain_odd_eo v w₂ x₂) ⟨c, hc⟩).trans
              (cps_odd_at_inr _ _ c hc b' hcl), funTensorFun_tmul]
            have hcl_sh : c.secondHalf (Fin.last b) = Sum.inr b' :=
              c.secondHalf_last.symm ▸ hcl
            erw [ih_even w₂ (MixedColouring.tail c)
              (Decidable.not_not.mp
                ((c.isEven_succ_right b' hcl).not.mp hc))]
            simp only [MixedColouring.firstHalf_tail,
              MixedColouring.secondHalf_tail]
            split_ifs with h
            · erw [(congr_fun (rhs_odd_eo w₂ x₂)
                  ⟨c.secondHalf, c.secondHalf_not_isEven hc h⟩).trans
                (cps_odd_at_inr _ _ c.secondHalf
                  (c.secondHalf_not_isEven hc h) b' hcl_sh),
                funTensorFun_tmul]
              ring
            · simp [zero_mul]
        | add t₁ t₂ ih₁ ih₂ =>
          have : ((t₁ + t₂, (0 : _)) : (SuperVect.tensorObj
              (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd) =
            ((t₁, (0 : _)) : _) + ((t₂, (0 : _)) : _) :=
            Prod.ext rfl (add_zero 0).symm
          rw [this]; exact Goal_add _ _ ih₁ ih₂
      -- Prove for (0, s) by TensorProduct.induction_on
      have h_oe : ∀ s, Goal ((0 : (superPow (stdSuperPair k ℓ) b).even ⊗[ℂ]
          (stdSuperPair k ℓ).odd), s) := by
        intro s; induction s using TensorProduct.induction_on with
        | zero =>
          simp only [hGoal]
          erw [op_zero, map_zero, LinearEquiv.map_zero, Pi.zero_apply]
          split_ifs with h
          · exact (mul_zero _).symm
          · rfl
        | tmul w₁ x₁ =>
          simp only [hGoal]
          rcases hcl : c (Fin.last (a + b)) with a' | b'
          · -- Last colour even: chain + cps_odd_at_inl + IH
            erw [(congr_fun (chain_odd_oe v w₁ x₁) ⟨c, hc⟩).trans
              (cps_odd_at_inl _ _ c hc a' hcl), funTensorFun_tmul]
            have hcl_sh : c.secondHalf (Fin.last b) = Sum.inl a' :=
              c.secondHalf_last.symm ▸ hcl
            erw [ih_odd w₁ (MixedColouring.tail c)
              ((c.isEven_succ_left a' hcl).not.mp hc)]
            simp only [MixedColouring.firstHalf_tail,
              MixedColouring.secondHalf_tail]
            split_ifs with h
            · erw [(congr_fun (rhs_odd_oe w₁ x₁)
                  ⟨c.secondHalf, c.secondHalf_not_isEven hc h⟩).trans
                (cps_odd_at_inl _ _ c.secondHalf
                  (c.secondHalf_not_isEven hc h) a' hcl_sh),
                funTensorFun_tmul]
              ring
            · simp [zero_mul]
          · -- Last colour odd: both sides vanish
            erw [(congr_fun (chain_odd_oe v w₁ x₁) ⟨c, hc⟩).trans
              (cps_odd_at_inr _ _ c hc b' hcl)]
            simp only [map_zero, Pi.zero_apply]
            split_ifs with h
            · have hcl_sh : c.secondHalf (Fin.last b) = Sum.inr b' :=
                c.secondHalf_last.symm ▸ hcl
              erw [(congr_fun (rhs_odd_oe w₁ x₁)
                  ⟨c.secondHalf, c.secondHalf_not_isEven hc h⟩).trans
                (cps_odd_at_inr _ _ c.secondHalf
                  (c.secondHalf_not_isEven hc h) b' hcl_sh)]
              simp [map_zero, mul_zero]
            · rfl
        | add s₁ s₂ ih₁ ih₂ =>
          have : (((0 : _), s₁ + s₂) : (SuperVect.tensorObj
              (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd) =
            (((0 : _), s₁) : _) + (((0 : _), s₂) : _) :=
            Prod.ext (add_zero 0).symm rfl
          rw [this]; exact Goal_add _ _ ih₁ ih₂
      -- Combine: (u_eo, u_oe) = (u_eo, 0) + (0, u_oe)
      have hu : ((u_eo, u_oe) : (SuperVect.tensorObj
          (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).odd) =
        ((u_eo, (0 : _)) : _) + (((0 : _), u_oe) : _) :=
        Prod.ext (add_zero u_eo).symm (zero_add u_oe).symm
      rw [hu]; exact Goal_add _ _ (h_eo u_eo) (h_oe u_oe)

-- Raised budget: specializing the mutual induction re-elaborates
-- the paired statement.
/-- **The merge coordinate product rule**: coordinates of a
merged even pair multiply over the halves, vanishing when the
halves are odd. -/
theorem colourMerge_coord {k ℓ : ℕ} (a b : ℕ)
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (w : (superPow (stdSuperPair k ℓ) b).even)
    (c : MixedColouring k ℓ (a + b)) (hc : c.IsEven) :
    (colourPowerEquiv k ℓ (a + b)).evenEquiv
        (((powMerge (stdSuperPair k ℓ) a b) :
          SuperVect.Hom _ _).evenMap (evenPair v w)) ⟨c, hc⟩ =
      if h : MixedColouring.IsEven c.firstHalf then
        (colourPowerEquiv k ℓ a).evenEquiv v ⟨c.firstHalf, h⟩ *
        (colourPowerEquiv k ℓ b).evenEquiv w ⟨c.secondHalf,
          c.secondHalf_isEven hc h⟩
      else 0 :=
  (colourMerge_pair a v b).1 w c hc

/-- **The even-odd merge coordinate product rule**: odd
coordinates of a merged even-odd pair multiply over the halves,
supported on even first halves. -/
theorem colourMerge_coord_evenOdd {k ℓ : ℕ} (a b : ℕ)
    (v : (superPow (stdSuperPair k ℓ) a).even)
    (u : (superPow (stdSuperPair k ℓ) b).odd)
    (c : MixedColouring k ℓ (a + b)) (hc : ¬ c.IsEven) :
    (colourPowerEquiv k ℓ (a + b)).oddEquiv
        (((powMerge (stdSuperPair k ℓ) a b) :
          SuperVect.Hom _ _).oddMap
          ((v ⊗ₜ[ℂ] u, 0) :
            (SuperVect.tensorObj (superPow (stdSuperPair k ℓ) a)
              (superPow (stdSuperPair k ℓ) b)).odd))
        ⟨c, hc⟩ =
      if h : MixedColouring.IsEven c.firstHalf then
        (colourPowerEquiv k ℓ a).evenEquiv v ⟨c.firstHalf, h⟩ *
        (colourPowerEquiv k ℓ b).oddEquiv u ⟨c.secondHalf,
          c.secondHalf_not_isEven hc h⟩
      else 0 :=
  (colourMerge_pair a v b).2 u c hc

end RS
