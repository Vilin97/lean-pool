/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapPeelSplit
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BasisCoord

/-!
# The diagonal cap pairing

The colour-side closed form of the cap value, defined by the very
recursion the peel induction produces: the peel coefficient at
the peeled colouring times the split factor — the smaller diagonal
against the two-position form entry, vanishing on odd halves.
-/

namespace RS

variable {k ℓ : ℕ}

/-- The peeled colouring: the inverse peel reindex. -/
def peelColour (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    MixedColouring k ℓ ((m + m) + 2) := fun j =>
  c ((capPeelPerm m)⁻¹ ((finCongr (capPeelArity m)).symm j))

/-- The peeled colouring undoes the peel reindex. -/
theorem peelColour_spec (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    (peelColour m c ∘ ⇑(finCongr (capPeelArity m))) ∘
      ⇑(capPeelPerm m) = c :=
  funext (fun x => congrArg c (by
    rw [_root_.Equiv.symm_apply_apply]
    exact _root_.Equiv.symm_apply_apply (capPeelPerm m) x))

/-- The peeled colouring is the unique solution of the peel
reindex equation. -/
theorem eq_peelColour_of (m : ℕ)
    {c : MixedColouring k ℓ ((m + 1) + (m + 1))}
    {c' : MixedColouring k ℓ ((m + m) + 2)}
    (hspec : (c' ∘ ⇑(finCongr (capPeelArity m))) ∘
      ⇑(capPeelPerm m) = c) :
    c' = peelColour m c := by
  subst hspec
  apply Eq.symm
  funext j
  change c' (finCongr (capPeelArity m) ((capPeelPerm m)
    ((capPeelPerm m)⁻¹
      ((finCongr (capPeelArity m)).symm j)))) = c' j
  rw [show (capPeelPerm m) ((capPeelPerm m)⁻¹
      ((finCongr (capPeelArity m)).symm j)) =
    (finCongr (capPeelArity m)).symm j from
    _root_.Equiv.apply_symm_apply _ _]
  rw [_root_.Equiv.apply_symm_apply]

/-- The peeled colouring preserves parity. -/
theorem peelColour_isEven (m : ℕ)
    {c : MixedColouring k ℓ ((m + 1) + (m + 1))}
    (hc : c.IsEven) :
    MixedColouring.IsEven (peelColour m c) := by
  have h1 : MixedColouring.IsEven
      (c ∘ ⇑((capPeelPerm m)⁻¹)) := hc.comp _
  have h2 : peelColour m c =
      (c ∘ ⇑((capPeelPerm m)⁻¹)) ∘
        ⇑(finCongr (capPeelArity m).symm) := by
    funext j
    change c ((capPeelPerm m)⁻¹
      ((finCongr (capPeelArity m)).symm j)) = _
    rfl
  rw [h2]
  exact (isEven_comp_finCongr (capPeelArity m).symm _).mpr h1

/-- The peeled colouring on values. -/
theorem peelColour_apply (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1)))
    (j : Fin ((m + m) + 2)) :
    peelColour m c j = c ⟨capPeelInv m j.val, by
      have := j.isLt
      unfold capPeelInv
      split_ifs <;> omega⟩ :=
  congrArg c (Fin.ext rfl)

/-- The peel fixes the low first-half slots. -/
theorem peelColour_low (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1)))
    (j : Fin ((m + m) + 2)) (h : j.val < m) :
    peelColour m c j = c ⟨j.val, by omega⟩ := by
  rw [peelColour_apply]
  refine congrArg c (Fin.ext ?_)
  change capPeelInv m j.val = j.val
  unfold capPeelInv
  rw [ite_eq_left h]

/-- The second peeled-pair slot carries the last slot. -/
theorem peelColour_pairSnd (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    peelColour m c ⟨(m + m) + 1, by omega⟩ =
      c ⟨(m + 1) + m, by omega⟩ := by
  rw [peelColour_apply]
  refine congrArg c (Fin.ext ?_)
  change capPeelInv m ((m + m) + 1) = (m + 1) + m
  unfold capPeelInv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  omega

/-- **The diagonal cap pairing**: the colour-side cap value. -/
noncomputable def betaDiag :
    (m : ℕ) → MixedColouring k ℓ (m + m) → ℂ
  | 0, _ => 1
  | m + 1, c =>
      wordSign (adjWord (capPeelPerm m))
          (peelColour m c ∘ ⇑(finCongr (capPeelArity m))) *
        (if _h : MixedColouring.IsEven
            (MixedColouring.firstHalf (a := m + m) (b := 2)
              (peelColour m c)) then
          betaDiag m (MixedColouring.firstHalf
              (a := m + m) (b := 2) (peelColour m c)) *
            colourFormEntry k ℓ
              (MixedColouring.secondHalf
                (a := m + m) (b := 2) (peelColour m c) 0)
              (MixedColouring.secondHalf
                (a := m + m) (b := 2) (peelColour m c) 1)
        else 0)

/-- The base of the diagonal pairing. -/
theorem betaDiag_zero (c : MixedColouring k ℓ 0) :
    betaDiag 0 c = 1 := rfl

/-- The successor equation of the diagonal pairing. -/
theorem betaDiag_succ (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    betaDiag (m + 1) c =
      wordSign (adjWord (capPeelPerm m))
          (peelColour m c ∘ ⇑(finCongr (capPeelArity m))) *
        (if _h : MixedColouring.IsEven
            (MixedColouring.firstHalf (a := m + m) (b := 2)
              (peelColour m c)) then
          betaDiag m (MixedColouring.firstHalf
              (a := m + m) (b := 2) (peelColour m c)) *
            colourFormEntry k ℓ
              (MixedColouring.secondHalf
                (a := m + m) (b := 2) (peelColour m c) 0)
              (MixedColouring.secondHalf
                (a := m + m) (b := 2) (peelColour m c) 1)
        else 0) := rfl

end RS
