/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPairing

/-!
# The colour form entries are the standard form

The single-position layer of the accompanying paper's Lemma 5.1(a):
the pinned colour
form entry agrees with the standard super form on the
corresponding basis vectors — the orthonormal pairing on even
colours, the symplectic pairing on odd colours.
-/

namespace RS

/-- On even colours the entry is the orthonormal pairing. -/
theorem colourFormEntry_even (k ℓ : ℕ) (i j : Fin k) :
    colourFormEntry k ℓ (Sum.inl i) (Sum.inl j) =
      stdFormEven k (stdE k i) (stdE k j) := by
  rw [stdFormEven_stdE]
  rfl

/-- On odd colours it is the symplectic one. -/
theorem colourFormEntry_odd (k ℓ : ℕ) (a b : Fin (2 * ℓ)) :
    colourFormEntry k ℓ (Sum.inr a) (Sum.inr b) =
      stdFormOdd ℓ (stdF ℓ a) (stdF ℓ b) := by
  rw [stdFormOdd_stdF]
  show (if a.val + ℓ = b.val then (1 : ℂ)
    else if b.val + ℓ = a.val then -1 else 0) =
    if b = oddPartner ℓ a then -(oddPartnerSign ℓ a : ℂ) else 0
  unfold oddPartner oddPartnerSign
  by_cases h : a.val < ℓ
  · rw [dif_pos h, if_pos h]
    by_cases hb : a.val + ℓ = b.val
    · rw [if_pos hb,
        if_pos (show b = ⟨a.val + ℓ, by omega⟩ from
          Fin.ext (show b.val = a.val + ℓ by omega))]
      norm_num
    · rw [if_neg hb,
        if_neg (show ¬(b.val + ℓ = a.val) by omega),
        if_neg (show ¬(b = ⟨a.val + ℓ, by omega⟩) from
          fun he => hb (by
            have hv : b.val = a.val + ℓ := congrArg Fin.val he
            omega))]
  · rw [dif_neg h, if_neg h,
      if_neg (show ¬(a.val + ℓ = b.val) by
        have := b.isLt
        omega)]
    by_cases hb : b.val + ℓ = a.val
    · rw [if_pos hb,
        if_pos (show b = ⟨a.val - ℓ, by omega⟩ from
          Fin.ext (show b.val = a.val - ℓ by omega))]
      norm_num
    · rw [if_neg hb,
        if_neg (show ¬(b = ⟨a.val - ℓ, by omega⟩) from
          fun he => hb (by
            have hv : b.val = a.val - ℓ := congrArg Fin.val he
            omega))]

end RS
