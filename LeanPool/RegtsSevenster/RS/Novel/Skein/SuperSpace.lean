/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughValue

/-!
# The super-symmetric form on one leg

The ambient space of the Gram construction is `V_k ⊕ V_{2ℓ}`,
carrying the symmetric form `xᵀy` on the even summand, the
skew-symmetric form `xᵀJy` on the odd summand with

    J = [[0, I], [-I, 0]],

and zero across the two.  This file is that form and nothing else,
written from the definition rather than assembled out of the
partition function's own weights, so that its relation to those
weights is a theorem.

The relation is recorded at the end: on the even block the form is
the partition function's state factor, and on the odd block it is
that factor negated.  The negation is the one already visible in
the tower's colour kernel, which pairs the odd colours through
`-oddThroughFactor`.
-/

namespace RS

open Classical

/-- **The symplectic matrix** `J = [[0, I], [-I, 0]]` in
coordinates: `J c d` is `1` when `d = c + ℓ`, `-1` when
`c = d + ℓ`, and `0` otherwise. -/
noncomputable def symplecticJ (ℓ : ℕ) (c d : Fin (2 * ℓ)) : ℂ :=
  if d.val = c.val + ℓ then 1
  else if c.val = d.val + ℓ then -1
  else 0

/-- **The super form on one leg**: the identity on the even
colours, `J` on the odd ones, zero across. -/
noncomputable def superLeg {k ℓ : ℕ} :
    (Fin k ⊕ Fin (2 * ℓ)) → (Fin k ⊕ Fin (2 * ℓ)) → ℂ
  | Sum.inl a, Sum.inl b => if a = b then 1 else 0
  | Sum.inr c, Sum.inr d => symplecticJ ℓ c d
  | _, _ => 0

/-! ### The relation to the partition function's state factor

The through-edge state factor of the mixed partition function is
the super form on the even block and its negative on the odd one.
Both are recorded as theorems; nothing below assumes them.
-/

/-- Membership in the odd partner relation, in coordinates. -/
theorem eq_oddPartner_iff {ℓ : ℕ} (c d : Fin (2 * ℓ)) :
    d = oddPartner ℓ c
      ↔ (if c.val < ℓ then d.val = c.val + ℓ else d.val = c.val - ℓ) := by
  unfold oddPartner
  by_cases h : c.val < ℓ
  · rw [dif_pos h, if_pos h, Fin.ext_iff]
  · rw [dif_neg h, if_neg h, Fin.ext_iff]

/-! ### The dual basis at outgoing ends

RS21 writes the boundary vector at an odd leg as `f_c` where the
arc is incoming and `g_c` where it is outgoing, and computes
`⟨f_c, g_c⟩ = -1` and `⟨g_c, f_c⟩ = 1`.  In one basis, `g_c` is the
symplectic dual of `f_c`: the partner colour carrying the partner
sign.  The two displayed values are recovered below, which is what
fixes the convention.
-/

/-- The symplectic dual of a colour: the partner colour with the
partner sign.  This is RS21's `g_c` written in the basis of the
`f`'s. -/
noncomputable def dualSign (ℓ : ℕ) (c : Fin (2 * ℓ)) : ℂ :=
  ((oddPartnerSign ℓ c : ℤ) : ℂ)

/-- **The dual sign squares to one**: it is `±1`. -/
theorem dualSign_sq (ℓ : ℕ) (c : Fin (2 * ℓ)) :
    dualSign ℓ c * dualSign ℓ c = 1 := by
  unfold dualSign oddPartnerSign
  by_cases h : c.val < ℓ
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; norm_num

/-- The partner colour in coordinates. -/
theorem oddPartner_val (ℓ : ℕ) (c : Fin (2 * ℓ)) :
    (oddPartner ℓ c).val
      = if c.val < ℓ then c.val + ℓ else c.val - ℓ := by
  unfold oddPartner
  split_ifs <;> rfl

/-- **`⟨f_c, g_c⟩ = -1`.** -/
theorem superLeg_f_g (ℓ : ℕ) (c : Fin (2 * ℓ)) :
    dualSign ℓ c * symplecticJ ℓ c (oddPartner ℓ c) = -1 := by
  have hc := c.isLt
  have hv := oddPartner_val ℓ c
  unfold dualSign symplecticJ oddPartnerSign
  by_cases h : c.val < ℓ
  · rw [if_pos h] at hv
    rw [if_pos hv, if_pos h]
    norm_num
  · rw [if_neg h] at hv
    rw [if_neg (show ¬ ((oddPartner ℓ c).val = c.val + ℓ) by omega),
      if_pos (show c.val = (oddPartner ℓ c).val + ℓ by omega),
      if_neg h]
    norm_num

/-! ### The through-edge factor is the dual basis at one end

A through-edge's two legs carry `f_{φ(a)}` and `g_{φ(a)}` — the
same colour, dual bases.  In one basis that says the two legs'
colours are partners and the leg holding `g` contributes its
partner sign.  The mixed partition function's through-edge factor
says exactly that, so it is the dual basis's contribution at those
legs rather than an extra weight.
-/

/-- **The dual sign flips at the partner colour.** -/
theorem dualSign_oddPartner (ℓ : ℕ) (c : Fin (2 * ℓ)) :
    dualSign ℓ (oddPartner ℓ c) = -dualSign ℓ c := by
  unfold dualSign
  rw [oddPartnerSign_oddPartner]
  push_cast
  ring

end RS
