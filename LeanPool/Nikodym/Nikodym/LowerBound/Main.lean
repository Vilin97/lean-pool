/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.Definition
import LeanPool.Nikodym.Nikodym.LowerBound.CarrierBound

/-!
# The Nikodym lower bound, conditional on the algebraic interface

This file implements blueprint nodes **C10** and **C11** of the lower-bound side of the sharp
finite-field Nikodym exponent, conditionally on `AlgebraInterface F d` (the not-yet-discharged
algebraic input theorems A08, J02, B03).

Let `F` be a finite field with `q` elements, `d ≥ 2`, `N ⊆ F^d` a Nikodym set and
`B = F^d \ N` its complement.

* `IsNikodym.exists_privateFamily`: `B` carries a private family of lines (node F05): through
  each `x ∈ B` the Nikodym line of `x` meets `B` only at `x`.
* `card_compl_pow_mul_card_le_of_interface` (C10): with `C = 8 d² + 1` and `m = 2 ^ (d - 1)`,
  `|B| ^ m * q ≤ C ^ m * q ^ (d m)`, from the carrier theorem C09 applied to the zero ideal
  (quotient dimension `d`, degree `1`).
* `card_ge_pow_sub_of_interface` (C11): the displayed real inequality
  `q ^ d - C q ^ (d - 2 ^ (1 - d)) ≤ |N|`, obtained from C10 by taking `m`-th roots in `ℝ`.

The unconditional statements `Nikodym.card_compl_pow_mul_card_le` and `Nikodym.card_ge_pow_sub`
in `Nikodym.Main` follow from these once an `AlgebraInterface F d` is constructed.
-/

namespace Nikodym.LowerBound

open Finset

variable {F : Type*} [Field F] [Fintype F] {d : ℕ}

/-- Blueprint C10 (via F05): the complement `B = F^d \ N` of a Nikodym set carries a private
family of lines indexed by `B`: the anchor of `x ∈ B` is `x` and its direction is a Nikodym
witness `v x`, whose line meets `B` only at `x`. -/
theorem _root_.Nikodym.IsNikodym.exists_privateFamily [DecidableEq (Fin d → F)]
    {N : Finset (Fin d → F)} (hN : IsNikodym N) :
    Nonempty (PrivateFamily F d ↥(univ \ N)) := by
  choose v hv hvN using hN
  refine ⟨⟨Subtype.val, fun x ↦ v x, fun x ↦ hv x, ?_⟩⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩ t (h : y = x + t • v x)
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at h
    exact Subtype.ext h
  · exact absurd (h ▸ hvN x t ht) (mem_sdiff.mp hy).2

/-- Blueprint C10: **the Nikodym lower bound in natural-number form**, conditional on the
algebraic interface. For a Nikodym set `N ⊆ F^d` with `d ≥ 2`, `q = |F|`, `C = 8 d² + 1` and
`m = 2 ^ (d - 1)`, one has `|F^d \ N| ^ m * q ≤ C ^ m * q ^ (d m)`. -/
theorem card_compl_pow_mul_card_le_of_interface (H : AlgebraInterface F d) (hd : 2 ≤ d)
    (N : Finset (Fin d → F)) (hN : IsNikodym N) :
    (Fintype.card F ^ d - N.card) ^ 2 ^ (d - 1) * Fintype.card F ≤
      (8 * d ^ 2 + 1) ^ 2 ^ (d - 1) * Fintype.card F ^ (d * 2 ^ (d - 1)) := by
  classical
  obtain ⟨P⟩ := hN.exists_privateFamily
  have h := PrivateFamily.carrier_bound H hd (k := d) (by omega) P (I := ⊥) Ideal.isPrime_bot
    quotDim_bot fun _ ↦ bot_le
  rwa [degree_bot, mul_one, Fintype.card_coe, card_univ_sdiff, Fintype.card_fun,
    Fintype.card_fin] at h

/-- Blueprint C11: **the Nikodym lower bound in real form**, conditional on the algebraic
interface. For a Nikodym set `N ⊆ F^d` with `d ≥ 2` and `q = |F|`,
`q ^ d - (8 d² + 1) q ^ (d - 2 ^ (1 - d)) ≤ |N|`. -/
theorem card_ge_pow_sub_of_interface (H : AlgebraInterface F d) (hd : 2 ≤ d)
    (N : Finset (Fin d → F)) (hN : IsNikodym N) :
    (Fintype.card F : ℝ) ^ d -
        (8 * d ^ 2 + 1) * (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ))) ≤
      N.card := by
  classical
  have h := card_compl_pow_mul_card_le_of_interface H hd N hN
  set q := Fintype.card F with hq_def
  set m := 2 ^ (d - 1) with hm_def
  have hm : 0 < m := by positivity
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hq : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hNq : N.card ≤ q ^ d := by
    have h := card_le_univ N
    rwa [Fintype.card_fun, Fintype.card_fin] at h
  -- the real form of C10
  have hR : ((q ^ d - N.card : ℕ) : ℝ) ^ m * q ≤ (8 * d ^ 2 + 1) ^ m * (q : ℝ) ^ (d * m) := by
    exact_mod_cast h
  -- the exponent `2 ^ (1 - d)` is `1 / m`
  have hexp : (2 : ℝ) ^ (1 - (d : ℝ)) = (m : ℝ)⁻¹ := by
    have h1 : (1 : ℝ) - d = -((d - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      push_cast
      ring
    rw [h1, Real.rpow_neg (by norm_num), Real.rpow_natCast, hm_def]
    push_cast
    rfl
  -- take `m`-th roots
  have hX : ((q ^ d - N.card : ℕ) : ℝ) ≤
      (8 * d ^ 2 + 1) * (q : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ))) := by
    rw [hexp]
    refine le_of_pow_le_pow_left₀ hm.ne' (by positivity) ?_
    have hpow : ((q : ℝ) ^ ((d : ℝ) - (m : ℝ)⁻¹)) ^ m = (q : ℝ) ^ (d * m) / q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, sub_mul, inv_mul_cancel₀ hm',
        Real.rpow_sub hq, Real.rpow_one, ← Nat.cast_mul, Real.rpow_natCast]
    rw [mul_pow, hpow, mul_div_assoc', le_div_iff₀ hq]
    exact hR
  rw [Nat.cast_sub hNq, Nat.cast_pow] at hX
  linarith

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
