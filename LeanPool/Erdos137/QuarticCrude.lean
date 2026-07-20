/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.BlockFramework

/-!
# Erdős Problem #137: the quartic (`g = 4`) crude block route — sharp threshold `n > k^4`

This module instantiates the generic crude (non-smooth) block route `master_ineq_crude_g`
(`BlockFramework`, PART E) at the block length `g = 4`. The crude master inequality reads
`n ^ (4 - 2) ≤ k ^ (2 * 4)`, i.e. `n ^ 2 ≤ k ^ 8`, equivalently `n ≤ k ^ 4`. So under the quartic
block radical hypothesis `BlockRadLB4`, for `k ≥ 4` and `n > k^4` the product `F k n` is **not
powerful** (`not_powerful_of_large_g4`); for each fixed `k ≥ 4`, `F k n` is powerful for only
finitely many `n` (`g4_crude_finiteness`).

## Why `g = 4`

The quartic crude route gives the **fully explicit** threshold `n > k^4`, with no `o(1)` and no
unformalized Mertens input. This is the complementary high-`n` input for the usual
squarefree-counting reduction: combined with the low-range prime obstruction and Pandey's
unconditional squarefree
short-interval count below `k ^ {5 + δ}`, it is the high-`n` part of the intended joint `(n, k)`
finiteness argument
(Pandey is NOT formalized here). The crude exponent is `2g/(g-2) = 2 + 4/(g-2)`, so `g = 4` is the
**first (minimal) block length for which the crude threshold drops below the `k^5` squarefree
ceiling**, and it gives the clean integer threshold `k^4`. Larger fixed block lengths give still
smaller crude exponents — for example `g = 6` gives `k^3` — but require correspondingly
higher-degree block radical inputs (`g = 5` gives the non-integer `k^{10/3}`).

## What is proved (no `sorry`, only Mathlib's three axioms)

* `not_powerful_of_large_g4` : `BlockRadLB4 → 4 ≤ k → k^4 < n → ¬ Powerful (F k n)` — the headline.
* `g4_crude_finiteness` : `BlockRadLB4 → 4 ≤ k → {n | 1 ≤ n ∧ Powerful (F k n)}.Finite`.

The ONLY hypothesis is `BlockRadLB4` (the `g = 4` instance of `BlockRadLBg`); it is a premise, not
an `axiom`, so it does not appear in any axiom footprint.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-- **(H, g = 4) Quartic block radical lower bound (abc-extremal form).** Langevin/abc applied to
each squarefree quartic block `g(m) = m(m+1)(m+2)(m+3)`, assembled over the `⌊k/4⌋` blocks:
`(F k n)^{3/4} ≤ ∏ rad over quartic blocks`. The `g = 4` instance of `BlockRadLBg`; the exponent
`3/4 = (4-1)/4` and the guard `4 ≤ k` matches `g ≤ k`. -/
def BlockRadLB4 : Prop :=
  ∀ k n : ℕ, 4 ≤ k → 1 ≤ n →
    (F k n : ℝ) ^ ((3 : ℝ) / 4) ≤
      ((∏ j ∈ Finset.range (k / 4), rad (F 4 (n + 4 * j)) : ℕ) : ℝ)

/-- `BlockRadLB4` is exactly the `g = 4` instance of the generic `BlockRadLBg` (the exponents
`3/4` and `(4-1)/4` agree, and the guard `4 ≤ k` matches `g ≤ k`). -/
lemma blockRadLB4_iff : BlockRadLB4 ↔ BlockRadLBg 4 := by
  unfold BlockRadLB4 BlockRadLBg
  constructor
  · intro h k n hk hn
    have := h k n hk hn
    rwa [show (((4 : ℕ) : ℝ) - 1) / ((4 : ℕ) : ℝ) = (3 : ℝ) / 4 by norm_num]
  · intro h k n hk hn
    have := h k n hk hn
    rwa [show (((4 : ℕ) : ℝ) - 1) / ((4 : ℕ) : ℝ) = (3 : ℝ) / 4 by norm_num] at this

/-! ## The `g = 4` block objects as literal instances of the generic framework -/

/-- The quartic block product `B4 k n`: the `g = 4` instance of the generic `Bg`. -/
def B4 (k n : ℕ) : ℕ := Bg 4 k n

/-- `overlap4 p` is the number of quartic blocks `p` divides: the `g = 4` instance of `overlapg`. -/
def overlap4 (k n p : ℕ) : ℕ := overlapg 4 k n p

/-- The over-count `W4 k n`: the `g = 4` instance of the generic `Wg`. -/
def W4 (k n : ℕ) : ℕ := Wg 4 k n

/-- **`B4 k n` divides `F k n`** (the `g = 4` instance of `Bg_dvd_F`). -/
lemma B4_dvd_F (k n : ℕ) : B4 k n ∣ F k n := Bg_dvd_F (by norm_num) k n

/-- **Overlap bound (g = 4): `W4 k n ≤ k^k`.** The `g = 4` instance of `Wg_le_pow`. -/
theorem W4_le_pow {k n : ℕ} (hn : 1 ≤ n) : W4 k n ≤ k ^ k :=
  Wg_le_pow (by norm_num) hn

/-! ## The sharp quartic crude headline (threshold `k^4`) -/

/-- **Quartic crude headline.** Under `BlockRadLB4`, for `k ≥ 4` and `n > k^4`, `F k n` is not
powerful. From the crude master inequality `n^2 ≤ k^8` (= `master_ineq_crude_g 4`): `k^4 < n` forces
`k^8 = (k^4)^2 < n^2`, contradiction. -/
theorem not_powerful_of_large_g4 (hBlock : BlockRadLB4) {k n : ℕ}
    (hk : 4 ≤ k) (hn : k ^ 4 < n) : ¬ Powerful (F k n) := by
  intro hPow
  have hn1 : 1 ≤ n := by have : 1 ≤ k ^ 4 := Nat.one_le_pow _ _ (by omega); omega
  have hmaster : n ^ 2 ≤ k ^ 8 := by
    have := master_ineq_crude_g 4 (blockRadLB4_iff.mp hBlock) (by norm_num) hk hn1 hPow
    simpa using this   -- (4-2)=2, 2*4=8
  have hlt : k ^ 8 < n ^ 2 := by
    have h2 : (k ^ 4) ^ 2 < n ^ 2 := Nat.pow_lt_pow_left hn (by norm_num)
    have : (k ^ 4) ^ 2 = k ^ 8 := by ring
    omega
  omega

/-- **Per-`k` finiteness (quartic crude).** For `k ≥ 4` under `BlockRadLB4`,
`{n ≥ 1 : F k n powerful}` is finite (all satisfy `n ≤ k^4`). -/
theorem g4_crude_finiteness (hBlock : BlockRadLB4) {k : ℕ} (hk : 4 ≤ k) :
    {n : ℕ | 1 ≤ n ∧ Powerful (F k n)}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (k ^ 4))
  intro n hn; simp only [Set.mem_setOf_eq] at hn; simp only [Set.mem_Iic]
  by_contra hcon; push Not at hcon
  exact not_powerful_of_large_g4 hBlock hk hcon hn.2

end  -- noncomputable section

end Erdos137
